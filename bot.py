"""Telegram bot engine: long-polling, concurrent per-user dispatch, sales flows, admin actions."""
import asyncio
import html
import io
import json
import logging
import random
import re
import secrets
import time

from panels import get_adapter, PanelError
from tg import TG, TGError

log = logging.getLogger("bot")

FA = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")
EN = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")
TZ = 12600  # Asia/Tehran (+03:30)
PAY_ROLES = ("owner", "full", "pay")
SUP_ROLES = ("owner", "full", "support")
ROUTES = {"buy": "buy", "services": "svc", "renew": "svc", "wallet": "wal", "test": "test",
          "ref": "ref", "help": "help", "support": "sup"}
KIND = {"buy": "خرید سرویس", "renew": "تمدید سرویس", "charge": "شارژ کیف پول"}


def H(s):
    return html.escape(str(s if s is not None else ""))


def fa(x):
    return str(x).translate(FA)


def money(n):
    return fa(f"{int(n or 0):,}").replace(",", "٬") + " تومان"


def gbtxt(v):
    return "نامحدود" if not v else fa("%g" % v) + " گیگ"


def now():
    return int(time.time())


def g2j(gy, gm, gd):
    gdm = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = 355666 + 365 * gy + (gy2 + 3) // 4 - (gy2 + 99) // 100 + (gy2 + 399) // 400 + gd + gdm[gm - 1]
    jy = -1595 + 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm, jd = 1 + days // 31, 1 + days % 31
    else:
        jm, jd = 7 + (days - 186) // 30, 1 + (days - 186) % 30
    return jy, jm, jd


def jdate(ts):
    if not ts:
        return "نامحدود"
    t = time.gmtime(ts + TZ)
    y, m, d = g2j(t.tm_year, t.tm_mon, t.tm_mday)
    return fa(f"{y}/{m:02d}/{d:02d}")


def bar(p, n=10):
    k = max(0, min(n, round(p * n)))
    return "▰" * k + "▱" * (n - k)


def btn(text, data=None, url=None, style=None, web_app=None):
    b = {"text": text}
    if url:
        b["url"] = url
    elif web_app:
        b["web_app"] = {"url": web_app}
    else:
        b["callback_data"] = data
    if style:
        b["style"] = style
    return b


def ik(rows):
    return {"inline_keyboard": [r for r in rows if r]}


def back(to="m", text="بازگشت"):
    return [btn(text, to)]


MAX_RETRIES = 40
RETRY_GAP = [15, 20, 30, 45, 60, 90, 120, 180]  # seconds; about 2 hours in total before refunding


class BotManager:
    def __init__(self, db, session):
        self.db = db
        self.s = session
        self.tg = None
        self.task = None
        self.running = False
        self.me = {}
        self.started = 0
        self.last_error = ""
        self.sem = asyncio.Semaphore(400)
        self.locks = {}
        self.order_locks = {}
        self.rate = {}
        self.join_cache = {}
        self.updates = 0
        self.last_poll = 0
        self.restarts = 0
        self.bc = {"running": False, "total": 0, "sent": 0, "failed": 0, "target": "", "started": 0}
        self.bg = []
        self.health = {}  # server_id -> {"ok", "ms", "err", "at", "fails"}
        self.srv_sem = {}

    # ================================================================ lifecycle
    async def start(self, token=None):
        await self.stop()
        token = token or self.db.get("token")
        if not token:
            return False
        tg = TG(token, self.s)
        try:
            me = await tg.call("getMe")
        except TGError as e:
            self.last_error = str(e)
            return False
        self.tg, self.me = tg, me
        self.db.set("bot_info", {"username": me.get("username"), "name": me.get("first_name"), "id": me["id"]})
        try:
            await tg.call("deleteWebhook", drop_pending_updates=False)
            await tg.call("setMyCommands", commands=[{"command": "start", "description": "منوی اصلی"}])
        except TGError:
            pass
        self.running = True
        self.started = now()
        self.last_error = ""
        self.last_poll = time.monotonic()
        self.task = asyncio.create_task(self.poll())
        log.info("bot @%s started", me.get("username"))
        return True

    async def stop(self):
        self.running = False
        if self.task:
            self.task.cancel()
            try:
                await self.task
            except BaseException:
                pass
        self.task = None

    def status(self):
        return {"running": self.running, "username": self.me.get("username"), "name": self.me.get("first_name"),
                "started": self.started, "error": self.last_error, "updates": self.updates,
                "has_token": bool(self.db.get("token")), "restarts": self.restarts}

    async def poll(self):
        offset = 0
        while self.running:
            try:
                ups = await self.tg.call("getUpdates", offset=offset, timeout=50,
                                         allowed_updates=["message", "callback_query"])
                self.last_poll = time.monotonic()
            except asyncio.CancelledError:
                raise
            except TGError as e:
                self.last_error = str(e)
                if e.code == 401:
                    self.running = False
                    log.error("token rejected by Telegram")
                    break
                await asyncio.sleep(5 if e.code == 409 else 2)
                continue
            except Exception as e:  # noqa
                self.last_error = repr(e)
                await asyncio.sleep(2)
                continue
            for u in ups:
                offset = u["update_id"] + 1
                self.updates += 1
                asyncio.create_task(self.dispatch(u))

    async def dispatch(self, u):
        src = u.get("message") or u.get("callback_query") or {}
        uid = (src.get("from") or {}).get("id")
        if not uid:
            return
        lock = self.locks.get(uid)
        if lock is None:
            lock = self.locks[uid] = asyncio.Lock()
        async with lock:
            async with self.sem:
                try:
                    if "message" in u:
                        await asyncio.wait_for(self.on_message(u["message"]), 90)
                    else:
                        await asyncio.wait_for(self.on_callback(u["callback_query"]), 90)
                except asyncio.TimeoutError:
                    log.warning("handler timeout for %s", uid)
                except TGError as e:
                    log.warning("telegram error for %s: %s", uid, e)
                except Exception:
                    log.exception("handler error")
        if len(self.locks) > 20000:
            self.locks = {k: v for k, v in self.locks.items() if v.locked()}

    # ================================================================ helpers
    def admins(self):
        return self.db.get("admins") or []

    def is_admin(self, uid, roles=None):
        for a in self.admins():
            if str(a.get("id")) == str(uid):
                return roles is None or a.get("role") == "owner" or a.get("role") in roles
        return False

    def T(self, key, **kw):
        t = self.db.get("texts").get(key, "")
        for k, v in kw.items():
            t = t.replace("{" + k + "}", str(v))
        return t

    def tog(self, k):
        return bool(self.db.get("toggles").get(k))

    def user(self, uid):
        return self.db.one("SELECT * FROM users WHERE id=?", uid)

    def set_state(self, uid, st=""):
        self.db.run("UPDATE users SET state=? WHERE id=?", st, uid)

    async def call(self, method, **kw):
        if not self.tg:
            raise TGError(0, "bot offline")
        return await self.tg.call(method, **kw)

    async def send(self, chat, text, kb=None, **kw):
        if not self.tg:
            raise TGError(0, "bot offline")
        try:
            return await self.tg.call("sendMessage", chat_id=chat, text=text, parse_mode="HTML", reply_markup=kb,
                                      link_preview_options={"is_disabled": True}, **kw)
        except TGError as e:
            if "parse" in e.desc or "entities" in e.desc:
                return await self.tg.call("sendMessage", chat_id=chat, text=re.sub(r"<[^>]+>", "", text),
                                          reply_markup=kb, **kw)
            raise

    async def safe_send(self, chat, text, kb=None):
        try:
            return await self.send(chat, text, kb)
        except TGError:
            return None

    async def edit(self, cq, text, kb=None):
        m = cq.get("message") or {}
        chat = (m.get("chat") or {}).get("id") or cq["from"]["id"]
        if not m or m.get("photo") or m.get("document"):
            return await self.send(chat, text, kb)
        try:
            return await self.tg.call("editMessageText", chat_id=chat, message_id=m["message_id"], text=text,
                                      parse_mode="HTML", reply_markup=kb, link_preview_options={"is_disabled": True})
        except TGError as e:
            if "not modified" in e.desc:
                return None
            return await self.send(chat, text, kb)

    async def answer(self, cq, text="", alert=False):
        if cq.get("_a"):
            return
        cq["_a"] = True
        try:
            await self.tg.call("answerCallbackQuery", callback_query_id=cq["id"], text=text or None,
                               show_alert=alert or None)
        except TGError:
            pass

    async def notify_admins(self, text, kb=None, roles=None):
        for a in self.admins():
            if roles and a.get("role") != "owner" and a.get("role") not in roles:
                continue
            await self.safe_send(a["id"], text, kb)

    def spam(self, uid):
        if not self.tog("antispam"):
            return False
        t = time.monotonic()
        r = self.rate.get(uid)
        if not r:
            self.rate[uid] = [t, 1, 0]
            return False
        if r[2] > t:
            return True
        if t - r[0] > 10:
            r[0], r[1] = t, 1
            return False
        r[1] += 1
        if r[1] > 40:
            r[2] = t + 30
            return True
        return False

    def touch(self, frm, ref=None):
        uid = frm["id"]
        u = self.user(uid)
        t = now()
        if not u:
            ref_ok = ref and ref != uid and self.user(ref)
            self.db.run("INSERT OR IGNORE INTO users(id, username, first_name, created, last_seen, ref_by) VALUES(?,?,?,?,?,?)",
                        uid, frm.get("username") or "", frm.get("first_name") or "", t, t, ref if ref_ok else None)
            u = self.user(uid)
            if ref_ok:
                cfg = self.db.get("ref")
                if cfg.get("enabled") and cfg.get("gift"):
                    self.db.run("UPDATE users SET balance=balance+?, ref_earned=ref_earned+? WHERE id=?",
                                int(cfg["gift"]), int(cfg["gift"]), ref)
                    asyncio.create_task(self.safe_send(ref, f"یک زیرمجموعه جدید از طریق لینک شما عضو شد و مبلغ <b>{money(cfg['gift'])}</b> به کیف پول شما اضافه شد."))
            return u, True
        if (u.get("username") or "") != (frm.get("username") or "") or (u.get("first_name") or "") != (frm.get("first_name") or "") or t - (u.get("last_seen") or 0) > 300:
            self.db.run("UPDATE users SET username=?, first_name=?, last_seen=? WHERE id=?",
                        frm.get("username") or "", frm.get("first_name") or "", t, uid)
        return u, False

    def channel_link(self):
        ch = (self.db.get("channel") or "").strip()
        if ch.startswith("http"):
            return ch
        return "https://t.me/" + ch.lstrip("@") if ch.startswith("@") else ""

    async def is_member(self, uid):
        ch = (self.db.get("channel") or "").strip()
        if not ch:
            return True
        c = self.join_cache.get(uid)
        if c and c > time.monotonic():
            return True
        chat = ch if ch.startswith("-") else "@" + ch.split("/")[-1].lstrip("@")
        try:
            m = await self.call("getChatMember", chat_id=chat, user_id=uid)
            ok = m.get("status") in ("member", "administrator", "creator", "restricted")
        except TGError as e:
            log.warning("force join check failed: %s (is the bot admin of the channel?)", e)
            ok = True
        if ok:
            self.join_cache[uid] = time.monotonic() + 600
        return ok

    async def gate(self, uid, u, admin):
        if admin:
            return True
        if u and u.get("banned"):
            await self.safe_send(uid, self.T("banned"))
            return False
        if self.tog("maintenance"):
            await self.safe_send(uid, self.T("maintenance"))
            return False
        if self.tog("force_join") and self.db.get("channel") and not await self.is_member(uid):
            link = self.channel_link()
            await self.safe_send(uid, self.T("join"), ik([[btn("عضویت در کانال", url=link, style="primary")] if link else None,
                                                         [btn("عضو شدم", "join_chk", style="success")]]))
            return False
        if self.tog("phone") and not (u or {}).get("phone"):
            await self.safe_send(uid, self.T("phone"), {"keyboard": [[{"text": "تأیید شماره تلفن", "request_contact": True}]],
                                                         "resize_keyboard": True, "one_time_keyboard": True})
            return False
        return True

    # ================================================================ menu
    def menu_kb(self, admin):
        rows, half = [], []
        for b in self.db.get("buttons"):
            if not b.get("enabled"):
                continue
            if b.get("id") == "test" and not self.tog("test"):
                continue
            st = b.get("style") or None
            if b.get("type") == "link":
                if not b.get("value"):
                    continue
                bb = btn(b["text"], url=b["value"], style=st)
            elif b.get("type") == "text":
                bb = btn(b["text"], "c:" + str(b["id"]), style=st)
            else:
                bb = btn(b["text"], ROUTES.get(b["id"], "m"), style=st)
            if b.get("wide"):
                if half:
                    rows.append(half)
                    half = []
                rows.append([bb])
            else:
                half.append(bb)
                if len(half) == 2:
                    rows.append(half)
                    half = []
        if half:
            rows.append(half)
        if admin:
            url = self.db.get("panel_url") or ""
            if url.startswith("https://"):
                rows.append([btn("پنل مدیریت", web_app=url, style="primary")])
            elif url:
                rows.append([btn("پنل مدیریت", url=url, style="primary")])
        return ik(rows)

    async def menu(self, uid, u, admin, cq=None):
        text = self.T("welcome", name=H((u or {}).get("first_name") or "کاربر"))
        kb = self.menu_kb(admin)
        if cq:
            await self.edit(cq, text, kb)
        else:
            await self.send(uid, text, kb)

    # ================================================================ messages
    async def on_message(self, m):
        if (m.get("chat") or {}).get("type") != "private":
            return
        frm = m["from"]
        uid = frm["id"]
        text = (m.get("text") or "").strip()
        ref = None
        if text.startswith("/start"):
            arg = text[6:].strip()
            if arg.startswith("ref_") and arg[4:].isdigit():
                ref = int(arg[4:])
        u, _ = self.touch(frm, ref)
        admin = self.is_admin(uid)
        if not admin and self.spam(uid):
            return
        if m.get("contact"):
            c = m["contact"]
            if c.get("user_id") == uid:
                self.db.run("UPDATE users SET phone=? WHERE id=?", c.get("phone_number"), uid)
                u = self.user(uid)
                await self.send(uid, "شماره شما تأیید شد.", {"remove_keyboard": True})
                if await self.gate(uid, u, admin):
                    await self.menu(uid, u, admin)
            return
        if not await self.gate(uid, u, admin):
            return
        state = u.get("state") or ""
        if text.startswith("/start") or text == "/menu":
            if state:
                self.set_state(uid)
            return await self.menu(uid, u, admin)
        if admin and text == "/panel":
            url = self.db.get("panel_url") or ""
            kb = ik([[btn("ورود به پنل مدیریت", web_app=url, style="primary") if url.startswith("https://") else btn("ورود به پنل مدیریت", url=url or "https://t.me")]])
            return await self.send(uid, "<b>پنل مدیریت</b>", kb)
        if admin and text == "/stats":
            return await self.send(uid, self.stats_text())
        if m.get("photo") or (m.get("document") and (str(m["document"].get("mime_type", "")).startswith("image")
                                                      or str(m["document"].get("mime_type", "")) == "application/pdf")):
            if state.startswith("receipt:"):
                return await self.receipt(uid, m, int(state.split(":")[1]))
            # the customer pressed another button before sending the receipt: still accept it for the open order
            o = self.db.one("SELECT id FROM orders WHERE user_id=? AND status='await_receipt' AND created>? ORDER BY id DESC LIMIT 1",
                            uid, now() - 86400 * 2)
            if o:
                return await self.receipt(uid, m, o["id"])
        if state:
            return await self.on_state(uid, u, admin, state, m, text)
        await self.menu(uid, u, admin)

    def stats_text(self):
        d = self.db
        ds = (now() + TZ) // 86400 * 86400 - TZ
        return ("<b>آمار سریع</b>\n\n"
                f"کاربران: <b>{fa(d.val('SELECT COUNT(*) FROM users'))}</b>\n"
                f"کاربران جدید امروز: <b>{fa(d.val('SELECT COUNT(*) FROM users WHERE created>=?', ds))}</b>\n"
                f"سرویس‌های فعال: <b>{fa(d.val('SELECT COUNT(*) FROM services WHERE status=?', 'active'))}</b>\n"
                f"فروش امروز: <b>{money(d.val('SELECT COALESCE(SUM(amount),0) FROM orders WHERE status IN (?,?) AND kind!=? AND handled_at>=?', 'approved', 'paid', 'charge', ds))}</b>\n"
                f"رسیدهای در انتظار: <b>{fa(d.val('SELECT COUNT(*) FROM orders WHERE status=?', 'pending'))}</b>")

    async def on_state(self, uid, u, admin, state, m, text):
        if state.startswith("receipt:"):
            return await self.send(uid, "لطفاً <b>تصویر رسید</b> پرداخت را ارسال کنید.", ik([[btn("انصراف", "x", style="danger")]]))
        if not text:
            return await self.send(uid, "لطفاً پیام متنی ارسال کنید.")
        if state.startswith("disc:"):
            self.set_state(uid)
            return await self.apply_discount(uid, int(state.split(":")[1]), text)
        if state == "charge":
            n = re.sub(r"[^\d]", "", text.translate(EN))
            amount = int(n) if n else 0
            mn, mx = int(self.db.get("min_charge")), int(self.db.get("max_charge"))
            if amount < mn or amount > mx:
                return await self.send(uid, f"مبلغ باید بین <b>{money(mn)}</b> و <b>{money(mx)}</b> باشد. دوباره ارسال کنید:",
                                       ik([[btn("انصراف", "x", style="danger")]]))
            self.set_state(uid)
            oid = self.db.run("INSERT INTO orders(user_id, kind, base_amount, amount, status, created) VALUES(?,?,?,?,?,?)",
                              uid, "charge", amount, amount, "draft", now())
            return await self.card_pay(uid, oid)
        if state == "ticket" or state.startswith("ticket:"):
            self.set_state(uid)
            t = now()
            if state == "ticket":
                tid = self.db.run("INSERT INTO tickets(user_id, subject, status, created, updated) VALUES(?,?,?,?,?)",
                                  uid, text[:60], "open", t, t)
            else:
                tid = int(state.split(":")[1])
                self.db.run("UPDATE tickets SET status='open', updated=? WHERE id=? AND user_id=?", t, tid, uid)
            self.db.run("INSERT INTO ticket_msgs(ticket_id, sender, text, created) VALUES(?,?,?,?)", tid, "u", text[:3500], t)
            await self.send(uid, self.T("ticket_ok", id=fa(tid)), ik([back()]))
            uname = f" (@{H(u.get('username'))})" if u.get("username") else ""
            return await self.notify_admins(
                f"<b>تیکت {fa(tid)}</b> | {H(u.get('first_name'))}{uname}\n<code>{uid}</code>\n\n<blockquote>{H(text[:3500])}</blockquote>",
                ik([[btn("پاسخ", f"adm:tr:{tid}", style="primary")]]), SUP_ROLES)
        if state.startswith("treply:") and admin:
            self.set_state(uid)
            ok = await self.ticket_reply(int(state.split(":")[1]), text)
            return await self.send(uid, "پاسخ برای کاربر ارسال شد." if ok else "ارسال پاسخ ناموفق بود.")
        self.set_state(uid)
        await self.menu(uid, u, admin)

    async def ticket_reply(self, tid, text):
        tk = self.db.one("SELECT * FROM tickets WHERE id=?", tid)
        if not tk:
            return False
        t = now()
        self.db.run("INSERT INTO ticket_msgs(ticket_id, sender, text, created) VALUES(?,?,?,?)", tid, "a", text, t)
        self.db.run("UPDATE tickets SET status='answered', updated=? WHERE id=?", t, tid)
        r = await self.safe_send(tk["user_id"], f"<b>پاسخ پشتیبانی</b> | تیکت {fa(tid)}\n\n<blockquote>{H(text)}</blockquote>",
                                 ik([[btn("ارسال پاسخ", f"tr:{tid}", style="primary")], back("m", "منوی اصلی")]))
        return r is not None

    # ================================================================ callbacks
    async def on_callback(self, cq):
        frm = cq["from"]
        uid = frm["id"]
        d = cq.get("data") or ""
        u, _ = self.touch(frm)
        admin = self.is_admin(uid)
        try:
            if not admin and self.spam(uid):
                return await self.answer(cq, "لطفاً کمی آهسته‌تر")
            if d.startswith("adm:"):
                if admin:
                    await self.admin_cb(cq, uid, d)
                return
            if d == "join_chk":
                self.join_cache.pop(uid, None)
                if await self.is_member(uid):
                    await self.answer(cq, "عضویت شما تأیید شد")
                    return await self.menu(uid, u, admin, cq)
                return await self.answer(cq, "هنوز در کانال عضو نشده‌اید", True)
            if not await self.gate(uid, u, admin):
                return
            st = u.get("state") or ""
            if st:
                if st.startswith("receipt:") and d in ("x", "m"):
                    # customer cancelled the payment: the order no longer waits for a receipt
                    self.db.run("UPDATE orders SET status='draft' WHERE id=? AND user_id=? AND status='await_receipt'", int(st.split(":")[1]), uid)
                self.set_state(uid)
            await self.route(cq, uid, u, admin, d)
        finally:
            await self.answer(cq)

    async def route(self, cq, uid, u, admin, d):
        p = d.split(":")
        k = p[0]
        if k in ("m", "x"):
            return await self.menu(uid, u, admin, cq)
        if k == "buy":
            return await self.show_buy(cq)
        if k == "cat":
            return await self.show_plans(cq, uid, u, p[1])
        if k == "p":
            return await self.new_order(cq, uid, u, "buy", int(p[1]))
        if k == "rp":
            return await self.new_order(cq, uid, u, "renew", int(p[2]), int(p[1]))
        if k == "pw":
            return await self.wallet_pay(cq, uid, int(p[1]))
        if k == "pc":
            return await self.card_pay(uid, int(p[1]), cq)
        if k == "pd":
            self.set_state(uid, f"disc:{p[1]}")
            return await self.edit(cq, "کد تخفیف خود را ارسال کنید:", ik([[btn("انصراف", f"po:{p[1]}", style="danger")]]))
        if k == "po":
            return await self.show_order(cq, uid, int(p[1]))
        if k == "svc":
            return await self.show_services(cq, uid)
        if k == "s":
            await self.answer(cq, "در حال دریافت اطلاعات...")
            return await self.show_service(cq, uid, int(p[1]))
        if k == "sq":
            return await self.send_qr(cq, uid, int(p[1]))
        if k == "sr":
            return await self.show_renew(cq, uid, u, int(p[1]))
        if k == "wal":
            return await self.edit(cq, self.T("wallet", balance=money(u.get("balance"))),
                                   ik([[btn("افزایش موجودی", "chg", style="success")], back()]))
        if k == "chg":
            if not self.db.get("pay_methods").get("card"):
                return await self.answer(cq, "شارژ کیف پول در حال حاضر غیرفعال است", True)
            self.set_state(uid, "charge")
            return await self.edit(cq, self.T("charge_ask", min=money(self.db.get("min_charge"))),
                                   ik([[btn("انصراف", "x", style="danger")]]))
        if k == "test":
            return await self.test_account(cq, uid, u)
        if k == "ref":
            cfg = self.db.get("ref")
            if not cfg.get("enabled"):
                return await self.answer(cq, "سیستم زیرمجموعه‌گیری فعال نیست", True)
            link = f"https://t.me/{self.me.get('username')}?start=ref_{uid}"
            cnt = self.db.val("SELECT COUNT(*) FROM users WHERE ref_by=?", uid)
            return await self.edit(cq, self.T("ref", percent=fa(cfg.get("percent", 0)), count=fa(cnt),
                                              earned=money(u.get("ref_earned")), link=link),
                                   ik([[btn("اشتراک‌گذاری لینک", url="https://t.me/share/url?url=" + link, style="primary")], back()]))
        if k == "help":
            return await self.edit(cq, self.T("help"), ik([back()]))
        if k == "sup":
            sup = (self.db.get("support") or "").strip().lstrip("@")
            return await self.edit(cq, self.T("support"), ik([[btn("ثبت تیکت جدید", "tnew", style="primary")],
                                                               [btn("پشتیبانی مستقیم", url="https://t.me/" + sup)] if sup else None,
                                                               back()]))
        if k == "tnew":
            self.set_state(uid, "ticket")
            return await self.edit(cq, self.T("ticket_ask"), ik([[btn("انصراف", "x", style="danger")]]))
        if k == "tr":
            self.set_state(uid, f"ticket:{p[1]}")
            return await self.send(uid, self.T("ticket_ask"), ik([[btn("انصراف", "x", style="danger")]]))
        if k == "c":
            for b in self.db.get("buttons"):
                if str(b.get("id")) == p[1]:
                    return await self.edit(cq, b.get("value") or "-", ik([back()]))
        return await self.menu(uid, u, admin, cq)

    # ================================================================ buying
    def price_for(self, u, plan):
        price = int(plan["price"])
        if u.get("is_reseller") and self.tog("reseller"):
            disc = u.get("reseller_discount") or self.db.get("reseller_discount") or 0
            price = int(price * (100 - int(disc)) / 100)
        return price

    def plans(self):
        return self.db.all("SELECT * FROM plans WHERE active=1 ORDER BY sort, price")

    def categories(self):
        cats = []
        for p in self.plans():
            c = p.get("category") or ""
            if c not in cats:
                cats.append(c)
        return cats

    async def show_buy(self, cq):
        cats = self.categories()
        if not cats:
            return await self.edit(cq, "در حال حاضر پلنی برای فروش وجود ندارد.", ik([back()]))
        if len(cats) == 1:
            return await self.show_plans(cq, cq["from"]["id"], self.user(cq["from"]["id"]), "0")
        rows = [[btn(c or "سایر پلن‌ها", f"cat:{i}", style="primary")] for i, c in enumerate(cats)]
        await self.edit(cq, self.T("buy"), ik(rows + [back()]))

    async def show_plans(self, cq, uid, u, idx):
        cats = self.categories()
        i = int(idx) if str(idx).isdigit() else 0
        cat = cats[i] if i < len(cats) else ""
        rows = [[btn(f"{p['name']} | {money(self.price_for(u, p))}", f"p:{p['id']}")] for p in self.plans()
                if (p.get("category") or "") == cat]
        await self.edit(cq, self.T("buy"), ik(rows + [back("buy" if len(cats) > 1 else "m")]))

    async def show_renew(self, cq, uid, u, sid):
        svc = self.db.one("SELECT * FROM services WHERE id=? AND user_id=?", sid, uid)
        if not svc:
            return await self.edit(cq, "سرویس یافت نشد.", ik([back("svc")]))
        srv = self.db.one("SELECT type FROM servers WHERE id=?", svc["server_id"])
        if not srv or srv["type"] == "stock":
            return await self.edit(cq, "تمدید خودکار برای این سرویس امکان‌پذیر نیست. لطفاً یک سرویس جدید خریداری کنید.",
                                   ik([[btn("خرید سرویس", "buy", style="success")], back("svc")]))
        rows = [[btn(f"{p['name']} | {money(self.price_for(u, p))}", f"rp:{sid}:{p['id']}")] for p in self.plans()
                if not p.get("server_id") or p["server_id"] == svc["server_id"]]
        await self.edit(cq, f"<b>تمدید سرویس</b> {H(svc['plan_name'])}\n\nپلن تمدید را انتخاب کنید:", ik(rows + [back(f"s:{sid}")]))

    async def new_order(self, cq, uid, u, kind, pid, sid=None):
        plan = self.db.one("SELECT * FROM plans WHERE id=? AND active=1", pid)
        if not plan:
            return await self.edit(cq, "این پلن در دسترس نیست.", ik([back("buy")]))
        if kind == "renew" and not self.db.one("SELECT id FROM services WHERE id=? AND user_id=?", sid, uid):
            return await self.edit(cq, "سرویس یافت نشد.", ik([back("svc")]))
        price = self.price_for(u, plan)
        oid = self.db.run("INSERT INTO orders(user_id, kind, plan_id, plan_name, service_id, base_amount, amount, status, created) VALUES(?,?,?,?,?,?,?,?,?)",
                          uid, kind, pid, plan["name"], sid, price, price, "draft", now())
        await self.show_order(cq, uid, oid)

    async def show_order(self, cq, uid, oid, msg=None):
        o = self.db.one("SELECT * FROM orders WHERE id=? AND user_id=?", oid, uid)
        if not o or o["status"] != "draft":
            return await self.edit(cq, "این سفارش منقضی شده است.", ik([back()])) if cq else None
        plan = self.db.one("SELECT * FROM plans WHERE id=?", o["plan_id"]) or {}
        u = self.user(uid)
        price = money(o["amount"])
        if o["amount"] != o["base_amount"]:
            price = f"<s>{money(o['base_amount'])}</s>  <b>{money(o['amount'])}</b>"
        else:
            price = f"<b>{price}</b>"
        lines = [f"<b>{H(plan.get('name'))}</b>" + (" | تمدید" if o["kind"] == "renew" else ""), "",
                 f"<blockquote>حجم: {gbtxt(plan.get('volume_gb'))}\nمدت: {fa(plan.get('days'))} روز\nتعداد کاربر: {fa(plan.get('users_limit') or 1)}</blockquote>",
                 f"مبلغ قابل پرداخت: {price}", f"موجودی کیف پول: {money(u.get('balance'))}"]
        if o.get("discount_code"):
            lines.append(f"کد تخفیف: <code>{H(o['discount_code'])}</code>")
        if msg:
            lines += ["", msg]
        if self.tog("rules"):
            lines += ["", f"<i>{self.T('rules')}</i>"]
        pm = self.db.get("pay_methods")
        rows = []
        if o["amount"] == 0:
            rows.append([btn("دریافت رایگان", f"pw:{oid}", style="success")])
        else:
            if pm.get("wallet"):
                rows.append([btn("پرداخت از کیف پول", f"pw:{oid}", style="success")])
            if pm.get("card") and self.db.val("SELECT COUNT(*) FROM cards WHERE active=1"):
                rows.append([btn("کارت به کارت", f"pc:{oid}", style="primary")])
        if not o.get("discount_code"):
            rows.append([btn("کد تخفیف دارم", f"pd:{oid}")])
        rows.append(back("buy" if o["kind"] == "buy" else f"sr:{o['service_id']}"))
        text = "\n".join(lines)
        if cq:
            await self.edit(cq, text, ik(rows))
        else:
            await self.send(uid, text, ik(rows))

    async def apply_discount(self, uid, oid, code):
        code = code.strip().upper()
        dc = self.db.one("SELECT * FROM discounts WHERE code=? AND active=1", code)
        msg = None
        if not dc or (dc["max_uses"] and dc["used"] >= dc["max_uses"]) or (dc["expire_at"] and dc["expire_at"] < now()):
            msg = "کد تخفیف نامعتبر یا منقضی شده است."
        else:
            o = self.db.one("SELECT * FROM orders WHERE id=? AND user_id=? AND status='draft'", oid, uid)
            if o:
                amount = max(0, int(o["base_amount"] * (100 - min(100, int(dc["percent"]))) / 100))
                self.db.run("UPDATE orders SET amount=?, discount_code=? WHERE id=?", amount, code, oid)
                msg = f"کد تخفیف {fa(dc['percent'])} درصدی اعمال شد."
        await self.show_order(None, uid, oid, msg)

    async def wallet_pay(self, cq, uid, oid):
        o = self.db.one("SELECT * FROM orders WHERE id=? AND user_id=?", oid, uid)
        if not o or o["status"] != "draft":
            return await self.answer(cq, "این سفارش قبلاً پرداخت شده یا منقضی شده است", True)
        amt = max(0, int(o["amount"]))

        def pay(c):  # balance and order change together or not at all
            if amt and not c.execute("UPDATE users SET balance=balance-? WHERE id=? AND balance>=?", (amt, uid, amt)).rowcount:
                return "low"
            if not c.execute("UPDATE orders SET status='paid', method='wallet', handled_at=?, handled_by='wallet', retry_at=? WHERE id=? AND status='draft'",
                             (now(), now() + 180 if o["kind"] in ("buy", "renew") else 0, oid)).rowcount:
                return None
            return "ok"
        r = self.db.tx(pay)
        if r != "ok":
            if r is None:
                return await self.answer(cq, "این سفارش قبلاً پرداخت شده یا منقضی شده است", True)
            await self.answer(cq, "موجودی کیف پول کافی نیست", True)
            return await self.edit(cq, f"موجودی کیف پول شما برای این خرید کافی نیست.\nمبلغ: <b>{money(amt)}</b>",
                                   ik([[btn("افزایش موجودی", "chg", style="success")],
                                       [btn("کارت به کارت", f"pc:{oid}", style="primary")] if self.db.get("pay_methods").get("card") else None,
                                       back()]))
        await self.answer(cq, "در حال آماده‌سازی سرویس...")
        await self.edit(cq, "در حال آماده‌سازی سرویس شما، چند لحظه صبر کنید...")
        await self.fulfil(oid)

    async def card_pay(self, uid, oid, cq=None):
        o = self.db.one("SELECT * FROM orders WHERE id=? AND user_id=?", oid, uid)
        if not o or o["status"] not in ("draft", "await_receipt"):
            return await self.safe_send(uid, "این سفارش منقضی شده است.")
        cards = self.db.all("SELECT * FROM cards WHERE active=1")
        if not cards:
            return await self.safe_send(uid, "در حال حاضر پرداخت کارت به کارت در دسترس نیست.")
        card = random.choice(cards) if self.tog("card_rotate") else cards[0]
        self.db.run("UPDATE orders SET status='await_receipt', method='card', card=? WHERE id=?", card["number"], oid)
        self.set_state(uid, f"receipt:{oid}")
        text = self.T("pay_card", amount=money(o["amount"]), card=H(card["number"]), owner=H(card["owner"]),
                      bank=f"({H(card['bank'])})" if card.get("bank") else "")
        kb = ik([[btn("انصراف", "x", style="danger")]])
        if cq:
            await self.edit(cq, text, kb)
        else:
            await self.send(uid, text, kb)

    def receipt_caption(self, o, extra=""):
        u = self.user(o["user_id"]) or {}
        un = f" (@{H(u.get('username'))})" if u.get("username") else ""
        lines = [f"<b>رسید جدید | سفارش {fa(o['id'])}</b>", "",
                 f"کاربر: {H(u.get('first_name'))}{un}", f"آیدی: <code>{o['user_id']}</code>",
                 f"نوع: {KIND.get(o['kind'], o['kind'])}"]
        if o.get("plan_name"):
            lines.append(f"پلن: {H(o['plan_name'])}")
        lines += [f"مبلغ: <b>{money(o['amount'])}</b>", f"کارت مقصد: <code>{H(o.get('card'))}</code>"]
        if extra:
            lines += ["", extra]
        return "\n".join(lines)

    async def receipt(self, uid, m, oid):
        o = self.db.one("SELECT * FROM orders WHERE id=? AND user_id=? AND status='await_receipt'", oid, uid)
        self.set_state(uid)
        if not o:
            return await self.send(uid, "این سفارش منقضی شده است.")
        if m.get("photo"):
            fid, ftype = m["photo"][-1]["file_id"], "photo"
        else:
            fid, ftype = m["document"]["file_id"], "document"
        self.db.run("UPDATE orders SET status='pending', receipt=?, receipt_type=?, created=? WHERE id=?", fid, ftype, now(), oid)
        await self.safe_send(uid, self.T("receipt_ok", id=fa(oid)), ik([back("m", "منوی اصلی")]))
        o = self.db.one("SELECT * FROM orders WHERE id=?", oid)
        kb = ik([[btn("تأیید", f"adm:ok:{oid}", style="success"), btn("رد", f"adm:no:{oid}", style="danger")]])
        msgs = []
        for a in self.admins():
            if a.get("role") not in PAY_ROLES:
                continue
            try:
                method = "sendPhoto" if ftype == "photo" else "sendDocument"
                r = await self.call(method, chat_id=a["id"], caption=self.receipt_caption(o), parse_mode="HTML",
                                    reply_markup=kb, **{ftype: fid})
                msgs.append([a["id"], r["message_id"]])
            except TGError as e:
                log.warning("receipt to admin %s failed: %s", a["id"], e)
                if e.code == 403:
                    continue  # this admin has not started the bot
                try:  # fall back to a text message so the approve buttons always reach the admin
                    r = await self.send(a["id"], self.receipt_caption(o, "تصویر رسید در پنل مدیریت قابل مشاهده است."), kb)
                    msgs.append([a["id"], r["message_id"], "t"])
                except TGError:
                    pass
        self.db.run("UPDATE orders SET admin_msgs=? WHERE id=?", json.dumps(msgs), oid)

    async def _mark_bg(self, o, line):
        try:
            await self.mark_admin_msgs(o, line)
        except Exception:  # noqa
            log.exception("mark admin msgs")

    async def mark_admin_msgs(self, o, line, kb=None):
        for item in json.loads(o.get("admin_msgs") or "[]"):
            chat, mid = item[0], item[1]
            text_msg = len(item) > 2
            try:
                if text_msg:
                    await self.call("editMessageText", chat_id=chat, message_id=mid, text=self.receipt_caption(o, line),
                                    parse_mode="HTML", reply_markup=kb or {"inline_keyboard": []})
                else:
                    await self.call("editMessageCaption", chat_id=chat, message_id=mid,
                                    caption=self.receipt_caption(o, line), parse_mode="HTML", reply_markup=kb or {"inline_keyboard": []})
            except TGError:
                pass

    async def admin_cb(self, cq, uid, d):
        p = d.split(":")
        if p[1] in ("ok", "no"):
            if not self.is_admin(uid, PAY_ROLES):
                return await self.answer(cq, "دسترسی تأیید پرداخت ندارید", True)
            name = cq["from"].get("first_name") or str(uid)
            if p[1] == "ok":
                await self.answer(cq, "در حال پردازش...")
                ok, msg = await self.approve(int(p[2]), name)
            else:
                ok, msg = await self.reject(int(p[2]), name)
            return await self.answer(cq, msg)
        if p[1] == "tr":
            if not self.is_admin(uid, SUP_ROLES):
                return await self.answer(cq, "دسترسی پاسخ به تیکت ندارید", True)
            self.set_state(uid, f"treply:{p[2]}")
            return await self.send(uid, f"پاسخ تیکت {fa(p[2])} را بنویسید:", ik([[btn("انصراف", "x", style="danger")]]))

    # ================================================================ order processing
    async def approve(self, oid, by="panel"):
        lock = self.order_locks.setdefault(oid, asyncio.Lock())
        async with lock:
            o = self.db.one("SELECT * FROM orders WHERE id=?", oid)
            if not o or o["status"] != "pending":
                return False, "این سفارش قبلاً بررسی شده است"
            # retry_at is a safety net: if the process restarts mid-delivery, the queue finishes the job
            if not self.db.exec("UPDATE orders SET status='approved', handled_by=?, handled_at=?, retry_at=? WHERE id=? AND status='pending'",
                                by, now(), now() + 180 if o["kind"] in ("buy", "renew") else 0, oid):
                return False, "این سفارش قبلاً بررسی شده است"
            ok = await self.fulfil(oid)  # the customer gets the config first, admin messages are updated afterwards
            line = {True: "تأیید شد و سرویس تحویل داده شد", None: "تأیید شد؛ سرویس در صف تحویل خودکار است"}.get(ok, "تأیید شد اما تحویل ناموفق بود و مبلغ به کیف پول برگشت")
            asyncio.create_task(self._mark_bg(o, f"وضعیت: <b>{line}</b> | توسط {H(by)}"))
        self.order_locks.pop(oid, None)
        return True, ("سفارش تأیید و سرویس تحویل داده شد" if ok else "سفارش تأیید شد؛ پنل موقتاً جواب نداد و ربات خودکار دوباره تلاش می‌کند" if ok is None
                      else "سفارش تأیید شد اما تحویل سرویس ناموفق بود و مبلغ به کیف پول کاربر برگشت")

    async def reject(self, oid, by="panel", reason=""):
        lock = self.order_locks.setdefault(oid, asyncio.Lock())
        async with lock:
            o = self.db.one("SELECT * FROM orders WHERE id=?", oid)
            if not o or o["status"] != "pending" or not self.db.exec(
                    "UPDATE orders SET status='rejected', handled_by=?, handled_at=?, note=? WHERE id=? AND status='pending'", by, now(), reason, oid):
                return False, "این سفارش قبلاً بررسی شده است"
        self.order_locks.pop(oid, None)
        await self.mark_admin_msgs(o, f"وضعیت: <b>رد شد</b> توسط {H(by)}")
        text = self.T("rejected", id=fa(oid)) + (f"\n\nعلت: {H(reason)}" if reason else "")
        await self.safe_send(o["user_id"], text, ik([back("m", "منوی اصلی")]))
        self.db.log(f"رد سفارش {oid} توسط {by}")
        return True, "سفارش رد شد"

    async def fulfil(self, oid):
        o = self.db.one("SELECT * FROM orders WHERE id=?", oid)
        uid = o["user_id"]
        try:
            if o["kind"] == "charge":
                self.db.run("UPDATE users SET balance=balance+? WHERE id=?", o["amount"], uid)
                u = self.user(uid)
                await self.safe_send(uid, self.T("charged", amount=money(o["amount"]), balance=money(u["balance"])),
                                     ik([[btn("خرید سرویس", "buy", style="success")], back("m", "منوی اصلی")]))
            elif o["kind"] == "buy":
                plan = self.db.one("SELECT * FROM plans WHERE id=?", o["plan_id"])
                if not plan:
                    raise PanelError("پلن حذف شده است")
                svc = self.db.one("SELECT * FROM services WHERE id=?", o["service_id"]) if o.get("service_id") else None
                if not svc:  # never build a second config for the same order (e.g. after a restart)
                    svc = await self.provision(uid, plan, o["amount"])
                    self.db.run("UPDATE orders SET service_id=? WHERE id=?", svc["id"], oid)
                await self.deliver(uid, svc)
            elif o["kind"] == "renew":
                plan = self.db.one("SELECT * FROM plans WHERE id=?", o["plan_id"])
                svc = self.db.one("SELECT * FROM services WHERE id=?", o["service_id"])
                if not plan or not svc:
                    raise PanelError("سرویس یا پلن یافت نشد")
                await self.renew_service(svc, plan)
                svc = self.db.one("SELECT * FROM services WHERE id=?", svc["id"])
                await self.safe_send(uid, self.T("renewed", plan=H(plan["name"]), volume=gbtxt(plan["volume_gb"]),
                                                 expire=jdate(svc["expire_at"])), ik([[btn("مشاهده سرویس", f"s:{svc['id']}", style="primary")]]))
        except (PanelError, asyncio.TimeoutError) as e:
            e = e if isinstance(e, PanelError) else PanelError("پنل در زمان مقرر جواب نداد")
            n = int(o.get("retries") or 0)
            if o["kind"] in ("buy", "renew") and n < MAX_RETRIES:
                # never lose a paid order: keep it in the delivery queue and retry automatically
                self.db.run("UPDATE orders SET retries=?, retry_at=?, note=? WHERE id=?", n + 1, now() + RETRY_GAP[min(n, len(RETRY_GAP) - 1)], str(e)[:300], oid)
                if n == 0:
                    await self.safe_send(uid, "پرداخت شما ثبت شد و سرویس در صف آماده‌سازی است. به محض آماده شدن، به صورت خودکار برایتان ارسال می‌شود و نیازی به پرداخت دوباره نیست.",
                                         ik([back("m", "منوی اصلی")]))
                    await self.notify_admins(f"<b>تأخیر در تحویل سفارش {fa(oid)}</b>\n\n{H(e)}\n\nربات به صورت خودکار دوباره تلاش می‌کند.", roles=PAY_ROLES)
                self.db.log(f"تحویل سفارش {oid} به صف تلاش مجدد رفت: {e}")
                return None
            self.db.run("UPDATE orders SET status='failed', retry_at=0, note=? WHERE id=?", str(e)[:300], oid)
            if o["amount"]:
                self.db.run("UPDATE users SET balance=balance+? WHERE id=?", o["amount"], uid)
            await self.safe_send(uid, "متأسفانه در آماده‌سازی سرویس مشکلی پیش آمد. مبلغ پرداختی به کیف پول شما برگشت داده شد و می‌توانید دوباره تلاش کنید.",
                                 ik([back("m", "منوی اصلی")]))
            await self.notify_admins(f"<b>خطا در تحویل سفارش {fa(oid)}</b>\n\n{H(e)}\n\nمبلغ به کیف پول کاربر <code>{uid}</code> برگشت داده شد.", roles=PAY_ROLES)
            self.db.log(f"خطا در تحویل سفارش {oid}: {e}")
            return False
        if o.get("retry_at"):
            self.db.run("UPDATE orders SET retry_at=0, note=NULL WHERE id=?", oid)
        if o.get("discount_code"):
            self.db.run("UPDATE discounts SET used=used+1 WHERE code=?", o["discount_code"])
        if o["kind"] in ("buy", "renew") and o["amount"]:
            await self.referral_reward(uid, o["amount"])
        self.db.log(f"سفارش {oid} ({KIND.get(o['kind'])}) با موفقیت انجام شد")
        return True

    async def referral_reward(self, uid, amount):
        cfg = self.db.get("ref")
        u = self.user(uid)
        if not cfg.get("enabled") or not u or not u.get("ref_by"):
            return
        r = int(amount * int(cfg.get("percent") or 0) / 100)
        if r <= 0:
            return
        self.db.run("UPDATE users SET balance=balance+?, ref_earned=ref_earned+? WHERE id=?", r, r, u["ref_by"])
        await self.safe_send(u["ref_by"], f"از خرید زیرمجموعه شما مبلغ <b>{money(r)}</b> به کیف پول شما اضافه شد.")

    def candidates(self, server_id=None, any_server=False):
        """Servers to try, best first: healthy and least loaded, then the rest as fallback."""
        rows = self.db.all("""SELECT s.*, (SELECT COUNT(*) FROM services v WHERE v.server_id=s.id AND v.status='active') used,
                              (SELECT COUNT(*) FROM stock k WHERE k.server_id=s.id AND k.used_by IS NULL) free
                              FROM servers s WHERE s.active=1""")
        ok = [r for r in rows if (not r["capacity"] or r["used"] < r["capacity"]) and (r["type"] != "stock" or r["free"] > 0)]
        load = lambda r: r["used"] / r["capacity"] if r["capacity"] else r["used"] / 100000
        bad = lambda r: 1 if (self.health.get(r["id"]) or {}).get("ok") is False else 0
        ok.sort(key=lambda r: (bad(r), load(r)))
        if server_id:
            pinned = [r for r in ok if r["id"] == int(server_id)]
            return pinned + ([r for r in ok if r["id"] != int(server_id)] if any_server else [])
        return ok

    def pick_server(self, server_id=None):
        c = self.candidates(server_id)
        return c[0] if c else None

    def _mark(self, sid, ok, ms=0, err=""):
        h = self.health.setdefault(sid, {"fails": 0})
        h.update(ok=ok, ms=ms, err=err[:200], at=now(), fails=0 if ok else h.get("fails", 0) + 1)

    async def _create_on(self, srv, uid, name, plan):
        if srv["type"] == "stock":
            row = self.db.one("SELECT id, config FROM stock WHERE server_id=? AND used_by IS NULL ORDER BY id LIMIT 1", srv["id"])
            if not row or not self.db.exec("UPDATE stock SET used_by=?, used_at=? WHERE id=? AND used_by IS NULL", uid, now(), row["id"]):
                raise PanelError("موجودی کانفیگ این سرور تمام شده است")
            return {"link": row["config"], "meta": {"stock_id": row["id"], "name": name}}
        sem = self.srv_sem.setdefault(srv["id"], asyncio.Semaphore(16))  # protects the panel from bursts
        async with sem:
            t0 = time.monotonic()
            res = await asyncio.wait_for(get_adapter(srv, self.s).create(
                name, float(plan.get("volume_gb") or 0), int(plan.get("days") or 0), int(plan.get("users_limit") or 1)), 22)
            self._mark(srv["id"], True, int((time.monotonic() - t0) * 1000))
            if not res.get("link"):
                raise PanelError("پنل کاربر را ساخت ولی لینک اتصال برنگرداند")
            return res

    async def provision(self, uid, plan, price=0, any_server=False):
        servers = self.candidates(plan.get("server_id"), any_server)
        if not servers:
            raise PanelError("سرور فعال با ظرفیت خالی وجود ندارد")
        srv, res, name, last = None, None, "", None
        tries = 3 if len(servers) == 1 else 2
        for srv in servers[:5]:
            for attempt in range(1 if srv["type"] == "stock" else tries):
                name = f"u{uid}_{secrets.token_hex(3)}"
                try:
                    res = await self._create_on(srv, uid, name, plan)
                    break
                except (PanelError, asyncio.TimeoutError) as e:
                    last = e if isinstance(e, PanelError) else PanelError("پنل در زمان مقرر جواب نداد")
                    if srv["type"] == "stock":
                        break
                    self._mark(srv["id"], False, err=str(last))
                    if "ورود به پنل ناموفق" in str(last) or (len(servers) > 1 and ("برقرار نشد" in str(last) or "جواب نداد" in str(last))):
                        break  # dead panel or wrong credentials: jump straight to the next server
                    await asyncio.sleep(0.6 * (attempt + 1))
            if res:
                break
        if not res:
            raise last or PanelError("ساخت سرویس ناموفق بود")
        exp = now() + int(plan["days"]) * 86400 if plan.get("days") else 0
        sid = self.db.run("""INSERT INTO services(user_id, plan_id, plan_name, server_id, name, remote, link, volume_gb, expire_at, price, status, created)
                             VALUES(?,?,?,?,?,?,?,?,?,?,?,?)""", uid, plan.get("id"), plan["name"], srv["id"], name,
                          json.dumps(res.get("meta") or {}), res.get("link") or "", plan.get("volume_gb") or 0, exp, price, "active", now())
        return self.db.one("SELECT * FROM services WHERE id=?", sid)

    async def renew_service(self, svc, plan):
        srv = self.db.one("SELECT * FROM servers WHERE id=?", svc["server_id"])
        if not srv:
            raise PanelError("سرور این سرویس حذف شده است")
        base = max(now(), svc["expire_at"] or 0) if svc["status"] == "active" else now()
        exp = base + int(plan["days"]) * 86400 if plan.get("days") else 0
        await asyncio.wait_for(get_adapter(srv, self.s).renew(json.loads(svc["remote"] or "{}"), float(plan.get("volume_gb") or 0),
                                                              exp, int(plan.get("users_limit") or 1)), 40)
        self.db.run("UPDATE services SET plan_id=?, plan_name=?, volume_gb=?, expire_at=?, status='active', notified=0 WHERE id=?",
                    plan["id"], plan["name"], plan.get("volume_gb") or 0, exp, svc["id"])

    def qr_png(self, data):
        import segno
        buf = io.BytesIO()
        segno.make(data, error="m").save(buf, kind="png", scale=8, border=3, dark="#0b1222")
        return buf.getvalue()

    async def deliver(self, uid, svc, test=False):
        text = self.T("delivered", plan=H(svc["plan_name"]), volume=gbtxt(svc["volume_gb"]),
                      expire=jdate(svc["expire_at"]), link=H(svc["link"]))
        kb = ik([[btn("سرویس‌های من", "svc", style="primary"), btn("آموزش اتصال", "help")]])
        await self.safe_send(uid, text, kb)  # link first, instantly
        if self.tog("qr") and svc["link"] and len(svc["link"]) < 2500:
            asyncio.create_task(self._send_qr_bg(uid, svc))

    async def _send_qr_bg(self, uid, svc):
        try:
            await self.call_files("sendPhoto", uid, self.qr_png(svc["link"]), caption=f"کد QR سرویس <b>{H(svc['plan_name'])}</b>")
        except Exception:
            pass

    async def call_files(self, method, chat, png, caption="", kb=None):
        return await self.tg.call(method, _files={"photo": ("qr.png", png)}, chat_id=chat, caption=caption,
                                  parse_mode="HTML", reply_markup=kb)

    # ================================================================ services
    async def show_services(self, cq, uid):
        rows = self.db.all("SELECT * FROM services WHERE user_id=? AND status!='deleted' ORDER BY id DESC LIMIT 30", uid)
        if not rows:
            return await self.edit(cq, self.T("no_service"), ik([[btn("خرید سرویس", "buy", style="success")], back()]))
        t = now()
        kb = []
        for s in rows:
            if s["status"] != "active":
                tag = "منقضی"
            elif s["expire_at"]:
                tag = f"{fa(max(0, (s['expire_at'] - t) // 86400))} روز"
            else:
                tag = "نامحدود"
            kb.append([btn(f"{s['plan_name']} | {tag}", f"s:{s['id']}", style=None if s["status"] == "active" else "danger")])
        await self.edit(cq, "<b>سرویس‌های من</b>\n\nبرای مشاهده جزئیات، سرویس را انتخاب کنید:", ik(kb + [back()]))

    async def show_service(self, cq, uid, sid):
        s = self.db.one("SELECT * FROM services WHERE id=? AND user_id=?", sid, uid)
        if not s:
            return await self.edit(cq, "سرویس یافت نشد.", ik([back("svc")]))
        srv = self.db.one("SELECT * FROM servers WHERE id=?", s["server_id"])
        usage = None
        if srv and srv["type"] != "stock":
            try:
                usage = await asyncio.wait_for(get_adapter(srv, self.s).usage(json.loads(s["remote"] or "{}")), 8)
                if usage.get("link") and usage["link"] != s["link"]:
                    self.db.run("UPDATE services SET link=? WHERE id=?", usage["link"], sid)
                    s["link"] = usage["link"]
            except Exception:
                usage = None
        t = now()
        st = "فعال" if s["status"] == "active" else "منقضی شده"
        lines = [f"<b>{H(s['plan_name'])}</b>", ""]
        info = [f"وضعیت: {st}", f"شناسه: {H(s['name'])}"]
        if usage and usage.get("total"):
            used, total = usage["used"], usage["total"]
            info.append(f"مصرف: {fa('%.2f' % (used / 1024 ** 3))} از {fa('%.2f' % (total / 1024 ** 3))} گیگ")
            info.append(bar(used / total if total else 0) + f" {fa(int(used * 100 / total))}٪")
        elif usage:
            info.append(f"مصرف: {fa('%.2f' % (usage['used'] / 1024 ** 3))} گیگ از نامحدود")
        else:
            info.append(f"حجم: {gbtxt(s['volume_gb'])}")
        if s["expire_at"]:
            left = max(0, (s["expire_at"] - t) // 86400)
            info.append(f"انقضا: {jdate(s['expire_at'])} ({fa(left)} روز مانده)")
        else:
            info.append("انقضا: نامحدود")
        lines.append("<blockquote>" + "\n".join(info) + "</blockquote>")
        lines += ["", "لینک اتصال:", f"<code>{H(s['link'])}</code>"]
        rows = [[btn("کد QR", f"sq:{sid}"), btn("تمدید", f"sr:{sid}", style="success")] if srv and srv["type"] != "stock" else [btn("کد QR", f"sq:{sid}")],
                back("svc")]
        await self.edit(cq, "\n".join(lines), ik(rows))

    async def send_qr(self, cq, uid, sid):
        s = self.db.one("SELECT * FROM services WHERE id=? AND user_id=?", sid, uid)
        if not s or not s["link"]:
            return await self.answer(cq, "لینکی برای این سرویس وجود ندارد", True)
        await self.answer(cq)
        await self.call_files("sendPhoto", uid, self.qr_png(s["link"]), caption=f"کد QR سرویس <b>{H(s['plan_name'])}</b>")

    async def test_account(self, cq, uid, u):
        if not self.tog("test"):
            return await self.answer(cq, "اکانت تست در حال حاضر غیرفعال است", True)
        if u.get("test_used"):
            return await self.answer(cq, self.T("test_used"), True)
        if not self.db.exec("UPDATE users SET test_used=1 WHERE id=? AND test_used=0", uid):
            return await self.answer(cq, self.T("test_used"), True)
        cfg = self.db.get("test_cfg")
        await self.answer(cq, "در حال ساخت اکانت تست...")
        await self.edit(cq, "در حال ساخت اکانت تست، چند لحظه صبر کنید...")
        plan = {"id": None, "name": "اکانت تست", "volume_gb": float(cfg.get("volume") or 1),
                "days": int(cfg.get("days") or 1), "users_limit": 1, "server_id": cfg.get("server_id")}
        try:
            svc = await self.provision(uid, plan, any_server=True)
        except (PanelError, asyncio.TimeoutError) as e:
            self.db.run("UPDATE users SET test_used=0 WHERE id=?", uid)
            self.db.log(f"خطا در ساخت اکانت تست: {e}")
            return await self.send(uid, "در حال حاضر امکان ساخت اکانت تست وجود ندارد. لطفاً بعداً تلاش کنید.", ik([back()]))
        await self.deliver(uid, svc, True)

    # ================================================================ background jobs
    def start_background(self):
        self.bg = [asyncio.create_task(self.loop_expire()), asyncio.create_task(self.loop_backup()),
                   asyncio.create_task(self.loop_watchdog()), asyncio.create_task(self.loop_retry()),
                   asyncio.create_task(self.loop_health())]

    async def loop_retry(self):
        """Delivery queue: paid orders whose panel was temporarily down are retried until delivered."""
        await asyncio.sleep(5)
        while True:
            try:
                for o in self.db.all("SELECT id FROM orders WHERE retry_at>0 AND retry_at<=? AND status IN ('approved','paid') LIMIT 50", now()):
                    lock = self.order_locks.setdefault(o["id"], asyncio.Lock())
                    if lock.locked():
                        continue
                    async with lock:
                        if self.db.exec("UPDATE orders SET retry_at=? WHERE id=? AND retry_at>0 AND retry_at<=?", now() + 120, o["id"], now()):
                            await self.fulfil(o["id"])
                    self.order_locks.pop(o["id"], None)
            except Exception:
                log.exception("retry loop")
            await asyncio.sleep(8)

    async def check_server(self, srv):
        t0 = time.monotonic()
        try:
            await asyncio.wait_for(get_adapter(srv, self.s).test(), 20)
            self._mark(srv["id"], True, int((time.monotonic() - t0) * 1000))
        except Exception as e:  # noqa
            self._mark(srv["id"], False, err=str(e) or "پنل جواب نداد")

    async def loop_health(self):
        """Keeps every panel logged in and the connection warm, so configs are created instantly."""
        await asyncio.sleep(3)
        while True:
            try:
                rows = self.db.all("SELECT * FROM servers WHERE active=1 AND type NOT IN ('stock')")
                await asyncio.gather(*(self.check_server(r) for r in rows))
                for sid in [k for k in self.health if k not in {r["id"] for r in rows}]:
                    self.health.pop(sid, None)
            except Exception:
                log.exception("health loop")
            await asyncio.sleep(150)

    async def loop_watchdog(self):
        """Keeps the bot alive: restarts polling if it stopped or stalled, cleans memory caches."""
        while True:
            await asyncio.sleep(30)
            try:
                want = bool(self.db.get("token")) and bool(self.db.get("bot_enabled"))
                dead = self.task is None or self.task.done()
                stalled = self.running and time.monotonic() - self.last_poll > 180
                if want and (dead or stalled or not self.running):
                    log.warning("watchdog: restarting bot (dead=%s stalled=%s)", dead, stalled)
                    self.restarts += 1
                    if await self.start():
                        self.db.log("ربات به صورت خودکار دوباره راه‌اندازی شد")
                t = time.monotonic()
                if len(self.rate) > 5000:
                    self.rate = {k: v for k, v in self.rate.items() if t - v[0] < 60 or v[2] > t}
                if len(self.join_cache) > 20000:
                    self.join_cache = {k: v for k, v in self.join_cache.items() if v > t}
            except Exception:
                log.exception("watchdog")

    async def loop_expire(self):
        await asyncio.sleep(30)
        while True:
            try:
                t = now()
                self.db.run("UPDATE services SET status='expired' WHERE status='active' AND expire_at>0 AND expire_at<?", t)
                self.db.run("DELETE FROM orders WHERE status IN ('draft','await_receipt') AND created<?", t - 86400 * 2)
                self.db.run("PRAGMA optimize")
                if self.tg and self.running and self.tog("expire_alert"):
                    rows = self.db.all("SELECT * FROM services WHERE status='active' AND notified=0 AND expire_at>? AND expire_at<?", t, t + 86400)
                    for s in rows:
                        self.db.run("UPDATE services SET notified=1 WHERE id=?", s["id"])
                        await self.safe_send(s["user_id"], self.T("expire_alert", plan=H(s["plan_name"])),
                                             ik([[btn("تمدید سرویس", f"sr:{s['id']}", style="success")]]))
                        await asyncio.sleep(0.05)
            except Exception:
                log.exception("expire loop")
            await asyncio.sleep(1200)

    async def loop_backup(self):
        await asyncio.sleep(120)
        while True:
            try:
                if self.tg and self.running and self.tog("backup") and now() - int(self.db.get("last_backup") or 0) > 86400:
                    path = self.db.path + ".bak"
                    self.db.backup(path)
                    with open(path, "rb") as f:
                        data = f.read()
                    for a in self.admins():
                        if a.get("role") == "owner":
                            try:
                                await self.tg.call("sendDocument", _files={"document": (f"backup-{time.strftime('%Y%m%d')}.db", data)},
                                                   chat_id=a["id"], caption="بکاپ خودکار دیتابیس | " + jdate(now()))
                            except TGError:
                                pass
                    self.db.set("last_backup", now())
            except Exception:
                log.exception("backup loop")
            await asyncio.sleep(1800)

    # ================================================================ broadcast
    BC_TARGETS = {
        "all": ("همه کاربران", "SELECT id FROM users WHERE banned=0"),
        "active": ("دارای سرویس فعال", "SELECT DISTINCT user_id AS id FROM services WHERE status='active'"),
        "nobuy": ("بدون خرید", "SELECT id FROM users WHERE banned=0 AND id NOT IN (SELECT user_id FROM services)"),
        "expired": ("سرویس منقضی‌شده", "SELECT DISTINCT user_id AS id FROM services WHERE status='expired' AND user_id NOT IN (SELECT user_id FROM services WHERE status='active')"),
        "resellers": ("نمایندگان", "SELECT id FROM users WHERE is_reseller=1"),
        "admins": ("ادمین‌ها (تست)", None),
    }

    def start_broadcast(self, target, text, btn_text="", btn_url="", pin=False):
        if self.bc["running"] or not self.tg or target not in self.BC_TARGETS:
            return False
        label, q = self.BC_TARGETS[target]
        ids = [a["id"] for a in self.admins()] if q is None else [r["id"] for r in self.db.all(q)]
        kb = ik([[btn(btn_text, url=btn_url, style="primary")]]) if btn_text and btn_url else None
        self.bc = {"running": True, "total": len(ids), "sent": 0, "failed": 0, "target": label, "started": now()}
        asyncio.create_task(self._bc_run(ids, text, kb, pin))
        self.db.log(f"شروع ارسال همگانی به {label} ({len(ids)} نفر)")
        return True

    async def _bc_one(self, uid, text, kb, pin):
        try:
            m = await self.send(uid, text, kb)
            if pin:
                try:
                    await self.tg.call("pinChatMessage", chat_id=uid, message_id=m["message_id"], disable_notification=True)
                except TGError:
                    pass
            return True
        except TGError:
            return False

    async def _bc_run(self, ids, text, kb, pin):
        try:
            for i in range(0, len(ids), 25):
                t0 = time.monotonic()
                res = await asyncio.gather(*[self._bc_one(x, text, kb, pin) for x in ids[i:i + 25]])
                self.bc["sent"] += sum(res)
                self.bc["failed"] += len(res) - sum(res)
                dt = time.monotonic() - t0
                if dt < 1.05:
                    await asyncio.sleep(1.05 - dt)
        finally:
            self.bc["running"] = False
            self.db.log(f"پایان ارسال همگانی: {self.bc['sent']} موفق، {self.bc['failed']} ناموفق")
