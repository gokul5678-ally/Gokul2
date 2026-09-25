#!/usr/bin/env python3
"""
Dual-Bot Architecture with Dynamic Multi-Channel Force-Join & Real Gmail IMAP:
- User Mail & Credit Bot (USER_BOT_TOKEN)
- Admin Operations & Approvals Bot (ADMIN_BOT_TOKEN)

Storage: Atomic JSON persistence via bot_storage.json using asyncio.Lock & os.replace.
Features:
- Full message listing with pagination (browse all messages in any mailbox).
- Real Gmail integration via IMAP using 16-character Google App Passwords.
- Mail.tm API disposable email lifecycles (5 Credits).
- Custom Mail with 16-character App Passwords (10 Credits, full 10 Credits refunded upon deletion).
- Dynamic multi-channel verification with 50 bonus credits on complete join.
- Admin can Add and Remove required channels dynamically via interactive buttons.
- Dynamic NPCI UPI QR code generation via HTTP API (Zero Pillow/C-dependency).
- 1-second focused inbox monitoring with 30-second self-destructing push alerts.
- Admin approvals dashboard, voucher creator, and host network diagnostics.
"""

import os
import re
import io
import json
import time
import random
import string
import asyncio
import logging
import signal
import urllib.parse
import imaplib
import email
from email.header import decode_header
from typing import Dict, Any, Optional, Tuple, Set, List

import httpx

from telegram import (
    Update,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
)
from telegram.constants import ParseMode, ChatMemberStatus
from telegram.error import BadRequest, TimedOut, TelegramError
from telegram.request import HTTPXRequest
from telegram.ext import (
    Application,
    ApplicationBuilder,
    CommandHandler,
    CallbackQueryHandler,
    MessageHandler,
    ContextTypes,
    filters,
)

# ============================================================================
# CONFIGURATION CONSTANTS
# ============================================================================
USER_BOT_TOKEN = "8913644447:AAHvAXA7gGmL8y46CR_ql2jyWxyLX0eoF00"
ADMIN_BOT_TOKEN = "8882255569:AAEfD02Mvwi5FLT4PymwBy0-UbDLj07o2rM"
ADMIN_TELEGRAM_ID = 7648203775

UPI_VPA = "6302836569@upi"
UPI_NAME = "gokul"

STORAGE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bot_storage.json")
MAIL_TM_BASE = "https://api.mail.tm"

# Credit Economics
CREDITS_PER_INR = 10
MIN_INR_PURCHASE = 5
COST_DISPOSABLE_MAIL = 5
COST_CUSTOM_MAIL = 10
REFUND_CUSTOM_MAIL = 10
JOIN_BONUS_CREDITS = 50
MSGS_PER_PAGE = 6

logging.basicConfig(
    format="%(asctime)s - [%(name)s] - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger("DualBotSystem")

# ============================================================================
# ATOMIC PERSISTENCE LAYER
# ============================================================================
storage_lock = asyncio.Lock()

data_store: Dict[str, Any] = {
    "users": {},
    "orders": {},
    "vouchers": {},
    "config": {
        "required_channels": ["@earningwithluffy"]
    },
    "metadata": {
        "total_generated_orders": 0,
        "circulating_credits": 0,
    }
}

user_active_mailbox: Dict[int, Optional[str]] = {}
user_active_view: Dict[int, Tuple[int, int]] = {}
user_input_states: Dict[int, Dict[str, Any]] = {}
admin_input_states: Dict[int, Dict[str, Any]] = {}
gmail_cache: Dict[str, List[Dict[str, Any]]] = {}
mailbox_pages: Dict[int, int] = {}


def load_storage_sync() -> None:
    global data_store
    if os.path.exists(STORAGE_FILE):
        try:
            with open(STORAGE_FILE, "r", encoding="utf-8") as f:
                data_store = json.load(f)
                if "config" not in data_store:
                    data_store["config"] = {"required_channels": ["@earningwithluffy"]}
                if "required_channel" in data_store["config"]:
                    old_ch = data_store["config"].pop("required_channel")
                    data_store["config"]["required_channels"] = [old_ch] if old_ch else []
                logger.info("Storage state loaded successfully.")
        except Exception as e:
            logger.error(f"Failed to read storage file: {e}. Initializing fresh store.")
    else:
        logger.info("No existing storage file found. Initializing new state.")


async def save_storage() -> None:
    async with storage_lock:
        tmp_file = f"{STORAGE_FILE}.tmp"
        try:
            loop = asyncio.get_running_loop()
            await loop.run_in_executor(None, _write_and_replace, tmp_file, STORAGE_FILE, data_store)
        except Exception as e:
            logger.error(f"Critical error executing atomic storage write: {e}")


def _write_and_replace(tmp_path: str, target_path: str, data: dict) -> None:
    with open(tmp_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp_path, target_path)


def get_or_create_user(user_id: int, username: Optional[str] = None) -> dict:
    uid_str = str(user_id)
    if uid_str not in data_store["users"]:
        sys_id = f"UID-{''.join(random.choices(string.ascii_uppercase + string.digits, k=6))}"
        data_store["users"][uid_str] = {
            "system_id": sys_id,
            "telegram_id": user_id,
            "username": username or "Unknown",
            "credits": 0,
            "bonus_claimed": False,
            "mailboxes": {},
            "joined_at": int(time.time()),
        }
    else:
        if username:
            data_store["users"][uid_str]["username"] = username
        if "bonus_claimed" not in data_store["users"][uid_str]:
            data_store["users"][uid_str]["bonus_claimed"] = False
    return data_store["users"][uid_str]


def find_user_by_any_id(identifier: str) -> Optional[Tuple[str, dict]]:
    clean_id = identifier.strip()
    if clean_id in data_store["users"]:
        return clean_id, data_store["users"][clean_id]
    for uid, udata in data_store["users"].items():
        if udata.get("system_id", "").upper() == clean_id.upper():
            return uid, udata
    return None

# ============================================================================
# DYNAMIC MULTI-CHANNEL FORCE-JOIN ENGINE
# ============================================================================
async def get_unjoined_channels(bot, user_id: int) -> List[str]:
    channels = data_store.get("config", {}).get("required_channels", [])
    unjoined = []
    for ch in channels:
        ch_clean = ch.strip()
        if not ch_clean:
            continue
        try:
            member = await bot.get_chat_member(chat_id=ch_clean, user_id=user_id)
            if member.status not in [ChatMemberStatus.MEMBER, ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER]:
                unjoined.append(ch_clean)
        except Exception as e:
            logger.warning(f"Error checking membership for {ch_clean}: {e}")
            unjoined.append(ch_clean)
    return unjoined


def build_force_join_screen(unjoined_channels: List[str]) -> Tuple[str, InlineKeyboardMarkup]:
    text = (
        "⚠️ <b>Access Restricted! Mandatory Channels Not Joined</b>\n\n"
        "To use this bot and receive your <b>50 Welcome Bonus Credits</b>, you must join all our required channels:\n\n"
    )
    keyboard = []
    for idx, ch in enumerate(unjoined_channels, start=1):
        clean_handle = ch.replace("@", "").strip()
        text += f"{idx}. <b>{ch}</b>\n"
        keyboard.append([InlineKeyboardButton(f"📢 Join {ch}", url=f"https://t.me/{clean_handle}")])

    text += "\n<i>After joining each channel, tap the verify button below to unlock the bot!</i>"
    keyboard.append([InlineKeyboardButton("✅ Joined / Verify", callback_data="u:verify_join")])
    return text, InlineKeyboardMarkup(keyboard)

# ============================================================================
# REAL GMAIL IMAP CLIENT (FETCH ALL MESSAGES)
# ============================================================================
def fetch_gmail_inbox_sync(user_email: str, app_password: str) -> List[Dict[str, Any]]:
    clean_pass = app_password.replace(" ", "")
    results = []
    try:
        mail = imaplib.IMAP4_SSL("imap.gmail.com", port=993)
        mail.login(user_email, clean_pass)
        mail.select("INBOX")

        status, response = mail.search(None, "ALL")
        if status != "OK" or not response[0]:
            mail.logout()
            return []

        msg_ids = response[0].split()

        for msg_id in reversed(msg_ids):
            res, msg_data = mail.fetch(msg_id, "(RFC822)")
            for response_part in msg_data:
                if isinstance(response_part, tuple):
                    raw_email = email.message_from_bytes(response_part[1])

                    # Decode Subject
                    raw_sub = raw_email.get("Subject", "No Subject")
                    decoded_parts = decode_header(raw_sub)
                    subject = ""
                    for part, encoding in decoded_parts:
                        if isinstance(part, bytes):
                            subject += part.decode(encoding or "utf-8", errors="ignore")
                        else:
                            subject += str(part)

                    # Decode Sender
                    raw_sender = raw_email.get("From", "Unknown Sender")
                    decoded_sender_parts = decode_header(raw_sender)
                    sender = ""
                    for part, encoding in decoded_sender_parts:
                        if isinstance(part, bytes):
                            sender += part.decode(encoding or "utf-8", errors="ignore")
                        else:
                            sender += str(part)

                    # Extract Body
                    body = ""
                    if raw_email.is_multipart():
                        for p in raw_email.walk():
                            if p.get_content_type() == "text/plain":
                                body = p.get_payload(decode=True).decode(errors="ignore")
                                break
                    else:
                        payload = raw_email.get_payload(decode=True)
                        if payload:
                            body = payload.decode(errors="ignore")

                    results.append({
                        "id": msg_id.decode(),
                        "from": {"name": sender, "address": sender},
                        "subject": subject,
                        "text": body,
                    })

        mail.logout()
    except Exception as e:
        logger.warning(f"Gmail IMAP check error for {user_email}: {e}")
        return []

    return results


async def check_gmail_messages(user_email: str, app_password: str) -> List[Dict[str, Any]]:
    return await asyncio.to_thread(fetch_gmail_inbox_sync, user_email, app_password)

# ============================================================================
# MAIL.TM & UPI HELPERS
# ============================================================================
async def mail_tm_get_domain(client: httpx.AsyncClient) -> Optional[str]:
    try:
        resp = await client.get(f"{MAIL_TM_BASE}/domains")
        if resp.status_code == 200:
            domains = resp.json().get("hydra:member", [])
            active = [d["domain"] for d in domains if d.get("isActive")]
            if active:
                return random.choice(active)
    except Exception as e:
        logger.warning(f"Mail.tm domain retrieval error: {e}")
    return None


async def mail_tm_create_account(client: httpx.AsyncClient, email_addr: str, password: str) -> Optional[dict]:
    try:
        resp = await client.post(f"{MAIL_TM_BASE}/accounts", json={"address": email_addr, "password": password})
        if resp.status_code in (200, 201):
            return resp.json()
    except Exception as e:
        logger.warning(f"Mail.tm account creation error: {e}")
    return None


async def mail_tm_get_token(client: httpx.AsyncClient, email_addr: str, password: str) -> Optional[str]:
    try:
        resp = await client.post(f"{MAIL_TM_BASE}/token", json={"address": email_addr, "password": password})
        if resp.status_code == 200:
            return resp.json().get("token")
    except Exception as e:
        logger.warning(f"Mail.tm authentication error: {e}")
    return None


async def mail_tm_delete_remote(client: httpx.AsyncClient, account_id: str, token: str) -> bool:
    try:
        resp = await client.delete(
            f"{MAIL_TM_BASE}/accounts/{account_id}",
            headers={"Authorization": f"Bearer {token}"},
        )
        return resp.status_code in (200, 204)
    except Exception as e:
        logger.warning(f"Mail.tm remote deletion failed: {e}")
        return False


async def mail_tm_fetch_inbox(client: httpx.AsyncClient, token: str) -> list:
    try:
        resp = await client.get(f"{MAIL_TM_BASE}/messages", headers={"Authorization": f"Bearer {token}"})
        if resp.status_code == 200:
            return resp.json().get("hydra:member", [])
    except Exception as e:
        logger.warning(f"Mail.tm inbox check failed: {e}")
    return []


async def mail_tm_fetch_message_detail(client: httpx.AsyncClient, msg_id: str, token: str) -> Optional[dict]:
    try:
        resp = await client.get(f"{MAIL_TM_BASE}/messages/{msg_id}", headers={"Authorization": f"Bearer {token}"})
        if resp.status_code == 200:
            return resp.json()
    except Exception as e:
        logger.warning(f"Mail.tm message detail fetch failed: {e}")
    return None


def extract_security_code(content: str) -> Optional[str]:
    match = re.search(r"\b(?:\d{4,8}|[A-Z0-9]{6})\b", content)
    return match.group(0) if match else None


async def fetch_upi_qr_bytes(vpa: str, name: str, amount_inr: float, order_id: str) -> Optional[io.BytesIO]:
    uri = f"upi://pay?pa={vpa}&pn={name}&am={amount_inr:.2f}&cu=INR&tn=Order_{order_id}"
    encoded_uri = urllib.parse.quote(uri)
    api_url = f"https://api.qrserver.com/v1/create-qr-code/?size=300x300&data={encoded_uri}"
    try:
        async with httpx.AsyncClient(timeout=10.0) as client:
            resp = await client.get(api_url)
            if resp.status_code == 200:
                bio = io.BytesIO(resp.content)
                bio.seek(0)
                return bio
    except Exception as e:
        logger.warning(f"QR server fallback error: {e}")
    return None

# ============================================================================
# USER BOT: UI SCREENS & NAVIGATION
# ============================================================================
def build_user_home_screen(user_id: int) -> Tuple[str, InlineKeyboardMarkup]:
    user_info = get_or_create_user(user_id)
    mailboxes = user_info.get("mailboxes", {})
    text = (
        f"<b>📫 Digital Mailbox &amp; Verification Suite</b>\n\n"
        f"👤 <b>System ID:</b> <code>{user_info['system_id']}</code>\n"
        f"💰 <b>Balance:</b> <code>{user_info['credits']} Credits</code>\n"
        f"📬 <b>Active Mailboxes:</b> <code>{len(mailboxes)}</code>\n\n"
        f"Select an operation below:"
    )
    keyboard = [
        [
            InlineKeyboardButton("➕ Disposable Mail (5 Cr)", callback_data="u:new_disp"),
            InlineKeyboardButton("🔐 Add Gmail App Pass (10 Cr)", callback_data="u:add_custom"),
        ],
        [
            InlineKeyboardButton("📂 My Mailboxes", callback_data="u:list_mail"),
            InlineKeyboardButton("💳 Top Up Credits", callback_data="u:topup"),
        ],
        [
            InlineKeyboardButton("🎟️ Redeem Code", callback_data="u:redeem_prompt"),
            InlineKeyboardButton("🔄 Refresh Dashboard", callback_data="u:home"),
        ],
    ]
    return text, InlineKeyboardMarkup(keyboard)


def build_mailbox_view(user_id: int, mail_id: str, messages: list, page: int = 0) -> Tuple[str, InlineKeyboardMarkup]:
    user_info = get_or_create_user(user_id)
    mail_data = user_info.get("mailboxes", {}).get(mail_id, {})
    address = mail_data.get("address", "Unknown")
    password = mail_data.get("password", "N/A")
    m_type = mail_data.get("type", "disposable")

    type_badge = "⚡ Disposable" if m_type == "disposable" else "🔐 Real Gmail"
    total_msgs = len(messages)
    total_pages = max(1, (total_msgs + MSGS_PER_PAGE - 1) // MSGS_PER_PAGE)
    page = max(0, min(page, total_pages - 1))
    mailbox_pages[user_id] = page

    text = (
        f"<b>📧 Mailbox Monitor:</b> <code>{address}</code>\n"
        f"🏷️ <b>Type:</b> {type_badge}\n"
        f"🔑 <b>Pass / App Key:</b> <code>{password}</code>\n"
        f"📨 <b>Total Messages:</b> <code>{total_msgs}</code> (Page {page + 1}/{total_pages})\n\n"
        f"<i>Status: Continuous 1-second auto-sync active.</i>"
    )

    keyboard = []
    # Slice messages for current page
    start_idx = page * MSGS_PER_PAGE
    end_idx = start_idx + MSGS_PER_PAGE
    page_messages = messages[start_idx:end_idx]

    for offset, msg in enumerate(page_messages, start=1):
        global_num = start_idx + offset
        sender = msg.get("from", {}).get("name") or msg.get("from", {}).get("address") or "Unknown"
        if len(sender) > 24:
            sender = sender[:21] + "..."
        keyboard.append([InlineKeyboardButton(f"💬 #{global_num} From: {sender}", callback_data=f"u:msg:{mail_id}:{msg['id']}")])

    # Pagination navigation buttons
    nav_row = []
    if page > 0:
        nav_row.append(InlineKeyboardButton("⬅️ Previous", callback_data=f"u:page:{mail_id}:{page - 1}"))
    if page < total_pages - 1:
        nav_row.append(InlineKeyboardButton("Next ➡️", callback_data=f"u:page:{mail_id}:{page + 1}"))
    if nav_row:
        keyboard.append(nav_row)

    refund_label = "🗑️ Delete & Refund 10 Cr" if m_type == "custom" else "🗑️ Delete Mailbox"
    keyboard.append([InlineKeyboardButton(refund_label, callback_data=f"u:del:{mail_id}")])
    keyboard.append([InlineKeyboardButton("🔙 Back to Mailboxes", callback_data="u:list_mail")])
    return text, InlineKeyboardMarkup(keyboard)

# ============================================================================
# BACKGROUND WORKER & NOTIFICATION TASKS
# ============================================================================
async def user_inbox_polling_worker(user_app: Application) -> None:
    async with httpx.AsyncClient(timeout=10.0) as client:
        while True:
            try:
                active_users = list(user_active_mailbox.items())
                for user_id, active_mail_id in active_users:
                    if not active_mail_id:
                        continue

                    user_info = data_store["users"].get(str(user_id))
                    if not user_info:
                        continue

                    mail_data = user_info.get("mailboxes", {}).get(active_mail_id)
                    if not mail_data:
                        continue

                    messages = []
                    m_type = mail_data.get("type", "disposable")

                    if m_type == "disposable":
                        token = mail_data.get("token")
                        if not token:
                            continue
                        messages = await mail_tm_fetch_inbox(client, token)
                    elif m_type == "custom":
                        messages = await check_gmail_messages(mail_data["address"], mail_data["password"])
                        gmail_cache[active_mail_id] = messages

                    seen_ids: Set[str] = set(mail_data.get("seen_ids", []))
                    new_messages = [m for m in messages if str(m["id"]) not in seen_ids]

                    if new_messages:
                        for nm in new_messages:
                            msg_id = str(nm["id"])
                            seen_ids.add(msg_id)
                            mail_data["total_received"] = mail_data.get("total_received", 0) + 1

                            sender_addr = nm.get("from", {}).get("address", "Unknown")
                            subject = nm.get("subject", "No Subject")
                            body = ""

                            if m_type == "disposable":
                                detail = await mail_tm_fetch_message_detail(client, msg_id, mail_data["token"])
                                body = detail.get("text", "") if detail else ""
                            else:
                                body = nm.get("text", "")

                            otp = extract_security_code(body)

                            alert_text = (
                                f"🚨 <b>New Email Received!</b>\n"
                                f"📬 <b>To:</b> <code>{mail_data['address']}</code>\n"
                                f"👤 <b>From:</b> <code>{sender_addr}</code>\n"
                                f"📝 <b>Subject:</b> {subject}\n"
                            )
                            if otp:
                                alert_text += f"🔑 <b>Detected Code / OTP:</b> <code>{otp}</code>\n"
                            alert_text += "\n⏱️ <i>This notification will self-destruct in 30 seconds.</i>"

                            target_chat = user_active_view.get(user_id, (user_id, 0))[0]
                            asyncio.create_task(send_self_destruct_alert(user_app, target_chat, alert_text, 30))

                        mail_data["seen_ids"] = list(seen_ids)
                        await save_storage()

                        if user_id in user_active_view:
                            chat_id, view_msg_id = user_active_view[user_id]
                            cur_page = mailbox_pages.get(user_id, 0)
                            v_text, v_kb = build_mailbox_view(user_id, active_mail_id, messages, cur_page)
                            try:
                                await user_app.bot.edit_message_text(
                                    chat_id=chat_id,
                                    message_id=view_msg_id,
                                    text=v_text,
                                    parse_mode=ParseMode.HTML,
                                    reply_markup=v_kb,
                                )
                            except BadRequest as e:
                                if "Message is not modified" not in str(e):
                                    logger.warning(f"UI update skipped: {e}")
            except Exception as e:
                logger.error(f"Error in polling worker: {e}")

            await asyncio.sleep(1)


async def send_self_destruct_alert(app: Application, chat_id: int, text: str, seconds: int = 30) -> None:
    try:
        sent = await app.bot.send_message(
            chat_id=chat_id,
            text=text,
            parse_mode=ParseMode.HTML,
            disable_notification=False,
        )
        await asyncio.sleep(seconds)
        await app.bot.delete_message(chat_id=chat_id, message_id=sent.message_id)
    except Exception:
        pass

# ============================================================================
# USER BOT: HANDLERS & CALLBACK DISPATCHER
# ============================================================================
async def user_start_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    user_info = get_or_create_user(user.id, user.username)
    await save_storage()

    unjoined = await get_unjoined_channels(context.bot, user.id)
    if unjoined:
        text, kb = build_force_join_screen(unjoined)
        sent_msg = await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        user_active_view[user.id] = (sent_msg.chat_id, sent_msg.message_id)
        return

    if not user_info.get("bonus_claimed", False):
        user_info["credits"] += JOIN_BONUS_CREDITS
        user_info["bonus_claimed"] = True
        await save_storage()
        await update.message.reply_text(
            f"🎉 <b>Welcome Bonus Awarded!</b>\nWe granted you <b>+{JOIN_BONUS_CREDITS} Credits</b> for joining our channels.",
            parse_mode=ParseMode.HTML,
        )

    user_active_mailbox[user.id] = None
    text, kb = build_user_home_screen(user.id)
    msg = await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    user_active_view[user.id] = (msg.chat_id, msg.message_id)


async def user_callback_dispatcher(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    user = update.effective_user
    user_id = user.id
    user_info = get_or_create_user(user_id, user.username)
    data = query.data
    chat_id = query.message.chat_id
    user_active_view[user_id] = (chat_id, query.message.message_id)

    # 1. Join Verification Button Handler
    if data == "u:verify_join":
        unjoined = await get_unjoined_channels(context.bot, user_id)
        if unjoined:
            await query.answer("❌ You still haven't joined all channels!", show_alert=True)
            text, kb = build_force_join_screen(unjoined)
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
            return

        bonus_notice = ""
        if not user_info.get("bonus_claimed", False):
            user_info["credits"] += JOIN_BONUS_CREDITS
            user_info["bonus_claimed"] = True
            await save_storage()
            bonus_notice = f"🎉 <b>+{JOIN_BONUS_CREDITS} Welcome Bonus Credits added to your account!</b>\n\n"

        await query.answer("✅ Verification Successful! Access unlocked.")
        user_active_mailbox[user_id] = None
        text, kb = build_user_home_screen(user_id)
        await query.edit_message_text(f"{bonus_notice}{text}", parse_mode=ParseMode.HTML, reply_markup=kb)
        return

    # 2. Strict Check for All Other Buttons
    unjoined = await get_unjoined_channels(context.bot, user_id)
    if unjoined:
        text, kb = build_force_join_screen(unjoined)
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return

    async with httpx.AsyncClient(timeout=10.0) as client:
        if data == "u:home":
            user_active_mailbox[user_id] = None
            text, kb = build_user_home_screen(user_id)
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

        elif data == "u:list_mail":
            user_active_mailbox[user_id] = None
            boxes = user_info.get("mailboxes", {})
            if not boxes:
                text = "📭 <b>No active mailboxes found.</b>"
                kb = InlineKeyboardMarkup([
                    [InlineKeyboardButton("➕ Disposable Mail (5 Cr)", callback_data="u:new_disp")],
                    [InlineKeyboardButton("🔐 Add Gmail App Pass (10 Cr)", callback_data="u:add_custom")],
                    [InlineKeyboardButton("🔙 Back to Dashboard", callback_data="u:home")],
                ])
                await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
                return

            text = f"📂 <b>Your Active Mailboxes</b> (<code>{len(boxes)}</code> Total):"
            keyboard = []
            for mid, mdata in boxes.items():
                badge = "⚡" if mdata.get("type") == "disposable" else "🔐"
                keyboard.append([InlineKeyboardButton(f"{badge} {mdata['address']}", callback_data=f"u:open:{mid}")])
            keyboard.append([InlineKeyboardButton("🔙 Back to Dashboard", callback_data="u:home")])
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard))

        elif data.startswith("u:open:"):
            mail_id = data.split(":", 2)[2]
            boxes = user_info.get("mailboxes", {})
            if mail_id not in boxes:
                await query.edit_message_text("⚠️ Mailbox no longer exists.", reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔙 Back", callback_data="u:list_mail")]
                ]))
                return

            user_active_mailbox[user_id] = mail_id
            mdata = boxes[mail_id]
            messages = []
            m_type = mdata.get("type", "disposable")

            if m_type == "disposable" and mdata.get("token"):
                messages = await mail_tm_fetch_inbox(client, mdata["token"])
            elif m_type == "custom":
                messages = await check_gmail_messages(mdata["address"], mdata["password"])
                gmail_cache[mail_id] = messages

            mailbox_pages[user_id] = 0
            text, kb = build_mailbox_view(user_id, mail_id, messages, 0)
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

        elif data.startswith("u:page:"):
            _, _, mail_id, page_str = data.split(":")
            target_page = int(page_str)
            boxes = user_info.get("mailboxes", {})
            if mail_id not in boxes:
                await query.answer("Mailbox not found.", show_alert=True)
                return

            mdata = boxes[mail_id]
            messages = []
            m_type = mdata.get("type", "disposable")

            if m_type == "disposable" and mdata.get("token"):
                messages = await mail_tm_fetch_inbox(client, mdata["token"])
            elif m_type == "custom":
                messages = gmail_cache.get(mail_id) or await check_gmail_messages(mdata["address"], mdata["password"])

            text, kb = build_mailbox_view(user_id, mail_id, messages, target_page)
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

        elif data.startswith("u:msg:"):
            _, _, mail_id, msg_id = data.split(":")
            mdata = user_info.get("mailboxes", {}).get(mail_id)
            if not mdata:
                await query.answer("Mailbox expired or unavailable.", show_alert=True)
                return

            m_type = mdata.get("type", "disposable")
            sender_name = "N/A"
            sender_addr = "N/A"
            subject = "(No Subject)"
            body_text = "(No content)"

            if m_type == "disposable":
                if not mdata.get("token"):
                    await query.answer("Mailbox token expired.", show_alert=True)
                    return
                detail = await mail_tm_fetch_message_detail(client, msg_id, mdata["token"])
                if detail:
                    sender_name = detail.get("from", {}).get("name", "N/A")
                    sender_addr = detail.get("from", {}).get("address", "N/A")
                    subject = detail.get("subject", "(No Subject)")
                    body_text = detail.get("text") or "(No plain text content)"
            else:
                cached_msgs = gmail_cache.get(mail_id, [])
                target = next((m for m in cached_msgs if str(m["id"]) == str(msg_id)), None)
                if target:
                    sender_name = target.get("from", {}).get("name", "N/A")
                    sender_addr = target.get("from", {}).get("address", "N/A")
                    subject = target.get("subject", "(No Subject)")
                    body_text = target.get("text") or "(No plain text content)"

            otp = extract_security_code(body_text)
            otp_banner = f"\n🔑 <b>Detected Verification Code:</b> <code>{otp}</code>\n" if otp else ""
            preview = body_text[:1200] + ("..." if len(body_text) > 1200 else "")

            view_text = (
                f"📨 <b>Email Message</b>\n\n"
                f"👤 <b>From:</b> {sender_name} (<code>{sender_addr}</code>)\n"
                f"📝 <b>Subject:</b> {subject}\n"
                f"{otp_banner}\n"
                f"📄 <b>Content:</b>\n<pre>{preview}</pre>"
            )
            cur_page = mailbox_pages.get(user_id, 0)
            kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back to Messages", callback_data=f"u:page:{mail_id}:{cur_page}")]])
            await query.edit_message_text(view_text, parse_mode=ParseMode.HTML, reply_markup=kb)

        elif data.startswith("u:del:"):
            mail_id = data.split(":", 2)[2]
            boxes = user_info.get("mailboxes", {})
            if mail_id in boxes:
                mdata = boxes[mail_id]
                m_type = mdata.get("type", "disposable")
                refund_awarded = 0

                if m_type == "custom":
                    user_info["credits"] += REFUND_CUSTOM_MAIL
                    refund_awarded = REFUND_CUSTOM_MAIL
                    gmail_cache.pop(mail_id, None)
                elif m_type == "disposable":
                    if mdata.get("total_received", 0) == 0:
                        user_info["credits"] += COST_DISPOSABLE_MAIL
                        refund_awarded = COST_DISPOSABLE_MAIL
                    if mdata.get("token"):
                        await mail_tm_delete_remote(client, mail_id, mdata["token"])

                del boxes[mail_id]
                await save_storage()

                notice = "🗑️ Mailbox deleted."
                if refund_awarded > 0:
                    notice += f" +{refund_awarded} Credits refunded!"
                await query.answer(notice, show_alert=True)

            user_active_mailbox[user_id] = None
            text, kb = build_user_home_screen(user_id)
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

        elif data == "u:new_disp":
            if user_info["credits"] < COST_DISPOSABLE_MAIL:
                await query.answer(f"Insufficient funds! Requires {COST_DISPOSABLE_MAIL} Credits.", show_alert=True)
                return

            await query.edit_message_text("⏳ <i>Allocating Mail.tm disposable address...</i>", parse_mode=ParseMode.HTML)
            domain = await mail_tm_get_domain(client)
            if not domain:
                await query.edit_message_text("❌ Domain pool unreachable. Try again shortly.", reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔙 Back", callback_data="u:home")]
                ]))
                return

            rand_user = f"box_{''.join(random.choices(string.ascii_lowercase + string.digits, k=7))}"
            email_addr = f"{rand_user}@{domain}"
            password = "".join(random.choices(string.ascii_letters + string.digits + "!@#$%", k=14))

            created = await mail_tm_create_account(client, email_addr, password)
            if not created:
                await query.edit_message_text("❌ Failed to register mailbox with upstream API.", reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔙 Back", callback_data="u:home")]
                ]))
                return

            token = await mail_tm_get_token(client, email_addr, password)
            if not token:
                await query.edit_message_text("❌ Account authentication failed.", reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔙 Back", callback_data="u:home")]
                ]))
                return

            user_info["credits"] -= COST_DISPOSABLE_MAIL
            mail_id = created["id"]
            user_info["mailboxes"][mail_id] = {
                "id": mail_id,
                "type": "disposable",
                "address": email_addr,
                "password": password,
                "token": token,
                "seen_ids": [],
                "total_received": 0,
            }
            await save_storage()

            user_active_mailbox[user_id] = mail_id
            mailbox_pages[user_id] = 0
            text, kb = build_mailbox_view(user_id, mail_id, [], 0)
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

        elif data == "u:add_custom":
            if user_info["credits"] < COST_CUSTOM_MAIL:
                await query.answer(f"Insufficient credits! Requires {COST_CUSTOM_MAIL} Credits.", show_alert=True)
                return

            user_input_states[user_id] = {"stage": "AWAITING_CUSTOM_EMAIL"}
            prompt = (
                f"🔐 <b>Add Real Gmail Account (16-Digit App Password)</b>\n\n"
                f"• Cost: <b>{COST_CUSTOM_MAIL} Credits</b>\n"
                f"• Refund Policy: <b>Full {REFUND_CUSTOM_MAIL} Credits refunded upon deletion</b>\n\n"
                f"Please reply with your Gmail address:\n"
                f"<i>Example: yourname@gmail.com</i>"
            )
            kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="u:home")]])
            await query.edit_message_text(prompt, parse_mode=ParseMode.HTML, reply_markup=kb)

        elif data == "u:topup":
            topup_text = (
                f"💳 <b>Credit Top-Up Exchange</b>\n\n"
                f"• <b>Rate:</b> 1 ₹ = 10 Credits\n"
                f"• <b>Minimum:</b> ₹{MIN_INR_PURCHASE} (50 Credits)\n\n"
                f"Select an amount to generate an instant NPCI QR code:"
            )
            keyboard = [
                [
                    InlineKeyboardButton("₹10 (100 Cr)", callback_data="u:pay:10"),
                    InlineKeyboardButton("₹25 (250 Cr)", callback_data="u:pay:25"),
                    InlineKeyboardButton("₹50 (500 Cr)", callback_data="u:pay:50"),
                ],
                [
                    InlineKeyboardButton("₹100 (1000 Cr)", callback_data="u:pay:100"),
                    InlineKeyboardButton("Custom Amount", callback_data="u:pay_custom"),
                ],
                [InlineKeyboardButton("🔙 Back to Dashboard", callback_data="u:home")],
            ]
            await query.edit_message_text(topup_text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard))

        elif data.startswith("u:pay:"):
            amt = float(data.split(":")[2])
            await initiate_payment_invoice(update, context, amt)

        elif data == "u:pay_custom":
            user_input_states[user_id] = {"stage": "AWAITING_PAYMENT_AMOUNT"}
            text = f"💵 <b>Enter Top-Up Amount in ₹</b> (Minimum ₹{MIN_INR_PURCHASE}):"
            kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="u:topup")]])
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

        elif data == "u:redeem_prompt":
            user_input_states[user_id] = {"stage": "AWAITING_VOUCHER_CODE"}
            text = "🎟️ <b>Enter Redeem Voucher Code:</b>\n<i>Send the voucher code in chat.</i>"
            kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="u:home")]])
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def initiate_payment_invoice(update: Update, context: ContextTypes.DEFAULT_TYPE, amount_inr: float) -> None:
    user = update.effective_user
    user_id = user.id
    order_id = "".join(random.choices(string.digits, k=12))
    credits_awarded = int(amount_inr * CREDITS_PER_INR)

    data_store["orders"][order_id] = {
        "order_id": order_id,
        "user_id": user_id,
        "amount_inr": amount_inr,
        "credits": credits_awarded,
        "status": "PENDING_VERIFICATION",
        "created_at": int(time.time()),
    }
    await save_storage()

    caption = (
        f"💳 <b>Payment Invoice Generated</b>\n\n"
        f"🆔 <b>Order ID:</b> <code>{order_id}</code>\n"
        f"💵 <b>Amount Payable:</b> <b>₹{amount_inr:.2f}</b>\n"
        f"🪙 <b>Credits:</b> <b>{credits_awarded} Credits</b>\n"
        f"🏷️ <b>UPI VPA:</b> <code>{UPI_VPA}</code>\n\n"
        f"1. Scan the QR code or pay to the UPI ID.\n"
        f"2. After payment, <b>reply with the 12-digit Order ID</b> or <b>send a screenshot</b> of the receipt."
    )
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back to Dashboard", callback_data="u:home")]])
    user_input_states[user_id] = {"stage": "AWAITING_PAYMENT_PROOF", "order_id": order_id}

    qr_io = await fetch_upi_qr_bytes(UPI_VPA, UPI_NAME, amount_inr, order_id)
    query = update.callback_query

    if qr_io:
        if query:
            await query.message.reply_photo(photo=qr_io, caption=caption, parse_mode=ParseMode.HTML, reply_markup=kb)
        else:
            await update.message.reply_photo(photo=qr_io, caption=caption, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        intent_uri = f"upi://pay?pa={UPI_VPA}&pn={urllib.parse.quote(UPI_NAME)}&am={amount_inr:.2f}&cu=INR&tn=Order_{order_id}"
        fallback_text = f"{caption}\n\n👉 <a href='{intent_uri}'>Tap here to open UPI App</a>"
        if query:
            await query.message.reply_text(fallback_text, parse_mode=ParseMode.HTML, reply_markup=kb)
        else:
            await update.message.reply_text(fallback_text, parse_mode=ParseMode.HTML, reply_markup=kb)

# ============================================================================
# USER BOT: MESSAGE INPUT HANDLERS
# ============================================================================
async def user_text_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    user_id = user.id

    unjoined = await get_unjoined_channels(context.bot, user_id)
    if unjoined:
        text, kb = build_force_join_screen(unjoined)
        await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return

    text = update.message.text.strip()
    user_info = get_or_create_user(user_id, user.username)
    state = user_input_states.get(user_id, {})
    current_stage = state.get("stage")

    if text.startswith("/redeem"):
        parts = text.split()
        if len(parts) > 1:
            await execute_voucher_redemption(update, user_id, parts[1].strip())
        else:
            await update.message.reply_text("Usage: <code>/redeem VOUCHER-CODE</code>", parse_mode=ParseMode.HTML)
        return

    if current_stage == "AWAITING_CUSTOM_EMAIL":
        if not re.match(r"^[^@]+@[^@]+\.[^@]+$", text):
            await update.message.reply_text("⚠️ Invalid email format. Try again or tap cancel:")
            return
        user_input_states[user_id] = {"stage": "AWAITING_CUSTOM_PASS", "email": text}
        await update.message.reply_text(
            f"📧 Address: <code>{text}</code>\n\n"
            f"Now send the <b>16-digit Google App Password</b>:\n"
            f"<i>(Example: abcd efgh ijkl mnop)</i>\n\n"
            f"⚠️ <i>Make sure IMAP is enabled in your Gmail settings!</i>",
            parse_mode=ParseMode.HTML,
        )
        return

    elif current_stage == "AWAITING_CUSTOM_PASS":
        raw_code = text.replace(" ", "")
        if len(raw_code) != 16 or not raw_code.isalnum():
            await update.message.reply_text("⚠️ App password must be exactly 16 characters. Please resend:")
            return

        if user_info["credits"] < COST_CUSTOM_MAIL:
            await update.message.reply_text("❌ Insufficient credits.", parse_mode=ParseMode.HTML)
            user_input_states.pop(user_id, None)
            return

        email_addr = state["email"]
        await update.message.reply_text("⏳ <i>Testing Gmail IMAP connection & loading inbox...</i>", parse_mode=ParseMode.HTML)
        
        test_fetch = await check_gmail_messages(email_addr, raw_code)
        
        user_info["credits"] -= COST_CUSTOM_MAIL
        custom_id = f"c_{''.join(random.choices(string.ascii_lowercase + string.digits, k=8))}"

        user_info["mailboxes"][custom_id] = {
            "id": custom_id,
            "type": "custom",
            "address": email_addr,
            "password": raw_code,
            "seen_ids": [str(m["id"]) for m in test_fetch],
            "total_received": len(test_fetch),
        }
        gmail_cache[custom_id] = test_fetch
        await save_storage()
        user_input_states.pop(user_id, None)

        ack = (
            f"✅ <b>Gmail Account Connected Successfully!</b>\n"
            f"📧 <code>{email_addr}</code>\n"
            f"💰 Charged: <code>{COST_CUSTOM_MAIL} Credits</code>\n"
            f"🛡️ <i>Full {REFUND_CUSTOM_MAIL} Credits will be refunded when deleted.</i>\n\n"
            f"Loaded <b>{len(test_fetch)}</b> total messages."
        )
        t, kb = build_user_home_screen(user_id)
        await update.message.reply_text(ack, parse_mode=ParseMode.HTML)
        msg = await update.message.reply_text(t, parse_mode=ParseMode.HTML, reply_markup=kb)
        user_active_view[user_id] = (msg.chat_id, msg.message_id)
        return

    elif current_stage == "AWAITING_PAYMENT_AMOUNT":
        try:
            amt = float(text)
            if amt < MIN_INR_PURCHASE:
                await update.message.reply_text(f"Minimum amount is ₹{MIN_INR_PURCHASE}. Please enter a valid sum:")
                return
            user_input_states.pop(user_id, None)
            await initiate_payment_invoice(update, context, amt)
        except ValueError:
            await update.message.reply_text("Invalid amount. Enter a numeric value in ₹:")
        return

    elif current_stage == "AWAITING_PAYMENT_PROOF":
        order_id = state.get("order_id")
        if order_id and order_id in data_store["orders"]:
            ord_data = data_store["orders"][order_id]
            ord_data["user_utr_or_note"] = text
            ord_data["submitted_at"] = int(time.time())
            await save_storage()
            user_input_states.pop(user_id, None)
            await update.message.reply_text("✅ Receipt details routed to Admin for verification.", parse_mode=ParseMode.HTML)
            await alert_admin_new_payment(context.application.bot_data["admin_bot"], order_id)
            return

    elif current_stage == "AWAITING_VOUCHER_CODE":
        user_input_states.pop(user_id, None)
        await execute_voucher_redemption(update, user_id, text)
        return


async def user_photo_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    user_id = user.id

    unjoined = await get_unjoined_channels(context.bot, user_id)
    if unjoined:
        text, kb = build_force_join_screen(unjoined)
        await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return

    state = user_input_states.get(user_id, {})
    if state.get("stage") == "AWAITING_PAYMENT_PROOF":
        photo = update.message.photo[-1]
        order_id = state.get("order_id")
        if order_id and order_id in data_store["orders"]:
            ord_data = data_store["orders"][order_id]
            ord_data["photo_file_id"] = photo.file_id
            ord_data["submitted_at"] = int(time.time())
            await save_storage()
            user_input_states.pop(user_id, None)
            await update.message.reply_text("✅ Screenshot submitted! Awaiting administrator approval.", parse_mode=ParseMode.HTML)
            await alert_admin_new_payment(context.application.bot_data["admin_bot"], order_id, photo.file_id)


async def execute_voucher_redemption(update: Update, user_id: int, code: str) -> None:
    code = code.strip().upper()
    vouchers = data_store.get("vouchers", {})
    if code not in vouchers:
        await update.message.reply_text("❌ Invalid or expired voucher code.", parse_mode=ParseMode.HTML)
        return

    v_data = vouchers[code]
    redeemed_users = v_data.get("claimed_by", [])
    if user_id in redeemed_users:
        await update.message.reply_text("⚠️ You have already claimed this voucher.", parse_mode=ParseMode.HTML)
        return

    if len(redeemed_users) >= v_data["max_uses"]:
        await update.message.reply_text("❌ Voucher has reached maximum redemption capacity.", parse_mode=ParseMode.HTML)
        return

    credits_to_add = v_data["credits"]
    uinfo = get_or_create_user(user_id)
    uinfo["credits"] += credits_to_add
    redeemed_users.append(user_id)
    v_data["claimed_by"] = redeemed_users
    await save_storage()

    await update.message.reply_text(
        f"🎉 <b>Success!</b> Code redeemed for <b>+{credits_to_add} Credits</b>.\n"
        f"💰 New Balance: <code>{uinfo['credits']} Credits</code>",
        parse_mode=ParseMode.HTML,
    )

# ============================================================================
# ADMIN BOT: DASHBOARD & DYNAMIC CHANNEL MANAGEMENT
# ============================================================================
def build_admin_dashboard() -> Tuple[str, InlineKeyboardMarkup]:
    pending_count = sum(1 for o in data_store["orders"].values() if o.get("status") == "PENDING_VERIFICATION")
    total_users = len(data_store["users"])
    total_credits = sum(u.get("credits", 0) for u in data_store["users"].values())
    channels = data_store.get("config", {}).get("required_channels", [])

    badge = f" ({pending_count})" if pending_count > 0 else ""
    text = (
        f"<b>🛡️ Administrative Command Console</b>\n\n"
        f"👥 <b>Total Users:</b> <code>{total_users}</code>\n"
        f"🪙 <b>Circulating Credits:</b> <code>{total_credits}</code>\n"
        f"⏳ <b>Pending Payment Reviews:</b> <code>{pending_count}</code>\n"
        f"📢 <b>Active Channels:</b> <code>{len(channels)}</code>"
    )
    keyboard = [
        [InlineKeyboardButton(f"📥 Pending Approvals{badge}", callback_data="a:queue")],
        [
            InlineKeyboardButton("📢 Manage Channels", callback_data="a:channel_menu"),
            InlineKeyboardButton("🎟️ Create Voucher", callback_data="a:new_voucher"),
        ],
        [
            InlineKeyboardButton("🎁 Gift Credits", callback_data="a:gift_prompt"),
            InlineKeyboardButton("👥 User Directory", callback_data="a:users"),
        ],
        [
            InlineKeyboardButton("🌐 Host Network Info", callback_data="a:net_info"),
            InlineKeyboardButton("🔄 Refresh Panel", callback_data="a:dash"),
        ],
    ]
    return text, InlineKeyboardMarkup(keyboard)


def build_admin_channel_menu() -> Tuple[str, InlineKeyboardMarkup]:
    channels = data_store.get("config", {}).get("required_channels", [])
    text = "📢 <b>Channel Force-Join Settings</b>\n\n"
    if channels:
        text += "<b>Current Required Channels:</b>\n"
        for idx, ch in enumerate(channels, start=1):
            text += f"{idx}. <code>{ch}</code>\n"
    else:
        text += "<i>No channels currently enforced (bot is open to everyone).</i>\n"

    keyboard = [
        [InlineKeyboardButton("➕ Add Channel", callback_data="a:add_ch_prompt")],
        [InlineKeyboardButton("🗑️ Remove Channel", callback_data="a:del_ch_menu")],
        [InlineKeyboardButton("🔙 Back to Dashboard", callback_data="a:dash")],
    ]
    return text, InlineKeyboardMarkup(keyboard)


async def alert_admin_new_payment(admin_bot, order_id: str, photo_file_id: Optional[str] = None) -> None:
    order = data_store["orders"].get(order_id)
    if not order:
        return
    caption = (
        f"🔔 <b>New Payment Verification Request</b>\n\n"
        f"🆔 <b>Order:</b> <code>{order_id}</code>\n"
        f"👤 <b>User Telegram ID:</b> <code>{order['user_id']}</code>\n"
        f"💵 <b>Amount:</b> ₹{order['amount_inr']} (<b>+{order['credits']} Credits</b>)\n"
    )
    kb = InlineKeyboardMarkup([
        [
            InlineKeyboardButton("✅ Approve", callback_data=f"a:appr:{order_id}"),
            InlineKeyboardButton("❌ Reject", callback_data=f"a:rejc:{order_id}"),
        ]
    ])
    try:
        if photo_file_id:
            await admin_bot.send_photo(chat_id=ADMIN_TELEGRAM_ID, photo=photo_file_id, caption=caption, parse_mode=ParseMode.HTML, reply_markup=kb)
        else:
            await admin_bot.send_message(chat_id=ADMIN_TELEGRAM_ID, text=caption, parse_mode=ParseMode.HTML, reply_markup=kb)
    except Exception as e:
        logger.error(f"Failed to alert admin of payment: {e}")


async def admin_start_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        return
    text, kb = build_admin_dashboard()
    await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def admin_callback_dispatcher(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        return

    data = query.data
    user_bot: Application = context.application.bot_data["user_bot"]

    if data == "a:dash":
        text, kb = build_admin_dashboard()
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

    elif data == "a:channel_menu":
        text, kb = build_admin_channel_menu()
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

    elif data == "a:add_ch_prompt":
        admin_input_states[ADMIN_TELEGRAM_ID] = {"stage": "ADD_CHANNEL"}
        text = (
            "➕ <b>Add Required Channel</b>\n\n"
            "Send the channel username (e.g., <code>@mychannel</code>):\n"
            "<i>Remember to add the User Bot as an Admin in the channel first!</i>"
        )
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="a:channel_menu")]])
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

    elif data == "a:del_ch_menu":
        channels = data_store.get("config", {}).get("required_channels", [])
        if not channels:
            await query.answer("No channels to delete!", show_alert=True)
            return
        text = "🗑️ <b>Select Channel to Remove:</b>"
        keyboard = []
        for ch in channels:
            keyboard.append([InlineKeyboardButton(f"❌ Delete {ch}", callback_data=f"a:del_ch:{ch}")])
        keyboard.append([InlineKeyboardButton("🔙 Cancel", callback_data="a:channel_menu")])
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard))

    elif data.startswith("a:del_ch:"):
        ch_to_del = data.split(":", 2)[2]
        channels = data_store.get("config", {}).get("required_channels", [])
        if ch_to_del in channels:
            channels.remove(ch_to_del)
            await save_storage()
            await query.answer(f"Channel {ch_to_del} removed!", show_alert=True)
        text, kb = build_admin_channel_menu()
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

    elif data == "a:queue":
        pending = [o for o in data_store["orders"].values() if o.get("status") == "PENDING_VERIFICATION"]
        if not pending:
            await query.edit_message_text("✅ <b>No pending approvals.</b>", parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🔙 Dashboard", callback_data="a:dash")]
            ]))
            return

        target = pending[0]
        oid = target["order_id"]
        uid = target["user_id"]
        uinfo = data_store["users"].get(str(uid), {})
        text = (
            f"📋 <b>Review Payment Order</b>\n\n"
            f"🆔 <b>Order:</b> <code>{oid}</code>\n"
            f"👤 <b>System ID:</b> <code>{uinfo.get('system_id', 'N/A')}</code>\n"
            f"💬 <b>User ID:</b> <code>{uid}</code>\n"
            f"💵 <b>Amount:</b> ₹{target['amount_inr']}\n"
            f"🪙 <b>Credits to Award:</b> {target['credits']}\n"
        )
        kb = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("✅ Approve", callback_data=f"a:appr:{oid}"),
                InlineKeyboardButton("❌ Reject", callback_data=f"a:rejc:{oid}"),
            ],
            [InlineKeyboardButton("🔙 Dashboard", callback_data="a:dash")],
        ])

        if target.get("photo_file_id"):
            await query.message.reply_photo(photo=target["photo_file_id"], caption=text, parse_mode=ParseMode.HTML, reply_markup=kb)
            await query.message.delete()
        else:
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)

    elif data.startswith("a:appr:"):
        oid = data.split(":")[2]
        order = data_store["orders"].get(oid)
        if order and order.get("status") == "PENDING_VERIFICATION":
            order["status"] = "APPROVED"
            uid = order["user_id"]
            credits_added = order["credits"]
            uinfo = get_or_create_user(uid)
            uinfo["credits"] += credits_added
            await save_storage()

            await query.edit_message_text(f"✅ Approved Order <code>{oid}</code> (+{credits_added} Credits).", parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("Next Pending", callback_data="a:queue")],
                [InlineKeyboardButton("Dashboard", callback_data="a:dash")],
            ]))

            try:
                await user_bot.bot.send_message(
                    chat_id=uid,
                    text=f"✅ <b>Payment Approved!</b>\nAdded <b>+{credits_added} Credits</b> to your balance.",
                    parse_mode=ParseMode.HTML,
                )
            except Exception:
                pass

    elif data.startswith("a:rejc:"):
        oid = data.split(":")[2]
        order = data_store["orders"].get(oid)
        if order and order.get("status") == "PENDING_VERIFICATION":
            order["status"] = "REJECTED"
            await save_storage()
            await query.edit_message_text(f"❌ Rejected Order <code>{oid}</code>.", parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("Next Pending", callback_data="a:queue")],
                [InlineKeyboardButton("Dashboard", callback_data="a:dash")],
            ]))
            try:
                await user_bot.bot.send_message(
                    chat_id=order["user_id"],
                    text=f"❌ <b>Payment Rejected:</b> Order <code>{oid}</code> could not be verified.",
                    parse_mode=ParseMode.HTML,
                )
            except Exception:
                pass

    elif data == "a:new_voucher":
        admin_input_states[ADMIN_TELEGRAM_ID] = {"stage": "VOUCHER_CREDITS"}
        await query.edit_message_text("🎟️ <b>Create Voucher:</b> Send the credit amount (e.g. 50):", parse_mode=ParseMode.HTML)

    elif data == "a:gift_prompt":
        admin_input_states[ADMIN_TELEGRAM_ID] = {"stage": "GIFT_TARGET"}
        await query.edit_message_text("🎁 <b>Direct Credit Gift:</b> Send recipient's System ID or Telegram ID:", parse_mode=ParseMode.HTML)

    elif data == "a:users":
        users = list(data_store["users"].values())[-10:]
        lines = ["📋 <b>Latest Registered Users:</b>\n"]
        for u in users:
            lines.append(f"• <code>{u['system_id']}</code> | ID: <code>{u['telegram_id']}</code> | Cr: <b>{u['credits']}</b>")
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Dashboard", callback_data="a:dash")]])
        await query.edit_message_text("\n".join(lines), parse_mode=ParseMode.HTML, reply_markup=kb)

    elif data == "a:net_info":
        await inspect_network_host(query)


async def inspect_network_host(target) -> None:
    ip = "Unknown"
    async with httpx.AsyncClient(timeout=5.0) as client:
        try:
            r = await client.get("https://api.ipify.org?format=json")
            if r.status_code == 200:
                ip = r.json().get("ip", "Unknown")
        except Exception as e:
            ip = f"Error: {e}"

    text = f"🌐 <b>Host Network Inspection</b>\n\nPublic Outbound IP: <code>{ip}</code>"
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Dashboard", callback_data="a:dash")]])
    if hasattr(target, "edit_message_text"):
        await target.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await target.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def admin_text_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user.id != ADMIN_TELEGRAM_ID:
        return
    text = update.message.text.strip()
    state = admin_input_states.get(ADMIN_TELEGRAM_ID, {})
    stage = state.get("stage")

    if text in ("/current_ip", "/change_ip"):
        await inspect_network_host(update.message)
        return

    if stage == "ADD_CHANNEL":
        clean_ch = text.split("/")[-1]
        channel_name = clean_ch if clean_ch.startswith("@") else f"@{clean_ch}"
        channels = data_store.get("config", {}).get("required_channels", [])

        if channel_name in channels:
            await update.message.reply_text("⚠️ This channel is already in the list.")
        else:
            channels.append(channel_name)
            await save_storage()
            await update.message.reply_text(
                f"✅ <b>Channel Added:</b> <code>{channel_name}</code>\n"
                f"All users must now join this channel to access the bot.",
                parse_mode=ParseMode.HTML,
            )
        admin_input_states.pop(ADMIN_TELEGRAM_ID, None)
        t, kb = build_admin_channel_menu()
        await update.message.reply_text(t, parse_mode=ParseMode.HTML, reply_markup=kb)
        return

    elif stage == "VOUCHER_CREDITS":
        try:
            cr = int(text)
            admin_input_states[ADMIN_TELEGRAM_ID] = {"stage": "VOUCHER_MAX_USES", "credits": cr}
            await update.message.reply_text(f"Credits set to {cr}. Now specify <b>Maximum Number of Claims</b>:")
        except ValueError:
            await update.message.reply_text("Enter a valid integer credit value:")
        return

    elif stage == "VOUCHER_MAX_USES":
        try:
            uses = int(text)
            cr = state["credits"]
            code = f"GIFT-{''.join(random.choices(string.ascii_uppercase + string.digits, k=8))}"
            data_store["vouchers"][code] = {
                "code": code,
                "credits": cr,
                "max_uses": uses,
                "claimed_by": [],
                "created_at": int(time.time()),
            }
            await save_storage()
            admin_input_states.pop(ADMIN_TELEGRAM_ID, None)
            await update.message.reply_text(
                f"🎟️ <b>Voucher Created!</b>\n\n"
                f"Code: <code>{code}</code>\n"
                f"Value: <b>{cr} Credits</b>\n"
                f"Capacity: <b>{uses} Claims</b>\n\n"
                f"Redeem command: <code>/redeem {code}</code>",
                parse_mode=ParseMode.HTML,
            )
        except ValueError:
            await update.message.reply_text("Enter a valid integer number of claims:")
        return

    elif stage == "GIFT_TARGET":
        target = find_user_by_any_id(text)
        if not target:
            await update.message.reply_text("⚠️ User not found. Send a valid System ID or Telegram ID:")
            return
        uid, udata = target
        admin_input_states[ADMIN_TELEGRAM_ID] = {"stage": "GIFT_AMOUNT", "target_uid": uid}
        await update.message.reply_text(f"Target: <code>{udata['system_id']}</code>. Send credit amount to grant:")
        return

    elif stage == "GIFT_AMOUNT":
        try:
            cr = int(text)
            uid = state["target_uid"]
            uinfo = data_store["users"][uid]
            uinfo["credits"] += cr
            await save_storage()
            admin_input_states.pop(ADMIN_TELEGRAM_ID, None)

            await update.message.reply_text(f"🎁 Granted <b>+{cr} Credits</b> to <code>{uinfo['system_id']}</code>!", parse_mode=ParseMode.HTML)
            user_bot: Application = context.application.bot_data["user_bot"]
            try:
                await user_bot.bot.send_message(
                    chat_id=int(uid),
                    text=f"🎁 <b>Credit Gift Received!</b>\nAn administrator granted you <b>+{cr} Credits</b>.",
                    parse_mode=ParseMode.HTML,
                )
            except Exception:
                pass
        except ValueError:
            await update.message.reply_text("Invalid credit amount. Enter an integer:")
        return

# ============================================================================
# CONCURRENT EVENT LOOP
# ============================================================================
async def main() -> None:
    load_storage_sync()

    req_config = HTTPXRequest(
        connect_timeout=30.0,
        read_timeout=30.0,
        write_timeout=30.0,
        pool_timeout=30.0,
    )

    user_app = ApplicationBuilder().token(USER_BOT_TOKEN).request(req_config).build()
    admin_app = ApplicationBuilder().token(ADMIN_BOT_TOKEN).request(req_config).build()

    user_app.bot_data["admin_bot"] = admin_app.bot
    admin_app.bot_data["user_bot"] = user_app

    # User Handlers
    user_app.add_handler(CommandHandler("start", user_start_handler))
    user_app.add_handler(CommandHandler("redeem", user_text_handler))
    user_app.add_handler(CallbackQueryHandler(user_callback_dispatcher))
    user_app.add_handler(MessageHandler(filters.PHOTO, user_photo_handler))
    user_app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, user_text_handler))

    # Admin Handlers
    admin_app.add_handler(CommandHandler("start", admin_start_handler))
    admin_app.add_handler(CommandHandler("current_ip", admin_text_handler))
    admin_app.add_handler(CommandHandler("change_ip", admin_text_handler))
    admin_app.add_handler(CallbackQueryHandler(admin_callback_dispatcher))
    admin_app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, admin_text_handler))

    shutdown_event = asyncio.Event()

    def signal_handler():
        logger.info("Shutdown signal received. Commencing graceful teardown...")
        shutdown_event.set()

    loop = asyncio.get_running_loop()
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            loop.add_signal_handler(sig, signal_handler)
        except NotImplementedError:
            pass

    async with user_app, admin_app:
        await user_app.initialize()
        await admin_app.initialize()

        await user_app.start()
        await admin_app.start()

        await user_app.updater.start_polling(drop_pending_updates=True, timeout=20)
        await admin_app.updater.start_polling(drop_pending_updates=True, timeout=20)

        polling_worker_task = asyncio.create_task(user_inbox_polling_worker(user_app))

        logger.info("Both User and Admin Bots successfully started in concurrent loop.")

        await shutdown_event.wait()

        logger.info("Stopping polling routines and background tasks...")
        polling_worker_task.cancel()
        try:
            await polling_worker_task
        except asyncio.CancelledError:
            pass

        await user_app.updater.stop()
        await admin_app.updater.stop()

        await user_app.stop()
        await admin_app.stop()

        logger.info("Flushing runtime state to disk...")
        await save_storage()
        logger.info("Teardown complete. Exiting cleanly.")


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        logger.info("Bot execution terminated.")
