"""
Mendikot — single-file web game.
Backend (FastAPI + WebSocket) + game engine + embedded React frontend (no Babel).

Run:
    pip install fastapi uvicorn
    python main.py
Open http://localhost:8000
"""

import asyncio
import json
import random
import string
import time
import uuid
from contextlib import asynccontextmanager
from dataclasses import dataclass, field
from typing import Optional

import uvicorn
from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse

# ================================================================ constants

SUITS = ["S", "H", "D", "C"]
RANKS = ["2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A"]
RANK_VALUE = {r: i for i, r in enumerate(RANKS)}

PHASE1_TRICKS = 5          # tricks played from the initial 5-card deal
TOTAL_TRICKS = 13
TRICK_PAUSE = 3.0          # seconds a finished trick stays on the table
BOT_DELAY = (0.6, 1.4)     # bot "thinking" window (seconds)
RECONNECT_GRACE = 15.0     # wait this long for a rejoin before cancelling
ROOM_TTL = 600             # GC: remove rooms inactive for 10 minutes
GC_INTERVAL = 60
BOT_NAMES = {1: "West Bot", 2: "North Bot", 3: "East Bot"}


def team_of(seat): return "A" if seat % 2 == 0 else "B"
def new_deck(): return [r + s for s in SUITS for r in RANKS]
def card_suit(c): return c[-1]
def card_rank(c): return c[:-1]
def rank_value(c): return RANK_VALUE[c[:-1]]
def is_mendi(c): return c[:-1] == "10"
def sort_key(c): return (SUITS.index(c[-1]), RANK_VALUE[c[:-1]])


def clean_name(s):
    s = (s or "").strip()[:18]
    return s or "Player"


def new_id():
    return uuid.uuid4().hex


# ================================================================ game engine

@dataclass
class MendikotHand:
    dealer: int
    hands: dict                      # seat -> [card, ...]
    boot: list                       # undealt 32 cards
    leader: int                      # seat that leads the current trick
    boot_dealt: bool = False
    trump: Optional[str] = None
    trump_card: Optional[str] = None
    trick: list = field(default_factory=list)        # [(seat, card)] in play order
    last_trick: list = field(default_factory=list)   # shown during the pause
    last_trick_winner: Optional[int] = None
    trick_num: int = 1
    turn: Optional[int] = None
    paused: bool = False
    complete: bool = False
    winner: Optional[str] = None     # 'A' | 'B' | None (draw)
    mendi: dict = field(default_factory=lambda: {"A": [], "B": []})   # suits of won 10s
    team_cards: dict = field(default_factory=lambda: {"A": 0, "B": 0})
    exempt: set = field(default_factory=set)         # mid-trick follow-suit exemption
    pending_boot: bool = False

    @classmethod
    def new_hand(cls, dealer):
        deck = new_deck()
        random.shuffle(deck)
        order = [(dealer + 1 + i) % 4 for i in range(4)]
        hands = {s: [] for s in range(4)}
        for _ in range(5):
            for s in order:
                hands[s].append(deck.pop())
        for s in range(4):
            hands[s].sort(key=sort_key)
        leader = (dealer + 1) % 4
        return cls(dealer=dealer, hands=hands, boot=deck, leader=leader, turn=leader)

    # ---- legality ----------------------------------------------------------

    def must_reveal(self, seat):
        """True if `seat` is void in the led suit during phase 1 and must reveal trump."""
        if self.complete or self.paused or self.turn != seat or not self.trick:
            return False
        if self.trump is not None or self.boot_dealt or seat in self.exempt:
            return False
        led = card_suit(self.trick[0][1])
        return all(card_suit(c) != led for c in self.hands[seat])

    def legal_cards(self, seat):
        if self.complete or self.paused or self.turn != seat:
            return []
        hand = self.hands[seat]
        if not self.trick or seat in self.exempt:
            return list(hand)
        led = card_suit(self.trick[0][1])
        follows = [c for c in hand if card_suit(c) == led]
        return follows if follows else list(hand)   # void: reveal candidates or any card

    # ---- actions -----------------------------------------------------------

    def play(self, seat, card, as_reveal=False):
        self.hands[seat].remove(card)
        if not self.trick:                          # first play of a new trick
            self.last_trick = []
            self.last_trick_winner = None
        self.trick.append((seat, card))
        if as_reveal:
            self.trump = card_suit(card)
            self.trump_card = card
            led = card_suit(self.trick[0][1])
            played = {s for s, _ in self.trick}
            for s in range(4):                      # mid-trick exemption (defensive)
                if s not in played and all(card_suit(c) != led for c in self.hands[s]):
                    self.exempt.add(s)
        if len(self.trick) == 4:
            self.paused = True
            self.turn = None
        else:
            self.turn = (seat + 1) % 4

    def resolve_trick(self):
        led = card_suit(self.trick[0][1])
        trump = self.trump

        def power(sc):
            c = sc[1]
            if trump and card_suit(c) == trump:
                return (2, rank_value(c))
            if card_suit(c) == led:
                return (1, rank_value(c))
            return (0, rank_value(c))

        wseat, _ = max(self.trick, key=power)
        team = team_of(wseat)
        self.team_cards[team] += 4
        gained = [card_suit(c) for _, c in self.trick if is_mendi(c)]
        self.mendi[team].extend(gained)
        self.last_trick = list(self.trick)
        self.last_trick_winner = wseat
        self.trick = []
        self.exempt.clear()
        self.pending_boot = (not self.boot_dealt) and (
            self.trump is not None or self.trick_num >= PHASE1_TRICKS)
        if self.trick_num >= TOTAL_TRICKS:
            self.complete = True
            a, b = len(self.mendi["A"]), len(self.mendi["B"])
            self.winner = "A" if a > b else ("B" if b > a else None)
            self.turn = None
        else:
            self.trick_num += 1
            self.leader = wseat
            self.turn = wseat
        return wseat, team, gained

    def deal_boot(self):
        self.boot_dealt = True
        self.pending_boot = False
        order = [(self.dealer + 1 + i) % 4 for i in range(4)]
        for s in order:
            self.hands[s].extend(self.boot[:8])
            del self.boot[:8]
            self.hands[s].sort(key=sort_key)

    # ---- bots ---------------------------------------------------------------

    def bot_choose(self, seat):
        """Lowest legal card; if forced to reveal, lowest card overall."""
        if self.must_reveal(seat):
            return min(self.hands[seat], key=rank_value), True
        return min(self.legal_cards(seat), key=rank_value), False


# ================================================================ rooms

@dataclass
class Player:
    pid: str
    name: str
    seat: int
    is_bot: bool = False
    ws: Optional[WebSocket] = None
    connected: bool = False


@dataclass
class Room:
    code: str
    players: dict = field(default_factory=dict)      # seat -> Player
    host_seat: int = 0
    dealer: int = 0
    started: bool = False
    solo: bool = False
    hand: Optional[MendikotHand] = None
    last_active: float = field(default_factory=time.time)
    tasks: set = field(default_factory=set)


class RoomManager:
    def __init__(self):
        self.rooms = {}

    def get(self, code):
        if not code:
            return None
        return self.rooms.get(str(code).strip().upper())

    def add(self, room):
        self.rooms[room.code] = room

    def remove(self, code):
        room = self.rooms.pop(code, None)
        if room:
            for t in room.tasks:
                t.cancel()
        return room

    def new_code(self):
        while True:
            code = "".join(random.choices(string.ascii_uppercase + string.digits, k=5))
            if code not in self.rooms:
                return code


MGR = RoomManager()


# ================================================================ payloads

def seat_info(room, s):
    p = room.players.get(s)
    return {"seat": s, "name": p.name if p else None, "team": team_of(s),
            "is_bot": p.is_bot if p else False, "connected": p.connected if p else False}


def game_payload(room, seat):
    hand = room.hand
    return {
        "type": "game_state", "seat": seat,
        "hand": hand.hands[seat],
        "legal": hand.legal_cards(seat),
        "must_reveal": hand.must_reveal(seat),
        "turn": hand.turn,
        "trick": [{"seat": s, "card": c} for s, c in hand.trick],
        "last_trick": [{"seat": s, "card": c} for s, c in hand.last_trick],
        "last_trick_winner": hand.last_trick_winner,
        "trick_num": hand.trick_num,
        "trump": hand.trump, "trump_card": hand.trump_card,
        "boot_dealt": hand.boot_dealt,
        "mendi": hand.mendi, "team_cards": hand.team_cards,
        "dealer": hand.dealer, "leader": hand.leader,
        "paused": hand.paused, "complete": hand.complete, "winner": hand.winner,
        "seats": [seat_info(room, s) for s in range(4)],
        "hand_sizes": {s: len(hand.hands[s]) for s in range(4)},
    }


def lobby_payload(room, for_pid=None):
    you = None
    for s, p in room.players.items():
        if p.pid == for_pid:
            you = {"seat": s, "host": s == room.host_seat}
    return {"type": "lobby", "code": room.code,
            "seats": [seat_info(room, s) for s in range(4)],
            "full": len(room.players) == 4,
            "host_seat": room.host_seat, "you": you}


async def send(ws, obj):
    try:
        await ws.send_text(json.dumps(obj))
    except Exception:
        pass


async def broadcast(room, obj):
    text = json.dumps(obj)
    for p in room.players.values():
        if not p.is_bot and p.connected and p.ws:
            try:
                await p.ws.send_text(text)
            except Exception:
                p.connected = False


async def broadcast_state(room):
    for p in room.players.values():
        if not p.is_bot and p.connected and p.ws:
            await send(p.ws, game_payload(room, p.seat))


async def broadcast_lobby(room):
    for p in room.players.values():
        if not p.is_bot and p.connected and p.ws:
            await send(p.ws, lobby_payload(room, p.pid))


# ================================================================ game flow

def schedule_bot(room):
    hand = room.hand
    if hand is None or hand.complete or hand.paused or hand.turn is None:
        return
    p = room.players.get(hand.turn)
    if p and p.is_bot:
        t = asyncio.create_task(bot_turn(room))
        room.tasks.add(t)


async def bot_turn(room):
    try:
        await asyncio.sleep(random.uniform(*BOT_DELAY))
        hand = room.hand
        if (room.code not in MGR.rooms or hand is None or room.hand is not hand
                or hand.complete or hand.paused or hand.turn is None):
            return
        seat = hand.turn
        p = room.players.get(seat)
        if not p or not p.is_bot:
            return
        card, reveal = hand.bot_choose(seat)
        await do_move(room, seat, card, reveal)
    except asyncio.CancelledError:
        pass


async def do_move(room, seat, card, reveal):
    hand = room.hand
    hand.play(seat, card, as_reveal=reveal)
    if reveal:
        await broadcast(room, {"type": "trump_revealed", "seat": seat,
                               "card": card, "suit": hand.trump})
    await broadcast(room, {"type": "card_played", "seat": seat, "card": card})
    if len(hand.trick) == 4:
        t = asyncio.create_task(trick_end(room))
        room.tasks.add(t)
    else:
        await broadcast_state(room)
        schedule_bot(room)


async def trick_end(room):
    try:
        hand = room.hand
        wseat, team, gained = hand.resolve_trick()
        await broadcast(room, {"type": "trick_won", "winner": wseat,
                               "team": team, "mendi": gained})
        await broadcast_state(room)
        await asyncio.sleep(TRICK_PAUSE)
        if room.code not in MGR.rooms or room.hand is not hand:
            return
        if hand.complete:
            await broadcast(room, {"type": "hand_complete", "winner": hand.winner,
                                   "mendi": hand.mendi, "team_cards": hand.team_cards})
            await broadcast_state(room)
            return
        if hand.pending_boot:
            hand.deal_boot()
            await broadcast(room, {"type": "boot_dealt"})
        hand.paused = False
        await broadcast_state(room)
        schedule_bot(room)
    except asyncio.CancelledError:
        pass


async def start_game(room):
    room.started = True
    room.hand = MendikotHand.new_hand(room.dealer)
    await broadcast(room, {"type": "game_start", "dealer": room.dealer})
    await broadcast_state(room)
    schedule_bot(room)


async def cancel_room(room, reason):
    if room.code not in MGR.rooms:
        return
    await broadcast(room, {"type": "room_cancelled", "reason": reason})
    MGR.remove(room.code)


async def grace_cancel(room, pid, name):
    try:
        await asyncio.sleep(RECONNECT_GRACE)
        if room.code not in MGR.rooms:
            return
        p = next((p for p in room.players.values() if p.pid == pid), None)
        if p and not p.connected:
            await cancel_room(room, name + " disconnected")
    except asyncio.CancelledError:
        pass


async def handle_disconnect(room, pid):
    if room.code not in MGR.rooms:
        return
    p = next((p for p in room.players.values() if p.pid == pid), None)
    if not p:
        return
    p.connected = False
    p.ws = None
    room.last_active = time.time()
    if not room.started:
        if p.seat == room.host_seat:
            await cancel_room(room, "Host left")
        else:
            room.players.pop(p.seat, None)
            if room.players:
                await broadcast_lobby(room)
            else:
                MGR.remove(room.code)
    else:
        await broadcast(room, {"type": "seat_status", "seat": p.seat, "connected": False})
        if not room.solo:
            t = asyncio.create_task(grace_cancel(room, pid, p.name))
            room.tasks.add(t)


# ================================================================ server

async def gc_loop():
    while True:
        await asyncio.sleep(GC_INTERVAL)
        now = time.time()
        dead = [c for c, r in MGR.rooms.items() if now - r.last_active > ROOM_TTL]
        for code in dead:
            room = MGR.rooms.get(code)
            if room:
                await broadcast(room, {"type": "room_cancelled", "reason": "Room expired"})
                MGR.remove(code)


@asynccontextmanager
async def lifespan(_app):
    task = asyncio.create_task(gc_loop())
    yield
    task.cancel()


app = FastAPI(lifespan=lifespan)


@app.get("/")
async def index():
    return HTMLResponse(PAGE)


@app.websocket("/ws")
async def ws_endpoint(ws: WebSocket):
    await ws.accept()
    room: Optional[Room] = None
    me: Optional[Player] = None

    async def err(message):
        await send(ws, {"type": "error", "message": message})

    try:
        while True:
            try:
                msg = json.loads(await ws.receive_text())
            except json.JSONDecodeError:
                continue

            if room and room.code not in MGR.rooms:      # room vanished under us
                room, me = None, None
            if room:
                room.last_active = time.time()
            mtype = msg.get("type")

            # ---------------- lobby / room lifecycle ----------------
            if mtype == "create_room":
                if room:
                    continue
                team = "B" if msg.get("team") == "B" else "A"
                code = MGR.new_code()
                rm = Room(code=code)
                seat = 0 if team == "A" else 1
                pl = Player(pid=new_id(), name=clean_name(msg.get("name")),
                            seat=seat, ws=ws, connected=True)
                rm.players[seat] = pl
                rm.host_seat = rm.dealer = seat
                MGR.add(rm)
                room, me = rm, pl
                await send(ws, {"type": "joined", "player_id": pl.pid, "code": code,
                                "seat": seat, "host": True, "solo": False})
                await send(ws, lobby_payload(rm, pl.pid))

            elif mtype == "join_room":
                if room:
                    continue
                rm = MGR.get(msg.get("code"))
                if not rm:
                    await err("Room not found")
                    continue
                if rm.started:
                    await err("That game already started")
                    continue
                seats = [1, 3] if msg.get("team") == "B" else [0, 2]
                seat = next((s for s in seats if s not in rm.players), None)
                if seat is None:
                    await err("That team is full")
                    continue
                pl = Player(pid=new_id(), name=clean_name(msg.get("name")),
                            seat=seat, ws=ws, connected=True)
                rm.players[seat] = pl
                room, me = rm, pl
                await send(ws, {"type": "joined", "player_id": pl.pid, "code": rm.code,
                                "seat": seat, "host": False, "solo": False})
                await broadcast_lobby(rm)

            elif mtype == "start_solo":
                if room:
                    continue
                code = MGR.new_code()
                rm = Room(code=code, solo=True)
                pl = Player(pid=new_id(), name=clean_name(msg.get("name")),
                            seat=0, ws=ws, connected=True)
                rm.players[0] = pl
                for s in (1, 2, 3):
                    rm.players[s] = Player(pid=new_id(), name=BOT_NAMES[s],
                                           seat=s, is_bot=True, connected=True)
                rm.host_seat = rm.dealer = 0
                MGR.add(rm)
                room, me = rm, pl
                await send(ws, {"type": "joined", "player_id": pl.pid, "code": code,
                                "seat": 0, "host": True, "solo": True})
                await start_game(rm)

            elif mtype == "rejoin":
                rm = MGR.get(msg.get("code"))
                pl = next((p for p in rm.players.values()
                           if p.pid == msg.get("player_id")), None) if rm else None
                if not rm or not pl or pl.is_bot:
                    await send(ws, {"type": "rejoin_failed",
                                    "message": "Could not rejoin the room"})
                    continue
                pl.ws = ws
                pl.connected = True
                room, me = rm, pl
                await broadcast(rm, {"type": "seat_status", "seat": pl.seat, "connected": True})
                if rm.started and rm.hand:
                    await send(ws, game_payload(rm, pl.seat))
                else:
                    await send(ws, lobby_payload(rm, pl.pid))

            elif mtype == "start_game":
                if not room or not me:
                    continue
                if me.seat != room.host_seat:
                    await err("Only the host can start the game")
                    continue
                if room.started:
                    continue
                if len(room.players) < 4:
                    await err("Waiting for all 4 seats")
                    continue
                await start_game(room)

            elif mtype == "leave":
                if not room or not me:
                    continue
                rm, pl = room, me
                room, me = None, None
                if rm.solo:
                    await send(ws, {"type": "room_cancelled", "reason": ""})
                    MGR.remove(rm.code)
                elif rm.started:
                    await cancel_room(rm, pl.name + " left the game")
                elif pl.seat == rm.host_seat:
                    await cancel_room(rm, "Host left")
                else:
                    rm.players.pop(pl.seat, None)
                    if rm.players:
                        await broadcast_lobby(rm)
                    else:
                        MGR.remove(rm.code)

            # ---------------- gameplay ----------------
            elif mtype == "play_card":
                if not room or not me or not room.hand:
                    continue
                hand = room.hand
                if hand.complete or hand.paused or hand.turn != me.seat:
                    await err("Not your turn")
                    continue
                if hand.must_reveal(me.seat):
                    await err("You cannot follow suit — reveal a trump card instead")
                    continue
                card = msg.get("card")
                if card not in hand.legal_cards(me.seat):
                    await err("You must follow the led suit")
                    continue
                await do_move(room, me.seat, card, False)

            elif mtype == "reveal_trump":
                if not room or not me or not room.hand:
                    continue
                hand = room.hand
                if hand.complete or hand.paused or hand.turn != me.seat:
                    await err("Not your turn")
                    continue
                if not hand.must_reveal(me.seat):
                    await err("You can only reveal trump when you cannot follow suit")
                    continue
                card = msg.get("card")
                if card not in hand.hands[me.seat]:
                    await err("That card is not in your hand")
                    continue
                await do_move(room, me.seat, card, True)

            elif mtype == "rematch":
                if not room or not me or not room.started or not room.hand:
                    continue
                if me.seat != room.host_seat:
                    await err("Only the host can start a rematch")
                    continue
                if not room.hand.complete:
                    continue
                room.dealer = (room.dealer + 1) % 4
                room.hand = MendikotHand.new_hand(room.dealer)
                await broadcast(room, {"type": "new_hand", "dealer": room.dealer})
                await broadcast_state(room)
                schedule_bot(room)

    except WebSocketDisconnect:
        pass
    except Exception:
        pass
    finally:
        if room and me:
            await handle_disconnect(room, me.pid)


# ================================================================ frontend
# React 18 UMD only — components are written with React.createElement.
# No JSX, no Babel, no build step.

PAGE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no">
<title>ꯗ꯭ꯁ ꯐꯥꯕꯤ</title>
<style>
:root{
  --bg:#0b2318; --felt1:#2f8f5e; --felt2:#1c6440; --felt3:#124a2d;
  --panel:#0f3524; --panel2:#123b29; --ink:#f2efe4; --muted:#9fc4ae;
  --gold:#ffd76a; --gold2:#d9a93f; --red:#c0392b; --black:#20242a;
  --ta:#6ab7ff; --tb:#ff8a80;
}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html,body{margin:0;padding:0;height:100%;background:var(--bg);color:var(--ink);
  font-family:system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
#root{height:100%}
button{font-family:inherit}
.app{height:100vh;height:100dvh;max-width:520px;margin:0 auto;display:flex;
  flex-direction:column;position:relative;overflow:hidden}
.view{flex:1;display:flex;flex-direction:column;gap:14px;padding:26px 22px;overflow-y:auto}
.view.center{justify-content:center}
h1,h2,h3{margin:0}
.logo{text-align:center;margin-bottom:8vh}
.logo h1{font-size:42px;letter-spacing:8px;color:var(--gold);font-weight:800}
.tagline{color:var(--muted);margin:8px 0 0}
.btn{display:flex;flex-direction:column;align-items:center;gap:2px;width:100%;
  padding:14px;border-radius:14px;border:0;font-size:17px;font-weight:700;cursor:pointer}
.btn.big{padding:18px 14px}
.btn.gold{background:linear-gradient(180deg,#f5d67f,var(--gold2));color:#3c2d07}
.btn.green{background:#2c8a5c;color:#fff}
.btn.ghost{background:transparent;border:1px solid #ffffff3d;color:var(--ink);font-weight:600}
.btn:disabled{opacity:.45}
.btn-sub{font-size:12px;font-weight:500;opacity:.75}
.fld{display:flex;flex-direction:column;gap:6px;font-size:13px;color:var(--muted)}
input{width:100%;padding:13px;border-radius:12px;border:1px solid #ffffff2e;
  background:#ffffff12;color:#fff;font-size:16px;outline:none}
input:focus{border-color:var(--gold)}
.team-pick{display:flex;gap:10px}
.team-btn{flex:1;padding:14px 8px;border-radius:14px;border:2px solid #ffffff2e;
  background:#ffffff0d;color:var(--ink);font-size:16px;font-weight:700;cursor:pointer;
  display:flex;flex-direction:column;gap:2px;align-items:center}
.team-btn.sel.ta{border-color:var(--ta);background:#6ab7ff22}
.team-btn.sel.tb{border-color:var(--tb);background:#ff8a8022}
.muted{color:var(--muted)} .small{font-size:13px} .center-text{text-align:center}
.room-code{color:var(--gold);letter-spacing:4px;font-weight:800}
.chip{display:inline-block;background:#ffffff22;border-radius:8px;padding:1px 7px;
  font-size:10px;margin-left:6px;vertical-align:middle;letter-spacing:1px}
.lobby-teams{display:flex;gap:12px}
.lobby-team{flex:1;background:#ffffff0d;border-radius:16px;padding:10px}
.lt-title{font-weight:700;font-size:13px;letter-spacing:1px;margin-bottom:4px}
.lobby-team.ta .lt-title{color:var(--ta)} .lobby-team.tb .lt-title{color:var(--tb)}
.lobby-seat{background:#ffffff12;border-radius:12px;padding:10px;margin-top:8px;min-height:54px}
.lobby-seat.open{border:1px dashed #ffffff3d;background:transparent}
.ls-name{font-weight:600;font-size:14px}
.ls-sub{font-size:11px;color:var(--muted);margin-top:2px}
.game{flex:1;display:flex;flex-direction:column;min-height:0}
.game-top{flex:0 0 auto;display:flex;align-items:center;justify-content:space-between;
  padding:8px 10px 2px;gap:8px}
.icon-btn{background:#ffffff14;border:0;color:var(--ink);border-radius:10px;
  width:34px;height:34px;font-size:15px;cursor:pointer}
.status-line{flex:1;text-align:center;font-size:13px;color:#ffe9b3;min-height:16px}
.score-cluster{flex:0 0 auto;display:flex;gap:8px;padding:6px 10px;align-items:stretch}
.team-panel{flex:1;background:var(--panel);border-radius:12px;padding:6px 8px;
  display:flex;flex-direction:column;gap:4px}
.team-panel.ta{box-shadow:inset 0 3px 0 var(--ta)}
.team-panel.tb{box-shadow:inset 0 3px 0 var(--tb)}
.team-name{font-size:11px;font-weight:700;letter-spacing:1px;color:var(--muted)}
.card-count{font-size:11px;color:var(--muted)}
.ten-slots{display:flex;gap:4px}
.ten-slot{width:24px;height:34px;border-radius:5px;border:1px dashed #ffffff4d;
  display:flex;flex-direction:column;align-items:center;justify-content:center;line-height:1}
.ten-slot.filled{background:#faf8ef;border:1px solid #00000055;
  animation:mendi-spring .55s cubic-bezier(.2,1.8,.4,1)}
.ten-rank{font-size:11px;font-weight:800} .ten-suit{font-size:11px}
.red{color:var(--red)} .blk{color:var(--black)}
.trump-box{flex:0 0 auto;display:flex;flex-direction:column;align-items:center;
  justify-content:center;gap:3px}
.trump-label{font-size:10px;letter-spacing:2px;color:var(--gold);font-weight:700}
.mini-card{width:42px;height:60px;font-size:16px}
.felt{flex:1;position:relative;margin:6px 10px;min-height:130px;
  background:radial-gradient(ellipse at 50% 42%,var(--felt1) 0%,var(--felt2) 58%,var(--felt3) 100%);
  border-radius:34px 48px 40px 52px;box-shadow:inset 0 0 46px #00000066}
.seat-marker{position:absolute;display:flex;flex-direction:column;align-items:center;gap:1px;
  background:#0f3524e0;padding:6px 10px;border-radius:12px;min-width:86px;transition:opacity .3s}
.pos-left{left:8px;top:50%;transform:translateY(-50%)}
.pos-top{top:10px;left:50%;transform:translateX(-50%)}
.pos-right{right:8px;top:50%;transform:translateY(-50%)}
.sm-name{font-size:12px;font-weight:700;max-width:110px;overflow:hidden;
  text-overflow:ellipsis;white-space:nowrap}
.sm-sub{font-size:10px;color:var(--muted)}
.seat-marker.active{box-shadow:0 0 0 2px var(--gold);animation:pulse 1.3s ease-in-out infinite}
.seat-marker.off{opacity:.4}
@keyframes pulse{50%{box-shadow:0 0 0 2px var(--gold),0 0 16px #ffd76a99}}
.trick-center{position:absolute;inset:0}
.tc-pos{position:absolute;left:50%;top:50%;transform:translate(-50%,-50%)}
.tc-self{transform:translate(-50%,-50%) translateY(32px)}
.tc-top{transform:translate(-50%,-50%) translateY(-32px)}
.tc-left{transform:translate(-50%,-50%) translateX(-44px)}
.tc-right{transform:translate(-50%,-50%) translateX(44px)}
.card{position:relative;background:#faf8ef;border-radius:8px;box-shadow:0 2px 6px #00000070;
  display:flex;align-items:center;justify-content:center;flex:0 0 auto;user-select:none}
.c-corner{position:absolute;top:3px;left:4px;font-weight:800;line-height:1;
  font-size:.62em;text-align:center}
.c-pip{font-size:1.45em;transform:translateY(6%)}
.card.back{background:linear-gradient(135deg,#27608f,#153a5c);color:#fff;border:2px solid #ffffff33}
.card.pop{animation:card-in .26s ease-out}
.card.dim{opacity:.5}
.card.glow{box-shadow:0 0 0 3px var(--gold),0 3px 12px #000000aa}
.card.legal{cursor:pointer}
.card.legal:hover{transform:translateY(-4px)}
.card.idle{filter:saturate(.5) brightness(.75)}
@keyframes card-in{from{transform:translateY(18px) scale(.75);opacity:0}}
.hand-area{flex:0 0 auto;padding:2px 8px 12px}
.reveal-bar{display:flex;justify-content:center;padding:4px 0 6px}
.reveal-hint{font-size:13px;color:#ffe9b3;text-align:center}
.hand-strip{display:flex;justify-content:center;align-items:flex-end;min-height:70px}
.hcard-wrap{transition:transform .15s}
.hcard-wrap.sel{transform:translateY(-16px)}
.hcard-wrap.sel .card{box-shadow:0 0 0 3px var(--gold),0 6px 14px #000000aa}
.overlay{position:absolute;inset:0;background:#000000a8;display:flex;align-items:center;
  justify-content:center;z-index:40;padding:22px}
.panel{background:var(--panel2);border:1px solid #ffffff24;border-radius:18px;padding:22px;
  width:100%;max-width:340px;display:flex;flex-direction:column;gap:12px;text-align:center}
.result-rows{display:flex;flex-direction:column;gap:4px;font-size:14px}
.trump-flash{position:absolute;inset:0;z-index:60;display:flex;flex-direction:column;
  align-items:center;justify-content:center;gap:6px;
  background:radial-gradient(circle at 50% 50%,#ffffff30,#000000cc);
  animation:tf-fade 1.15s ease-out forwards;pointer-events:none}
.tf-glyph{font-size:112px;line-height:1;animation:tf-pop .5s cubic-bezier(.2,1.7,.4,1)}
.tf-glyph.red{color:#ff6b5e} .tf-glyph.blk{color:#e8e8f0}
.tf-label{font-size:16px;font-weight:700;color:var(--gold);letter-spacing:1px}
@keyframes tf-fade{0%{opacity:0}12%{opacity:1}72%{opacity:1}100%{opacity:0}}
@keyframes tf-pop{from{transform:scale(.25) rotate(-14deg)}}
@keyframes mendi-spring{0%{transform:scale(.2)}60%{transform:scale(1.2)}100%{transform:scale(1)}}
.toast{position:absolute;bottom:118px;left:50%;transform:translateX(-50%);
  background:#000000d0;padding:9px 16px;border-radius:20px;z-index:70;font-size:13.5px;
  white-space:nowrap;animation:card-in .18s ease-out}
.reconnect-banner{position:absolute;top:0;left:0;right:0;background:#a35c00;
  text-align:center;padding:4px 8px;z-index:80;font-size:12.5px}
</style>
</head>
<body>
<div id="root"></div>
<script src="https://unpkg.com/react@18.3.1/umd/react.production.min.js"></script>
<script src="https://unpkg.com/react-dom@18.3.1/umd/react-dom.production.min.js"></script>
<script>
(function () {
  "use strict";
  var e = React.createElement;
  var FR = React.Fragment;
  var useState = React.useState, useEffect = React.useEffect, useRef = React.useRef;

  var SUIT_GLYPH = { S: "\\u2660", H: "\\u2665", D: "\\u2666", C: "\\u2663" };
  var SUIT_NAME = { S: "Spades", H: "Hearts", D: "Diamonds", C: "Clubs" };
  var isRed = function (s) { return s === "H" || s === "D"; };
  var cardLabel = function (c) { return c.slice(0, -1) + SUIT_GLYPH[c.slice(-1)]; };
  var seatName = function (gs, seat) {
    var p = gs.seats.find(function (x) { return x.seat === seat; });
    return p && p.name ? p.name : "?";
  };

  // ---------------------------------------------------------------- Card
  function Card(props) {
    var c = props.card, rank = c.slice(0, -1), suit = c.slice(-1);
    var st = props.w ? { width: props.w + "px", height: Math.round(props.w * 1.42) + "px",
      fontSize: Math.round(props.w * 0.34) + "px" } : null;
    return e("div", {
      className: "card " + (isRed(suit) ? "red" : "blk") + (props.cls ? " " + props.cls : "") +
        (props.pop ? " pop" : "") + (props.dim ? " dim" : "") + (props.glow ? " glow" : ""),
      style: st, onClick: props.onClick
    },
      e("div", { className: "c-corner" },
        e("div", null, rank), e("div", null, SUIT_GLYPH[suit])),
      e("div", { className: "c-pip" }, SUIT_GLYPH[suit]));
  }

  // ---------------------------------------------------------------- score cluster
  function TenSlots(props) {
    return e("div", { className: "ten-slots" }, ["S", "H", "D", "C"].map(function (s) {
      if (props.suits.indexOf(s) >= 0) {
        return e("div", { key: s, className: "ten-slot filled" },
          e("span", { className: "ten-rank " + (isRed(s) ? "red" : "blk") }, "10"),
          e("span", { className: "ten-suit " + (isRed(s) ? "red" : "blk") }, SUIT_GLYPH[s]));
      }
      return e("div", { key: s, className: "ten-slot" });
    }));
  }
  function TeamPanel(props) {
    var t = props.team;
    return e("div", { className: "team-panel " + t.toLowerCase() },
      e("div", { className: "team-name" }, "TEAM " + t),
      e(TenSlots, { suits: props.gs.mendi[t] }),
      e("div", { className: "card-count" }, props.gs.team_cards[t] + " cards"));
  }
  function ScoreCluster(props) {
    var gs = props.gs;
    return e("div", { className: "score-cluster" },
      e(TeamPanel, { team: "A", gs: gs }),
      e("div", { className: "trump-box" },
        gs.trump_card
          ? e(Card, { card: gs.trump_card, w: 42, pop: true })
          : e("div", { className: "card back mini-card" }, "?")),
      e(TeamPanel, { team: "B", gs: gs }));
  }

  // ---------------------------------------------------------------- table pieces
  function SeatMarker(props) {
    var p = props.p;
    return e("div", {
      className: "seat-marker " + props.pos +
        (props.active ? " active" : "") + (!p.connected ? " off" : "")
    },
      e("div", { className: "sm-name" }, p.name || "?"),
      e("div", { className: "sm-sub" },
        (p.is_bot ? "BOT \\u00b7 " : "") + props.count + " cards" + (p.connected ? "" : " \\u00b7 away")));
  }
  function TrickCenter(props) {
    var gs = props.gs;
    var cards = gs.trick.length ? gs.trick : (gs.paused ? gs.last_trick : []);
    if (!cards.length) return e("div", { className: "trick-center" });
    var cls = ["tc-self", "tc-left", "tc-top", "tc-right"];
    return e("div", { className: "trick-center" }, cards.map(function (pc) {
      var rel = (pc.seat - gs.seat + 4) % 4;
      var won = gs.paused && !gs.trick.length && pc.seat === gs.last_trick_winner;
      return e("div", { key: pc.seat + "-" + pc.card, className: "tc-pos " + cls[rel] },
        e(Card, { card: pc.card, w: 54, pop: true, dim: gs.paused && !won, glow: won }));
    }));
  }

  // ---------------------------------------------------------------- hand strip
  function HandStrip(props) {
    var gs = props.gs, n = gs.hand.length;
    var ref = useRef(null);
    var dims = useState({ w: 62, step: 32 }), d = dims[0], setDims = dims[1];

    useEffect(function () {
      var el = ref.current;
      if (!el) return;
      var compute = function () {
        var avail = el.clientWidth - 16, base = 62, r = 0.52;
        if (n <= 1) { setDims({ w: base, step: base }); return; }
        var need = base + (n - 1) * base * r;
        var scale = need > avail ? avail / need : 1;
        var w2 = Math.max(30, Math.floor(base * scale));
        setDims({ w: w2, step: Math.floor(w2 * r) });
      };
      compute();
      var ro = new ResizeObserver(compute);
      ro.observe(el);
      return function () { ro.disconnect(); };
    }, [n]);

    var w = d.w, overlap = -(w - d.step);
    var styleTxt = ".hcard{width:" + w + "px;height:" + Math.round(w * 1.42) +
      "px;font-size:" + Math.round(w * 0.32) + "px;border-radius:" +
      Math.max(4, Math.round(w * 0.11)) + "px}.hcard-wrap+.hcard-wrap{margin-left:" + overlap + "px}";

    var myTurn = props.myTurn;
    var legal = myTurn ? gs.legal : [];
    return e("div", { className: "hand-area" },
      e("style", null, styleTxt),
      (gs.must_reveal && myTurn) ? e("div", { className: "reveal-bar" },
        props.selected
          ? e("button", { className: "btn gold",
              onClick: function () { props.revealCard(props.selected); } },
              "Reveal " + cardLabel(props.selected))
          : e("div", { className: "reveal-hint" },
              "You can't follow card \\u2014 tap a card to reveal it")) : null,
      e("div", { className: "hand-strip", ref: ref }, gs.hand.map(function (c) {
        var isLegal = legal.indexOf(c) >= 0;
        var sel = props.selected === c;
        return e("div", { key: c, className: "hcard-wrap" + (sel ? " sel" : "") },
          e(Card, {
            card: c, cls: "hcard " + (isLegal ? "legal" : "idle"),
            onClick: function () {
              if (!myTurn) return;
              if (gs.must_reveal) props.setSelected(sel ? null : c);
              else if (isLegal) props.playCard(c);
            }
          }));
      })));
  }

  // ---------------------------------------------------------------- overlays
  function TrumpFlash(props) {
    var f = props.flash;
    return e("div", { key: f.id, className: "trump-flash" },
      e("div", { className: "tf-glyph " + (isRed(f.suit) ? "red" : "blk") }, SUIT_GLYPH[f.suit]),
      e("div", { className: "tf-label" }, cardLabel(f.card) + " \\u2014 " + SUIT_NAME[f.suit] + " is trump"));
  }
  function ResultOverlay(props) {
    var gs = props.gs;
    var title = gs.winner ? "Team " + gs.winner + " wins the hand!" : "Hand drawn \\u2014 2\\u00b72";
    return e("div", { className: "overlay" },
      e("div", { className: "panel" },
        e("h2", null, title),
        e("div", { className: "result-rows" },
          e("div", null, "Team A \\u2014 " + gs.mendi.A.length + " mendi (" + gs.team_cards.A + " cards)"),
          e("div", null, "Team B \\u2014 " + gs.mendi.B.length + " mendi (" + gs.team_cards.B + " cards)")),
        props.me && props.me.host
          ? e("button", { className: "btn gold", onClick: props.onRematch }, "Rematch")
          : e("div", { className: "muted small" }, "Waiting for the host to start a rematch\\u2026"),
        e("button", { className: "btn ghost", onClick: props.onExit }, "Leave")));
  }
  function ConfirmExit(props) {
    return e("div", { className: "overlay" },
      e("div", { className: "panel" },
        e("h3", null, "Leave the game?"),
        e("p", { className: "muted small" }, "This cancels the game for everyone at the table."),
        e("button", { className: "btn gold", onClick: props.onYes }, "Yes, leave"),
        e("button", { className: "btn ghost", onClick: props.onNo }, "Keep playing")));
  }

  // ---------------------------------------------------------------- menu views
  function MenuView(props) {
    return e("div", { className: "view center" },
      e("div", { className: "logo" },
        e("h1", null, "ꯗ꯭ꯁ ꯐꯥꯕꯤ"),
        e("p", { className: "tagline" }, "♥️♦️♠️♣️")),
      e("button", { className: "btn gold big", onClick: props.onSolo },
        "Solo", e("span", { className: "btn-sub" }, "Instant game vs 3 bots")),
      e("button", { className: "btn green big", onClick: props.onFriends },
        "Play with Friends", e("span", { className: "btn-sub" }, "Create or join a room")));
  }
  function HubView(props) {
    return e("div", { className: "view" },
      e("h2", null, "Play with Friends"),
      e("button", { className: "btn gold big", onClick: props.onCreate },
        "Create Room", e("span", { className: "btn-sub" }, "Get a code to share")),
      e("button", { className: "btn green big", onClick: props.onJoin },
        "Join Room", e("span", { className: "btn-sub" }, "Enter a room code")),
      e("button", { className: "btn ghost", onClick: props.onBack }, "Back"));
  }
  function TeamPicker(props) {
    return e("div", { className: "team-pick" }, ["A", "B"].map(function (t) {
      return e("button", {
        key: t, type: "button",
        className: "team-btn " + t.toLowerCase() + (props.team === t ? " sel" : ""),
        onClick: function () { props.setTeam(t); }
      }, "Team " + t, e("span", { className: "btn-sub" }, "You + one partner"));
    }));
  }
  function CreateView(props) {
    var n = useState(props.initial), name = n[0], setName = n[1];
    var t = useState("A"), team = t[0], setTeam = t[1];
    return e("div", { className: "view" },
      e("h2", null, "Create Room"),
      e("label", { className: "fld" }, "Your name",
        e("input", { value: name, maxLength: 18, placeholder: "Enter your name",
          onChange: function (ev) { setName(ev.target.value); } })),
      e("div", { className: "fld" }, "Pick your team"),
      e(TeamPicker, { team: team, setTeam: setTeam }),
      e("button", { className: "btn gold big", disabled: !name.trim(),
        onClick: function () { props.onSubmit(name.trim(), team); } }, "Create Room"),
      e("button", { className: "btn ghost", onClick: props.onBack }, "Back"));
  }
  function JoinView(props) {
    var n = useState(props.initial), name = n[0], setName = n[1];
    var c = useState(""), code = c[0], setCode = c[1];
    var t = useState("A"), team = t[0], setTeam = t[1];
    return e("div", { className: "view" },
      e("h2", null, "Join Room"),
      e("label", { className: "fld" }, "Your name",
        e("input", { value: name, maxLength: 18, placeholder: "Enter your name",
          onChange: function (ev) { setName(ev.target.value); } })),
      e("label", { className: "fld" }, "Room code",
        e("input", { value: code, maxLength: 5, placeholder: "e.g. 7KQ2M",
          style: { textTransform: "uppercase", letterSpacing: "4px" },
          onChange: function (ev) { setCode(ev.target.value.toUpperCase()); } })),
      e("div", { className: "fld" }, "Pick your team"),
      e(TeamPicker, { team: team, setTeam: setTeam }),
      e("button", { className: "btn gold big", disabled: !name.trim() || code.trim().length < 4,
        onClick: function () { props.onSubmit(name.trim(), code.trim(), team); } }, "Join Room"),
      e("button", { className: "btn ghost", onClick: props.onBack }, "Back"));
  }
  function RoomView(props) {
    var lobby = props.lobby, me = props.me;
    if (!lobby) return e("div", { className: "view center" }, "Loading\\u2026");
    var seatCard = function (s) {
      return e("div", { key: s.seat, className: "lobby-seat" + (s.name ? "" : " open") },
        s.name
          ? e(FR, null,
              e("div", { className: "ls-name" }, s.name,
                s.host ? e("span", { className: "chip" }, "HOST") : null,
                s.is_bot ? e("span", { className: "chip" }, "BOT") : null),
              e("div", { className: "ls-sub" }, s.connected ? "Ready" : "\\u2026"))
          : e("div", { className: "ls-name muted" }, "Open seat"));
    };
    var canStart = lobby.full && me && me.host;
    return e("div", { className: "view" },
      e("h2", null, "Room ", e("span", { className: "room-code" }, lobby.code)),
      e("p", { className: "muted small", style: { marginTop: 0 } }, "Share this code with your friends"),
      e("div", { className: "lobby-teams" },
        e("div", { className: "lobby-team ta" },
          e("div", { className: "lt-title" }, "Team A"),
          lobby.seats.filter(function (s) { return s.team === "A"; }).map(seatCard)),
        e("div", { className: "lobby-team tb" },
          e("div", { className: "lt-title" }, "Team B"),
          lobby.seats.filter(function (s) { return s.team === "B"; }).map(seatCard))),
      canStart
        ? e("button", { className: "btn gold big", onClick: props.onStart }, "Start Game")
        : e("div", { className: "muted center-text" },
            lobby.full ? "Waiting for host to start\\u2026" : "Waiting for players\\u2026"),
      e("button", { className: "btn ghost", onClick: props.onLeave }, "Leave Room"));
  }
  function GameView(props) {
    var gs = props.gs, me = props.me;
    if (!gs) return e("div", { className: "view center" }, "Dealing cards\\u2026");
    var myTurn = gs.turn === gs.seat && !gs.paused && !gs.complete;
    var status;
    if (gs.complete) status = "";
    else if (gs.paused) status = "Trick complete\\u2026";
    else if (myTurn) status = gs.must_reveal ? "Reveal!" : "Your turn";
    else status = seatName(gs, gs.turn) + " is playing\\u2026";
    var posCls = { 1: "pos-left", 2: "pos-top", 3: "pos-right" };
    return e("div", { className: "game" },
      e("div", { className: "game-top" },
        e("span", { className: "chip" }, me && !me.solo ? "Room " + me.code : "Solo"),
        e("span", { className: "status-line" }, status),
        e("button", { className: "icon-btn", onClick: props.onExit }, "\\u2715")),
      e(ScoreCluster, { gs: gs }),
      e("div", { className: "felt" },
        [1, 2, 3].map(function (dd) {
          var s = (gs.seat + dd) % 4;
          var p = gs.seats.find(function (x) { return x.seat === s; });
          return e(SeatMarker, { key: s, p: p, pos: posCls[dd], count: gs.hand_sizes[s],
            active: gs.turn === s && !gs.paused && !gs.complete });
        }),
        e(TrickCenter, { gs: gs })),
      e(HandStrip, { gs: gs, myTurn: myTurn, selected: props.selected,
        setSelected: props.setSelected, playCard: props.playCard, revealCard: props.revealCard }),
      gs.complete ? e(ResultOverlay, { gs: gs, me: me, onRematch: props.onRematch, onExit: props.onExit }) : null);
  }

  // ---------------------------------------------------------------- app root
  function App() {
    var v = useState("menu"), view = v[0], setView = v[1];
    var m = useState(null), me = m[0], setMe = m[1];
    var l = useState(null), lobby = l[0], setLobby = l[1];
    var g = useState(null), gs = g[0], setGs = g[1];
    var f = useState(null), flash = f[0], setFlash = f[1];
    var to = useState(null), toast = to[0], setToast = to[1];
    var ce = useState(false), confirmExit = ce[0], setConfirmExit = ce[1];
    var rc = useState(false), reconnecting = rc[0], setReconnecting = rc[1];
    var se = useState(null), selected = se[0], setSelected = se[1];

    var wsRef = useRef(null), meRef = useRef(null), queueRef = useRef([]),
        retryRef = useRef(0), leavingRef = useRef(false), toastTimer = useRef(null);

    var showToast = function (msg) {
      setToast({ msg: msg, id: Date.now() });
      if (toastTimer.current) clearTimeout(toastTimer.current);
      toastTimer.current = setTimeout(function () { setToast(null); }, 2600);
    };

    var hardReset = function (msg) {
      meRef.current = null;
      setMe(null); setGs(null); setLobby(null); setSelected(null); setConfirmExit(false);
      sessionStorage.removeItem("mk_pid"); sessionStorage.removeItem("mk_code");
      setView("menu");
      if (msg) showToast(msg);
    };

    var send = function (obj) {
      var ws = wsRef.current;
      if (ws && ws.readyState === 1) ws.send(JSON.stringify(obj));
      else queueRef.current.push(obj);
    };

    var onMsg = function (msg) {
      switch (msg.type) {
        case "joined": {
          var mm = { pid: msg.player_id, code: msg.code, seat: msg.seat, host: msg.host, solo: msg.solo };
          meRef.current = mm; setMe(mm);
          sessionStorage.setItem("mk_pid", mm.pid);
          sessionStorage.setItem("mk_code", mm.code);
          if (!mm.solo) setView("room");
          break;
        }
        case "lobby":
          setLobby(msg); setView("room");
          if (msg.you && meRef.current) {
            meRef.current = Object.assign({}, meRef.current, { seat: msg.you.seat, host: msg.you.host });
            setMe(meRef.current);
          }
          break;
        case "game_start": setGs(null); setSelected(null); setView("game"); break;
        case "new_hand": setSelected(null); break;
        case "game_state":
          setGs(msg); setView("game");
          if (meRef.current) {
            meRef.current = Object.assign({}, meRef.current, { seat: msg.seat });
            setMe(meRef.current);
          }
          break;
        case "card_played":
          if (meRef.current && msg.seat === meRef.current.seat) setSelected(null);
          break;
        case "trump_revealed": setFlash({ suit: msg.suit, card: msg.card, id: Date.now() }); break;
        case "boot_dealt": showToast("Boot dealt \\u2014 8 new cards each"); break;
        case "seat_status": {
          var patch = function (list) {
            return list && list.map(function (s) {
              return s.seat === msg.seat ? Object.assign({}, s, { connected: msg.connected }) : s;
            });
          };
          setGs(function (x) { return x ? Object.assign({}, x, { seats: patch(x.seats) }) : x; });
          setLobby(function (x) { return x ? Object.assign({}, x, { seats: patch(x.seats) }) : x; });
          break;
        }
        case "room_cancelled":
          if (leavingRef.current) hardReset(null);
          else hardReset(msg.reason ? "Room closed \\u2014 " + msg.reason : "Room closed");
          break;
        case "rejoin_failed": hardReset(msg.message || "Could not rejoin"); break;
        case "error": showToast(msg.message || "Error"); break;
        default: break;
      }
    };

    var connect = function () {
      var ws0 = wsRef.current;
      if (ws0 && (ws0.readyState === 0 || ws0.readyState === 1)) return;
      var proto = location.protocol === "https:" ? "wss" : "ws";
      var ws = new WebSocket(proto + "://" + location.host + "/ws");
      wsRef.current = ws;
      ws.onopen = function () {
        retryRef.current = 0; setReconnecting(false);
        if (meRef.current && meRef.current.pid) {
          ws.send(JSON.stringify({ type: "rejoin", code: meRef.current.code, player_id: meRef.current.pid }));
        }
        while (queueRef.current.length) ws.send(JSON.stringify(queueRef.current.shift()));
      };
      ws.onmessage = function (ev) { try { onMsg(JSON.parse(ev.data)); } catch (ex) {} };
      ws.onclose = function () {
        if (meRef.current && retryRef.current < 10) {
          retryRef.current += 1; setReconnecting(true);
          setTimeout(connect, 1200);
        } else if (meRef.current) {
          hardReset("Connection lost");
        }
      };
    };

    useEffect(function () {
      if (!flash) return;
      var t = setTimeout(function () { setFlash(null); }, 1200);
      return function () { clearTimeout(t); };
    }, [flash]);

    useEffect(function () {
      var pid = sessionStorage.getItem("mk_pid");
      var code = sessionStorage.getItem("mk_code");
      if (pid && code) {
        meRef.current = { pid: pid, code: code, seat: null, host: false, solo: false };
        setReconnecting(true);
        connect();
      }
    }, []);

    var getName = function () { return localStorage.getItem("mk_name") || ""; };
    var saveName = function (n) { localStorage.setItem("mk_name", n); };
    var act = function (obj) { connect(); send(obj); };

    var leaveAction = function () {
      leavingRef.current = true;
      send({ type: "leave" });
      setTimeout(function () { leavingRef.current = false; }, 1500);
      hardReset(null);
      setView("hub");
    };

    var content;
    if (view === "menu") content = e(MenuView, {
      onSolo: function () { act({ type: "start_solo", name: getName() || "Player" }); },
      onFriends: function () { setView("hub"); } });
    else if (view === "hub") content = e(HubView, {
      onCreate: function () { setView("create"); },
      onJoin: function () { setView("join"); },
      onBack: function () { setView("menu"); } });
    else if (view === "create") content = e(CreateView, { initial: getName(),
      onSubmit: function (n, t) { saveName(n); act({ type: "create_room", name: n, team: t }); },
      onBack: function () { setView("hub"); } });
    else if (view === "join") content = e(JoinView, { initial: getName(),
      onSubmit: function (n, c, t) { saveName(n); act({ type: "join_room", name: n, code: c, team: t }); },
      onBack: function () { setView("hub"); } });
    else if (view === "room") content = e(RoomView, { lobby: lobby, me: me,
      onStart: function () { send({ type: "start_game" }); }, onLeave: leaveAction });
    else content = e(GameView, { gs: gs, me: me, selected: selected, setSelected: setSelected,
      playCard: function (c) { send({ type: "play_card", card: c }); },
      revealCard: function (c) { setSelected(null); send({ type: "reveal_trump", card: c }); },
      onExit: function () { setConfirmExit(true); },
      onRematch: function () { send({ type: "rematch" }); } });

    return e("div", { className: "app" },
      content,
      reconnecting ? e("div", { className: "reconnect-banner" }, "Reconnecting\\u2026") : null,
      flash ? e(TrumpFlash, { flash: flash }) : null,
      confirmExit ? e(ConfirmExit, {
        onYes: function () { setConfirmExit(false); leaveAction(); },
        onNo: function () { setConfirmExit(false); } }) : null,
      toast ? e("div", { key: toast.id, className: "toast" }, toast.msg) : null);
  }

  ReactDOM.createRoot(document.getElementById("root")).render(e(App));
})();
</script>
</body>
</html>
"""

if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=8000)
