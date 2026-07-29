
from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
import asyncio
import json
import random
import uuid
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Optional, Set, Tuple, Any
from enum import Enum
import time

# ============== GAME CONSTANTS ==============
SUITS = ['♠', '♥', '♦', '♣']
SUIT_COLORS = {'♠': '#2d2d2d', '♣': '#2d2d2d', '♥': '#d32f2f', '♦': '#d32f2f'}
SUIT_NAMES = {'♠': 'spades', '♥': 'hearts', '♦': 'diamonds', '♣': 'clubs'}
RANKS = ['2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K', 'A']
RANK_VALUES = {r: i for i, r in enumerate(RANKS)}

TEAM_A = {0, 2}
TEAM_B = {1, 3}

def get_team(seat: int) -> str:
    return 'A' if seat in TEAM_A else 'B'

def other_team(team: str) -> str:
    return 'B' if team == 'A' else 'A'

# ============== DATA CLASSES ==============
@dataclass
class Card:
    suit: str
    rank: str

    def to_dict(self):
        return {
            'suit': self.suit,
            'rank': self.rank,
            'value': RANK_VALUES[self.rank],
            'is_ten': self.rank == '10',
            'color': SUIT_COLORS[self.suit]
        }

    def __hash__(self):
        return hash((self.suit, self.rank))

    def __eq__(self, other):
        if isinstance(other, Card):
            return self.suit == other.suit and self.rank == other.rank
        return False

@dataclass
class Player:
    seat: int
    name: str
    is_bot: bool = False
    hand: List[Card] = field(default_factory=list)
    connection_id: Optional[str] = None
    team: str = field(init=False)

    def __post_init__(self):
        self.team = get_team(self.seat)

    def to_dict(self, hide_hand=False):
        return {
            'seat': self.seat,
            'name': self.name,
            'is_bot': self.is_bot,
            'team': self.team,
            'hand_size': len(self.hand),
            'hand': [c.to_dict() for c in self.hand] if not hide_hand else None
        }

# ============== GAME ENGINE ==============
class MendikotGame:
    def __init__(self, dealer_seat=0):
        self.dealer_seat = dealer_seat
        self.leader_seat = (dealer_seat + 1) % 4
        self.current_seat = self.leader_seat
        self.trump_suit: Optional[str] = None
        self.trump_revealed = False
        self.trump_revealer: Optional[int] = None
        self.trump_card: Optional[Card] = None
        self.phase = 1  # 1 = first 5 cards, 2 = after boot
        self.trick_num = 1
        self.trick_cards: List[Optional[Card]] = [None, None, None, None]
        self.trick_leader = self.leader_seat
        self.led_suit: Optional[str] = None
        self.boot_dealt = False
        self.game_over = False
        self.winner: Optional[str] = None
        self.mendi: Dict[str, List[Card]] = {'A': [], 'B': []}
        self.cards_won: Dict[str, int] = {'A': 0, 'B': 0}
        self.tricks_won: Dict[str, int] = {'A': 0, 'B': 0}
        self.players: List[Player] = []
        self.deck: List[Card] = []
        self.boot: List[Card] = []
        self.history: List[dict] = []
        self.void_in_trick: Set[int] = set()  # Players void in led suit when trump revealed mid-trick
        self.trick_in_progress = False
        self.trick_complete = False
        self.trick_winner_seat: Optional[int] = None

    def create_deck(self):
        self.deck = [Card(s, r) for s in SUITS for r in RANKS]
        random.shuffle(self.deck)

    def deal_phase1(self):
        for p in self.players:
            p.hand = [self.deck.pop() for _ in range(5)]
            p.hand.sort(key=lambda c: (SUITS.index(c.suit), RANK_VALUES[c.rank]))
        self.boot = self.deck[:]
        self.deck = []

    def deal_boot(self):
        if self.boot_dealt:
            return
        for p in self.players:
            new_cards = [self.boot.pop() for _ in range(8)]
            p.hand.extend(new_cards)
            p.hand.sort(key=lambda c: (SUITS.index(c.suit), RANK_VALUES[c.rank]))
        self.boot_dealt = True
        self.phase = 2

    def start(self, player_names: List[Tuple[str, bool]]):
        self.players = [Player(i, name, is_bot) for i, (name, is_bot) in enumerate(player_names)]
        self.create_deck()
        self.deal_phase1()

    def get_legal_cards(self, seat: int) -> List[Card]:
        player = self.players[seat]
        if not self.led_suit:
            return player.hand[:]

        has_suit = any(c.suit == self.led_suit for c in player.hand)
        if has_suit:
            return [c for c in player.hand if c.suit == self.led_suit]

        # Void in led suit
        if self.trump_suit is None and self.phase == 1 and seat not in self.void_in_trick:
            # Must reveal trump - can play any card (the reveal mechanism handles this)
            return player.hand[:]

        return player.hand[:]

    def can_reveal_trump(self, seat: int) -> bool:
        if self.trump_suit is not None:
            return False
        if self.phase != 1:
            return False
        if self.led_suit is None:
            return False
        player = self.players[seat]
        has_led = any(c.suit == self.led_suit for c in player.hand)
        return not has_led and seat not in self.void_in_trick

    def play_card(self, seat: int, card: Card) -> dict:
        result = {'success': False, 'message': '', 'events': []}

        if self.game_over:
            result['message'] = 'Game is over'
            return result

        if seat != self.current_seat:
            result['message'] = 'Not your turn'
            return result

        if self.trick_complete:
            result['message'] = 'Trick is complete, waiting'
            return result

        player = self.players[seat]
        if card not in player.hand:
            result['message'] = 'Card not in hand'
            return result

        legal = self.get_legal_cards(seat)
        if card not in legal:
            result['message'] = 'Illegal card play'
            return result

        # Handle trump reveal
        revealed_now = False
        if self.can_reveal_trump(seat):
            self.trump_suit = card.suit
            self.trump_revealed = True
            self.trump_revealer = seat
            self.trump_card = card
            revealed_now = True
            self.void_in_trick.add(seat)
            result['events'].append({
                'type': 'trump_revealed',
                'seat': seat,
                'suit': card.suit,
                'card': card.to_dict()
            })

        # Play the card
        player.hand.remove(card)
        self.trick_cards[seat] = card

        if self.led_suit is None:
            self.led_suit = card.suit
            self.trick_leader = seat

        result['events'].append({
            'type': 'card_played',
            'seat': seat,
            'card': card.to_dict(),
            'trick_num': self.trick_num,
            'revealed_now': revealed_now
        })

        # Check if trick is complete
        if all(c is not None for c in self.trick_cards):
            self._resolve_trick()
            result['events'].extend(self._get_trick_events())
        else:
            self.current_seat = (self.current_seat + 1) % 4

        result['success'] = True
        return result

    def _resolve_trick(self):
        self.trick_complete = True
        self.trick_in_progress = False

        cards = [(seat, card) for seat, card in enumerate(self.trick_cards) if card is not None]

        if self.trump_suit:
            trump_cards = [(s, c) for s, c in cards if c.suit == self.trump_suit]
            if trump_cards:
                winner = max(trump_cards, key=lambda x: RANK_VALUES[x[1].rank])[0]
            else:
                suit_cards = [(s, c) for s, c in cards if c.suit == self.led_suit]
                winner = max(suit_cards, key=lambda x: RANK_VALUES[x[1].rank])[0]
        else:
            suit_cards = [(s, c) for s, c in cards if c.suit == self.led_suit]
            winner = max(suit_cards, key=lambda x: RANK_VALUES[x[1].rank])[0]

        self.trick_winner_seat = winner
        winning_team = get_team(winner)
        self.tricks_won[winning_team] += 1

        # Collect mendi (10s)
        tens = [c for s, c in cards if c.rank == '10']
        self.mendi[winning_team].extend(tens)
        self.cards_won[winning_team] += len(cards)

        # Check if boot should be dealt
        if not self.boot_dealt:
            if self.trick_num == 5 or self.trump_revealed:
                self.deal_boot()

        # Check if game over
        if self.trick_num >= 13:
            self._end_game()

    def _get_trick_events(self) -> List[dict]:
        events = [{
            'type': 'trick_won',
            'winner_seat': self.trick_winner_seat,
            'winning_team': get_team(self.trick_winner_seat),
            'trick_cards': [{**c.to_dict(), 'seat': i} for i, c in enumerate(self.trick_cards) if c],
            'tens_won': [c.to_dict() for c in self.trick_cards if c and c.rank == '10'],
            'trick_num': self.trick_num
        }]

        if self.boot_dealt and self.trick_num <= 5:
            events.append({'type': 'boot_dealt'})

        if self.game_over:
            events.append({
                'type': 'hand_complete',
                'winner': self.winner,
                'mendi_A': [c.to_dict() for c in self.mendi['A']],
                'mendi_B': [c.to_dict() for c in self.mendi['B']],
                'scores': {
                    'A': len(self.mendi['A']),
                    'B': len(self.mendi['B'])
                }
            })

        return events

    def next_trick(self):
        if not self.trick_complete or self.game_over:
            return False

        self.trick_num += 1
        self.trick_cards = [None, None, None, None]
        self.led_suit = None
        self.current_seat = self.trick_winner_seat
        self.trick_leader = self.trick_winner_seat
        self.trick_complete = False
        self.trick_in_progress = True
        self.trick_winner_seat = None
        self.void_in_trick = set()
        return True

    def _end_game(self):
        self.game_over = True
        a_count = len(self.mendi['A'])
        b_count = len(self.mendi['B'])

        if a_count > b_count:
            self.winner = 'A'
        elif b_count > a_count:
            self.winner = 'B'
        else:
            self.winner = 'draw'

    def get_state(self, for_seat: Optional[int] = None) -> dict:
        return {
            'dealer_seat': self.dealer_seat,
            'leader_seat': self.leader_seat,
            'current_seat': self.current_seat,
            'trump_suit': self.trump_suit,
            'trump_revealed': self.trump_revealed,
            'trump_revealer': self.trump_revealer,
            'trump_card': self.trump_card.to_dict() if self.trump_card else None,
            'phase': self.phase,
            'trick_num': self.trick_num,
            'trick_cards': [c.to_dict() if c else None for c in self.trick_cards],
            'trick_leader': self.trick_leader,
            'led_suit': self.led_suit,
            'boot_dealt': self.boot_dealt,
            'game_over': self.game_over,
            'winner': self.winner,
            'mendi': {
                'A': [c.to_dict() for c in self.mendi['A']],
                'B': [c.to_dict() for c in self.mendi['B']]
            },
            'cards_won': self.cards_won,
            'tricks_won': self.tricks_won,
            'players': [p.to_dict(hide_hand=for_seat is not None and p.seat != for_seat) for p in self.players],
            'trick_complete': self.trick_complete,
            'trick_winner_seat': self.trick_winner_seat,
            'for_seat': for_seat
        }

    def bot_choose_card(self, seat: int) -> Optional[Card]:
        player = self.players[seat]
        if not player.hand:
            return None

        legal = self.get_legal_cards(seat)
        if not legal:
            return None

        # Bot strategy: play lowest legal card
        # If forced to reveal trump, reveal lowest card overall
        if self.can_reveal_trump(seat):
            return min(player.hand, key=lambda c: (RANK_VALUES[c.rank], SUITS.index(c.suit)))

        return min(legal, key=lambda c: (RANK_VALUES[c.rank], SUITS.index(c.suit)))


# ============== ROOM MANAGEMENT ==============
class Room:
    def __init__(self, code: str, host_id: str, host_name: str, host_team: str):
        self.code = code
        self.host_id = host_id
        self.players: Dict[str, dict] = {}  # connection_id -> {name, seat, team}
        self.seats: Dict[int, Optional[str]] = {0: None, 1: None, 2: None, 3: None}
        self.team_counts = {'A': 0, 'B': 0}
        self.game: Optional[MendikotGame] = None
        self.started = False
        self.created_at = time.time()
        self.last_activity = time.time()
        self.solo = False
        self.dealer_rotation = 0
        self.connections: Dict[str, WebSocket] = {}
        self.bot_names = ['Raju', 'Vijay', 'Amit']

    def add_player(self, conn_id: str, name: str, team: str) -> Optional[int]:
        if self.started:
            return None
        if self.team_counts[team] >= 2:
            return None
        if conn_id in self.players:
            return self.players[conn_id]['seat']

        # Find seat for team
        team_seats = TEAM_A if team == 'A' else TEAM_B
        seat = None
        for s in team_seats:
            if self.seats[s] is None:
                seat = s
                break

        if seat is None:
            return None

        self.players[conn_id] = {'name': name, 'seat': seat, 'team': team}
        self.seats[seat] = conn_id
        self.team_counts[team] += 1
        self.last_activity = time.time()
        return seat

    def remove_player(self, conn_id: str):
        if conn_id not in self.players:
            return
        seat = self.players[conn_id]['seat']
        team = self.players[conn_id]['team']
        del self.players[conn_id]
        self.seats[seat] = None
        self.team_counts[team] -= 1
        if conn_id in self.connections:
            del self.connections[conn_id]
        self.last_activity = time.time()

    def is_full(self) -> bool:
        return len(self.players) == 4

    def is_host(self, conn_id: str) -> bool:
        return conn_id == self.host_id

    def start_game(self):
        if not self.is_full():
            return False
        self.started = True
        names = []
        for seat in range(4):
            conn_id = self.seats[seat]
            if conn_id:
                names.append((self.players[conn_id]['name'], False))
            else:
                names.append((self.bot_names.pop(0) if self.bot_names else f'Bot {seat}', True))

        self.game = MendikotGame(dealer_seat=self.dealer_rotation % 4)
        self.game.start(names)
        self.last_activity = time.time()
        return True

    def start_solo(self, player_name: str):
        self.solo = True
        self.started = True
        names = [(player_name, False), ('Vijay', True), ('Raju', True), ('Amit', True)]
        self.game = MendikotGame(dealer_seat=0)
        self.game.start(names)
        self.last_activity = time.time()
        return True

    def get_public_state(self) -> dict:
        return {
            'code': self.code,
            'started': self.started,
            'solo': self.solo,
            'players': [
                {
                    'seat': s,
                    'name': self.players[c]['name'] if c else None,
                    'team': self.players[c]['team'] if c else None,
                    'connected': c in self.connections if c else False,
                    'is_bot': False if c else True
                }
                for s, c in self.seats.items()
            ],
            'team_counts': self.team_counts,
            'host_id': self.host_id
        }


class RoomManager:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, str] = {}  # conn_id -> room_code

    def create_room(self, host_id: str, host_name: str, host_team: str) -> Room:
        code = ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6))
        while code in self.rooms:
            code = ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6))
        room = Room(code, host_id, host_name, host_team)
        room.add_player(host_id, host_name, host_team)
        self.rooms[code] = room
        return room

    def get_room(self, code: str) -> Optional[Room]:
        return self.rooms.get(code)

    def remove_room(self, code: str):
        if code in self.rooms:
            room = self.rooms[code]
            for conn_id in list(room.connections.keys()):
                if conn_id in self.connections:
                    del self.connections[conn_id]
            del self.rooms[code]

    def cleanup(self, ttl=600):
        now = time.time()
        to_remove = []
        for code, room in self.rooms.items():
            if now - room.last_activity > ttl:
                to_remove.append(code)
        for code in to_remove:
            self.remove_room(code)


manager = RoomManager()

# ============== WEBSOCKET PROTOCOL ==============
async def send(ws: WebSocket, msg: dict):
    try:
        await ws.send_json(msg)
    except:
        pass

async def broadcast(room: Room, msg: dict, exclude: Optional[str] = None):
    for conn_id, ws in list(room.connections.items()):
        if conn_id != exclude:
            await send(ws, msg)

async def handle_bot_turns(room: Room):
    if not room.game or room.game.game_over or room.game.trick_complete:
        return

    game = room.game
    seat = game.current_seat
    player = game.players[seat]

    if not player.is_bot:
        return

    await asyncio.sleep(1.2)

    if not room.game or room.game.game_over or room.game.trick_complete:
        return

    card = game.bot_choose_card(seat)
    if card is None:
        return

    result = game.play_card(seat, card)
    if result['success']:
        for event in result['events']:
            await broadcast(room, event)

        if game.trick_complete and not game.game_over:
            await asyncio.sleep(3.0)
            if room.game and room.game.trick_complete and not room.game.game_over:
                room.game.next_trick()
                await broadcast(room, {
                    'type': 'next_trick',
                    'state': game.get_state()
                })
                await handle_bot_turns(room)
        elif game.game_over:
            await broadcast(room, {
                'type': 'game_over',
                'state': game.get_state()
            })
        else:
            await handle_bot_turns(room)


# ============== FASTAPI APP ==============
app = FastAPI()

@app.on_event("startup")
async def startup():
    async def gc_loop():
        while True:
            await asyncio.sleep(60)
            manager.cleanup()
    asyncio.create_task(gc_loop())

@app.get("/")
async def root():
    return HTMLResponse(content=HTML_FRONTEND)

@app.websocket("/ws")
async def websocket_endpoint(ws: WebSocket):
    await ws.accept()
    conn_id = str(uuid.uuid4())
    room = None

    try:
        while True:
            data = await ws.receive_json()
            action = data.get('action')

            if action == 'create_room':
                name = data.get('name', 'Player')
                team = data.get('team', 'A')
                room = manager.create_room(conn_id, name, team)
                room.connections[conn_id] = ws
                manager.connections[conn_id] = room.code
                await send(ws, {
                    'type': 'room_created',
                    'room_code': room.code,
                    'seat': room.players[conn_id]['seat'],
                    'state': room.get_public_state()
                })

            elif action == 'join_room':
                code = data.get('room_code', '').upper().strip()
                name = data.get('name', 'Player')
                team = data.get('team', 'A')
                room = manager.get_room(code)
                if not room:
                    await send(ws, {'type': 'error', 'message': 'Room not found'})
                    continue
                if room.started:
                    await send(ws, {'type': 'error', 'message': 'Game already started'})
                    continue
                if room.team_counts[team] >= 2:
                    await send(ws, {'type': 'error', 'message': 'Team is full'})
                    continue
                seat = room.add_player(conn_id, name, team)
                if seat is None:
                    await send(ws, {'type': 'error', 'message': 'Could not join room'})
                    continue
                room.connections[conn_id] = ws
                manager.connections[conn_id] = room.code
                await send(ws, {
                    'type': 'room_joined',
                    'room_code': room.code,
                    'seat': seat,
                    'state': room.get_public_state()
                })
                await broadcast(room, {
                    'type': 'player_joined',
                    'state': room.get_public_state()
                }, exclude=conn_id)

            elif action == 'start_solo':
                name = data.get('name', 'Player')
                room = manager.create_room(conn_id, name, 'A')
                room.solo = True
                room.connections[conn_id] = ws
                manager.connections[conn_id] = room.code
                room.start_solo(name)
                await send(ws, {
                    'type': 'game_started',
                    'seat': 0,
                    'state': room.game.get_state(for_seat=0)
                })
                await handle_bot_turns(room)

            elif action == 'start_game':
                if not room or not room.is_host(conn_id):
                    await send(ws, {'type': 'error', 'message': 'Not authorized'})
                    continue
                if not room.is_full():
                    await send(ws, {'type': 'error', 'message': 'Room not full'})
                    continue
                room.start_game()
                for cid in room.players:
                    if cid in room.connections:
                        seat = room.players[cid]['seat']
                        await send(room.connections[cid], {
                            'type': 'game_started',
                            'seat': seat,
                            'state': room.game.get_state(for_seat=seat)
                        })
                await handle_bot_turns(room)

            elif action == 'play_card':
                if not room or not room.game:
                    continue
                seat = room.players.get(conn_id, {}).get('seat')
                if seat is None:
                    continue
                card_data = data.get('card', {})
                card = Card(card_data.get('suit'), card_data.get('rank'))
                result = room.game.play_card(seat, card)
                if result['success']:
                    for event in result['events']:
                        await broadcast(room, event)

                    if room.game.trick_complete and not room.game.game_over:
                        async def next_trick_delayed():
                            await asyncio.sleep(3.0)
                            if room.game and room.game.trick_complete and not room.game.game_over:
                                room.game.next_trick()
                                await broadcast(room, {
                                    'type': 'next_trick',
                                    'state': room.game.get_state()
                                })
                                await handle_bot_turns(room)
                        asyncio.create_task(next_trick_delayed())
                    elif room.game.game_over:
                        await broadcast(room, {
                            'type': 'game_over',
                            'state': room.game.get_state()
                        })
                    else:
                        await handle_bot_turns(room)
                else:
                    await send(ws, {'type': 'error', 'message': result['message']})

            elif action == 'reveal_trump':
                if not room or not room.game:
                    continue
                seat = room.players.get(conn_id, {}).get('seat')
                if seat is None:
                    continue
                card_data = data.get('card', {})
                card = Card(card_data.get('suit'), card_data.get('rank'))
                # Reveal trump is just playing a card when void
                result = room.game.play_card(seat, card)
                if result['success']:
                    for event in result['events']:
                        await broadcast(room, event)

                    if room.game.trick_complete and not room.game.game_over:
                        async def next_trick_delayed():
                            await asyncio.sleep(3.0)
                            if room.game and room.game.trick_complete and not room.game.game_over:
                                room.game.next_trick()
                                await broadcast(room, {
                                    'type': 'next_trick',
                                    'state': room.game.get_state()
                                })
                                await handle_bot_turns(room)
                        asyncio.create_task(next_trick_delayed())
                    elif room.game.game_over:
                        await broadcast(room, {
                            'type': 'game_over',
                            'state': room.game.get_state()
                        })
                    else:
                        await handle_bot_turns(room)
                else:
                    await send(ws, {'type': 'error', 'message': result['message']})

            elif action == 'rematch':
                if not room or not room.is_host(conn_id):
                    continue
                if not room.game or not room.game.game_over:
                    continue
                room.dealer_rotation += 1
                names = [(p.name, p.is_bot) for p in room.game.players]
                room.game = MendikotGame(dealer_seat=room.dealer_rotation % 4)
                room.game.start(names)
                for cid in room.players:
                    if cid in room.connections:
                        seat = room.players[cid]['seat']
                        await send(room.connections[cid], {
                            'type': 'game_started',
                            'seat': seat,
                            'state': room.game.get_state(for_seat=seat)
                        })
                await handle_bot_turns(room)

            elif action == 'leave_room':
                break

            elif action == 'ping':
                await send(ws, {'type': 'pong'})

    except WebSocketDisconnect:
        pass
    except Exception as e:
        print(f"WS Error: {e}")
    finally:
        if room:
            if room.solo:
                manager.remove_room(room.code)
            elif not room.started:
                if room.is_host(conn_id):
                    manager.remove_room(room.code)
                    await broadcast(room, {'type': 'room_cancelled', 'reason': 'Host left'})
                else:
                    room.remove_player(conn_id)
                    if conn_id in manager.connections:
                        del manager.connections[conn_id]
                    await broadcast(room, {
                        'type': 'player_left',
                        'state': room.get_public_state()
                    })
            else:
                # Game in progress - cancel for everyone
                if conn_id in room.players:
                    manager.remove_room(room.code)
                    await broadcast(room, {'type': 'room_cancelled', 'reason': 'Player disconnected during game'})

        try:
            await ws.close()
        except:
            pass


HTML_FRONTEND = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
<meta name="theme-color" content="#0a3d2a">
<title>Mendikot</title>
<script src="https://unpkg.com/react@18/umd/react.production.min.js" crossorigin></script>
<script src="https://unpkg.com/react-dom@18/umd/react-dom.production.min.js" crossorigin></script>
<script src="https://unpkg.com/@babel/standalone/babel.min.js"></script>
<style>
*, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }

:root {
  --felt: #0d5c3b;
  --felt-dark: #0a3d2a;
  --felt-light: #1a7a52;
  --gold: #d4af37;
  --gold-light: #f0d878;
  --card-bg: #f8f9fa;
  --card-border: #e0e0e0;
  --red-suit: #d32f2f;
  --black-suit: #2d2d2d;
  --shadow: 0 4px 20px rgba(0,0,0,0.4);
  --shadow-sm: 0 2px 8px rgba(0,0,0,0.3);
  --accent: #ff6b35;
  --bot-color: #64b5f6;
}

html, body, #root {
  height: 100%;
  overflow: hidden;
  font-family: 'Segoe UI', system-ui, -apple-system, sans-serif;
  background: var(--felt-dark);
  color: white;
  touch-action: manipulation;
  -webkit-tap-highlight-color: transparent;
}

/* ===== MENU & VIEWS ===== */
.view-container {
  height: 100%;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  padding: 20px;
  background: radial-gradient(ellipse at center, var(--felt) 0%, var(--felt-dark) 100%);
  position: relative;
}

.view-container::before {
  content: '';
  position: absolute;
  inset: 0;
  background-image: 
    radial-gradient(circle at 20% 30%, rgba(255,255,255,0.03) 0%, transparent 50%),
    radial-gradient(circle at 80% 70%, rgba(255,255,255,0.02) 0%, transparent 50%);
  pointer-events: none;
}

.logo {
  font-size: clamp(2.5rem, 8vw, 4rem);
  font-weight: 900;
  color: var(--gold);
  text-shadow: 0 4px 12px rgba(0,0,0,0.5);
  letter-spacing: 2px;
  margin-bottom: 8px;
  animation: logoPulse 3s ease-in-out infinite;
}

@keyframes logoPulse {
  0%, 100% { transform: scale(1); text-shadow: 0 4px 12px rgba(0,0,0,0.5); }
  50% { transform: scale(1.02); text-shadow: 0 6px 20px rgba(212,175,55,0.3); }
}

.subtitle {
  font-size: clamp(0.9rem, 3vw, 1.1rem);
  color: rgba(255,255,255,0.6);
  margin-bottom: 40px;
  text-align: center;
}

.btn {
  width: 100%;
  max-width: 320px;
  padding: 16px 24px;
  margin: 8px 0;
  border: none;
  border-radius: 16px;
  font-size: 1.1rem;
  font-weight: 700;
  cursor: pointer;
  transition: all 0.2s ease;
  text-transform: uppercase;
  letter-spacing: 1px;
  position: relative;
  overflow: hidden;
}

.btn-primary {
  background: linear-gradient(135deg, var(--gold) 0%, #b8941f 100%);
  color: #1a1a1a;
  box-shadow: 0 4px 15px rgba(212,175,55,0.3);
}

.btn-primary:hover, .btn-primary:active {
  transform: translateY(-2px);
  box-shadow: 0 6px 20px rgba(212,175,55,0.4);
}

.btn-secondary {
  background: rgba(255,255,255,0.1);
  color: white;
  border: 2px solid rgba(255,255,255,0.2);
  backdrop-filter: blur(10px);
}

.btn-secondary:hover, .btn-secondary:active {
  background: rgba(255,255,255,0.2);
  border-color: rgba(255,255,255,0.3);
}

.btn-danger {
  background: linear-gradient(135deg, #e53935 0%, #c62828 100%);
  color: white;
}

.btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
  transform: none !important;
}

.btn-row {
  display: flex;
  gap: 12px;
  width: 100%;
  max-width: 320px;
}

.btn-row .btn {
  flex: 1;
}

.input {
  width: 100%;
  max-width: 320px;
  padding: 14px 18px;
  margin: 8px 0;
  border: 2px solid rgba(255,255,255,0.15);
  border-radius: 14px;
  background: rgba(0,0,0,0.2);
  color: white;
  font-size: 1rem;
  outline: none;
  transition: border-color 0.2s;
}

.input:focus {
  border-color: var(--gold);
}

.input::placeholder {
  color: rgba(255,255,255,0.4);
}

.form-label {
  width: 100%;
  max-width: 320px;
  text-align: left;
  font-size: 0.85rem;
  color: rgba(255,255,255,0.7);
  margin-top: 12px;
  margin-bottom: 4px;
  text-transform: uppercase;
  letter-spacing: 1px;
}

.team-select {
  display: flex;
  gap: 12px;
  width: 100%;
  max-width: 320px;
  margin: 8px 0 16px;
}

.team-option {
  flex: 1;
  padding: 14px;
  border: 2px solid rgba(255,255,255,0.15);
  border-radius: 14px;
  text-align: center;
  cursor: pointer;
  transition: all 0.2s;
  font-weight: 700;
}

.team-option.selected {
  border-color: var(--gold);
  background: rgba(212,175,55,0.15);
}

.team-a { color: #4fc3f7; }
.team-b { color: #ff8a65; }

.back-btn {
  position: absolute;
  top: 16px;
  left: 16px;
  background: rgba(0,0,0,0.3);
  border: none;
  color: white;
  width: 40px;
  height: 40px;
  border-radius: 50%;
  display: flex;
  align-items: center;
  justify-content: center;
  cursor: pointer;
  font-size: 1.2rem;
  z-index: 10;
}

/* ===== ROOM LOBBY ===== */
.lobby-container {
  width: 100%;
  max-width: 400px;
}

.room-code-display {
  background: rgba(0,0,0,0.3);
  padding: 16px;
  border-radius: 16px;
  text-align: center;
  margin-bottom: 24px;
  border: 2px dashed rgba(255,255,255,0.2);
}

.room-code-display .code {
  font-size: 2rem;
  font-weight: 900;
  color: var(--gold);
  letter-spacing: 4px;
  font-family: monospace;
}

.seats-grid {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 12px;
  margin-bottom: 24px;
}

.seat-box {
  padding: 20px;
  border-radius: 16px;
  text-align: center;
  border: 2px solid rgba(255,255,255,0.1);
  background: rgba(0,0,0,0.2);
  transition: all 0.3s;
}

.seat-box.filled {
  border-color: var(--gold);
  background: rgba(212,175,55,0.1);
}

.seat-box .seat-name {
  font-weight: 700;
  font-size: 1.1rem;
}

.seat-box .seat-team {
  font-size: 0.8rem;
  opacity: 0.7;
  margin-top: 4px;
}

.waiting-text {
  text-align: center;
  color: rgba(255,255,255,0.6);
  font-size: 0.9rem;
}

/* ===== GAME LAYOUT ===== */
.game-container {
  height: 100%;
  display: flex;
  flex-direction: column;
  background: radial-gradient(ellipse at center, var(--felt) 0%, var(--felt-dark) 100%);
  position: relative;
  overflow: hidden;
}

.game-container::before {
  content: '';
  position: absolute;
  inset: 0;
  background-image: 
    repeating-linear-gradient(45deg, transparent, transparent 35px, rgba(0,0,0,0.03) 35px, rgba(0,0,0,0.03) 70px);
  pointer-events: none;
}

/* Score Board */
.score-board {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 10px 16px;
  background: rgba(0,0,0,0.3);
  backdrop-filter: blur(10px);
  border-bottom: 1px solid rgba(255,255,255,0.1);
  z-index: 5;
  min-height: 64px;
}

.score-team {
  display: flex;
  flex-direction: column;
  align-items: center;
  min-width: 70px;
}

.score-team .team-label {
  font-size: 0.7rem;
  text-transform: uppercase;
  letter-spacing: 1px;
  opacity: 0.8;
}

.score-team .mendi-count {
  font-size: 1.4rem;
  font-weight: 900;
  color: var(--gold);
}

.score-team .card-count {
  font-size: 0.7rem;
  opacity: 0.6;
}

.trump-area {
  display: flex;
  flex-direction: column;
  align-items: center;
}

.trump-card {
  width: 40px;
  height: 56px;
  background: var(--card-bg);
  border-radius: 6px;
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 1.4rem;
  font-weight: 900;
  box-shadow: var(--shadow-sm);
  border: 1px solid var(--card-border);
  transition: all 0.3s ease;
}

.trump-card.hidden {
  background: linear-gradient(135deg, #1a5276 0%, #154360 100%);
  color: var(--gold);
  font-size: 1.2rem;
}

.trump-label {
  font-size: 0.65rem;
  text-transform: uppercase;
  letter-spacing: 1px;
  margin-top: 4px;
  opacity: 0.8;
}

.mendi-slots {
  display: flex;
  gap: 3px;
  margin-top: 4px;
}

.mendi-slot {
  width: 18px;
  height: 24px;
  border-radius: 3px;
  border: 1px solid rgba(255,255,255,0.2);
  background: rgba(0,0,0,0.2);
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 0.6rem;
  transition: all 0.3s;
}

.mendi-slot.filled {
  background: var(--card-bg);
  border-color: var(--gold);
  color: var(--red-suit);
  font-weight: 900;
  animation: mendiPop 0.4s ease;
}

@keyframes mendiPop {
  0% { transform: scale(0) rotate(-10deg); }
  60% { transform: scale(1.2) rotate(5deg); }
  100% { transform: scale(1) rotate(0); }
}

/* Table Area */
.table-area {
  flex: 1;
  display: grid;
  grid-template-rows: auto 1fr auto;
  grid-template-columns: auto 1fr auto;
  grid-template-areas:
    ". top ."
    "left center right"
    ". bottom .";
  padding: 8px;
  gap: 8px;
  position: relative;
  min-height: 0;
}

.table-felt {
  grid-area: center;
  background: rgba(0,0,0,0.15);
  border-radius: 24px;
  border: 2px solid rgba(255,255,255,0.08);
  display: flex;
  align-items: center;
  justify-content: center;
  position: relative;
  min-height: 0;
  min-width: 0;
}

.seat-marker {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  padding: 8px 12px;
  border-radius: 12px;
  background: rgba(0,0,0,0.3);
  border: 2px solid rgba(255,255,255,0.1);
  transition: all 0.3s;
  min-width: 80px;
  max-width: 120px;
}

.seat-marker.active {
  border-color: var(--gold);
  background: rgba(212,175,55,0.15);
  box-shadow: 0 0 15px rgba(212,175,55,0.2);
  animation: activePulse 2s ease-in-out infinite;
}

@keyframes activePulse {
  0%, 100% { box-shadow: 0 0 15px rgba(212,175,55,0.2); }
  50% { box-shadow: 0 0 25px rgba(212,175,55,0.4); }
}

.seat-marker.bot {
  border-color: rgba(100,181,246,0.3);
}

.seat-marker .seat-avatar {
  width: 36px;
  height: 36px;
  border-radius: 50%;
  background: linear-gradient(135deg, var(--felt-light) 0%, var(--felt) 100%);
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 1rem;
  font-weight: 700;
  margin-bottom: 4px;
  border: 2px solid rgba(255,255,255,0.2);
}

.seat-marker.bot .seat-avatar {
  background: linear-gradient(135deg, #1565c0 0%, #0d47a1 100%);
}

.seat-marker .seat-name {
  font-size: 0.75rem;
  font-weight: 600;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  max-width: 100%;
}

.seat-marker .seat-cards {
  font-size: 0.65rem;
  opacity: 0.6;
  margin-top: 2px;
}

.seat-top { grid-area: top; justify-self: center; align-self: start; }
.seat-bottom { grid-area: bottom; justify-self: center; align-self: end; }
.seat-left { grid-area: left; justify-self: start; align-self: center; }
.seat-right { grid-area: right; justify-self: end; align-self: center; }

/* Trick Center */
.trick-center {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  grid-template-rows: repeat(2, 1fr);
  gap: 8px;
  width: min(180px, 50vw);
  height: min(240px, 35vh);
  position: relative;
}

.trick-slot {
  display: flex;
  align-items: center;
  justify-content: center;
  position: relative;
}

.trick-slot.pos-0 { grid-column: 2; grid-row: 2; } /* bottom / self */
.trick-slot.pos-1 { grid-column: 2; grid-row: 1; } /* right -> top in grid... wait, need to fix */

/* Actually let's use absolute positioning within trick-center for flexibility */
.trick-center-abs {
  position: relative;
  width: min(200px, 55vw);
  height: min(260px, 40vh);
}

.trick-card-pos {
  position: absolute;
  width: 56px;
  height: 78px;
  transition: all 0.4s cubic-bezier(0.34, 1.56, 0.64, 1);
}

.trick-card-pos.pos-0 { bottom: 0; left: 50%; transform: translateX(-50%); }
.trick-card-pos.pos-1 { top: 50%; right: 0; transform: translateY(-50%); }
.trick-card-pos.pos-2 { top: 0; left: 50%; transform: translateX(-50%); }
.trick-card-pos.pos-3 { top: 50%; left: 0; transform: translateY(-50%); }

/* ===== CARDS ===== */
.card {
  width: 56px;
  height: 78px;
  background: var(--card-bg);
  border-radius: 8px;
  border: 1px solid var(--card-border);
  box-shadow: var(--shadow-sm);
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  position: relative;
  cursor: pointer;
  user-select: none;
  transition: transform 0.2s, box-shadow 0.2s;
  flex-shrink: 0;
}

.card:hover:not(.disabled):not(.back) {
  transform: translateY(-8px) scale(1.05);
  box-shadow: 0 8px 25px rgba(0,0,0,0.3);
  z-index: 10;
}

.card.disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.card.back {
  background: linear-gradient(135deg, #1a5276 0%, #154360 100%);
  border-color: #1a5276;
}

.card.back::after {
  content: '';
  width: 36px;
  height: 50px;
  border: 2px solid rgba(255,255,255,0.15);
  border-radius: 4px;
  background: repeating-linear-gradient(
    45deg,
    transparent,
    transparent 4px,
    rgba(255,255,255,0.05) 4px,
    rgba(255,255,255,0.05) 8px
  );
}

.card-rank {
  font-size: 1.1rem;
  font-weight: 900;
  line-height: 1;
}

.card-suit {
  font-size: 1.3rem;
  line-height: 1;
  margin-top: 2px;
}

.card.red .card-rank, .card.red .card-suit { color: var(--red-suit); }
.card.black .card-rank, .card.black .card-suit { color: var(--black-suit); }

.card-corner-tl, .card-corner-br {
  position: absolute;
  font-size: 0.55rem;
  font-weight: 700;
  line-height: 1;
}

.card-corner-tl { top: 4px; left: 4px; }
.card-corner-br { bottom: 4px; right: 4px; transform: rotate(180deg); }

/* Card Animations */
@keyframes cardPopIn {
  0% { transform: scale(0) rotateY(90deg); opacity: 0; }
  70% { transform: scale(1.1) rotateY(0); opacity: 1; }
  100% { transform: scale(1) rotateY(0); opacity: 1; }
}

.card-pop-in {
  animation: cardPopIn 0.4s ease backwards;
}

@keyframes cardPlay {
  0% { transform: scale(1); opacity: 1; }
  50% { transform: scale(1.15) translateY(-20px); opacity: 1; }
  100% { transform: scale(1); opacity: 1; }
}

.card-play-anim {
  animation: cardPlay 0.5s ease;
}

@keyframes cardCollect {
  0% { transform: scale(1) rotate(0); opacity: 1; }
  100% { transform: scale(0.3) rotate(360deg); opacity: 0; }
}

.card-collect {
  animation: cardCollect 0.6s ease forwards;
}

@keyframes trumpFlash {
  0% { opacity: 0; }
  20% { opacity: 1; }
  80% { opacity: 1; }
  100% { opacity: 0; }
}

.trump-flash-overlay {
  position: fixed;
  inset: 0;
  z-index: 100;
  pointer-events: none;
  opacity: 0;
}

.trump-flash-overlay.active {
  animation: trumpFlash 1.5s ease;
}

@keyframes trumpStamp {
  0% { transform: scale(3) rotate(-15deg); opacity: 0; }
  50% { transform: scale(0.9) rotate(-5deg); opacity: 1; }
  70% { transform: scale(1.05) rotate(-5deg); opacity: 1; }
  100% { transform: scale(1) rotate(-5deg); opacity: 1; }
}

.trump-stamp {
  position: absolute;
  top: 50%;
  left: 50%;
  transform: translate(-50%, -50%);
  font-size: 4rem;
  font-weight: 900;
  color: var(--gold);
  text-shadow: 0 4px 20px rgba(0,0,0,0.8);
  opacity: 0;
  pointer-events: none;
  z-index: 20;
  white-space: nowrap;
}

.trump-stamp.show {
  animation: trumpStamp 0.6s ease forwards;
}

/* Hand Strip */
.hand-strip {
  display: flex;
  justify-content: center;
  align-items: flex-end;
  padding: 12px 8px 20px;
  min-height: 110px;
  background: linear-gradient(to top, rgba(0,0,0,0.4) 0%, transparent 100%);
  position: relative;
  z-index: 5;
  overflow-x: auto;
  scrollbar-width: none;
}

.hand-strip::-webkit-scrollbar { display: none; }

.hand-card-wrapper {
  position: relative;
  transition: margin 0.3s ease;
  flex-shrink: 0;
}

.reveal-btn {
  position: absolute;
  bottom: 100%;
  left: 50%;
  transform: translateX(-50%);
  margin-bottom: 8px;
  padding: 6px 12px;
  background: var(--accent);
  color: white;
  border: none;
  border-radius: 20px;
  font-size: 0.7rem;
  font-weight: 700;
  text-transform: uppercase;
  white-space: nowrap;
  cursor: pointer;
  animation: bounce 1s ease infinite;
  box-shadow: 0 4px 12px rgba(255,107,53,0.4);
}

@keyframes bounce {
  0%, 100% { transform: translateX(-50%) translateY(0); }
  50% { transform: translateX(-50%) translateY(-4px); }
}

/* Overlays */
.overlay {
  position: fixed;
  inset: 0;
  background: rgba(0,0,0,0.85);
  backdrop-filter: blur(8px);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 50;
  animation: fadeIn 0.3s ease;
}

@keyframes fadeIn {
  from { opacity: 0; }
  to { opacity: 1; }
}

.overlay-content {
  background: linear-gradient(135deg, var(--felt) 0%, var(--felt-dark) 100%);
  border: 2px solid rgba(255,255,255,0.15);
  border-radius: 24px;
  padding: 32px;
  text-align: center;
  max-width: 90vw;
  width: 360px;
  box-shadow: var(--shadow);
  animation: slideUp 0.4s ease;
}

@keyframes slideUp {
  from { transform: translateY(30px); opacity: 0; }
  to { transform: translateY(0); opacity: 1; }
}

.overlay-title {
  font-size: 1.8rem;
  font-weight: 900;
  color: var(--gold);
  margin-bottom: 16px;
}

.result-mendi {
  display: flex;
  justify-content: center;
  gap: 24px;
  margin: 20px 0;
}

.result-team {
  text-align: center;
}

.result-team .rt-label {
  font-size: 0.8rem;
  text-transform: uppercase;
  letter-spacing: 1px;
  margin-bottom: 8px;
}

.result-team .rt-score {
  font-size: 2.5rem;
  font-weight: 900;
  color: var(--gold);
}

.result-team .rt-mendi-cards {
  display: flex;
  gap: 4px;
  justify-content: center;
  margin-top: 8px;
}

.mini-card {
  width: 24px;
  height: 34px;
  background: var(--card-bg);
  border-radius: 4px;
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 0.7rem;
  font-weight: 900;
  border: 1px solid var(--card-border);
}

.mini-card.red { color: var(--red-suit); }
.mini-card.black { color: var(--black-suit); }

/* Toast */
.toast-container {
  position: fixed;
  top: 80px;
  left: 50%;
  transform: translateX(-50%);
  z-index: 40;
  display: flex;
  flex-direction: column;
  gap: 8px;
  pointer-events: none;
}

.toast {
  background: rgba(0,0,0,0.8);
  color: white;
  padding: 10px 20px;
  border-radius: 12px;
  font-size: 0.9rem;
  font-weight: 600;
  animation: toastIn 0.3s ease, toastOut 0.3s ease 2.7s forwards;
  border-left: 4px solid var(--gold);
  backdrop-filter: blur(10px);
  white-space: nowrap;
}

@keyframes toastIn {
  from { transform: translateY(-20px); opacity: 0; }
  to { transform: translateY(0); opacity: 1; }
}

@keyframes toastOut {
  to { transform: translateY(-20px); opacity: 0; }
}

/* Trick counter */
.trick-counter {
  position: absolute;
  top: 8px;
  right: 12px;
  font-size: 0.75rem;
  color: rgba(255,255,255,0.5);
  font-weight: 600;
}

/* Exit button */
.exit-btn {
  position: absolute;
  top: 8px;
  left: 8px;
  width: 36px;
  height: 36px;
  border-radius: 50%;
  background: rgba(0,0,0,0.3);
  border: 1px solid rgba(255,255,255,0.1);
  color: white;
  display: flex;
  align-items: center;
  justify-content: center;
  cursor: pointer;
  font-size: 1.1rem;
  z-index: 10;
}

/* Responsive adjustments */
@media (min-width: 768px) {
  .card {
    width: 64px;
    height: 90px;
    border-radius: 10px;
  }
  .card-rank { font-size: 1.3rem; }
  .card-suit { font-size: 1.5rem; }
  .trick-card-pos {
    width: 64px;
    height: 90px;
  }
  .trick-center-abs {
    width: 280px;
    height: 340px;
  }
  .seat-marker {
    padding: 12px 16px;
    min-width: 100px;
  }
  .seat-marker .seat-avatar {
    width: 44px;
    height: 44px;
    font-size: 1.2rem;
  }
  .hand-strip {
    min-height: 130px;
    padding-bottom: 24px;
  }
}

@media (max-height: 600px) {
  .score-board { min-height: 50px; padding: 6px 12px; }
  .trump-card { width: 32px; height: 44px; font-size: 1rem; }
  .card { width: 48px; height: 68px; }
  .hand-strip { min-height: 90px; padding-bottom: 12px; }
  .table-area { padding: 4px; gap: 4px; }
}

/* Landscape on mobile */
@media (max-height: 450px) and (orientation: landscape) {
  .game-container { flex-direction: row; }
  .score-board {
    flex-direction: column;
    width: 70px;
    min-width: 70px;
    border-right: 1px solid rgba(255,255,255,0.1);
    border-bottom: none;
    padding: 8px 4px;
  }
  .table-area {
    grid-template-rows: 1fr auto 1fr;
    grid-template-columns: auto 1fr auto;
    grid-template-areas:
      "left . right"
      "left center right"
      "left . right";
  }
  .hand-strip {
    width: 90px;
    min-width: 90px;
    flex-direction: column;
    align-items: center;
    padding: 8px 4px;
    overflow-y: auto;
    overflow-x: hidden;
  }
  .hand-card-wrapper { margin: -20px 0 0 0 !important; }
}
</style>
</head>
<body>
<div id="root"></div>
<script type="text/babel">

const { useState, useEffect, useRef, useCallback, useMemo } = React;

const SUITS = ["♠","♥","♦","♣"];
const SUIT_COLORS = {"♠":"black","♥":"red","♦":"red","♣":"black"};
const SUIT_BG_COLORS = {"♠":"#1a5276","♥":"#922b21","♦":"#922b21","♣":"#1a5276"};
const TEAM_COLORS = {"A":"#4fc3f7","B":"#ff8a65"};

function getPos(seat, mySeat) { return (seat - mySeat + 4) % 4; }

function CardEl({ card, onClick, disabled, hidden, style, className, index }) {
  if (hidden) {
    return React.createElement("div", {
      className: `card back ${className || ""}`,
      style: style
    });
  }
  const color = SUIT_COLORS[card.suit] || "black";
  const delay = index !== undefined ? `${index * 0.05}s` : "0s";
  return React.createElement("div", {
    className: `card ${color} ${disabled ? "disabled" : ""} ${className || ""}`,
    style: Object.assign({}, style, { animationDelay: delay }),
    onClick: disabled ? undefined : onClick
  }, [
    React.createElement("span", { key: "tl", className: "card-corner-tl" }, card.rank),
    React.createElement("span", { key: "r", className: "card-rank" }, card.rank),
    React.createElement("span", { key: "s", className: "card-suit" }, card.suit),
    React.createElement("span", { key: "br", className: "card-corner-br" }, card.rank)
  ]);
}

function ScoreBoard({ gameState, mySeat }) {
  if (!gameState) return null;
  const aMendi = (gameState.mendi && gameState.mendi.A) || [];
  const bMendi = (gameState.mendi && gameState.mendi.B) || [];
  const aCards = gameState.cards_won ? gameState.cards_won.A : 0;
  const bCards = gameState.cards_won ? gameState.cards_won.B : 0;
  const trumpSuit = gameState.trump_suit;
  const trumpRevealed = gameState.trump_revealed;

  const mendiSlots = (mendiList) => {
    const suits = ["♠","♥","♦","♣"];
    return suits.map(function(s) {
      const hasIt = mendiList.some(function(c) { return c.suit === s; });
      return React.createElement("div", {
        key: s,
        className: `mendi-slot ${hasIt ? "filled" : ""}`
      }, hasIt ? "10" : "");
    });
  };

  return React.createElement("div", { className: "score-board" }, [
    React.createElement("div", { key: "ta", className: "score-team" }, [
      React.createElement("span", { key: "l", className: "team-label", style: { color: TEAM_COLORS.A } }, "Team A"),
      React.createElement("span", { key: "c", className: "mendi-count" }, aMendi.length),
      React.createElement("div", { key: "s", className: "mendi-slots" }, mendiSlots(aMendi)),
      React.createElement("span", { key: "cc", className: "card-count" }, aCards + " cards")
    ]),
    React.createElement("div", { key: "tr", className: "trump-area" }, [
      React.createElement("div", {
        key: "tc",
        className: `trump-card ${!trumpRevealed ? "hidden" : ""}`
      }, trumpRevealed ? trumpSuit : "?"),
      React.createElement("span", { key: "tl", className: "trump-label" }, trumpRevealed ? "Trump" : "Hidden")
    ]),
    React.createElement("div", { key: "tb", className: "score-team" }, [
      React.createElement("span", { key: "l", className: "team-label", style: { color: TEAM_COLORS.B } }, "Team B"),
      React.createElement("span", { key: "c", className: "mendi-count" }, bMendi.length),
      React.createElement("div", { key: "s", className: "mendi-slots" }, mendiSlots(bMendi)),
      React.createElement("span", { key: "cc", className: "card-count" }, bCards + " cards")
    ])
  ]);
}

function SeatMarker({ player, isActive, position, isBot, cardCount }) {
  const posClass = position === 0 ? "seat-bottom" : position === 1 ? "seat-right" : position === 2 ? "seat-top" : "seat-left";
  const avatar = isBot ? "🤖" : (player ? player.name.charAt(0).toUpperCase() : "?");
  const name = player ? player.name : "Empty";

  return React.createElement("div", {
    className: `seat-marker ${posClass} ${isActive ? "active" : ""} ${isBot ? "bot" : ""}`
  }, [
    React.createElement("div", { key: "av", className: "seat-avatar" }, avatar),
    React.createElement("span", { key: "nm", className: "seat-name" }, name),
    React.createElement("span", { key: "cc", className: "seat-cards" }, cardCount !== undefined ? cardCount + " cards" : "")
  ]);
}

function TrickCenter({ trickCards, mySeat, collecting, winner, trickComplete }) {
  const positions = [0, 1, 2, 3];
  return React.createElement("div", { className: "trick-center-abs" }, [
    positions.map(function(p) {
      const actualSeat = (mySeat + p) % 4;
      const card = trickCards[actualSeat];
      const isWinner = trickComplete && winner === actualSeat;
      return React.createElement("div", {
        key: p,
        className: `trick-card-pos pos-${p} ${collecting ? "card-collect" : ""} ${isWinner ? "card-play-anim" : ""}`
      }, card ? React.createElement(CardEl, { card: card, hidden: false }) : null);
    }),
    trickComplete && winner !== null ? React.createElement("div", {
      key: "wintext",
      style: {
        position: "absolute",
        top: "50%",
        left: "50%",
        transform: "translate(-50%, -50%)",
        background: "rgba(0,0,0,0.7)",
        padding: "6px 14px",
        borderRadius: "20px",
        fontSize: "0.8rem",
        fontWeight: 700,
        color: "#fff",
        zIndex: 5,
        whiteSpace: "nowrap"
      }
    }, "Winner: Seat " + (winner + 1)) : null
  ]);
}

function HandStrip({ hand, gameState, mySeat, onPlayCard }) {
  const handRef = useRef(null);
  const [overlap, setOverlap] = useState(0);
  const [mustReveal, setMustReveal] = useState(false);

  useEffect(function() {
    function calc() {
      if (!handRef.current || !hand || !hand.length) { setOverlap(0); return; }
      const w = handRef.current.clientWidth;
      const isSmall = window.innerWidth < 400;
      const cardW = isSmall ? 48 : (window.innerWidth >= 768 ? 64 : 56);
      const total = cardW * hand.length;
      const ov = total > w ? (total - w) / Math.max(hand.length - 1, 1) + 2 : 0;
      setOverlap(Math.min(ov, cardW * 0.72));
    }
    calc();
    window.addEventListener("resize", calc);
    return function() { window.removeEventListener("resize", calc); };
  }, [hand ? hand.length : 0]);

  useEffect(function() {
    if (!gameState || !hand) { setMustReveal(false); return; }
    const current = gameState.current_seat;
    const led = gameState.led_suit;
    const phase = gameState.phase;
    const trump = gameState.trump_suit;
    if (current !== mySeat || !led || phase !== 1 || trump) { setMustReveal(false); return; }
    const hasLed = hand.some(function(c) { return c.suit === led; });
    setMustReveal(!hasLed);
  }, [gameState, hand, mySeat]);

  if (!hand || !hand.length) return null;

  const current = gameState ? gameState.current_seat : -1;
  const led = gameState ? gameState.led_suit : null;
  const trump = gameState ? gameState.trump_suit : null;
  const isMyTurn = current === mySeat;
  const trickComplete = gameState ? gameState.trick_complete : false;

  return React.createElement("div", { className: "hand-strip", ref: handRef },
    hand.map(function(card, i) {
      const isLegal = isMyTurn && !trickComplete && (function() {
        if (!led) return true;
        const hasLed = hand.some(function(c) { return c.suit === led; });
        if (hasLed) return card.suit === led;
        return true;
      })();

      return React.createElement("div", {
        key: card.suit + "-" + card.rank,
        className: "hand-card-wrapper",
        style: { marginLeft: i > 0 ? -overlap : 0 }
      }, [
        mustReveal && isMyTurn && !trickComplete ? React.createElement("button", {
          key: "rev",
          className: "reveal-btn",
          onClick: function(e) { e.stopPropagation(); onPlayCard(card, true); }
        }, "Reveal") : null,
        React.createElement(CardEl, {
          key: "c",
          card: card,
          index: i,
          disabled: !isLegal,
          className: "card-pop-in",
          onClick: function() { if (isLegal) onPlayCard(card, mustReveal); }
        })
      ]);
    })
  );
}

function TrumpFlashOverlay({ suit }) {
  if (!suit) return null;
  const bg = SUIT_BG_COLORS[suit] || "#1a5276";
  return React.createElement("div", {
    className: "trump-flash-overlay active",
    style: { background: bg }
  });
}

function TrumpStamp({ suit, show }) {
  if (!suit || !show) return null;
  return React.createElement("div", { className: "trump-stamp show" }, [
    React.createElement("span", { key: "s", style: { fontSize: "3rem" } }, suit),
    React.createElement("span", { key: "t", style: { fontSize: "1.2rem", display: "block" } }, "TRUMP")
  ]);
}

function ResultOverlay({ gameState, onRematch, onExit, isHost }) {
  if (!gameState || !gameState.game_over) return null;
  const winner = gameState.winner;
  const aMendi = (gameState.mendi && gameState.mendi.A) || [];
  const bMendi = (gameState.mendi && gameState.mendi.B) || [];
  const aScore = aMendi.length;
  const bScore = bMendi.length;

  let title = "Draw!";
  let titleColor = "#fff";
  if (winner === "A") { title = "Team A Wins!"; titleColor = TEAM_COLORS.A; }
  if (winner === "B") { title = "Team B Wins!"; titleColor = TEAM_COLORS.B; }

  const renderMiniCards = function(mendi) {
    return mendi.map(function(c, i) {
      return React.createElement("div", {
        key: i,
        className: `mini-card ${SUIT_COLORS[c.suit]}`
      }, [c.suit, React.createElement("span", { key: "r", style: { fontSize: "0.5rem", display: "block" } }, c.rank)]);
    });
  };

  return React.createElement("div", { className: "overlay" },
    React.createElement("div", { className: "overlay-content" }, [
      React.createElement("div", { key: "t", className: "overlay-title", style: { color: titleColor } }, title),
      React.createElement("div", { key: "sc", className: "result-mendi" }, [
        React.createElement("div", { key: "a", className: "result-team" }, [
          React.createElement("div", { key: "l", className: "rt-label", style: { color: TEAM_COLORS.A } }, "Team A"),
          React.createElement("div", { key: "s", className: "rt-score" }, aScore),
          React.createElement("div", { key: "c", className: "rt-mendi-cards" }, renderMiniCards(aMendi))
        ]),
        React.createElement("div", { key: "b", className: "result-team" }, [
          React.createElement("div", { key: "l", className: "rt-label", style: { color: TEAM_COLORS.B } }, "Team B"),
          React.createElement("div", { key: "s", className: "rt-score" }, bScore),
          React.createElement("div", { key: "c", className: "rt-mendi-cards" }, renderMiniCards(bMendi))
        ])
      ]),
      isHost ? React.createElement("button", {
        key: "rem",
        className: "btn btn-primary",
        onClick: onRematch,
        style: { marginTop: 16 }
      }, "Rematch") : null,
      React.createElement("button", {
        key: "ex",
        className: "btn btn-secondary",
        onClick: onExit,
        style: { marginTop: 8 }
      }, "Exit to Menu")
    ])
  );
}

function ConfirmExitOverlay({ onConfirm, onCancel }) {
  return React.createElement("div", { className: "overlay" },
    React.createElement("div", { className: "overlay-content" }, [
      React.createElement("div", { key: "t", className: "overlay-title" }, "Leave Game?"),
      React.createElement("p", { key: "m", style: { color: "rgba(255,255,255,0.7)", marginBottom: 20 } }, "This will end the game for everyone."),
      React.createElement("div", { key: "b", className: "btn-row" }, [
        React.createElement("button", { key: "y", className: "btn btn-danger", onClick: onConfirm }, "Leave"),
        React.createElement("button", { key: "n", className: "btn btn-secondary", onClick: onCancel }, "Stay")
      ])
    ])
  );
}

function ToastContainer({ toasts }) {
  return React.createElement("div", { className: "toast-container" },
    toasts.map(function(t) {
      return React.createElement("div", { key: t.id, className: "toast" }, t.message);
    })
  );
}

function DisconnectOverlay({ onReconnect, onMenu }) {
  return React.createElement("div", { className: "overlay" },
    React.createElement("div", { className: "overlay-content" }, [
      React.createElement("div", { key: "t", className: "overlay-title", style: { color: "#ff8a65" } }, "Disconnected"),
      React.createElement("p", { key: "m", style: { color: "rgba(255,255,255,0.7)", marginBottom: 20 } }, "Connection lost."),
      React.createElement("button", { key: "r", className: "btn btn-primary", onClick: onReconnect }, "Reconnect"),
      React.createElement("button", { key: "m", className: "btn btn-secondary", onClick: onMenu, style: { marginTop: 8 } }, "Main Menu")
    ])
  );
}

// Redefine SeatMarker with dealer badge
function SeatMarker({ player, isActive, position, isBot, cardCount, isDealer }) {
  const posClass = position === 0 ? "seat-bottom" : position === 1 ? "seat-right" : position === 2 ? "seat-top" : "seat-left";
  const avatar = isBot ? "🤖" : (player ? player.name.charAt(0).toUpperCase() : "?");
  const name = player ? player.name : "Empty";

  return React.createElement("div", {
    className: `seat-marker ${posClass} ${isActive ? "active" : ""} ${isBot ? "bot" : ""}`
  }, [
    React.createElement("div", { 
      key: "av", 
      className: "seat-avatar",
      style: { position: "relative" }
    }, [
      avatar,
      isDealer ? React.createElement("span", { 
        key: "d", 
        style: { 
          position: "absolute", 
          top: -4, 
          right: -4, 
          background: "var(--gold)", 
          color: "#000", 
          borderRadius: "50%", 
          width: 16, 
          height: 16, 
          fontSize: 10, 
          display: "flex", 
          alignItems: "center", 
          justifyContent: "center", 
          fontWeight: 900,
          border: "1px solid rgba(0,0,0,0.3)"
        } 
      }, "D") : null
    ]),
    React.createElement("span", { key: "nm", className: "seat-name" }, name),
    React.createElement("span", { key: "cc", className: "seat-cards" }, cardCount !== undefined ? cardCount + " cards" : "")
  ]);
}

// Redefine TrickCenter with staggered animation and winner name
function TrickCenter({ trickCards, mySeat, winner, trickComplete, trickNum, players }) {
  const positions = [0, 1, 2, 3];
  const winnerPlayer = players ? players.find(function(p) { return p.seat === winner; }) : null;
  return React.createElement("div", { className: "trick-center-abs" }, [
    positions.map(function(p) {
      const actualSeat = (mySeat + p) % 4;
      const card = trickCards[actualSeat];
      const isWinner = trickComplete && winner === actualSeat;
      return React.createElement("div", {
        key: "pos-" + trickNum + "-" + p,
        className: `trick-card-pos pos-${p} ${trickComplete ? "card-collect" : ""} ${isWinner ? "card-play-anim" : ""}`,
        style: trickComplete ? { animationDelay: (p * 0.1 + 0.5) + "s" } : {}
      }, card ? React.createElement(CardEl, { 
        card: card, 
        hidden: false, 
        className: "card-pop-in" 
      }) : null);
    }),
    trickComplete && winner !== null ? React.createElement("div", {
      key: "wintext",
      style: {
        position: "absolute",
        top: "50%",
        left: "50%",
        transform: "translate(-50%, -50%)",
        background: "rgba(0,0,0,0.7)",
        padding: "6px 14px",
        borderRadius: "20px",
        fontSize: "0.8rem",
        fontWeight: 700,
        color: "#fff",
        zIndex: 5,
        whiteSpace: "nowrap"
      }
    }, winnerPlayer ? winnerPlayer.name + " wins!" : "Winner") : null
  ]);
}

// Views
function MenuView(props) {
  return React.createElement("div", { className: "view-container" }, [
    React.createElement("h1", { key: "logo", className: "logo" }, "MENDIKOT"),
    React.createElement("p", { key: "sub", className: "subtitle" }, "The Classic Indian Card Game"),
    React.createElement("button", { key: "solo", className: "btn btn-primary", onClick: props.onSolo }, "Solo vs Bots"),
    React.createElement("button", { key: "multi", className: "btn btn-secondary", onClick: props.onMultiplayer }, "Play with Friends")
  ]);
}

function HubView(props) {
  return React.createElement("div", { className: "view-container" }, [
    React.createElement("button", { key: "back", className: "back-btn", onClick: props.onBack }, "←"),
    React.createElement("h2", { key: "t", className: "logo", style: { fontSize: "2rem", marginBottom: 40 } }, "Play with Friends"),
    React.createElement("button", { key: "cr", className: "btn btn-primary", onClick: props.onCreate }, "Create Room"),
    React.createElement("button", { key: "jr", className: "btn btn-secondary", onClick: props.onJoin }, "Join Room")
  ]);
}

function CreateView(props) {
  const [name, setName] = useState(localStorage.getItem("mendikot_name") || "");
  const [team, setTeam] = useState("A");

  function handleCreate() {
    if (!name.trim()) return;
    localStorage.setItem("mendikot_name", name.trim());
    props.onCreate(name.trim(), team);
  }

  return React.createElement("div", { className: "view-container" }, [
    React.createElement("button", { key: "back", className: "back-btn", onClick: props.onBack }, "←"),
    React.createElement("h2", { key: "t", style: { color: "var(--gold)", marginBottom: 24 } }, "Create Room"),
    React.createElement("label", { key: "ln", className: "form-label" }, "Your Name"),
    React.createElement("input", {
      key: "in",
      className: "input",
      value: name,
      onChange: function(e) { setName(e.target.value); },
      placeholder: "Enter your name",
      maxLength: 20
    }),
    React.createElement("label", { key: "lt", className: "form-label" }, "Choose Team"),
    React.createElement("div", { key: "ts", className: "team-select" }, [
      React.createElement("div", {
        key: "a",
        className: "team-option team-a " + (team === "A" ? "selected" : ""),
        onClick: function() { setTeam("A"); }
      }, "Team A"),
      React.createElement("div", {
        key: "b",
        className: "team-option team-b " + (team === "B" ? "selected" : ""),
        onClick: function() { setTeam("B"); }
      }, "Team B")
    ]),
    React.createElement("button", {
      key: "go",
      className: "btn btn-primary",
      onClick: handleCreate,
      disabled: !name.trim()
    }, "Create")
  ]);
}

function JoinView(props) {
  const [name, setName] = useState(localStorage.getItem("mendikot_name") || "");
  const [code, setCode] = useState("");
  const [team, setTeam] = useState("A");

  function handleJoin() {
    if (!name.trim() || !code.trim()) return;
    localStorage.setItem("mendikot_name", name.trim());
    props.onJoin(name.trim(), code.trim().toUpperCase(), team);
  }

  return React.createElement("div", { className: "view-container" }, [
    React.createElement("button", { key: "back", className: "back-btn", onClick: props.onBack }, "←"),
    React.createElement("h2", { key: "t", style: { color: "var(--gold)", marginBottom: 24 } }, "Join Room"),
    React.createElement("label", { key: "ln", className: "form-label" }, "Your Name"),
    React.createElement("input", {
      key: "in",
      className: "input",
      value: name,
      onChange: function(e) { setName(e.target.value); },
      placeholder: "Enter your name",
      maxLength: 20
    }),
    React.createElement("label", { key: "lc", className: "form-label" }, "Room Code"),
    React.createElement("input", {
      key: "ic",
      className: "input",
      value: code,
      onChange: function(e) { setCode(e.target.value.toUpperCase()); },
      placeholder: "Enter room code",
      maxLength: 8
    }),
    React.createElement("label", { key: "lt", className: "form-label" }, "Choose Team"),
    React.createElement("div", { key: "ts", className: "team-select" }, [
      React.createElement("div", {
        key: "a",
        className: "team-option team-a " + (team === "A" ? "selected" : ""),
        onClick: function() { setTeam("A"); }
      }, "Team A"),
      React.createElement("div", {
        key: "b",
        className: "team-option team-b " + (team === "B" ? "selected" : ""),
        onClick: function() { setTeam("B"); }
      }, "Team B")
    ]),
    React.createElement("button", {
      key: "go",
      className: "btn btn-primary",
      onClick: handleJoin,
      disabled: !name.trim() || !code.trim()
    }, "Join Room")
  ]);
}

function RoomView(props) {
  if (!props.roomState) return null;
  const players = props.roomState.players || [];
  const isFull = players.every(function(p) { return p.name !== null; });

  return React.createElement("div", { className: "view-container" }, [
    React.createElement("button", { key: "back", className: "back-btn", onClick: props.onLeave }, "←"),
    React.createElement("h2", { key: "t", style: { color: "var(--gold)", marginBottom: 8 } }, "Room Lobby"),
    React.createElement("div", { key: "code", className: "room-code-display" }, [
      React.createElement("div", { key: "l", style: { fontSize: "0.8rem", opacity: 0.7, marginBottom: 4 } }, "Room Code"),
      React.createElement("div", { key: "c", className: "code" }, props.roomState.code)
    ]),
    React.createElement("div", { key: "seats", className: "seats-grid" },
      players.map(function(p) {
        return React.createElement("div", {
          key: p.seat,
          className: "seat-box " + (p.name ? "filled" : "")
        }, [
          React.createElement("div", { key: "n", className: "seat-name" }, p.name || "Open"),
          React.createElement("div", {
            key: "t",
            className: "seat-team",
            style: { color: TEAM_COLORS[p.team] || "#fff" }
          }, p.team ? "Team " + p.team : "")
        ]);
      })
    ),
    props.isHost
      ? React.createElement("button", {
          key: "start",
          className: "btn btn-primary",
          onClick: props.onStart,
          disabled: !isFull
        }, isFull ? "Start Game" : "Waiting for players...")
      : React.createElement("p", { key: "wait", className: "waiting-text" }, "Waiting for host to start..."),
    React.createElement("button", {
      key: "leave",
      className: "btn btn-danger",
      onClick: props.onLeave,
      style: { marginTop: 12, opacity: 0.8 }
    }, "Leave Room")
  ]);
}

function GameView(props) {
  if (!props.gameState) return null;

  const players = props.gameState.players || [];
  const myPlayer = players.find(function(p) { return p.seat === props.mySeat; }) || {};
  const myHand = myPlayer.hand || [];
  const trickCards = props.gameState.trick_cards || [null, null, null, null];
  const currentSeat = props.gameState.current_seat;
  const trickComplete = props.gameState.trick_complete || false;
  const trickWinner = props.gameState.trick_winner_seat;
  const gameOver = props.gameState.game_over || false;
  const dealerSeat = props.gameState.dealer_seat;

  return React.createElement("div", { className: "game-container" }, [
    React.createElement(ScoreBoard, { key: "sb", gameState: props.gameState, mySeat: props.mySeat }),
    React.createElement("div", { key: "exit", className: "exit-btn", onClick: props.onExit }, "✕"),
    React.createElement("div", { key: "tc", className: "trick-counter" }, "Trick " + props.gameState.trick_num + "/13"),
    React.createElement("div", { key: "table", className: "table-area" }, [
      [0, 1, 2, 3].map(function(p) {
        const actualSeat = (props.mySeat + p) % 4;
        const player = players.find(function(pl) { return pl.seat === actualSeat; });
        const isActive = currentSeat === actualSeat && !trickComplete && !gameOver;
        return React.createElement(SeatMarker, {
          key: p,
          player: player,
          isActive: isActive,
          position: p,
          isBot: player ? player.is_bot : false,
          cardCount: player ? player.hand_size : 0,
          isDealer: dealerSeat === actualSeat
        });
      }),
      React.createElement("div", { key: "felt", className: "table-felt" }, [
        !props.gameState.boot_dealt ? React.createElement("div", {
          key: "boot",
          style: {
            position: "absolute",
            top: 8,
            left: "50%",
            transform: "translateX(-50%)",
            fontSize: "0.65rem",
            color: "rgba(255,255,255,0.5)",
            background: "rgba(0,0,0,0.3)",
            padding: "2px 10px",
            borderRadius: 10,
            zIndex: 5
          }
        }, "Boot: 32 cards") : null,
        React.createElement(TrickCenter, {
          key: "tc",
          trickCards: trickCards,
          mySeat: props.mySeat,
          winner: trickWinner,
          trickComplete: trickComplete,
          trickNum: props.gameState.trick_num,
          players: players
        }),
        React.createElement(TrumpStamp, {
          key: "stamp",
          suit: props.gameState.trump_suit,
          show: props.gameState.trump_revealed
        })
      ])
    ]),
    React.createElement(HandStrip, {
      key: "hand",
      hand: myHand,
      gameState: props.gameState,
      mySeat: props.mySeat,
      onPlayCard: props.onPlayCard
    }),
    gameOver
      ? React.createElement(ResultOverlay, {
          key: "res",
          gameState: props.gameState,
          onRematch: props.onRematch,
          onExit: props.onExit,
          isHost: props.isHost
        })
      : null
  ]);
}

// App
function App() {
  const wsRef = useRef(null);
  const trumpTimeoutRef = useRef(null);
  const [view, setView] = useState("menu");
  const [roomCode, setRoomCode] = useState("");
  const [mySeat, setMySeat] = useState(null);
  const [playerName, setPlayerName] = useState(localStorage.getItem("mendikot_name") || "");
  const [gameState, setGameState] = useState(null);
  const [roomState, setRoomState] = useState(null);
  const [toasts, setToasts] = useState([]);
  const [showConfirmExit, setShowConfirmExit] = useState(false);
  const [disconnected, setDisconnected] = useState(false);
  const [isHost, setIsHost] = useState(false);
  const [trumpFlash, setTrumpFlash] = useState(null);

  function send(msg) {
    if (wsRef.current && wsRef.current.readyState === 1) {
      wsRef.current.send(JSON.stringify(msg));
    }
  }

  function addToast(message) {
    const id = Date.now() + Math.random();
    setToasts(function(prev) { return [...prev, { id: id, message: message }]; });
    setTimeout(function() {
      setToasts(function(prev) { return prev.filter(function(t) { return t.id !== id; }); });
    }, 3000);
  }

  useEffect(function() {
    function connect() {
      const protocol = window.location.protocol === "https:" ? "wss:" : "ws:";
      const ws = new WebSocket(protocol + "//" + window.location.host + "/ws");
      wsRef.current = ws;

      ws.onopen = function() {
        setDisconnected(false);
      };

      ws.onmessage = function(e) {
        try {
          const msg = JSON.parse(e.data);
          handleMessage(msg);
        } catch(err) {
          console.error("WS parse error", err);
        }
      };

      ws.onclose = function() {
        setDisconnected(true);
        wsRef.current = null;
      };

      ws.onerror = function() {
        if (wsRef.current) wsRef.current.close();
      };
    }

    function handleMessage(msg) {
      switch(msg.type) {
        case "room_created":
          setRoomCode(msg.room_code);
          setMySeat(msg.seat);
          setRoomState(msg.state);
          setIsHost(true);
          setView("room");
          sessionStorage.setItem("mendikot_room", msg.room_code);
          sessionStorage.setItem("mendikot_seat", msg.seat);
          break;
        case "room_joined":
          setRoomCode(msg.room_code);
          setMySeat(msg.seat);
          setRoomState(msg.state);
          setIsHost(false);
          setView("room");
          sessionStorage.setItem("mendikot_room", msg.room_code);
          sessionStorage.setItem("mendikot_seat", msg.seat);
          break;
        case "player_joined":
        case "player_left":
          setRoomState(msg.state);
          break;
        case "game_started":
          setGameState(msg.state);
          setMySeat(msg.seat);
          setView("game");
          setDisconnected(false);
          setTrumpFlash(null);
          break;
        case "card_played":
          setGameState(function(prev) {
            if (!prev) return prev;
            const newTrick = prev.trick_cards ? [...prev.trick_cards] : [null, null, null, null];
            newTrick[msg.seat] = msg.card;
            const isTrickComplete = newTrick.every(function(c) { return c !== null; });
            const newPlayers = prev.players.map(function(p) {
              if (p.seat === msg.seat) {
                const newHandSize = (p.hand_size || 0) - 1;
                if (p.hand) {
                  const newHand = p.hand.filter(function(c) {
                    return !(c.suit === msg.card.suit && c.rank === msg.card.rank);
                  });
                  return Object.assign({}, p, { hand: newHand, hand_size: newHand.length });
                }
                return Object.assign({}, p, { hand_size: Math.max(0, newHandSize) });
              }
              return p;
            });
            return Object.assign({}, prev, {
              trick_cards: newTrick,
              current_seat: isTrickComplete ? prev.current_seat : (msg.seat + 1) % 4,
              led_suit: prev.led_suit || msg.card.suit,
              trick_leader: prev.trick_leader !== null ? prev.trick_leader : msg.seat,
              players: newPlayers,
              trump_suit: msg.revealed_now ? msg.card.suit : prev.trump_suit,
              trump_revealed: msg.revealed_now ? true : prev.trump_revealed,
              trump_revealer: msg.revealed_now ? msg.seat : prev.trump_revealer,
              trump_card: msg.revealed_now ? msg.card : prev.trump_card
            });
          });
          break;
        case "trump_revealed":
          setTrumpFlash({ suit: msg.suit, active: true });
          if (trumpTimeoutRef.current) clearTimeout(trumpTimeoutRef.current);
          trumpTimeoutRef.current = setTimeout(function() {
            setTrumpFlash(null);
          }, 1500);
          break;
        case "trick_won":
          setGameState(function(prev) {
            if (!prev) return prev;
            const winningTeam = msg.winning_team;
            const newMendiA = winningTeam === "A"
              ? [...(prev.mendi && prev.mendi.A ? prev.mendi.A : []), ...(msg.tens_won || [])]
              : (prev.mendi && prev.mendi.A ? prev.mendi.A : []);
            const newMendiB = winningTeam === "B"
              ? [...(prev.mendi && prev.mendi.B ? prev.mendi.B : []), ...(msg.tens_won || [])]
              : (prev.mendi && prev.mendi.B ? prev.mendi.B : []);
            const trickLen = msg.trick_cards ? msg.trick_cards.length : 0;
            return Object.assign({}, prev, {
              trick_complete: true,
              trick_winner_seat: msg.winner_seat,
              mendi: { A: newMendiA, B: newMendiB },
              cards_won: {
                A: winningTeam === "A" ? (prev.cards_won && prev.cards_won.A || 0) + trickLen : (prev.cards_won && prev.cards_won.A || 0),
                B: winningTeam === "B" ? (prev.cards_won && prev.cards_won.B || 0) + trickLen : (prev.cards_won && prev.cards_won.B || 0)
              },
              tricks_won: {
                A: winningTeam === "A" ? (prev.tricks_won && prev.tricks_won.A || 0) + 1 : (prev.tricks_won && prev.tricks_won.A || 0),
                B: winningTeam === "B" ? (prev.tricks_won && prev.tricks_won.B || 0) + 1 : (prev.tricks_won && prev.tricks_won.B || 0)
              }
            });
          });
          const tensCount = msg.tens_won ? msg.tens_won.length : 0;
          let winMsg = "Team " + msg.winning_team + " wins the trick!";
          if (tensCount > 0) {
            winMsg += " +" + tensCount + " mendi!";
          }
          addToast(winMsg);
          break;
        case "next_trick":
          setGameState(function(prev) {
            if (!prev) return msg.state;
            const newPlayers = msg.state.players.map(function(np) {
              const oldP = prev.players.find(function(p) { return p.seat === np.seat; });
              if (oldP && oldP.hand && !np.hand) {
                return Object.assign({}, np, { hand: oldP.hand, hand_size: oldP.hand.length });
              }
              return np;
            });
            return Object.assign({}, msg.state, {
              players: newPlayers,
              trick_cards: msg.state.trick_cards || [null, null, null, null]
            });
          });
          break;
        case "boot_dealt":
          addToast("Boot dealt! 8 new cards each");
          break;
        case "game_over":
          setGameState(function(prev) {
            if (!prev || !msg.state) return msg.state;
            const newPlayers = msg.state.players.map(function(np) {
              const oldP = prev.players.find(function(p) { return p.seat === np.seat; });
              if (oldP && oldP.hand && !np.hand) {
                return Object.assign({}, np, { hand: oldP.hand, hand_size: oldP.hand.length });
              }
              return np;
            });
            return Object.assign({}, msg.state, { players: newPlayers });
          });
          break;
        case "room_cancelled":
          addToast(msg.reason || "Room cancelled");
          setView("menu");
          setRoomCode("");
          setGameState(null);
          setRoomState(null);
          sessionStorage.removeItem("mendikot_room");
          sessionStorage.removeItem("mendikot_seat");
          break;
        case "error":
          addToast(msg.message || "Error occurred");
          break;
        case "pong":
          break;
        default:
          console.log("Unknown message", msg);
      }
    }

    connect();

    const pingInterval = setInterval(function() {
      if (wsRef.current && wsRef.current.readyState === 1) {
        send({ action: "ping" });
      }
    }, 30000);

    return function() {
      clearInterval(pingInterval);
      if (trumpTimeoutRef.current) clearTimeout(trumpTimeoutRef.current);
      if (wsRef.current) {
        wsRef.current.close();
        wsRef.current = null;
      }
    };
  }, []);

  function handleSolo() {
    const name = playerName || "Player";
    if (!playerName) setPlayerName(name);
    send({ action: "start_solo", name: name });
  }

  function handleCreateRoom(name, team) {
    send({ action: "create_room", name: name, team: team });
  }

  function handleJoinRoom(name, code, team) {
    send({ action: "join_room", name: name, room_code: code, team: team });
  }

  function handleStartGame() {
    send({ action: "start_game" });
  }

  function handlePlayCard(card, isReveal) {
    send({ action: "play_card", card: { suit: card.suit, rank: card.rank } });
  }

  function handleRematch() {
    send({ action: "rematch" });
  }

  function handleLeaveRoom() {
    send({ action: "leave_room" });
    setView("menu");
    setRoomCode("");
    setGameState(null);
    setRoomState(null);
    sessionStorage.removeItem("mendikot_room");
    sessionStorage.removeItem("mendikot_seat");
  }

  function handleConfirmExit() {
    send({ action: "leave_room" });
    setShowConfirmExit(false);
    setView("menu");
    setRoomCode("");
    setGameState(null);
    setRoomState(null);
    sessionStorage.removeItem("mendikot_room");
    sessionStorage.removeItem("mendikot_seat");
  }

  function handleReconnect() {
    window.location.reload();
  }

  return React.createElement(React.Fragment, null, [
    view === "menu" ? React.createElement(MenuView, { key: "vm", onSolo: handleSolo, onMultiplayer: function() { setView("hub"); } }) : null,
    view === "hub" ? React.createElement(HubView, { key: "vh", onCreate: function() { setView("create"); }, onJoin: function() { setView("join"); }, onBack: function() { setView("menu"); } }) : null,
    view === "create" ? React.createElement(CreateView, { key: "vc", onCreate: handleCreateRoom, onBack: function() { setView("hub"); } }) : null,
    view === "join" ? React.createElement(JoinView, { key: "vj", onJoin: handleJoinRoom, onBack: function() { setView("hub"); } }) : null,
    view === "room" ? React.createElement(RoomView, { key: "vr", roomState: roomState, mySeat: mySeat, isHost: isHost, onStart: handleStartGame, onLeave: handleLeaveRoom }) : null,
    view === "game" ? React.createElement(GameView, { key: "vg", gameState: gameState, mySeat: mySeat, onPlayCard: handlePlayCard, onExit: function() { setShowConfirmExit(true); }, isHost: isHost, onRematch: handleRematch }) : null,
    showConfirmExit ? React.createElement(ConfirmExitOverlay, { key: "ce", onConfirm: handleConfirmExit, onCancel: function() { setShowConfirmExit(false); } }) : null,
    disconnected && view !== "menu" ? React.createElement(DisconnectOverlay, { key: "do", onReconnect: handleReconnect, onMenu: function() { setView("menu"); setDisconnected(false); } }) : null,
    trumpFlash ? React.createElement(TrumpFlashOverlay, { key: "tf", suit: trumpFlash.suit }) : null,
    React.createElement(ToastContainer, { key: "tc", toasts: toasts })
  ]);
}

const root = ReactDOM.createRoot(document.getElementById("root"));
root.render(React.createElement(App));

</script>
</body>
</html>
"""
