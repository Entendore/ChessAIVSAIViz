#!/usr/bin/env python3
"""
AI vs AI → MP4  ·  Chess Battle
Single-file PySide6 application combining all modules.
"""

import sys
import os
import logging
import random
import time
import shutil
import subprocess
import tempfile
import atexit
import threading
import math
import wave
import csv
import re
import ast
import base64
from io import StringIO
from typing import Optional

import chess
import chess.pgn

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QLabel, QPushButton, QSpinBox, QDoubleSpinBox,
    QGroupBox, QComboBox, QFormLayout, QTabWidget,
    QFileDialog, QSlider, QCheckBox, QFrame,
    QLineEdit, QScrollArea, QSizePolicy, QMessageBox,
)
from PySide6.QtCore import Qt, QThread, QTimer, QObject, Signal, QRectF, QPointF, Property, QPropertyAnimation, QEasingCurve, QUrl
from PySide6.QtGui import (
    QApplication as QApp, QPainter, QColor, QFont, QLinearGradient,
    QRadialGradient, QPainterPath, QPen, QPalette, QImage, QPolygonF,
    QPixmap,
)
from PySide6.QtMultimedia import QSoundEffect

try:
    import cv2
    import numpy as np
    HAS_CV2 = True
    HAS_NUMPY = True
except ImportError:
    HAS_CV2 = False
    HAS_NUMPY = False

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False
    np = None

try:
    import imageio.v3 as iio
    HAS_IMAGEIO = True
except Exception:
    HAS_IMAGEIO = False

try:
    import pandas as pd
    HAS_PANDAS = True
except ImportError:
    HAS_PANDAS = False

try:
    import pyarrow.parquet as pq
    HAS_PYARROW = True
except ImportError:
    HAS_PYARROW = False

try:
    import duckdb
    HAS_DUCKDB = True
except ImportError:
    HAS_DUCKDB = False

HAS_QTMULTIMEDIA = True

csv.field_size_limit(2**31 - 1)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)-7s] %(name)s — %(message)s",
    datefmt="%H:%M:%S",
)
logger = logging.getLogger("AIvsAI2MP4")


# ════════════════════════════════════════════════════════════════════
#  CONSTANTS
# ════════════════════════════════════════════════════════════════════

def log(msg, level="INFO"):
    from datetime import datetime
    ts = datetime.now().strftime("%H:%M:%S.%f")[:-3]
    print(f"[{ts}] [{level}] {msg}", flush=True)

APP_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(APP_DIR, "data")

SQ_SIZE = 68
BOARD_PX = SQ_SIZE * 8

UNICODE_PIECES = {
    'K': '♔', 'Q': '♕', 'R': '♖', 'B': '♗', 'N': '♘', 'P': '♙',
    'k': '♚', 'q': '♛', 'r': '♜', 'b': '♝', 'n': '♞', 'p': '♟',
}

FILES_STR = 'abcdefgh'
RANKS_STR = '87654321'

PIECE_SYM = {
    (chess.PAWN,   chess.WHITE): '♙',
    (chess.KNIGHT, chess.WHITE): '♘',
    (chess.BISHOP, chess.WHITE): '♗',
    (chess.ROOK,   chess.WHITE): '♖',
    (chess.QUEEN,  chess.WHITE): '♕',
    (chess.KING,   chess.WHITE): '♔',
    (chess.PAWN,   chess.BLACK): '♟',
    (chess.KNIGHT, chess.BLACK): '♞',
    (chess.BISHOP, chess.BLACK): '♝',
    (chess.ROOK,   chess.BLACK): '♜',
    (chess.QUEEN,  chess.BLACK): '♛',
    (chess.KING,   chess.BLACK): '♚',
}

ANIM_SPEED_SLOW    = 500
ANIM_SPEED_DEFAULT = 250
ANIM_SPEED_FAST    = 100
ANIM_FPS           = 60

GAME_NORMAL       = "normal"
GAME_CHECKMATE    = "checkmate"
GAME_STALEMATE    = "stalemate"
GAME_DRAW         = "draw"
GAME_INSUFFICIENT = "insufficient"

MQ_GOOD       = "good"
MQ_BEST       = "best"
MQ_GREAT      = "great"
MQ_BRILLIANT  = "brilliant"
MQ_INACCURACY = "inaccuracy"
MQ_MISTAKE    = "mistake"
MQ_BLUNDER    = "blunder"
MQ_BOOK       = "book"

MQ_SHOW_BADGE = {MQ_BRILLIANT, MQ_BLUNDER}
MQ_SHOW_MOVES_BADGE = {MQ_BRILLIANT, MQ_BLUNDER, MQ_MISTAKE, MQ_GREAT}
MQ_SHOW_SQUARE_GLOW = {MQ_BRILLIANT, MQ_BLUNDER, MQ_MISTAKE}

MQ_COLORS = {
    MQ_GOOD:       QColor(120, 190, 120),
    MQ_BEST:       QColor(100, 180, 255),
    MQ_GREAT:      QColor(50, 170, 80),
    MQ_BRILLIANT:  QColor(0, 225, 180),
    MQ_INACCURACY: QColor(220, 190, 60),
    MQ_MISTAKE:    QColor(230, 140, 30),
    MQ_BLUNDER:    QColor(230, 40, 40),
    MQ_BOOK:       QColor(170, 160, 140),
}

MQ_VIDEO_COLORS = dict(MQ_COLORS)

MQ_BG_COLORS = {
    MQ_BRILLIANT:  QColor(0, 225, 180, 50),
    MQ_GREAT:      QColor(50, 170, 80, 35),
    MQ_MISTAKE:    QColor(230, 140, 30, 40),
    MQ_BLUNDER:    QColor(230, 40, 40, 55),
}

MQ_SQUARE_GLOW_COLORS = {
    MQ_BRILLIANT: QColor(0, 225, 180),
    MQ_BLUNDER:   QColor(230, 40, 40),
    MQ_MISTAKE:   QColor(230, 140, 30),
}

MQ_SYMBOLS = {
    MQ_GOOD:       "",
    MQ_BEST:       "!!",
    MQ_GREAT:      "!",
    MQ_BRILLIANT:  "★",
    MQ_INACCURACY: "?!",
    MQ_MISTAKE:    "!?",
    MQ_BLUNDER:    "✕",
    MQ_BOOK:       "♗",
}

MQ_ICONS = {
    MQ_GOOD:       "",
    MQ_BEST:       "!!",
    MQ_GREAT:      "!",
    MQ_BRILLIANT:  "★",
    MQ_INACCURACY: "?!",
    MQ_MISTAKE:    "!?",
    MQ_BLUNDER:    "✕",
    MQ_BOOK:       "♗",
}

MQ_LABELS = {
    MQ_GOOD:       "Good",
    MQ_BEST:       "Best",
    MQ_GREAT:      "Great",
    MQ_BRILLIANT:  "Brilliant",
    MQ_INACCURACY: "Inaccuracy",
    MQ_MISTAKE:    "Mistake",
    MQ_BLUNDER:    "Blunder",
    MQ_BOOK:       "Book",
}

PIECE_VAL = {'P': 100, 'N': 320, 'B': 330, 'R': 500, 'Q': 900, 'K': 20000}

PIECE_VALUES = {
    chess.PAWN:   1,
    chess.KNIGHT: 3,
    chess.BISHOP: 3,
    chess.ROOK:   5,
    chess.QUEEN:  9,
    chess.KING:   0,
}

class BoardTheme:
    def __init__(self, name="Classic",
                 light=(240, 217, 181), dark=(181, 136, 99),
                 border=(48, 26, 7), highlight=(255, 255, 0, 100),
                 last_move=(155, 199, 0, 100), arrow=(220, 50, 47, 200)):
        self.name = name
        self.light_sq = QColor(*light)
        self.dark_sq  = QColor(*dark)
        self.border   = QColor(*border)
        self.highlight = QColor(*highlight)
        self.last_move = QColor(*last_move)
        self.arrow_clr = QColor(*arrow)
        self.bg   = QColor(32, 32, 36)
        self.coord = QColor(180, 160, 130)

THEMES = {
    "Classic": BoardTheme(),
    "Blue":    BoardTheme("Blue", (208, 224, 243), (116, 150, 194), (40, 50, 70)),
    "Green":   BoardTheme("Green", (238, 238, 210), (118, 150, 86), (50, 60, 40)),
    "Brown":   BoardTheme("Brown", (222, 197, 165), (170, 120, 70), (60, 35, 15)),
    "Purple":  BoardTheme("Purple", (220, 210, 230), (150, 130, 170), (50, 40, 60)),
    "Ice":     BoardTheme("Ice", (230, 240, 250), (160, 190, 220), (50, 60, 80)),
}

PST = {
    'P': [[0,0,0,0,0,0,0,0],[50,50,50,50,50,50,50,50],[10,10,20,30,30,20,10,10],[5,5,10,25,25,10,5,5],[0,0,0,20,20,0,0,0],[5,-5,-10,0,0,-10,-5,5],[5,10,10,-20,-20,10,10,5],[0,0,0,0,0,0,0,0]],
    'N': [[-50,-40,-30,-30,-30,-30,-40,-50],[-40,-20,0,0,0,0,-20,-40],[-30,0,10,15,15,10,0,-30],[-30,5,15,20,20,15,5,-30],[-30,0,15,20,20,15,0,-30],[-30,5,10,15,15,10,5,-30],[-40,-20,0,5,5,0,-20,-40],[-50,-40,-30,-30,-30,-30,-40,-50]],
    'B': [[-20,-10,-10,-10,-10,-10,-10,-20],[-10,0,0,0,0,0,0,-10],[-10,0,10,10,10,10,0,-10],[-10,5,5,10,10,5,5,-10],[-10,0,5,10,10,5,0,-10],[-10,10,5,10,10,5,10,-10],[-10,5,0,0,0,0,5,-10],[-20,-10,-10,-10,-10,-10,-10,-20]],
    'R': [[0,0,0,0,0,0,0,0],[5,10,10,10,10,10,10,5],[-5,0,0,0,0,0,0,-5],[-5,0,0,0,0,0,0,-5],[-5,0,0,0,0,0,0,-5],[-5,0,0,0,0,0,0,-5],[-5,0,0,0,0,0,0,-5],[0,0,0,5,5,0,0,0]],
    'Q': [[-20,-10,-10,-5,-5,-10,-10,-20],[-10,0,0,0,0,0,0,-10],[-10,0,5,5,5,5,0,-10],[-5,0,5,5,5,5,0,-5],[0,0,5,5,5,5,0,-5],[-10,5,5,5,5,5,0,-10],[-10,0,5,0,0,0,0,-10],[-20,-10,-10,-5,-5,-10,-10,-20]],
    'K': [[-30,-40,-40,-50,-50,-40,-40,-30],[-30,-40,-40,-50,-50,-40,-40,-30],[-30,-40,-40,-50,-50,-40,-40,-30],[-30,-40,-40,-50,-50,-40,-40,-30],[-20,-30,-30,-40,-40,-30,-30,-20],[-10,-20,-20,-20,-20,-20,-20,-10],[20,20,0,0,0,0,20,20],[20,30,10,0,0,10,30,20]],
}

AI_MINIMAX   = 0
AI_MCTS      = 1
AI_STOCKFISH = 2

AI_MAP = {
    AI_MINIMAX:   "Minimax (α-β)",
    AI_MCTS:      "MCTS",
    AI_STOCKFISH: "Stockfish",
}

AI_SHORT_NAMES = {
    AI_MINIMAX:   "Minimax",
    AI_MCTS:      "MCTS",
    AI_STOCKFISH: "Stockfish",
}

SND_MOVE       = "move"
SND_CAPTURE    = "capture"
SND_CHECK      = "check"
SND_CASTLE     = "castle"
SND_CHECKMATE  = "checkmate"
SND_STALEMATE  = "stalemate"
SND_DRAW       = "draw"
SND_GAME_START = "game_start"
SND_UI_CLICK   = "ui_click"

SOUND_THEME_LIST = ["Classic", "Digital", "Cinematic", "Retro", "Ambient"]

RESOLUTION_LIST = ["1920×1080", "1280×720", "3840×2160", "1080×1920", "720×1280"]
RESOLUTION_SIZES = {
    "1920×1080": (1920, 1080),
    "1280×720":  (1280, 720),
    "3840×2160": (3840, 2160),
    "1080×1920": (1080, 1920),
    "720×1280":  (720, 1280),
}

DEFAULT_VIDEO_FPS       = 30
DEFAULT_MOVE_DURATION   = 2.0
DEFAULT_ANIM_DURATION   = 0.4
DEFAULT_TITLE_DURATION  = 3.0
DEFAULT_RESULT_DURATION = 3.0
DEFAULT_OUTPUT_DIR      = os.path.join(os.path.expanduser("~"), "Videos", "chess_battles")

class ExportConfig:
    def __init__(self):
        self.fps = DEFAULT_VIDEO_FPS
        self.title_enabled = True
        self.title_text = ""
        self.title_duration = DEFAULT_TITLE_DURATION
        self.title_bg = "#1a1a2e"
        self.title_fg = "#e0e0e0"
        self.title_font_size = 36
        self.end_enabled = True
        self.end_text = "Solved!"
        self.end_duration = DEFAULT_RESULT_DURATION
        self.end_bg = "#1a1a2e"
        self.end_fg = "#e0e0e0"
        self.end_font_size = 42
        self.move_anim_duration = DEFAULT_ANIM_DURATION
        self.pause_after_move = DEFAULT_MOVE_DURATION
        self.highlight_duration = 0.3
        self.max_workers = 4
        self.sq_size = SQ_SIZE
        self.theme_name = "Classic"
        self.move_quality = MQ_GOOD

def find_stockfish():
    env_path = os.environ.get("STOCKFISH_PATH")
    if env_path and os.path.isfile(env_path) and os.access(env_path, os.X_OK):
        return env_path
    candidates = [
        "stockfish", "stockfish-windows-x86-64-avx2",
        "stockfish-windows-x86-64-modern", "stockfish-windows-x86-64",
        "stockfish_17", "stockfish_16",
    ]
    if sys.platform == "win32":
        candidates = [c + ".exe" for c in candidates]
    for name in candidates:
        found = shutil.which(name)
        if found:
            return found
    if sys.platform == "win32":
        program_files = os.environ.get("ProgramFiles", r"C:\Program Files")
        program_files_x86 = os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")
        local_app_data = os.environ.get("LocalAppData", "")
        search_dirs = [program_files, program_files_x86, r"C:\Stockfish", r"D:\Stockfish"]
        if local_app_data:
            search_dirs.append(os.path.join(local_app_data, "Programs"))
        subfolder_names = ["stockfish", "Stockfish", "Stockfish Engine", ""]
        exe_names = [
            "stockfish-windows-x86-64-avx2.exe", "stockfish-windows-x86-64-modern.exe",
            "stockfish-windows-x86-64-sse41-popcnt.exe", "stockfish-windows-x86-64.exe",
            "stockfish.exe", "Stockfish.exe",
            "stockfish_17.exe", "stockfish_16.exe", "stockfish_15.exe", "stockfish_14.exe",
        ]
        for base_dir in search_dirs:
            if not os.path.isdir(base_dir):
                continue
            for exe in exe_names:
                p = os.path.join(base_dir, exe)
                if os.path.isfile(p):
                    return p
            for sub in subfolder_names:
                for exe in exe_names:
                    p = os.path.join(base_dir, sub, exe)
                    if os.path.isfile(p):
                        return p
            try:
                for entry in os.listdir(base_dir):
                    entry_lower = entry.lower()
                    if "stockfish" in entry_lower:
                        full = os.path.join(base_dir, entry)
                        if os.path.isfile(full) and full.lower().endswith(".exe"):
                            return full
                        if os.path.isdir(full):
                            try:
                                for inner in os.listdir(full):
                                    if inner.lower().endswith(".exe") and "stockfish" in inner.lower():
                                        return os.path.join(full, inner)
                            except OSError:
                                pass
            except OSError:
                pass
    elif sys.platform == "darwin":
        for p in ["/usr/local/bin/stockfish", "/opt/homebrew/bin/stockfish",
                  "/Applications/Stockfish.app/Contents/MacOS/stockfish"]:
            if os.path.isfile(p):
                return p
        for name in ["stockfish-macos-x86-64", "stockfish-macos-arm64"]:
            found = shutil.which(name)
            if found:
                return found
    else:
        for p in ["/usr/bin/stockfish", "/usr/local/bin/stockfish",
                  "/usr/games/stockfish", "/snap/bin/stockfish"]:
            if os.path.isfile(p):
                return p
        for name in ["stockfish-linux-x86-64-avx2",
                      "stockfish-linux-x86-64-modern", "stockfish-linux-x86-64"]:
            found = shutil.which(name)
            if found:
                return found
    return None

def parse_opening_image(img_val):
    pixmap = None
    img_dict = None
    if isinstance(img_val, dict):
        img_dict = img_val
    elif isinstance(img_val, str) and img_val.strip().startswith("{"):
        try:
            safe = img_val
            safe = re.sub(r'\bnull\b', 'None', safe)
            safe = re.sub(r'\btrue\b', 'True', safe)
            safe = re.sub(r'\bfalse\b', 'False', safe)
            safe = re.sub(r'\bNaN\b', 'None', safe)
            safe = re.sub(r'\bundefined\b', 'None', safe)
            img_dict = ast.literal_eval(safe)
        except Exception as e:
            log(f"Image parse error: {e}", "OPENINGS")
    if img_dict:
        try:
            bytes_val = img_dict.get('bytes')
            actual_bytes = None
            if isinstance(bytes_val, bytes):
                actual_bytes = bytes_val
            elif isinstance(bytes_val, str):
                try:
                    actual_bytes = base64.b64decode(bytes_val)
                except Exception:
                    pass
                if actual_bytes is None:
                    try:
                        actual_bytes = bytes(bytes_val, "utf-8").decode("unicode_escape").encode("latin1")
                    except Exception:
                        pass
            if actual_bytes:
                pixmap = QPixmap()
                pixmap.loadFromData(actual_bytes)
        except Exception as e:
            log(f"Image byte extraction error: {e}", "OPENINGS")
    return pixmap


# ════════════════════════════════════════════════════════════════════
#  ENGINES
# ════════════════════════════════════════════════════════════════════

class MinimaxEngine:
    def __init__(self):
        self._nodes = 0

    def search(self, board, depth):
        self._nodes = 0
        is_white = board.turn == chess.WHITE
        best_move = None
        best_score = float('-inf')
        alpha = float('-inf')
        beta = float('inf')
        policy = {}
        moves = list(board.legal_moves)
        moves.sort(key=lambda m: (0 if board.is_capture(m) else (1 if board.gives_check(m) else 2)))
        for move in moves:
            board.push(move)
            score = -self._alphabeta(board, depth - 1, -beta, -alpha, not is_white)
            board.pop()
            self._nodes += 1
            policy[move.uci()] = score
            if score > best_score:
                best_score = score
                best_move = move
            alpha = max(alpha, score)
        eval_cp = best_score if is_white else -best_score
        return best_move, eval_cp, self._nodes, policy

    def _alphabeta(self, board, depth, alpha, beta, maximizing):
        if depth == 0 or board.is_game_over():
            if depth == 0 and not board.is_game_over():
                return self._quiesce(board, alpha, beta, 3)
            return self._evaluate(board)
        self._nodes += 1
        moves = list(board.legal_moves)
        moves.sort(key=lambda m: (0 if board.is_capture(m) else (1 if board.gives_check(m) else 2)))
        if maximizing:
            value = float('-inf')
            for move in moves:
                board.push(move)
                value = max(value, self._alphabeta(board, depth - 1, alpha, beta, False))
                board.pop()
                alpha = max(alpha, value)
                if alpha >= beta:
                    break
            return value
        else:
            value = float('inf')
            for move in moves:
                board.push(move)
                value = min(value, self._alphabeta(board, depth - 1, alpha, beta, True))
                board.pop()
                beta = min(beta, value)
                if alpha >= beta:
                    break
            return value

    def _quiesce(self, board, alpha, beta, depth_left):
        self._nodes += 1
        stand_pat = self._evaluate(board)
        if depth_left == 0:
            return stand_pat
        if stand_pat >= beta:
            return beta
        alpha = max(alpha, stand_pat)
        for move in board.legal_moves:
            if not board.is_capture(move):
                continue
            board.push(move)
            score = -self._quiesce(board, -beta, -alpha, depth_left - 1)
            board.pop()
            if score >= beta:
                return beta
            alpha = max(alpha, score)
        return alpha

    def _evaluate(self, board):
        if board.is_checkmate():
            return -30000
        if board.is_stalemate() or board.is_insufficient_material():
            return 0
        score = 0
        for sq in chess.SQUARES:
            piece = board.piece_at(sq)
            if piece is None:
                continue
            pt = piece.symbol().upper()
            val = PIECE_VAL.get(pt, 0)
            pst = PST.get(pt)
            if piece.color == chess.WHITE:
                rank = chess.square_rank(sq)
                file_ = chess.square_file(sq)
                score += val + (pst[7 - rank][file_] if pst else 0)
            else:
                rank = chess.square_rank(sq)
                file_ = chess.square_file(sq)
                score -= val + (pst[rank][file_] if pst else 0)
        mobility = board.legal_moves.count()
        mob_bonus = 5 * mobility
        if board.turn == chess.WHITE:
            score += mob_bonus
        else:
            score -= mob_bonus
        return score if board.turn == chess.WHITE else -score


class _MCTSNode:
    __slots__ = ('board', 'move', 'parent', 'children', 'visits', 'wins', 'untried_moves')
    def __init__(self, board, move=None, parent=None):
        self.board = board
        self.move = move
        self.parent = parent
        self.children = []
        self.visits = 0
        self.wins = 0.0
        self.untried_moves = list(board.legal_moves)
        random.shuffle(self.untried_moves)
    def ucb1(self, c=1.414):
        if self.visits == 0:
            return float('inf')
        return (self.wins / self.visits + c * (2.0 * (self.parent.visits + 1) / (self.visits + 1)) ** 0.5)
    def best_child(self):
        return max(self.children, key=lambda ch: ch.ucb1())
    def expand(self):
        move = self.untried_moves.pop()
        next_board = self.board.copy()
        next_board.push(move)
        child = _MCTSNode(next_board, move=move, parent=self)
        self.children.append(child)
        return child
    def is_fully_expanded(self):
        return len(self.untried_moves) == 0
    def is_terminal(self):
        return self.board.is_game_over()


class MCTSEngine:
    def __init__(self):
        self._nodes = 0

    def search(self, board, iterations):
        self._nodes = 0
        root = _MCTSNode(board.copy())
        if not list(board.legal_moves):
            return None, 0.0, 0, {}
        for _ in range(iterations):
            node = root
            while not node.is_terminal() and node.is_fully_expanded():
                node = node.best_child()
            if not node.is_terminal() and not node.is_fully_expanded():
                node = node.expand()
            self._nodes += 1
            result = self._rollout(node.board.copy())
            while node is not None:
                node.visits += 1
                if node.board.turn == chess.WHITE:
                    node.wins += (1.0 - result)
                else:
                    node.wins += result
                node = node.parent
        if not root.children:
            return None, 0.0, self._nodes, {}
        best = max(root.children, key=lambda ch: ch.visits)
        policy = {ch.move.uci(): ch.visits / max(1, root.visits) for ch in root.children}
        wr = best.wins / max(1, best.visits)
        eval_cp = (wr - 0.5) * 600
        if board.turn == chess.BLACK:
            eval_cp = -eval_cp
        return best.move, eval_cp, self._nodes, policy

    def _rollout(self, board, max_moves=80):
        for _ in range(max_moves):
            if board.is_game_over():
                break
            moves = list(board.legal_moves)
            captures = [m for m in moves if board.is_capture(m)]
            if captures and random.random() < 0.3:
                move = random.choice(captures)
            else:
                move = random.choice(moves)
            board.push(move)
        if board.is_checkmate():
            return 1.0 if board.turn == chess.BLACK else 0.0
        return 0.5


class SyncUCI:
    def __init__(self, path, timeout=30):
        self._path = path
        self._timeout = timeout
        self._lock = threading.Lock()
        try:
            self._proc = subprocess.Popen(
                [path], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL, bufsize=0,
            )
            self._uci_init()
        except Exception as e:
            logger.error("Failed to start Stockfish: %s", e)
            raise

    def _send(self, cmd):
        self._proc.stdin.write((cmd + "\n").encode())
        self._proc.stdin.flush()

    def _read_line(self):
        return self._proc.stdout.readline().decode().strip()

    def _uci_init(self):
        self._send("uci")
        while True:
            line = self._read_line()
            if line == "uciok":
                break
        self._send("isready")
        while True:
            line = self._read_line()
            if line == "readyok":
                break

    def analyse(self, fen, depth=18, movetime=None):
        with self._lock:
            self._send("ucinewgame")
            self._send(f"position fen {fen}")
            if movetime is not None:
                self._send(f"go movetime {movetime}")
            else:
                self._send(f"go depth {depth}")
            best_move = None
            score_cp = 0.0
            while True:
                line = self._read_line()
                if not line:
                    break
                parts = line.split()
                if parts and parts[0] == "bestmove":
                    best_move = parts[1] if len(parts) > 1 else None
                    break
                if "score" in parts:
                    idx = parts.index("score")
                    if idx + 2 < len(parts):
                        stype = parts[idx + 1]
                        sval = parts[idx + 2]
                        if stype == "cp":
                            score_cp = int(sval)
                        elif stype == "mate":
                            mate_plies = int(sval)
                            score_cp = 10000 - abs(mate_plies)
                            if mate_plies < 0:
                                score_cp = -score_cp
            board = chess.Board(fen)
            if board.turn == chess.BLACK:
                score_cp = -score_cp
            return best_move, score_cp

    def close(self):
        try:
            self._send("quit")
            self._proc.wait(timeout=5)
        except Exception:
            try:
                self._proc.kill()
            except Exception:
                pass

    def __del__(self):
        try:
            self.close()
        except Exception:
            pass


def rgb_to_bgr_batch(frames):
    if not HAS_NUMPY:
        return [cv2.cvtColor(f, cv2.COLOR_RGB2BGR) for f in frames]
    try:
        import cupy as cp
        results = []
        for f in frames:
            gpu = cp.asarray(f)
            bgr = cp.stack([gpu[:, :, 2], gpu[:, :, 1], gpu[:, :, 0]], axis=2)
            results.append(cp.asnumpy(bgr))
        return results
    except ImportError:
        pass
    arr = np.stack(frames)
    bgr = arr[:, :, :, ::-1].copy()
    return [bgr[i] for i in range(len(frames))]


class ChessEngine:
    def __init__(self):
        self.reset()

    def reset(self):
        self.board = [
            ['r','n','b','q','k','b','n','r'],['p','p','p','p','p','p','p','p'],
            ['.','.','.','.','.','.','.','.'],['.','.','.','.','.','.','.','.'],
            ['.','.','.','.','.','.','.','.'],['.','.','.','.','.','.','.','.'],
            ['P','P','P','P','P','P','P','P'],['R','N','B','Q','K','B','N','R'],
        ]
        self.turn = 'w'
        self.castling = {'K': True, 'Q': True, 'k': True, 'q': True}
        self.ep = None
        self.history = []
        self.game_over = False
        self.result = ""
        self.last_move = None

    @staticmethod
    def is_white(p): return p != '.' and p.isupper()
    @staticmethod
    def is_black(p): return p != '.' and p.islower()
    @staticmethod
    def color_of(p): return 'w' if p.isupper() else ('b' if p != '.' else None)

    def copy_board(self): return [r[:] for r in self.board]

    def find_king(self, color):
        k = 'K' if color == 'w' else 'k'
        for r in range(8):
            for c in range(8):
                if self.board[r][c] == k: return (r, c)
        return None

    def attacked(self, row, col, by):
        kn = 'N' if by == 'w' else 'n'
        for dr, dc in [(-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)]:
            r2, c2 = row+dr, col+dc
            if 0<=r2<8 and 0<=c2<8 and self.board[r2][c2]==kn: return True
        ki = 'K' if by=='w' else 'k'
        for dr in (-1,0,1):
            for dc in (-1,0,1):
                if dr==0 and dc==0: continue
                r2,c2 = row+dr, col+dc
                if 0<=r2<8 and 0<=c2<8 and self.board[r2][c2]==ki: return True
        pw = 'P' if by=='w' else 'p'; pd = 1 if by=='w' else -1; r2 = row+pd
        if 0<=r2<8:
            for dc2 in (-1,1):
                c2 = col+dc2
                if 0<=c2<8 and self.board[r2][c2]==pw: return True
        rk = 'R' if by=='w' else 'r'; qu = 'Q' if by=='w' else 'q'
        for dr,dc in [(0,1),(0,-1),(1,0),(-1,0)]:
            r2,c2 = row+dr, col+dc
            while 0<=r2<8 and 0<=c2<8:
                p = self.board[r2][c2]
                if p!='.':
                    if p in (rk,qu): return True
                    break
                r2+=dr; c2+=dc
        bi = 'B' if by=='w' else 'b'
        for dr,dc in [(1,1),(1,-1),(-1,1),(-1,-1)]:
            r2,c2 = row+dr, col+dc
            while 0<=r2<8 and 0<=c2<8:
                p = self.board[r2][c2]
                if p!='.':
                    if p in (bi,qu): return True
                    break
                r2+=dr; c2+=dc
        return False

    def in_check(self, color):
        kp = self.find_king(color)
        return self.attacked(kp[0], kp[1], 'b' if color=='w' else 'w') if kp else True

    def pseudo_moves(self, r, c):
        p = self.board[r][c]
        if p=='.': return []
        co = self.color_of(p); pt = p.upper(); mv = []
        if pt=='P':
            d = -1 if co=='w' else 1; sr = 6 if co=='w' else 1; nr = r+d
            if 0<=nr<8 and self.board[nr][c]=='.':
                mv.append((nr,c)); nr2 = r+2*d
                if r==sr and self.board[nr2][c]=='.': mv.append((nr2,c))
            for dc in (-1,1):
                nc = c+dc; nr2 = r+d
                if 0<=nr2<8 and 0<=nc<8:
                    t = self.board[nr2][nc]
                    if (t!='.' and self.color_of(t)!=co) or (self.ep and (nr2,nc)==self.ep): mv.append((nr2,nc))
        elif pt=='N':
            for dr,dc in [(-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)]:
                r2,c2 = r+dr, c+dc
                if 0<=r2<8 and 0<=c2<8:
                    t = self.board[r2][c2]
                    if t=='.' or self.color_of(t)!=co: mv.append((r2,c2))
        elif pt in ('B','R','Q'):
            dirs = []
            if pt in ('B','Q'): dirs += [(1,1),(1,-1),(-1,1),(-1,-1)]
            if pt in ('R','Q'): dirs += [(0,1),(0,-1),(1,0),(-1,0)]
            for dr,dc in dirs:
                r2,c2 = r+dr, c+dc
                while 0<=r2<8 and 0<=c2<8:
                    t = self.board[r2][c2]
                    if t=='.': mv.append((r2,c2))
                    elif self.color_of(t)!=co: mv.append((r2,c2)); break
                    else: break
                    r2+=dr; c2+=dc
        elif pt=='K':
            for dr in (-1,0,1):
                for dc in (-1,0,1):
                    if dr==0 and dc==0: continue
                    r2,c2 = r+dr, c+dc
                    if 0<=r2<8 and 0<=c2<8:
                        t = self.board[r2][c2]
                        if t=='.' or self.color_of(t)!=co: mv.append((r2,c2))
            enemy = 'b' if co=='w' else 'w'
            if co=='w' and r==7 and c==4:
                if (self.castling['K'] and self.board[7][5]=='.' and self.board[7][6]=='.' and self.board[7][7]=='R'):
                    if not self.attacked(7,4,enemy) and not self.attacked(7,5,enemy) and not self.attacked(7,6,enemy): mv.append((7,6))
                if (self.castling['Q'] and self.board[7][3]=='.' and self.board[7][2]=='.' and self.board[7][1]=='.' and self.board[7][0]=='R'):
                    if not self.attacked(7,4,enemy) and not self.attacked(7,3,enemy) and not self.attacked(7,2,enemy): mv.append((7,2))
            elif co=='b' and r==0 and c==4:
                if (self.castling['k'] and self.board[0][5]=='.' and self.board[0][6]=='.' and self.board[0][7]=='r'):
                    if not self.attacked(0,4,enemy) and not self.attacked(0,5,enemy) and not self.attacked(0,6,enemy): mv.append((0,6))
                if (self.castling['q'] and self.board[0][3]=='.' and self.board[0][2]=='.' and self.board[0][1]=='.' and self.board[0][0]=='r'):
                    if not self.attacked(0,4,enemy) and not self.attacked(0,3,enemy) and not self.attacked(0,2,enemy): mv.append((0,2))
        return mv

    def legal_moves(self, r, c):
        p = self.board[r][c]
        if p=='.' or self.color_of(p)!=self.turn: return []
        co = self.color_of(p); out = []
        for tr,tc in self.pseudo_moves(r,c):
            sb = self.copy_board(); sep = self.ep; sc = dict(self.castling)
            self.board[tr][tc] = p; self.board[r][c] = '.'
            if p.upper()=='P' and self.ep and (tr,tc)==self.ep: self.board[r][tc] = '.'
            if p.upper()=='K' and abs(tc-c)==2:
                if tc==6: self.board[r][5]=self.board[r][7]; self.board[r][7]='.'
                elif tc==2: self.board[r][3]=self.board[r][0]; self.board[r][0]='.'
            chk = self.in_check(co)
            self.board = sb; self.ep = sep; self.castling = sc
            if not chk: out.append((tr,tc))
        return out

    def all_legal_moves(self, color=None):
        if color is None: color = self.turn
        out = []
        for r in range(8):
            for c in range(8):
                if self.color_of(self.board[r][c])==color:
                    for m in self.legal_moves(r,c): out.append(((r,c),m))
        return out

    def make_move(self, fr, fc, tr, tc, promo=None):
        p = self.board[fr][fc]
        if p=='.': return None
        co = self.color_of(p); cap = self.board[tr][tc]
        info = {'from':(fr,fc),'to':(tr,tc),'piece':p,'captured':cap,
                'castle':False,'ep':False,'promo':None,'check':False,'mate':False,'notation':''}
        self.history.append({'board':self.copy_board(),'turn':self.turn,
            'castling':dict(self.castling),'ep':self.ep,
            'last_move':self.last_move,'game_over':self.game_over,'result':self.result})
        if p.upper()=='P' and self.ep and (tr,tc)==self.ep:
            info['ep']=True; info['captured']=self.board[fr][tc]; self.board[fr][tc]='.'
        self.ep = None
        if p.upper()=='P' and abs(tr-fr)==2: self.ep = ((fr+tr)//2, fc)
        if p.upper()=='K' and abs(tc-fc)==2:
            info['castle']=True
            if tc==6: self.board[fr][5]=self.board[fr][7]; self.board[fr][7]='.'
            elif tc==2: self.board[fr][3]=self.board[fr][0]; self.board[fr][0]='.'
        self.board[tr][tc]=p; self.board[fr][fc]='.'
        prow = 0 if co=='w' else 7
        if p.upper()=='P' and tr==prow:
            pp = promo or ('Q' if co=='w' else 'q')
            self.board[tr][tc]=pp; info['promo']=pp
        if (fr,fc)==(7,4): self.castling['K']=False; self.castling['Q']=False
        if (fr,fc)==(0,4): self.castling['k']=False; self.castling['q']=False
        for pos,key in [((7,7),'K'),((7,0),'Q'),((0,7),'k'),((0,0),'q')]:
            if (fr,fc)==pos or (tr,tc)==pos: self.castling[key]=False
        self.last_move = ((fr,fc),(tr,tc))
        self.turn = 'b' if self.turn=='w' else 'w'
        if self.in_check(self.turn):
            info['check']=True
            if not self.all_legal_moves(self.turn):
                info['mate']=True; self.game_over=True
                self.result = "White wins!" if self.turn=='b' else "Black wins!"
        elif not self.all_legal_moves(self.turn):
            self.game_over=True; self.result="Stalemate — Draw"
        info['notation'] = self._nota(info)
        return info

    def undo(self):
        if not self.history: return False
        s = self.history.pop()
        self.board=s['board']; self.turn=s['turn']; self.castling=s['castling']
        self.ep=s['ep']; self.last_move=s['last_move']
        self.game_over=s['game_over']; self.result=s['result']
        return True

    def _nota(self, info):
        if info['castle']: n = "O-O" if info['to'][1]==6 else "O-O-O"
        else:
            pt=info['piece'].upper(); fr,fc=info['from']; tr,tc=info['to']
            n = "" if pt=='P' else pt
            if info['captured']!='.':
                if pt=='P': n += FILES_STR[fc]
                n += 'x'
            n += FILES_STR[tc]+RANKS_STR[tr]
            if info['promo']: n += '='+info['promo'].upper()
        if info['mate']: n+='#'
        elif info['check']: n+='+'
        return n

    def load_fen(self, fen):
        parts = fen.split(); rows = parts[0].split('/')
        self.board = []
        for row_str in rows:
            row = []
            for ch in row_str:
                if ch.isdigit(): row.extend(['.']*int(ch))
                else: row.append(ch)
            self.board.append(row)
        self.turn = 'w' if parts[1]=='w' else 'b'
        self.castling = {'K':'K' in parts[2],'Q':'Q' in parts[2],'k':'k' in parts[2],'q':'q' in parts[2]}
        self.ep = None
        if len(parts)>3 and parts[3]!='-':
            c = ord(parts[3][0])-ord('a'); r = 8-int(parts[3][1])
            self.ep = (r,c)
        self.history=[]; self.game_over=False; self.result=""; self.last_move=None

    def parse_uci(self, uci_str):
        if not uci_str or len(uci_str)<4: return None, None
        fc = ord(uci_str[0])-ord('a'); fr = 8-int(uci_str[1])
        tc = ord(uci_str[2])-ord('a'); tr = 8-int(uci_str[3])
        promo = uci_str[4] if len(uci_str)==5 else None
        return ((fr,fc),(tr,tc)), promo

    def evaluate(self):
        s = 0
        for r in range(8):
            for c in range(8):
                p = self.board[r][c]
                if p=='.': continue
                pt = p.upper(); v = PIECE_VAL.get(pt,0); t = PST.get(pt)
                if p.isupper(): s += v + (t[r][c] if t else 0)
                else: s -= v + (t[7-r][c] if t else 0)
        return s


# ════════════════════════════════════════════════════════════════════
#  MOVE ANALYZER
# ════════════════════════════════════════════════════════════════════

def classify_move(eval_before, eval_after, is_white_move, board=None, move=None, move_number=0):
    if move_number <= 2:
        return MQ_BOOK
    if is_white_move:
        delta = eval_after - eval_before
    else:
        delta = eval_before - eval_after
    def _clamp(cp):
        return max(-3000, min(3000, cp))
    delta = _clamp(delta)
    if delta <= -200:
        abs_before = abs(eval_before)
        if abs_before < 5000:
            return MQ_BLUNDER
    if delta <= -100:
        return MQ_MISTAKE
    if delta <= -50:
        return MQ_INACCURACY
    is_sacrifice = _detect_sacrifice(board, move) if (board and move) else False
    if delta >= 150 and is_sacrifice:
        return MQ_BRILLIANT
    if delta >= 80:
        return MQ_GREAT
    if delta >= -15:
        return MQ_BEST
    return MQ_GOOD

def _detect_sacrifice(board, move):
    if not move or not board:
        return False
    piece = board.piece_at(move.from_square)
    if not piece:
        return False
    piece_val = PIECE_VALUES.get(piece.piece_type, 0)
    if piece_val <= 1:
        return False
    captured = board.piece_at(move.to_square)
    if captured:
        cap_val = PIECE_VALUES.get(captured.piece_type, 0)
        if cap_val >= piece_val:
            return False
    attackers = board.attackers(not piece.color, move.to_square)
    for atk_sq in attackers:
        atk = board.piece_at(atk_sq)
        if atk and PIECE_VALUES.get(atk.piece_type, 0) < piece_val:
            return True
    return False

class MoveAnalyzer:
    def __init__(self):
        self._evals = []
        self._qualities = []
        self._move_number = 0

    def reset(self):
        self._evals.clear()
        self._qualities.clear()
        self._move_number = 0

    def push(self, eval_cp, is_white, board=None, move=None):
        self._move_number += 1
        prev = self._evals[-1] if self._evals else 0.0
        q = classify_move(prev, eval_cp, is_white, board, move, self._move_number)
        self._evals.append(eval_cp)
        self._qualities.append(q)
        return q

    @property
    def evals(self):
        return list(self._evals)

    @property
    def qualities(self):
        return list(self._qualities)

    @property
    def last_quality(self):
        return self._qualities[-1] if self._qualities else MQ_GOOD


# ════════════════════════════════════════════════════════════════════
#  BOARD RENDERER
# ════════════════════════════════════════════════════════════════════

class BoardRenderer:
    def __init__(self, board=None, theme=None, flipped=False):
        self.board = board or chess.Board()
        self.theme = theme if theme is not None else THEMES.get(
            "Classic", BoardTheme())
        self.flipped = flipped
        self.show_coords = True
        self.selected_sq = None
        self.legal_targets = []
        self.last_move = None
        self.highlighted = set()
        self.arrows = []
        self.anim_move = None
        self.anim_rook_move = None
        self.anim_progress = 1.0
        self._check_square = None
        self._check_opacity = 0.0
        self.move_quality = MQ_GOOD
        self.policy_vis = {}
        self._cache_sz = -1
        self._font_piece = None
        self._font_coord = None
        self._font_badge_normal = None
        self._font_badge_symbol = None
        self._pen_white_shadow = None
        self._pen_white_outline = None
        self._pen_black_shadow = None
        self._pen_badge_outline = None
        self._pen_badge_outer_ring = None

    def _update_cache(self, sz):
        isz = int(sz * 100)
        if isz == self._cache_sz:
            return
        self._cache_sz = isz
        self._font_piece = QFont("Segoe UI Symbol", sz * 0.72)
        self._font_piece.setStyleStrategy(QFont.PreferAntialias)
        self._font_coord = QFont("Inter", max(7, int(sz * 0.13)))
        self._font_coord.setBold(True)
        self._font_badge_normal = QFont("Inter", max(8, int(sz * 0.26 * 0.9)), QFont.Bold)
        self._font_badge_symbol = QFont("Segoe UI Symbol", max(9, int(sz * 0.26 * 1.1)), QFont.Bold)
        self._pen_white_shadow  = QPen(QColor(0, 0, 0, 50), max(1, sz * 0.03))
        self._pen_white_outline = QPen(QColor(0, 0, 0, 200), max(1, sz * 0.04))
        self._pen_black_shadow  = QPen(QColor(0, 0, 0, 60), max(1, sz * 0.03))
        self._pen_badge_outline = QPen(QColor(255, 255, 255, 140), max(1.0, sz * 0.012))
        self._pen_badge_outer_ring = QPen(QColor(255, 255, 255, 80), max(0.8, sz * 0.008))

    def render(self, size=1080):
        img = QImage(size, size, QImage.Format_ARGB32)
        img.fill(QColor(0, 0, 0, 0))
        p = QPainter(img)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.TextAntialiasing)
        m = size * 0.05 if self.show_coords else 0
        sz = (size - 2 * m) / 8
        self._paint(p, size, m, sz)
        p.end()
        return img

    def _sq_rect(self, sq, t, m, sz):
        f, r = chess.square_file(sq), chess.square_rank(sq)
        c = (7 - f) if self.flipped else f
        rw = r if self.flipped else (7 - r)
        return QRectF(m + c * sz, m + rw * sz, sz, sz)

    def _paint(self, p, t, m, sz):
        self._update_cache(sz)
        bg_grad = QLinearGradient(0, 0, 0, t)
        bg_grad.setColorAt(0.0, self.theme.bg.darker(110))
        bg_grad.setColorAt(1.0, self.theme.bg)
        p.fillRect(QRectF(0, 0, t, t), bg_grad)
        if self.last_move and self.move_quality in MQ_SHOW_SQUARE_GLOW:
            self._draw_square_glow(p, self.last_move.to_square, t, m, sz)
        for s in chess.SQUARES:
            rect = self._sq_rect(s, t, m, sz)
            f, r = chess.square_file(s), chess.square_rank(s)
            base = self.theme.light_sq if (f + r) % 2 == 0 else self.theme.dark_sq
            p.fillRect(rect, base)
            if self.last_move and s in (self.last_move.from_square, self.last_move.to_square):
                p.fillRect(rect, self.theme.last_move)
            if s == self.selected_sq:
                p.fillRect(rect, self.theme.highlight)
            if s in self.highlighted:
                p.fillRect(rect, QColor(0, 130, 255, 80))
        if self.last_move and self.move_quality in MQ_SHOW_SQUARE_GLOW:
            self._draw_square_quality_overlay(p, self.last_move.to_square, t, m, sz)
        if self._check_square is not None and self._check_opacity > 0:
            cr = self._sq_rect(self._check_square, t, m, sz)
            rg = QRadialGradient(cr.center(), sz * 0.7)
            rg.setColorAt(0.0, QColor(255, 30, 30, int(self._check_opacity * 160)))
            rg.setColorAt(0.6, QColor(255, 0, 0, int(self._check_opacity * 70)))
            rg.setColorAt(1.0, QColor(255, 0, 0, 0))
            p.setPen(Qt.NoPen)
            p.setBrush(rg)
            p.drawRect(cr)
        if self.show_coords:
            p.setFont(self._font_coord)
            p.setPen(self.theme.coord)
            for i in range(8):
                fl = chr(ord("h") - i if self.flipped else ord("a") + i)
                rn = str(i + 1 if self.flipped else 8 - i)
                p.drawText(QRectF(m + i * sz + sz / 2 - sz / 2, t - m, sz, m), Qt.AlignCenter, fl)
                p.drawText(QRectF(0, m + i * sz, m, sz), Qt.AlignCenter, rn)
        ats = self.anim_move.to_square if self.anim_move else None
        rts = self.anim_rook_move[1] if self.anim_rook_move else None
        for s in chess.SQUARES:
            pc = self.board.piece_at(s)
            if pc:
                if self.anim_move and s == ats:
                    continue
                if self.anim_rook_move and s == rts:
                    continue
                self._draw_piece(p, pc, self._sq_rect(s, t, m, sz), sz)
        if self.anim_move:
            pc = self.board.piece_at(self.anim_move.to_square)
            if pc:
                pr = self.anim_progress
                lift = 4.0 * pr * (1.0 - pr) * 0.18
                scale = 1.0 + 4.0 * pr * (1.0 - pr) * 0.1
                rf = self._sq_rect(self.anim_move.from_square, t, m, sz)
                rt = self._sq_rect(self.anim_move.to_square, t, m, sz)
                x = rf.x() + (rt.x() - rf.x()) * pr
                y = rf.y() + (rt.y() - rf.y()) * pr - (sz * lift)
                w, h = sz * scale, sz * scale
                p.setPen(Qt.NoPen)
                so = 30 + int(70 * (lift / 0.18)) if lift > 0 else 30
                p.setBrush(QColor(0, 0, 0, so))
                sy = rf.y() + (rt.y() - rf.y()) * pr + sz * 0.85
                p.drawEllipse(QRectF(x + (w - sz * 0.7) / 2, sy, sz * 0.7, sz * 0.15))
                self._draw_piece(p, pc, QRectF(x, y, w, h), sz * scale)
        if self.anim_rook_move:
            rfs, rts_val = self.anim_rook_move
            pc = self.board.piece_at(rts_val)
            if pc:
                pr = self.anim_progress
                lift = 4.0 * pr * (1.0 - pr) * 0.12
                scale = 1.0 + 4.0 * pr * (1.0 - pr) * 0.06
                rf = self._sq_rect(rfs, t, m, sz)
                rt = self._sq_rect(rts_val, t, m, sz)
                x = rf.x() + (rt.x() - rf.x()) * pr
                y = rf.y() + (rt.y() - rf.y()) * pr - (sz * lift)
                w, h = sz * scale, sz * scale
                p.setPen(Qt.NoPen)
                shadow_a = 30 + int(50 * (lift / 0.12)) if lift > 0 else 30
                p.setBrush(QColor(0, 0, 0, shadow_a))
                sy = rf.y() + (rt.y() - rf.y()) * pr + sz * 0.85
                p.drawEllipse(QRectF(x + (w - sz * 0.7) / 2, sy, sz * 0.7, sz * 0.15))
                self._draw_piece(p, pc, QRectF(x, y, w, h), sz * scale)
        if self.last_move and self.move_quality in MQ_SHOW_BADGE:
            self._draw_quality_badge(p, self.last_move.to_square, t, m, sz)

    def _draw_square_glow(self, p, sq, t, m, sz):
        rect = self._sq_rect(sq, t, m, sz)
        glow_color = MQ_SQUARE_GLOW_COLORS.get(self.move_quality, QColor(150, 150, 150))
        glow_extent = sz * 0.35
        rg = QRadialGradient(rect.center(), glow_extent + sz * 0.5)
        c = glow_color
        rg.setColorAt(0.0, QColor(c.red(), c.green(), c.blue(), 120))
        rg.setColorAt(0.4, QColor(c.red(), c.green(), c.blue(), 60))
        rg.setColorAt(0.7, QColor(c.red(), c.green(), c.blue(), 20))
        rg.setColorAt(1.0, QColor(c.red(), c.green(), c.blue(), 0))
        p.setPen(Qt.NoPen)
        p.setBrush(rg)
        outer = rect.adjusted(-glow_extent, -glow_extent, glow_extent, glow_extent)
        p.drawRoundedRect(outer, 8, 8)

    def _draw_square_quality_overlay(self, p, sq, t, m, sz):
        rect = self._sq_rect(sq, t, m, sz)
        glow_color = MQ_SQUARE_GLOW_COLORS.get(self.move_quality, QColor(150, 150, 150))
        c = glow_color
        border_w = max(3, sz * 0.04)
        p.setPen(QPen(QColor(c.red(), c.green(), c.blue(), 200), border_w))
        p.setBrush(Qt.NoBrush)
        p.drawRect(rect.adjusted(border_w / 2, border_w / 2, -border_w / 2, -border_w / 2))

    def _draw_quality_badge(self, p, sq, t, m, sz):
        rect = self._sq_rect(sq, t, m, sz)
        quality = self.move_quality
        color = MQ_COLORS.get(quality, QColor(150, 150, 150))
        icon = MQ_ICONS.get(quality, "")
        r = sz * 0.26
        cx = rect.right() - r - sz * 0.04
        cy = rect.top() + r + sz * 0.04
        center = QPointF(cx, cy)
        if quality == MQ_BRILLIANT:
            for radius_mult, alpha in [(5.0, 50), (3.5, 80), (2.5, 110)]:
                glow = QRadialGradient(center, r * radius_mult)
                glow.setColorAt(0.0, QColor(color.red(), color.green(), color.blue(), alpha))
                glow.setColorAt(0.5, QColor(color.red(), color.green(), color.blue(), alpha // 3))
                glow.setColorAt(1.0, QColor(color.red(), color.green(), color.blue(), 0))
                p.setPen(Qt.NoPen)
                p.setBrush(glow)
                p.drawEllipse(QRectF(cx - r * radius_mult, cy - r * radius_mult, r * 2 * radius_mult, r * 2 * radius_mult))
        elif quality == MQ_BLUNDER:
            for radius_mult, alpha in [(5.0, 60), (3.5, 90), (2.5, 120)]:
                glow = QRadialGradient(center, r * radius_mult)
                glow.setColorAt(0.0, QColor(color.red(), color.green(), color.blue(), alpha))
                glow.setColorAt(0.5, QColor(color.red(), color.green(), color.blue(), alpha // 3))
                glow.setColorAt(1.0, QColor(color.red(), color.green(), color.blue(), 0))
                p.setPen(Qt.NoPen)
                p.setBrush(glow)
                p.drawEllipse(QRectF(cx - r * radius_mult, cy - r * radius_mult, r * 2 * radius_mult, r * 2 * radius_mult))
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(0, 0, 0, 90))
        p.drawEllipse(QRectF(cx - r + 1.5, cy - r + 2, 2 * r, 2 * r))
        outer_r = r + max(2, sz * 0.025)
        p.setBrush(Qt.NoBrush)
        p.setPen(QPen(QColor(color.red(), color.green(), color.blue(), 100), max(1, sz * 0.012)))
        p.drawEllipse(QRectF(cx - outer_r, cy - outer_r, 2 * outer_r, 2 * outer_r))
        bg_grad = QRadialGradient(QPointF(cx - r * 0.3, cy - r * 0.3), r * 1.5)
        bg_grad.setColorAt(0.0, color.lighter(130))
        bg_grad.setColorAt(1.0, color)
        p.setPen(Qt.NoPen)
        p.setBrush(bg_grad)
        p.drawEllipse(QRectF(cx - r, cy - r, 2 * r, 2 * r))
        p.setPen(self._pen_badge_outline)
        p.setBrush(Qt.NoBrush)
        p.drawEllipse(QRectF(cx - r, cy - r, 2 * r, 2 * r))
        if icon:
            if icon in ("★", "✕"):
                p.setFont(self._font_badge_symbol)
            else:
                p.setFont(self._font_badge_normal)
            p.setPen(QColor(0, 0, 0, 80))
            p.drawText(QRectF(cx - r + 1, cy - r + 1, 2 * r, 2 * r), Qt.AlignCenter, icon)
            p.setPen(QColor(255, 255, 255))
            p.drawText(QRectF(cx - r, cy - r, 2 * r, 2 * r), Qt.AlignCenter, icon)

    def _draw_piece(self, p, piece, rect, sz):
        sym = PIECE_SYM.get((piece.piece_type, piece.color), "?")
        p.setFont(self._font_piece)
        if piece.color == chess.WHITE:
            p.setPen(self._pen_white_shadow)
            p.drawText(rect.adjusted(0, sz * 0.02, 0, sz * 0.02), Qt.AlignCenter, sym)
            p.setPen(self._pen_white_outline)
            p.drawText(rect, Qt.AlignCenter, sym)
            p.setPen(QColor(255, 255, 255))
            p.drawText(rect, Qt.AlignCenter, sym)
        else:
            p.setPen(self._pen_black_shadow)
            p.drawText(rect.adjusted(0, sz * 0.02, 0, sz * 0.02), Qt.AlignCenter, sym)
            p.setPen(QColor(30, 30, 30))
            p.drawText(rect, Qt.AlignCenter, sym)


# ════════════════════════════════════════════════════════════════════
#  MOVE LIST RENDERER
# ════════════════════════════════════════════════════════════════════

def render_movelist_2col(p, mx, my, mw, mh, move_list_text, current_move_index, move_qualities=None):
    if mw < 160 or mh < 80:
        return
    qualities = move_qualities or [MQ_GOOD] * len(move_list_text)
    p.setPen(QPen(QColor(48, 48, 56), 1.0))
    p.setBrush(QColor(22, 22, 26))
    p.drawRoundedRect(QRectF(mx, my, mw, mh), 8, 8)
    hh = 34
    hr = QRectF(mx + 1, my + 1, mw - 2, hh)
    hg = QLinearGradient(hr.topLeft(), hr.bottomLeft())
    hg.setColorAt(0.0, QColor(48, 48, 56))
    hg.setColorAt(1.0, QColor(38, 38, 44))
    p.setPen(Qt.NoPen)
    p.setBrush(hg)
    cr = 7
    hp = QPainterPath()
    hp.moveTo(hr.left(), hr.bottom())
    hp.lineTo(hr.left(), hr.top() + cr)
    hp.quadTo(hr.left(), hr.top(), hr.left() + cr, hr.top())
    hp.lineTo(hr.right() - cr, hr.top())
    hp.quadTo(hr.right(), hr.top(), hr.right(), hr.top() + cr)
    hp.lineTo(hr.right(), hr.bottom())
    hp.closeSubpath()
    p.drawPath(hp)
    p.setFont(QFont("Inter", 10, QFont.Bold))
    p.setPen(QColor(165, 170, 185))
    p.drawText(QRectF(mx + 14, my + 1, mw - 28, hh), Qt.AlignVCenter | Qt.AlignLeft, "♟  MOVES")
    p.setPen(QPen(QColor(58, 58, 68), 0.8))
    p.drawLine(QPointF(mx + 8, my + hh + 1), QPointF(mx + mw - 8, my + hh + 1))
    pairs = []
    i = 0
    while i < len(move_list_text):
        num = i // 2 + 1
        wm = move_list_text[i]
        bm = move_list_text[i + 1] if i + 1 < len(move_list_text) else None
        wq = qualities[i] if i < len(qualities) else MQ_GOOD
        bq = qualities[i + 1] if i + 1 < len(qualities) else MQ_GOOD
        pairs.append((num, wm, bm, i, i + 1 if bm is not None else -1, wq, bq))
        i += 2
    if not pairs:
        p.setFont(QFont("Inter", 9))
        p.setPen(QColor(85, 85, 105))
        p.drawText(QRectF(mx, my + hh, mw, mh - hh), Qt.AlignCenter, "No moves yet")
        return
    pad_x, pad_top = 10, 6
    line_h = 26
    content_y = my + hh + pad_top
    content_h = mh - hh - pad_top * 2
    rows_avail = max(1, int(content_h / line_h))
    num_cols = 1
    ppc = math.ceil(len(pairs) / num_cols)
    col_w = mw - pad_x * 2
    start_pair = 0
    if current_move_index >= 0:
        cp = current_move_index // 2
        if cp >= rows_avail:
            start_pair = max(0, min(cp - rows_avail + 2, len(pairs) - rows_avail))
    for ci in range(num_cols):
        cx = mx + pad_x + ci * col_w
        start = ci * ppc + start_pair
        end = min(start + ppc, len(pairs))
        end = min(end, start_pair + rows_avail)
        num_w = 30
        move_w = max(20, (col_w - num_w - 12) / 2)
        w_x = cx + num_w + 4
        b_x = w_x + move_w + 4
        for row in range(end - start):
            pidx = start + row
            if pidx >= len(pairs):
                break
            num, wm, bm, widx, bidx, wq, bq = pairs[pidx]
            ry = content_y + row * line_h
            if row % 2 == 0:
                p.setPen(Qt.NoPen)
                p.setBrush(QColor(30, 30, 38, 100))
                p.drawRoundedRect(QRectF(cx - 2, ry, col_w + 4, line_h - 1), 3, 3)
            is_cur_row = (widx == current_move_index or bidx == current_move_index)
            if is_cur_row:
                p.setPen(Qt.NoPen)
                p.setBrush(QColor(38, 95, 190, 45))
                p.drawRoundedRect(QRectF(cx - 2, ry, col_w + 4, line_h - 1), 3, 3)
            p.setFont(QFont("Consolas", 9))
            p.setPen(QColor(80, 80, 100))
            p.drawText(QRectF(cx, ry, num_w, line_h - 1), Qt.AlignVCenter | Qt.AlignRight, f"{num}.")
            _draw_move_cell(p, w_x, ry, move_w, line_h, wm, wq, widx == current_move_index)
            if bm is not None:
                _draw_move_cell(p, b_x, ry, move_w, line_h, bm, bq, bidx == current_move_index)

def _draw_move_cell(p, x, y, w, h, san, quality, is_current):
    sym = MQ_SYMBOLS.get(quality, "")
    show_pill = quality in MQ_SHOW_MOVES_BADGE and sym
    show_dot = (quality not in MQ_SHOW_MOVES_BADGE and quality in MQ_BG_COLORS and MQ_BG_COLORS.get(quality, QColor(0, 0, 0, 0)).alpha() > 0)
    badge_w = 30 if show_pill else (12 if show_dot else 0)
    bg = MQ_BG_COLORS.get(quality, QColor(0, 0, 0, 0))
    if bg.alpha() > 0:
        p.setPen(Qt.NoPen)
        p.setBrush(bg)
        p.drawRoundedRect(QRectF(x - 2, y + 2, w + 4, h - 5), 3, 3)
    if is_current:
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(42, 110, 210, 70))
        p.drawRoundedRect(QRectF(x - 3, y + 2, w + 6, h - 5), 4, 4)
    p.setFont(QFont("Consolas", 11, QFont.Bold if is_current else QFont.Normal))
    p.setPen(QColor(82, 160, 245) if is_current else QColor(208, 210, 220))
    p.drawText(QRectF(x, y, w - badge_w, h - 1), Qt.AlignVCenter | Qt.AlignLeft, san)
    if show_pill:
        bx = x + w - badge_w
        color = MQ_COLORS.get(quality, QColor(150, 150, 150))
        pill = QRectF(bx + 2, y + (h - 16) / 2, badge_w - 4, 16)
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(0, 0, 0, 50))
        p.drawRoundedRect(pill.adjusted(0.5, 1, 0.5, 1), 8, 8)
        p.setBrush(color)
        p.drawRoundedRect(pill, 8, 8)
        p.setPen(QPen(QColor(255, 255, 255, 60), 0.6))
        p.setBrush(Qt.NoBrush)
        p.drawRoundedRect(pill, 8, 8)
        if sym in ("★", "✕"):
            fnt = QFont("Segoe UI Symbol", max(7, int(16 * 0.6)), QFont.Bold)
        else:
            fnt = QFont("Inter", max(7, int(16 * 0.55)), QFont.Bold)
        p.setFont(fnt)
        p.setPen(QColor(255, 255, 255))
        p.drawText(pill, Qt.AlignCenter, sym)
    elif show_dot:
        dot_r = 3
        dot_x = x + w - badge_w + 4
        dot_y = y + h / 2
        dot_color = MQ_COLORS.get(quality, QColor(150, 150, 150))
        p.setPen(Qt.NoPen)
        p.setBrush(dot_color)
        p.drawEllipse(QRectF(dot_x - dot_r, dot_y - dot_r, dot_r * 2, dot_r * 2))


# ════════════════════════════════════════════════════════════════════
#  SOUND ENGINE
# ════════════════════════════════════════════════════════════════════

class SoundEngine(QObject):
    sound_played = Signal(str)

    def __init__(self, parent=None):
        super().__init__(parent)
        self._theme_name = "Classic"
        self._volume = 0.70
        self._muted = False
        self._enabled = True
        self._effects = {}
        self._sound_files = {}
        self._temp_dir = tempfile.mkdtemp(prefix="chess_snd_")
        self._sr = 44100
        if not HAS_NUMPY or not HAS_QTMULTIMEDIA:
            self._enabled = False
            return
        try:
            self._generate_all_themes()
            self._apply_theme(self._theme_name)
            atexit.register(self.cleanup)
        except Exception as e:
            logger.warning(f"Sound engine init failed: {e}")
            self._enabled = False

    def play(self, event):
        if not self._enabled or self._muted:
            return
        fx = self._effects.get(event)
        if fx:
            if fx.isPlaying():
                fx.stop()
            fx.play()
            self.sound_played.emit(event)

    def play_move_sound(self, board, move):
        if not self._enabled or self._muted:
            return
        piece = board.piece_at(move.from_square)
        is_cap = board.is_capture(move)
        is_castle = (piece and piece.piece_type == chess.KING and abs(chess.square_file(move.from_square) - chess.square_file(move.to_square)) == 2)
        gives_check = board.gives_check(move)
        board.push(move)
        is_mate = board.is_checkmate()
        is_stale = board.is_stalemate()
        is_draw = board.is_game_over() and not is_mate and not is_stale
        board.pop()
        if is_mate:       self.play(SND_CHECKMATE)
        elif is_stale:    self.play(SND_STALEMATE)
        elif is_draw:     self.play(SND_DRAW)
        elif gives_check: self.play(SND_CHECK)
        elif is_castle:   self.play(SND_CASTLE)
        elif is_cap:      self.play(SND_CAPTURE)
        else:             self.play(SND_MOVE)

    def play_game_end(self, result_type):
        m = {"checkmate": SND_CHECKMATE, "stalemate": SND_STALEMATE, "draw": SND_DRAW}
        self.play(m.get(result_type, SND_DRAW))

    def set_theme(self, name):
        if name == self._theme_name or not self._enabled:
            return
        self._theme_name = name
        self._apply_theme(name)

    def set_volume(self, vol):
        self._volume = max(0.0, min(1.0, vol))
        for fx in self._effects.values():
            fx.setVolume(self._volume)

    def set_muted(self, m):
        self._muted = m

    @property
    def enabled(self): return self._enabled
    @property
    def theme(self): return self._theme_name
    @property
    def volume(self): return self._volume
    @property
    def muted(self): return self._muted
    @property
    def available_themes(self): return SOUND_THEME_LIST if self._enabled else []

    def get_sound_path(self, event, theme=None):
        if not self._enabled:
            return None
        t = theme or self._theme_name
        return self._sound_files.get(t, {}).get(event)

    def cleanup(self):
        try:
            shutil.rmtree(self._temp_dir, ignore_errors=True)
        except Exception:
            pass

    def _apply_theme(self, name):
        if name not in self._sound_files:
            return
        for fx in self._effects.values():
            if fx.isPlaying():
                fx.stop()
        self._effects.clear()
        for event, fp in self._sound_files[name].items():
            fx = QSoundEffect(self)
            fx.setSource(QUrl.fromLocalFile(os.path.abspath(fp)))
            fx.setVolume(self._volume)
            self._effects[event] = fx

    def _generate_all_themes(self):
        gens = {"Classic": self._gen_classic, "Digital": self._gen_digital,
                "Cinematic": self._gen_cinematic, "Retro": self._gen_retro,
                "Ambient": self._gen_ambient}
        for tn, gen in gens.items():
            try:
                samples = gen()
                self._sound_files[tn] = {}
                for event, arr in samples.items():
                    fp = self._write_wav(f"{tn.lower()}_{event}.wav", arr)
                    self._sound_files[tn][event] = fp
                logger.info("Sound theme '%s' generated (%d sounds)", tn, len(samples))
            except Exception as e:
                logger.warning("Theme '%s' failed: %s", tn, e)

    def _write_wav(self, fn, s16):
        fp = os.path.join(self._temp_dir, fn)
        with wave.open(fp, "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(self._sr)
            wf.writeframes(s16.tobytes())
        return fp

    @staticmethod
    def _to_int16(a):
        a = np.clip(a, -1.0, 1.0)
        return (a * 32767).astype(np.int16)

    def _gen_classic(self):
        sr = self._sr; s = {}
        t = np.linspace(0, .08, int(sr * .08), False); e = np.exp(-t * 60)
        s[SND_MOVE] = self._to_int16((np.random.randn(len(t)) * .3 * e + np.sin(2 * np.pi * 800 * t) * e * .2) * .5)
        t = np.linspace(0, .12, int(sr * .12), False); e = np.exp(-t * 40)
        s[SND_CAPTURE] = self._to_int16((np.random.randn(len(t)) * .5 * e + np.sin(2 * np.pi * 400 * t) * e * .4) * .6)
        t = np.linspace(0, .2, int(sr * .2), False); e = np.exp(-t * 15)
        s[SND_CHECK] = self._to_int16((np.sin(2 * np.pi * 1200 * t) * e * .4 + np.sin(2 * np.pi * 900 * t) * e * .3) * .5)
        t1 = np.linspace(0, .06, int(sr * .06), False); g = np.zeros(int(sr * .04)); t2 = np.linspace(0, .06, int(sr * .06), False)
        s[SND_CASTLE] = self._to_int16(np.concatenate([np.random.randn(len(t1)) * np.exp(-t1 * 50) * .3, g, np.random.randn(len(t2)) * np.exp(-t2 * 50) * .3]) * .5)
        t = np.linspace(0, .6, int(sr * .6), False); e = np.exp(-t * 4)
        s[SND_CHECKMATE] = self._to_int16((np.sin(2 * np.pi * 523 * t) * e * .2 + np.sin(2 * np.pi * 659 * t) * e * .2 + np.sin(2 * np.pi * 784 * t) * e * .2) * .5)
        t = np.linspace(0, .3, int(sr * .3), False); e = np.exp(-t * 8)
        s[SND_STALEMATE] = self._to_int16(np.sin(2 * np.pi * 440 * t) * e * .3); s[SND_DRAW] = s[SND_STALEMATE]
        t = np.linspace(0, .4, int(sr * .4), False); e = np.exp(-t * 6)
        s[SND_GAME_START] = self._to_int16((np.sin(2 * np.pi * 660 * t) * e * .25 + np.sin(2 * np.pi * 880 * t) * e * .15) * .5)
        t = np.linspace(0, .03, int(sr * .03), False); e = np.exp(-t * 100)
        s[SND_UI_CLICK] = self._to_int16(np.sin(2 * np.pi * 1000 * t) * e * .2)
        return s

    def _gen_digital(self):
        sr = self._sr; s = {}
        t = np.linspace(0, .06, int(sr * .06), False); e = np.exp(-t * 50)
        s[SND_MOVE] = self._to_int16(np.sin(2 * np.pi * 1000 * t) * e * .4)
        t = np.linspace(0, .08, int(sr * .08), False); e = np.exp(-t * 35)
        s[SND_CAPTURE] = self._to_int16(np.sin(2 * np.pi * 600 * t) * e * .5)
        t1 = np.linspace(0, .04, int(sr * .04), False); g = np.zeros(int(sr * .02)); t2 = np.linspace(0, .04, int(sr * .04), False)
        s[SND_CHECK] = self._to_int16(np.concatenate([np.sin(2 * np.pi * 1400 * t1) * np.exp(-t1 * 40) * .4, g, np.sin(2 * np.pi * 1400 * t2) * np.exp(-t2 * 40) * .4]) * .5)
        t = np.linspace(0, .1, int(sr * .1), False); e = np.exp(-t * 25)
        s[SND_CASTLE] = self._to_int16((np.sin(2 * np.pi * 800 * t) + np.sin(2 * np.pi * 1200 * t)) * e * .2)
        t = np.linspace(0, .5, int(sr * .5), False); e = np.exp(-t * 5); f = 1200 - 800 * t / .5
        s[SND_CHECKMATE] = self._to_int16(np.sin(2 * np.pi * f * t) * e * .4)
        t = np.linspace(0, .2, int(sr * .2), False); e = np.exp(-t * 12)
        s[SND_STALEMATE] = self._to_int16(np.sin(2 * np.pi * 500 * t) * e * .3); s[SND_DRAW] = s[SND_STALEMATE]
        t = np.linspace(0, .15, int(sr * .15), False); e = np.exp(-t * 15)
        s[SND_GAME_START] = self._to_int16((np.sin(2 * np.pi * 800 * t) * e * .3 + np.sin(2 * np.pi * 1200 * t) * e * .2) * .5)
        t = np.linspace(0, .02, int(sr * .02), False); e = np.exp(-t * 120)
        s[SND_UI_CLICK] = self._to_int16(np.sin(2 * np.pi * 1500 * t) * e * .2)
        return s

    def _gen_cinematic(self):
        sr = self._sr; s = {}
        t = np.linspace(0, .15, int(sr * .15), False); e = np.exp(-t * 25)
        s[SND_MOVE] = self._to_int16((np.sin(2 * np.pi * 150 * t) * e * .4 + np.random.randn(len(t)) * e * .15) * .6)
        t = np.linspace(0, .2, int(sr * .2), False); e = np.exp(-t * 18)
        s[SND_CAPTURE] = self._to_int16((np.sin(2 * np.pi * 100 * t) * e * .5 + np.sin(2 * np.pi * 200 * t) * e * .3 + np.random.randn(len(t)) * e * .2) * .6)
        t = np.linspace(0, .25, int(sr * .25), False); e = np.exp(-t * 12)
        s[SND_CHECK] = self._to_int16((np.sin(2 * np.pi * 880 * t) * e * .3 + np.sin(2 * np.pi * 1320 * t) * e * .2) * .5)
        t = np.linspace(0, .18, int(sr * .18), False); e = np.exp(-t * 20)
        s[SND_CASTLE] = self._to_int16((np.sin(2 * np.pi * 180 * t) * e * .35 + np.random.randn(len(t)) * e * .15) * .55)
        t = np.linspace(0, 1., int(sr * 1.), False); e = np.exp(-t * 2.5)
        s[SND_CHECKMATE] = self._to_int16((np.sin(2 * np.pi * 261 * t) * e * .15 + np.sin(2 * np.pi * 329 * t) * e * .15 + np.sin(2 * np.pi * 392 * t) * e * .15 + np.sin(2 * np.pi * 523 * t) * e * .1) * .6)
        t = np.linspace(0, .5, int(sr * .5), False); e = np.exp(-t * 5)
        s[SND_STALEMATE] = self._to_int16(np.sin(2 * np.pi * 330 * t) * e * .25); s[SND_DRAW] = s[SND_STALEMATE]
        t = np.linspace(0, .6, int(sr * .6), False); e = np.exp(-t * 3)
        s[SND_GAME_START] = self._to_int16((np.sin(2 * np.pi * 220 * t) * e * .2 + np.sin(2 * np.pi * 440 * t) * e * .15) * .5)
        t = np.linspace(0, .04, int(sr * .04), False); e = np.exp(-t * 60)
        s[SND_UI_CLICK] = self._to_int16(np.sin(2 * np.pi * 600 * t) * e * .15)
        return s

    def _gen_retro(self):
        sr = self._sr; s = {}
        t = np.linspace(0, .05, int(sr * .05), False); e = (t < .025).astype(float) * .8 + .2
        s[SND_MOVE] = self._to_int16(np.sign(np.sin(2 * np.pi * 800 * t)) * e * .3)
        t = np.linspace(0, .08, int(sr * .08), False); e = np.exp(-t * 40)
        s[SND_CAPTURE] = self._to_int16(np.sign(np.random.randn(len(t))) * e * .3)
        t = np.linspace(0, .1, int(sr * .1), False); e = np.exp(-t * 25)
        s[SND_CHECK] = self._to_int16(np.sign(np.sin(2 * np.pi * 1200 * t)) * e * .35)
        t = np.linspace(0, .07, int(sr * .07), False); e = np.exp(-t * 30)
        s[SND_CASTLE] = self._to_int16(np.sign(np.sin(2 * np.pi * 500 * t)) * e * .3)
        pts = []
        for f in [523, 659, 784, 1047]:
            t = np.linspace(0, .12, int(sr * .12), False); e = np.exp(-t * 12)
            pts.append(np.sign(np.sin(2 * np.pi * f * t)) * e * .25)
        s[SND_CHECKMATE] = self._to_int16(np.concatenate(pts) * .5)
        t = np.linspace(0, .15, int(sr * .15), False); e = np.exp(-t * 15)
        s[SND_STALEMATE] = self._to_int16(np.sign(np.sin(2 * np.pi * 350 * t)) * e * .25); s[SND_DRAW] = s[SND_STALEMATE]
        t = np.linspace(0, .2, int(sr * .2), False); e = np.exp(-t * 10)
        s[SND_GAME_START] = self._to_int16(np.sign(np.sin(2 * np.pi * 660 * t)) * e * .25)
        t = np.linspace(0, .02, int(sr * .02), False)
        s[SND_UI_CLICK] = self._to_int16(np.sign(np.sin(2 * np.pi * 2000 * t)) * .15)
        return s

    def _gen_ambient(self):
        sr = self._sr; s = {}
        t = np.linspace(0, .3, int(sr * .3), False); e = np.exp(-t * 8)
        s[SND_MOVE] = self._to_int16((np.sin(2 * np.pi * 440 * t) * e * .15 + np.sin(2 * np.pi * 442 * t) * e * .15) * .5)
        t = np.linspace(0, .4, int(sr * .4), False); e = np.exp(-t * 6)
        s[SND_CAPTURE] = self._to_int16((np.sin(2 * np.pi * 330 * t) * e * .2 + np.sin(2 * np.pi * 332 * t) * e * .2) * .5)
        t = np.linspace(0, .35, int(sr * .35), False); e = np.exp(-t * 7)
        s[SND_CHECK] = self._to_int16((np.sin(2 * np.pi * 660 * t) * e * .2 + np.sin(2 * np.pi * 662 * t) * e * .2) * .5)
        t = np.linspace(0, .35, int(sr * .35), False); e = np.exp(-t * 6)
        s[SND_CASTLE] = self._to_int16((np.sin(2 * np.pi * 392 * t) * e * .18 + np.sin(2 * np.pi * 394 * t) * e * .18) * .5)
        t = np.linspace(0, 1.2, int(sr * 1.2), False); e = np.exp(-t * 1.8)
        s[SND_CHECKMATE] = self._to_int16((np.sin(2 * np.pi * 261 * t) * e * .1 + np.sin(2 * np.pi * 261.5 * t) * e * .1 + np.sin(2 * np.pi * 329 * t) * e * .1 + np.sin(2 * np.pi * 329.5 * t) * e * .1 + np.sin(2 * np.pi * 392 * t) * e * .08) * .6)
        t = np.linspace(0, .6, int(sr * .6), False); e = np.exp(-t * 3)
        s[SND_STALEMATE] = self._to_int16((np.sin(2 * np.pi * 350 * t) * e * .15 + np.sin(2 * np.pi * 352 * t) * e * .15) * .4); s[SND_DRAW] = s[SND_STALEMATE]
        t = np.linspace(0, .8, int(sr * .8), False); e = np.exp(-t * 2.5)
        s[SND_GAME_START] = self._to_int16((np.sin(2 * np.pi * 440 * t) * e * .12 + np.sin(2 * np.pi * 442 * t) * e * .12 + np.sin(2 * np.pi * 550 * t) * e * .08) * .5)
        t = np.linspace(0, .05, int(sr * .05), False); e = np.exp(-t * 40)
        s[SND_UI_CLICK] = self._to_int16(np.sin(2 * np.pi * 700 * t) * e * .1)
        return s


# ════════════════════════════════════════════════════════════════════
#  VIDEO RENDERER
# ════════════════════════════════════════════════════════════════════

class VideoRenderer:
    def __init__(self, board_renderer, w=1920, h=1080, bg_color=QColor(28, 28, 30)):
        self.board_renderer = board_renderer
        self.w, self.h = w, h
        self.bg_color = bg_color
        self.eval_cp = 0.0
        self.eval_history = []
        self.move_qualities = []
        self.move_text = ""
        self.white_name = "White"
        self.black_name = "Black"
        self.white_engine_info = ""
        self.black_engine_info = ""
        self.overlays = []
        self.move_list_text = []
        self.current_move_index = 0
        self.game_state = GAME_NORMAL
        self.game_result = ""
        self.game_detail = ""

    @staticmethod
    def _cp2r(cp):
        if cp >= 9000: return 1.0
        if cp <= -9000: return 0.0
        return 1.0 / (1.0 + math.exp(-0.004 * max(-10000, min(10000, cp))))

    def render(self):
        img = QImage(self.w, self.h, QImage.Format_ARGB32)
        bg = QLinearGradient(0, 0, 0, self.h)
        bg.setColorAt(0.0, QColor(30, 30, 34))
        bg.setColorAt(1.0, QColor(22, 22, 26))
        img.fill(QColor(0, 0, 0, 0))
        p = QPainter(img)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.TextAntialiasing)
        p.fillRect(QRectF(0, 0, self.w, self.h), bg)
        if self.h > self.w:
            self._render_portrait(p)
        else:
            self._render_landscape(p)
        for ov in self.overlays:
            if os.path.exists(ov["path"]):
                oi = QImage(ov["path"])
                if not oi.isNull():
                    p.drawImage(QRectF(ov["x"], ov["y"], ov["w"], ov["h"]), oi)
        p.end()
        return img

    def render_title_screen(self):
        img = QImage(self.w, self.h, QImage.Format_ARGB32)
        bg = QLinearGradient(0, 0, 0, self.h)
        bg.setColorAt(0.0, QColor(26, 26, 30))
        bg.setColorAt(0.5, QColor(30, 30, 36))
        bg.setColorAt(1.0, QColor(22, 22, 26))
        img.fill(QColor(0, 0, 0, 0))
        p = QPainter(img)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.TextAntialiasing)
        p.fillRect(QRectF(0, 0, self.w, self.h), bg)
        cx, cy = self.w / 2, self.h / 2
        if self.h > self.w:
            self._render_title_portrait(p, cx, cy)
        else:
            self._render_title_landscape(p, cx, cy)
        p.end()
        return img

    def _render_title_landscape(self, p, cx, cy):
        bsz = int(min(self.w * 0.35, self.h * 0.6))
        bx = cx - bsz / 2; by = cy - bsz / 2 - 10
        p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 100))
        p.drawRoundedRect(QRectF(bx - 15, by - 15, bsz + 30, bsz + 30), 12, 12)
        bimg = self.board_renderer.render(bsz)
        p.setOpacity(0.25); p.drawImage(QRectF(bx, by, bsz, bsz), bimg); p.setOpacity(1.0)
        card_w = min(340, max(120, (self.w - bsz) / 2 - 60)); card_h = 120
        left_cx = max(10, (bx - card_w) / 2)
        self._draw_player_card(p, left_cx, cy - card_h / 2, card_w, card_h, self.white_name, self.white_engine_info, True)
        right_cx = min(self.w - card_w - 10, bx + bsz + (self.w - bx - bsz - card_w) / 2)
        self._draw_player_card(p, right_cx, cy - card_h / 2, card_w, card_h, self.black_name, self.black_engine_info, False)
        vs_r = 48
        p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 80))
        p.drawEllipse(QRectF(cx - vs_r + 2, cy - vs_r + 2, vs_r * 2, vs_r * 2))
        vs_grad = QLinearGradient(cx, cy - vs_r, cx, cy + vs_r)
        vs_grad.setColorAt(0.0, QColor(60, 120, 210)); vs_grad.setColorAt(1.0, QColor(40, 90, 170))
        p.setBrush(vs_grad); p.drawEllipse(QRectF(cx - vs_r, cy - vs_r, vs_r * 2, vs_r * 2))
        p.setPen(QPen(QColor(255, 255, 255, 50), 1.5)); p.setBrush(Qt.NoBrush)
        p.drawEllipse(QRectF(cx - vs_r, cy - vs_r, vs_r * 2, vs_r * 2))
        p.setFont(QFont("Inter", 28, QFont.Bold)); p.setPen(QColor(255, 255, 255))
        p.drawText(QRectF(cx - vs_r, cy - vs_r, vs_r * 2, vs_r * 2), Qt.AlignCenter, "VS")
        p.setFont(QFont("Inter", 11)); p.setPen(QColor(120, 120, 140))
        sub_y = by + bsz + 40
        p.drawText(QRectF(0, sub_y, self.w, 30), Qt.AlignHCenter | Qt.AlignTop, "AI vs AI  ·  Chess Battle")

    def _render_title_portrait(self, p, cx, cy):
        bsz = int(self.w * 0.5); bx = cx - bsz / 2; by = cy - bsz / 2 + 30
        p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 100))
        p.drawRoundedRect(QRectF(bx - 12, by - 12, bsz + 24, bsz + 24), 10, 10)
        bimg = self.board_renderer.render(bsz)
        p.setOpacity(0.25); p.drawImage(QRectF(bx, by, bsz, bsz), bimg); p.setOpacity(1.0)
        card_w = min(300, self.w - 60); card_h = 80
        self._draw_player_card(p, (self.w - card_w) / 2, by - card_h - 30, card_w, card_h, self.white_name, self.white_engine_info, True)
        self._draw_player_card(p, (self.w - card_w) / 2, by + bsz + 30, card_w, card_h, self.black_name, self.black_engine_info, False)
        vs_r = 36
        p.setPen(Qt.NoPen)
        vs_grad = QLinearGradient(cx, cy - vs_r, cx, cy + vs_r)
        vs_grad.setColorAt(0.0, QColor(60, 120, 210)); vs_grad.setColorAt(1.0, QColor(40, 90, 170))
        p.setBrush(vs_grad); p.drawEllipse(QRectF(cx - vs_r, cy - vs_r, vs_r * 2, vs_r * 2))
        p.setFont(QFont("Inter", 22, QFont.Bold)); p.setPen(QColor(255, 255, 255))
        p.drawText(QRectF(cx - vs_r, cy - vs_r, vs_r * 2, vs_r * 2), Qt.AlignCenter, "VS")

    def _draw_player_card(self, p, x, y, w, h, name, engine_info, is_white):
        p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 60))
        p.drawRoundedRect(QRectF(x + 2, y + 2, w, h), 8, 8)
        card_bg = QLinearGradient(x, y, x, y + h)
        card_bg.setColorAt(0.0, QColor(42, 42, 48)); card_bg.setColorAt(1.0, QColor(34, 34, 40))
        p.setBrush(card_bg); p.setPen(QPen(QColor(60, 60, 70), 1.0))
        p.drawRoundedRect(QRectF(x, y, w, h), 8, 8)
        icon_r = 24; icon_x = x + 18; icon_y = y + (h - icon_r * 2) / 2
        p.setPen(Qt.NoPen); p.setBrush(QColor(240, 240, 240) if is_white else QColor(50, 50, 55))
        p.drawEllipse(QRectF(icon_x, icon_y, icon_r * 2, icon_r * 2))
        p.setPen(QPen(QColor(0, 0, 0, 150), 1)); p.drawEllipse(QRectF(icon_x, icon_y, icon_r * 2, icon_r * 2))
        sym = "♔" if is_white else "♚"
        p.setFont(QFont("Segoe UI Symbol", 20, QFont.Bold))
        p.setPen(QColor(30, 30, 30) if is_white else QColor(220, 220, 220))
        p.drawText(QRectF(icon_x, icon_y, icon_r * 2, icon_r * 2), Qt.AlignCenter, sym)
        text_x = icon_x + icon_r * 2 + 14; text_w = max(40, w - 100)
        p.setPen(QColor(225, 225, 230)); p.setFont(QFont("Inter", 14, QFont.Bold))
        p.drawText(QRectF(text_x, y + 8, text_w, h / 2), Qt.AlignVCenter | Qt.AlignLeft, name)
        p.setPen(QColor(140, 140, 160)); p.setFont(QFont("Inter", 10))
        p.drawText(QRectF(text_x, y + h / 2 - 4, text_w, h / 2), Qt.AlignVCenter | Qt.AlignLeft, engine_info)

    def render_result_screen(self):
        img = self.render()
        p = QPainter(img)
        p.setRenderHint(QPainter.Antialiasing); p.setRenderHint(QPainter.TextAntialiasing)
        p.fillRect(QRectF(0, 0, self.w, self.h), QColor(0, 0, 0, 160))
        cx, cy = self.w / 2, self.h / 2
        card_w, card_h = min(600, self.w * 0.5), min(260, self.h * 0.3)
        p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 80))
        p.drawRoundedRect(QRectF(cx - card_w / 2 + 4, cy - card_h / 2 + 4, card_w, card_h), 16, 16)
        card_bg = QLinearGradient(cx, cy - card_h / 2, cx, cy + card_h / 2)
        card_bg.setColorAt(0.0, QColor(38, 38, 44)); card_bg.setColorAt(1.0, QColor(30, 30, 36))
        p.setBrush(card_bg); p.setPen(QPen(QColor(70, 70, 80), 1.5))
        p.drawRoundedRect(QRectF(cx - card_w / 2, cy - card_h / 2, card_w, card_h), 16, 16)
        if self.game_state == GAME_CHECKMATE:
            w_wins = "1-0" in self.game_result
            accent = QColor(40, 180, 70) if w_wins else QColor(200, 50, 50)
            result_txt = "CHECKMATE"; score_txt = self.game_result
        else:
            accent = QColor(180, 160, 50); result_txt = "DRAW"; score_txt = "½ - ½"
        bar_h = 5
        p.setPen(Qt.NoPen); p.setBrush(accent)
        path = QPainterPath(); r = 16
        bx1, by1 = cx - card_w / 2, cy - card_h / 2
        path.moveTo(bx1 + r, by1); path.lineTo(bx1 + card_w - r, by1)
        path.quadTo(bx1 + card_w, by1, bx1 + card_w, by1 + r)
        path.lineTo(bx1 + card_w, by1 + bar_h); path.lineTo(bx1, by1 + bar_h)
        path.lineTo(bx1, by1 + r); path.quadTo(bx1, by1, bx1 + r, by1)
        path.closeSubpath(); p.drawPath(path)
        p.setFont(QFont("Inter", 28, QFont.Bold)); p.setPen(accent)
        p.drawText(QRectF(cx - card_w / 2, cy - card_h / 2 + bar_h + 20, card_w, 50), Qt.AlignHCenter | Qt.AlignTop, result_txt)
        p.setFont(QFont("Inter", 42, QFont.Bold)); p.setPen(QColor(240, 240, 245))
        p.drawText(QRectF(cx - card_w / 2, cy - card_h / 2 + bar_h + 65, card_w, 70), Qt.AlignHCenter | Qt.AlignTop, score_txt)
        if self.game_detail:
            p.setFont(QFont("Inter", 12)); p.setPen(QColor(140, 140, 160))
            p.drawText(QRectF(cx - card_w / 2, cy - card_h / 2 + bar_h + 135, card_w, 30), Qt.AlignHCenter | Qt.AlignTop, self.game_detail)
        n = len(self.move_list_text)
        p.setFont(QFont("Inter", 10)); p.setPen(QColor(100, 100, 120))
        p.drawText(QRectF(cx - card_w / 2, cy - card_h / 2 + card_h - 40, card_w, 24), Qt.AlignHCenter | Qt.AlignTop, f"{n} moves played")
        p.end()
        return img

    def _draw_player_bar_v(self, p, x, y, w, h, name, engine_info, eval_cp, is_white):
        p.setPen(Qt.NoPen); p.setBrush(QColor(30, 30, 34))
        p.drawRoundedRect(QRectF(x, y, w, h), 6, 6)
        p.setPen(QPen(QColor(55, 55, 65), 0.8)); p.setBrush(Qt.NoBrush)
        p.drawRoundedRect(QRectF(x, y, w, h), 6, 6)
        icon_r = 18; icon_x = x + 12; icon_y = y + (h - icon_r * 2) / 2
        p.setPen(Qt.NoPen); p.setBrush(QColor(240, 240, 240) if is_white else QColor(50, 50, 55))
        p.drawEllipse(QRectF(icon_x, icon_y, icon_r * 2, icon_r * 2))
        p.setPen(QPen(QColor(0, 0, 0, 150), 1)); p.drawEllipse(QRectF(icon_x, icon_y, icon_r * 2, icon_r * 2))
        sym = "♔" if is_white else "♚"
        p.setFont(QFont("Segoe UI Symbol", 14, QFont.Bold))
        p.setPen(QColor(30, 30, 30) if is_white else QColor(210, 210, 210))
        p.drawText(QRectF(icon_x, icon_y, icon_r * 2, icon_r * 2), Qt.AlignCenter, sym)
        name_w = max(40, w - 130)
        p.setPen(QColor(220, 220, 225)); p.setFont(QFont("Inter", 12, QFont.Bold))
        p.drawText(QRectF(icon_x + icon_r * 2 + 10, y, name_w, h / 2 + 4), Qt.AlignVCenter | Qt.AlignLeft, name)
        p.setPen(QColor(140, 140, 155)); p.setFont(QFont("Inter", 9))
        p.drawText(QRectF(icon_x + icon_r * 2 + 10, y + h / 2 - 4, name_w, h / 2 + 4), Qt.AlignVCenter | Qt.AlignLeft, engine_info)
        if abs(eval_cp) > 9000:
            txt = f"M{int(abs(eval_cp) - 10000)}"
        else:
            txt = f"{eval_cp / 100.0:+.1f}"
        pill_w = 60; pill_h = 22; pill_x = x + w - pill_w - 10; pill_y = y + (h - pill_h) / 2
        if abs(eval_cp) > 9000:
            pill_bg = QColor(28, 165, 55, 200) if eval_cp > 0 else QColor(200, 45, 45, 200); pill_fg = QColor(255, 255, 255)
        elif eval_cp >= 0:
            pill_bg = QColor(245, 242, 235, 210); pill_fg = QColor(32, 30, 26)
        else:
            pill_bg = QColor(38, 38, 48, 210); pill_fg = QColor(220, 218, 210)
        p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 50))
        p.drawRoundedRect(QRectF(pill_x + 1, pill_y + 1, pill_w, pill_h), 10, 10)
        p.setBrush(pill_bg); p.drawRoundedRect(QRectF(pill_x, pill_y, pill_w, pill_h), 10, 10)
        p.setFont(QFont("Inter", 11, QFont.Bold)); p.setPen(pill_fg)
        p.drawText(QRectF(pill_x, pill_y, pill_w, pill_h), Qt.AlignCenter, txt)

    def _draw_gameover_pill_v(self, p, ebx, by, ebw, bsz):
        epx, eph = max(40, ebw + 20), 24
        if "1-0" in self.game_result:
            txt, ety = "♔ 1-0", by + eph / 2 + 10; epbg, epfg = QColor(255, 255, 255, 225), QColor(28, 28, 28)
        elif "0-1" in self.game_result:
            txt, ety = "♚ 0-1", by + bsz - eph / 2 - 10; epbg, epfg = QColor(28, 28, 28, 235), QColor(228, 228, 228)
        else:
            txt, ety = "½-½", by + bsz / 2; epbg, epfg = QColor(135, 125, 48, 235), QColor(255, 255, 255)
        epill = QRectF(ebx + (ebw - epx) / 2, ety - eph / 2, epx, eph)
        p.setFont(QFont("Inter", max(8, min(12, int(ebw * 0.3))), QFont.Bold))
        p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 45)); p.drawRoundedRect(epill.adjusted(1, 1, 1, 1), 10, 10)
        p.setBrush(epbg); p.drawRoundedRect(epill, 10, 10); p.setPen(epfg); p.drawText(epill, Qt.AlignCenter, txt)

    def _draw_gameover_pill_h(self, p, ebx, eby, ebw, ebh):
        pill_w, pill_h = max(50, ebh + 30), 24
        if "1-0" in self.game_result:
            txt, pill_x = "♔ 1-0", ebx + pill_w / 2 + 10; pbg, pfg = QColor(255, 255, 255, 225), QColor(28, 28, 28)
        elif "0-1" in self.game_result:
            txt, pill_x = "♚ 0-1", ebx + ebw - pill_w / 2 - 10; pbg, pfg = QColor(28, 28, 28, 235), QColor(228, 228, 228)
        else:
            txt, pill_x = "½-½", ebx + ebw / 2; pbg, pfg = QColor(135, 125, 48, 235), QColor(255, 255, 255)
        pill = QRectF(pill_x - pill_w / 2, eby + (ebh - pill_h) / 2, pill_w, pill_h)
        p.setFont(QFont("Inter", 12, QFont.Bold))
        p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 80)); p.drawRoundedRect(pill.adjusted(1, 2, 1, 2), 11, 11)
        p.setBrush(pbg); p.drawRoundedRect(pill, 11, 11); p.setPen(pfg); p.drawText(pill, Qt.AlignCenter, txt)

    def _render_portrait(self, p):
        margin = 20; bsz = self.w - 2 * margin; bx, by = margin, margin + 45
        p.setPen(QColor(195, 195, 205)); p.setFont(QFont("Inter", 22, QFont.Bold))
        p.drawText(QRectF(bx, margin, bsz, 35), Qt.AlignLeft | Qt.AlignVCenter, f"♚ {self.black_name}")
        bimg = self.board_renderer.render(bsz); p.drawImage(QRectF(bx, by, bsz, bsz), bimg)
        wy = by + bsz + 10
        p.drawText(QRectF(bx, wy, bsz, 35), Qt.AlignLeft | Qt.AlignVCenter, f"♔ {self.white_name}")
        ebx = bx; eby = wy + 45; ebh = 32; ebw = bsz; cr = 5
        p.setPen(QPen(QColor(50, 50, 58), 1.0)); p.setBrush(QColor(16, 16, 20))
        p.drawRoundedRect(QRectF(ebx - 2, eby - 2, ebw + 4, ebh + 4), cr + 2, cr + 2)
        blk = QLinearGradient(ebx, eby, ebx + ebw, eby)
        blk.setColorAt(0.0, QColor(38, 38, 45)); blk.setColorAt(1.0, QColor(58, 58, 66))
        p.setPen(Qt.NoPen); p.setBrush(blk); p.drawRoundedRect(QRectF(ebx, eby, ebw, ebh), cr, cr)
        ratio = self._cp2r(self.eval_cp); ww = max(0, min(ebw, int(ebw * ratio)))
        if ww > 0:
            wg = QLinearGradient(ebx, eby, ebx + ww, eby)
            wg.setColorAt(0.0, QColor(246, 243, 236)); wg.setColorAt(1.0, QColor(230, 226, 216))
            p.setBrush(wg)
            path = QPainterPath()
            if ww >= ebw: path.addRoundedRect(QRectF(ebx, eby, ebw, ebh), cr, cr)
            elif ww < cr * 2: path.addRoundedRect(QRectF(ebx, eby, ww, ebh), cr, cr)
            else:
                path.moveTo(ebx + cr, eby); path.lineTo(ebx + ww, eby); path.lineTo(ebx + ww, eby + ebh)
                path.lineTo(ebx + cr, eby + ebh); path.quadTo(ebx, eby + ebh, ebx, eby + ebh - cr)
                path.lineTo(ebx, eby + cr); path.quadTo(ebx, eby, ebx + cr, eby); path.closeSubpath()
            p.drawPath(path)
        xdy = ebx + ww
        if 0 < ww < ebw:
            p.setPen(QPen(QColor(105, 100, 90, 150), 1.5)); p.drawLine(QPointF(xdy, eby + 2), QPointF(xdy, eby + ebh - 2))
        if self.game_state == GAME_NORMAL:
            is_mate = abs(self.eval_cp) > 9000
            txt = (f"M{int(abs(self.eval_cp) - 10000)}" if is_mate else f"{self.eval_cp / 100.0:+.1f}")
            p.setFont(QFont("Inter", 12, QFont.Bold)); fm = p.fontMetrics()
            tw = fm.horizontalAdvance(txt) + 16; pill_w, pill_h = max(tw, 32), 22
            pill_x = max(ebx + pill_w / 2 + 4, min(ebx + ebw - pill_w / 2 - 4, xdy))
            pill = QRectF(pill_x - pill_w / 2, eby + (ebh - pill_h) / 2, pill_w, pill_h)
            on_white = (pill_x <= ebx + ww) if 0 < ww < ebw else (self.eval_cp >= 0)
            if is_mate: pbg = QColor(28, 165, 55, 225) if self.eval_cp > 0 else QColor(205, 40, 40, 225); pfg = QColor(255, 255, 255)
            elif on_white: pbg, pfg = QColor(255, 255, 255, 210), QColor(32, 30, 26)
            else: pbg, pfg = QColor(20, 20, 28, 210), QColor(235, 232, 224)
            p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 80)); p.drawRoundedRect(pill.adjusted(1, 2, 1, 2), 11, 11)
            p.setBrush(pbg); p.drawRoundedRect(pill, 11, 11)
            p.setPen(QPen(QColor(255, 255, 255, 35), 0.8)); p.drawRoundedRect(pill, 11, 11)
            p.setPen(pfg); p.drawText(pill, Qt.AlignCenter, txt)
        else:
            self._draw_gameover_pill_h(p, ebx, eby, ebw, ebh)
        mly = eby + ebh + 12; mlh = self.h - mly - margin
        if mlh > 60:
            render_movelist_2col(p, bx, mly, bsz, mlh, self.move_list_text, self.current_move_index, self.move_qualities)
        if self.game_state != GAME_NORMAL:
            self._draw_gameover_banner(p, bx, by, bsz)

    def _render_landscape(self, p):
        margin = 20; bsz = int(self.h * 0.92); by = (self.h - bsz) // 2
        ebw = max(32, int(bsz * 0.035)); ebx = margin
        ratio = self._cp2r(self.eval_cp); wh = max(0, min(bsz, int(bsz * ratio)))
        p.setPen(QPen(QColor(50, 50, 58), 1.0)); p.setBrush(QColor(16, 16, 20))
        p.drawRoundedRect(QRectF(ebx - 2, by - 2, ebw + 4, bsz + 4), 7, 7)
        blk = QLinearGradient(ebx, by, ebx, by + bsz)
        blk.setColorAt(0.0, QColor(58, 58, 66)); blk.setColorAt(0.5, QColor(44, 44, 52)); blk.setColorAt(1.0, QColor(38, 38, 45))
        p.setPen(Qt.NoPen); p.setBrush(blk); p.drawRoundedRect(QRectF(ebx, by, ebw, bsz), 5, 5)
        if wh > 0:
            wt = by + bsz - wh
            wg = QLinearGradient(ebx, wt, ebx, by + bsz)
            wg.setColorAt(0.0, QColor(230, 226, 216)); wg.setColorAt(0.4, QColor(238, 235, 226)); wg.setColorAt(1.0, QColor(246, 243, 236))
            p.setBrush(wg)
            if wh >= bsz: p.drawRoundedRect(QRectF(ebx, by, ebw, bsz), 5, 5)
            elif wh < 10: p.drawRoundedRect(QRectF(ebx, wt, ebw, wh), 5, 5)
            else:
                path = QPainterPath(); path.moveTo(ebx, wt); path.lineTo(ebx + ebw, wt)
                path.lineTo(ebx + ebw, by + bsz - 5); path.quadTo(ebx + ebw, by + bsz, ebx + ebw - 5, by + bsz)
                path.lineTo(ebx + 5, by + bsz); path.quadTo(ebx, by + bsz, ebx, by + bsz - 5)
                path.lineTo(ebx, wt); path.closeSubpath(); p.drawPath(path)
        p.setPen(QPen(QColor(115, 175, 250, 60), 1, Qt.DashLine))
        p.drawLine(QPointF(ebx + 2, by + bsz / 2), QPointF(ebx + ebw - 2, by + bsz / 2))
        bdy = by + bsz - wh
        if 0 < wh < bsz:
            p.setPen(QPen(QColor(105, 100, 90, 150), 1.5)); p.drawLine(QPointF(ebx + 2, bdy), QPointF(ebx + ebw - 2, bdy))
        if self.game_state == GAME_NORMAL:
            is_mate = abs(self.eval_cp) > 9000
            txt = (f"M{int(abs(self.eval_cp) - 10000)}" if is_mate else f"{self.eval_cp / 100.0:+.1f}")
            efsz = max(9, min(14, int(ebw * 0.36))); p.setFont(QFont("Inter", efsz, QFont.Bold))
            efm = p.fontMetrics(); etw = efm.horizontalAdvance(txt) + 12; epx, eph = max(etw, 30), 22
            ety = bdy if 0 < wh < bsz else by + bsz / 2
            ety = max(by + eph / 2 + 4, min(by + bsz - eph / 2 - 4, ety))
            epill = QRectF(ebx + (ebw - epx) / 2, ety - eph / 2, epx, eph)
            on_w = (ety >= by + bsz - wh) if 0 < wh < bsz else (self.eval_cp >= 0)
            if is_mate: epbg = QColor(28, 165, 55, 215) if self.eval_cp > 0 else QColor(205, 40, 40, 215); epfg = QColor(255, 255, 255)
            else: epbg = QColor(255, 255, 255, 195) if on_w else QColor(20, 20, 28, 205); epfg = QColor(32, 30, 26) if on_w else QColor(235, 232, 224)
            p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 45)); p.drawRoundedRect(epill.adjusted(1, 1, 1, 1), 10, 10)
            p.setBrush(epbg); p.drawRoundedRect(epill, 10, 10); p.setPen(epfg); p.drawText(epill, Qt.AlignCenter, txt)
        else:
            self._draw_gameover_pill_v(p, ebx, by, ebw, bsz)
        bx_board = ebx + ebw + margin
        if bx_board + bsz > self.w: bsz = max(100, self.w - bx_board - margin)
        bimg = self.board_renderer.render(bsz); p.drawImage(QRectF(bx_board, by, bsz, bsz), bimg)
        mx = bx_board + bsz + margin; mw = self.w - mx - margin
        if mw > 160:
            bar_h = 52; gap = 8
            black_eval = -self.eval_cp
            self._draw_player_bar_v(p, mx, by, mw, bar_h, self.black_name, self.black_engine_info, black_eval, False)
            ml_y = by + bar_h + gap; ml_h = bsz - 2 * (bar_h + gap); ml_h = max(60, ml_h)
            render_movelist_2col(p, mx, ml_y, mw, ml_h, self.move_list_text, self.current_move_index, self.move_qualities)
            white_y = by + bsz - bar_h; white_eval = self.eval_cp
            self._draw_player_bar_v(p, mx, white_y, mw, bar_h, self.white_name, self.white_engine_info, white_eval, True)
        if self.game_state != GAME_NORMAL:
            self._draw_gameover_banner(p, bx_board, by, bsz, landscape=True)

    def _draw_gameover_banner(self, p, bx, by, bsz, landscape=False):
        if landscape:
            banner_h = int(self.h * 0.06); banner_y = by + bsz + 10
            if banner_y + banner_h > self.h: banner_y = by + bsz - banner_h - 5
        else:
            banner_h = int(bsz * 0.08); banner_y = by + bsz - banner_h - 30
        banner = QRectF(bx, banner_y, bsz, banner_h)
        if self.game_state == GAME_CHECKMATE:
            w_wins = self.eval_cp > 0 or self.game_result == "1-0"
            bg = QColor(22, 135, 50, 205) if w_wins else QColor(185, 32, 32, 205)
            txt = (f"♔ CHECKMATE  {self.game_result or '1-0'}" if w_wins else f"♚ CHECKMATE  {self.game_result or '0-1'}")
        else:
            bg = QColor(155, 135, 38, 195); detail = self.game_detail or ""
            txt = f"½-½  {detail}" if detail else "½-½  DRAW"
        p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 70)); p.drawRoundedRect(banner.adjusted(2, 2, 2, 2), 6, 6)
        p.setBrush(bg); p.setPen(QPen(QColor(255, 255, 255, 45), 1.0)); p.drawRoundedRect(banner, 6, 6)
        p.setFont(QFont("Inter", max(10, int(banner_h * 0.45)), QFont.Bold)); p.setPen(QColor(255, 255, 255, 235))
        p.drawText(banner, Qt.AlignCenter, txt)


# ════════════════════════════════════════════════════════════════════
#  WIDGETS
# ════════════════════════════════════════════════════════════════════

class MoveListWidget(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self._moves = []; self._qualities = []; self._current = -1
        self.setMinimumWidth(280); self.setMinimumHeight(200)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

    def add_move(self, san, quality=MQ_GOOD):
        self._moves.append(san); self._qualities.append(quality)
        self._current = len(self._moves) - 1; self.update()

    def set_moves(self, moves, qualities=None, current=-1):
        self._moves = list(moves); self._qualities = list(qualities) if qualities else [MQ_GOOD] * len(moves)
        self._current = current; self.update()

    def set_current(self, idx): self._current = idx; self.update()

    def clear(self): self._moves.clear(); self._qualities.clear(); self._current = -1; self.update()

    @property
    def moves(self): return list(self._moves)
    @property
    def qualities(self): return list(self._qualities)
    @property
    def current_index(self): return self._current

    def paintEvent(self, _):
        p = QPainter(self); p.setRenderHint(QPainter.Antialiasing); p.setRenderHint(QPainter.TextAntialiasing)
        render_movelist_2col(p, 0, 0, self.width(), self.height(), self._moves, self._current, self._qualities)
        p.end()


class BoardPreviewWidget(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self._renderer = BoardRenderer(); self._anim_progress_val = 1.0
        self._active_anim = None; self._anim_duration = 300
        self.setMinimumSize(360, 360); self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

    def _get_ap(self): return self._anim_progress_val
    def _set_ap(self, v): self._anim_progress_val = v; self._renderer.anim_progress = v; self.update()
    animProgress = Property(float, _get_ap, _set_ap)

    @property
    def flipped(self): return self._renderer.flipped

    def set_board(self, board, last_move=None):
        self._renderer.board = board; self._renderer.last_move = last_move
        self._renderer.anim_move = None; self._renderer.anim_rook_move = None
        self._renderer.anim_progress = 1.0; self._anim_progress_val = 1.0; self.update()

    def set_theme(self, theme): self._renderer.theme = theme; self.update()
    def set_flipped(self, f): self._renderer.flipped = f; self.update()
    def set_anim_duration(self, ms): self._anim_duration = max(50, int(ms))
    def set_show_coords(self, show): self._renderer.show_coords = show; self.update()
    def set_move_quality(self, q): self._renderer.move_quality = q; self.update()

    def animate_move(self, move):
        self._renderer.anim_move = move; self._renderer.anim_progress = 0.0; self._anim_progress_val = 0.0
        rook_move = None
        pc = self._renderer.board.piece_at(move.to_square)
        if (pc and pc.piece_type == chess.KING and abs(chess.square_file(move.from_square) - chess.square_file(move.to_square)) == 2):
            rank = chess.square_rank(move.from_square)
            if chess.square_file(move.to_square) > chess.square_file(move.from_square):
                rook_move = (chess.square(7, rank), chess.square(5, rank))
            else:
                rook_move = (chess.square(0, rank), chess.square(3, rank))
        self._renderer.anim_rook_move = rook_move
        if self._active_anim is not None:
            self._active_anim.stop(); self._active_anim = None
        anim = QPropertyAnimation(self, b"animProgress")
        anim.setDuration(self._anim_duration); anim.setStartValue(0.0); anim.setEndValue(1.0)
        anim.setEasingCurve(QEasingCurve.OutQuint)

        def cleanup():
            self._renderer.anim_move = None; self._renderer.anim_rook_move = None
            self._renderer.anim_progress = 1.0; self._anim_progress_val = 1.0; self.update()

        anim.finished.connect(cleanup); anim.start(); self._active_anim = anim

    def paintEvent(self, _):
        p = QPainter(self); p.setRenderHint(QPainter.Antialiasing); p.setRenderHint(QPainter.TextAntialiasing)
        t = min(self.width(), self.height())
        m = t * 0.05 if self._renderer.show_coords else 0; sz = (t - 2 * m) / 8
        self._renderer._paint(p, t, m, sz); p.end()


class EvalBarWidget(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self._eval_cp = 0.0; self._anim_cp = 0.0
        self._game_state = GAME_NORMAL; self._game_result = ""; self._game_detail = ""
        self.setFixedWidth(48 + 16); self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Expanding)
        self.setMinimumHeight(200)
        self._animation = QPropertyAnimation(self, b"anim_cp")
        self._animation.setDuration(450); self._animation.setEasingCurve(QEasingCurve.OutQuart)

    def set_game_state(self, state, result="", detail=""):
        self._game_state = state; self._game_result = result; self._game_detail = detail; self.update()

    def reset_game_state(self):
        self._game_state = GAME_NORMAL; self._game_result = ""; self._game_detail = ""; self.update()

    def _get_ac(self): return self._anim_cp
    def _set_ac(self, v): self._anim_cp = v; self.update()
    anim_cp = Property(float, _get_ac, _set_ac)

    def set_eval(self, cp):
        old = self._eval_cp; self._eval_cp = cp
        if self._game_state != GAME_NORMAL or abs(cp) > 9000 or abs(old) > 9000:
            self._anim_cp = float(cp); self.update(); return
        self._animation.stop(); self._animation.setStartValue(self._anim_cp)
        self._animation.setEndValue(float(cp))
        self._animation.start()

    @staticmethod
    def _cp2r(cp):
        if cp >= 9000: return 1.0
        if cp <= -9000: return 0.0
        return 1.0 / (1.0 + math.exp(-0.004 * max(-10000, min(10000, cp))))

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.TextAntialiasing)

        W, H = self.width(), self.height()
        pad, cr = 8, 6
        bx, by, bw, bh = pad, pad, W - 2 * pad, H - 2 * pad

        p.setPen(QPen(QColor(50, 50, 58), 1.0))
        p.setBrush(QColor(16, 16, 20))
        p.drawRoundedRect(QRectF(0, 0, W, H), cr + 2, cr + 2)

        blk = QLinearGradient(bx, by, bx, by + bh)
        blk.setColorAt(0.0, QColor(58, 58, 66))
        blk.setColorAt(0.5, QColor(44, 44, 52))
        blk.setColorAt(1.0, QColor(38, 38, 45))
        p.setPen(Qt.NoPen)
        p.setBrush(blk)
        p.drawRoundedRect(QRectF(bx, by, bw, bh), cr, cr)

        ratio = self._cp2r(self._anim_cp)
        wh = max(0, min(bh, int(bh * ratio)))
        if wh > 0:
            wt = by + bh - wh
            wg = QLinearGradient(bx, wt, bx, by + bh)
            wg.setColorAt(0.0, QColor(230, 226, 216))
            wg.setColorAt(0.4, QColor(238, 235, 226))
            wg.setColorAt(1.0, QColor(246, 243, 236))
            p.setBrush(wg)
            if wh >= bh:
                p.drawRoundedRect(QRectF(bx, by, bw, bh), cr, cr)
            elif wh < cr * 2:
                p.drawRoundedRect(QRectF(bx, wt, bw, wh), cr, cr)
            else:
                path = QPainterPath()
                path.moveTo(bx, wt)
                path.lineTo(bx + bw, wt)
                path.lineTo(bx + bw, by + bh - cr)
                path.quadTo(bx + bw, by + bh, bx + bw - cr, by + bh)
                path.lineTo(bx + cr, by + bh)
                path.quadTo(bx, by + bh, bx, by + bh - cr)
                path.lineTo(bx, wt)
                path.closeSubpath()
                p.drawPath(path)

        ig = QLinearGradient(bx, by, bx, by + bh)
        ig.setColorAt(0.0, QColor(0, 0, 0, 50))
        ig.setColorAt(0.1, QColor(0, 0, 0, 18))
        ig.setColorAt(0.5, QColor(255, 255, 255, 12))
        ig.setColorAt(0.9, QColor(0, 0, 0, 8))
        ig.setColorAt(1.0, QColor(0, 0, 0, 35))
        p.setBrush(ig)
        p.drawRoundedRect(QRectF(bx, by, bw, bh), cr, cr)

        bdy = by + bh - wh
        if 0 < wh < bh:
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(105, 100, 90, 35))
            p.drawRect(QRectF(bx + 2, bdy - 2, bw - 4, 5))
            p.setPen(QPen(QColor(105, 100, 90, 150), 1.5))
            p.drawLine(QPointF(bx + 2, bdy), QPointF(bx + bw - 2, bdy))

        if self._game_state == GAME_NORMAL:
            is_mate = abs(self._eval_cp) > 9000
            txt = (f"M{int(abs(self._eval_cp) - 10000)}" if is_mate
                   else f"{self._eval_cp / 100.0:+.1f}")
            fnt = QFont("Inter", max(8, min(12, int(bw * 0.27))), QFont.Bold)
            p.setFont(fnt)
            fm = p.fontMetrics()
            tw = fm.horizontalAdvance(txt) + 16
            pill_w, pill_h = max(tw, 32), 22
            ty = bdy if 0 < wh < bh else by + bh / 2
            ty = max(by + pill_h / 2 + 4, min(by + bh - pill_h / 2 - 4, ty))
            pill = QRectF((W - pill_w) / 2, ty - pill_h / 2, pill_w, pill_h)
            on_white = (ty >= by + bh - wh) if 0 < wh < bh else (self._eval_cp >= 0)
            if is_mate:
                pbg = QColor(28, 165, 55, 225) if self._eval_cp > 0 else QColor(205, 40, 40, 225)
                pfg = QColor(255, 255, 255)
            elif on_white:
                pbg, pfg = QColor(255, 255, 255, 210), QColor(32, 30, 26)
            else:
                pbg, pfg = QColor(20, 20, 28, 210), QColor(235, 232, 224)
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(0, 0, 0, 80))
            p.drawRoundedRect(pill.adjusted(1, 2, 1, 2), 11, 11)
            p.setBrush(pbg)
            p.drawRoundedRect(pill, 11, 11)
            p.setPen(QPen(QColor(255, 255, 255, 35), 0.8))
            p.drawRoundedRect(pill, 11, 11)
            p.setPen(pfg)
            p.drawText(pill, Qt.AlignCenter, txt)
        else:
            pill_w, pill_h = max(32, int(bw * 0.8)), 24
            pill_x = (W - pill_w) / 2
            if "1-0" in self._game_result:
                txt = "♔ 1-0"; pill_y = by + 15
                pbg, pfg = QColor(255, 255, 255, 225), QColor(28, 28, 28)
            elif "0-1" in self._game_result:
                txt = "♚ 0-1"; pill_y = by + bh - pill_h - 15
                pbg, pfg = QColor(28, 28, 28, 235), QColor(228, 228, 228)
            else:
                txt = "½-½"; pill_y = by + (bh - pill_h) / 2
                pbg, pfg = QColor(135, 125, 48, 235), QColor(255, 255, 255)
            pill = QRectF(pill_x, pill_y, pill_w, pill_h)
            p.setFont(QFont("Inter", max(8, min(11, int(bw * 0.25))), QFont.Bold))
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(0, 0, 0, 80))
            p.drawRoundedRect(pill.adjusted(1, 2, 1, 2), 11, 11)
            p.setBrush(pbg)
            p.drawRoundedRect(pill, 11, 11)
            p.setPen(pfg)
            p.drawText(pill, Qt.AlignCenter, txt)

        p.end()


# ════════════════════════════════════════════════════════════════════
#  WORKERS
# ════════════════════════════════════════════════════════════════════

def _ease_out_quint(t):
    return 1.0 - (1.0 - t) ** 5


class GameWorker(QObject):
    move_made = Signal(chess.Board, chess.Move, float, int, dict, str, str, str)
    game_over = Signal(str, str, str)
    error = Signal(str)
    finished = Signal()

    def __init__(self, white_type, white_depth, black_type, black_depth,
                 stockfish_path=None, move_delay=100):
        super().__init__()
        self.white_type = white_type
        self.white_depth = white_depth
        self.black_type = black_type
        self.black_depth = black_depth
        self.stockfish_path = stockfish_path
        self._move_delay = move_delay
        self._stop = False
        self.board = chess.Board()

    def stop(self):
        self._stop = True

    def run(self):
        engines = {}
        sf_instance = None
        try:
            for color, (etype, depth) in enumerate([
                (self.white_type, self.white_depth),
                (self.black_type, self.black_depth),
            ]):
                if etype == 0:
                    engines[color] = ("minimax", MinimaxEngine(), depth)
                elif etype == 1:
                    engines[color] = ("mcts", MCTSEngine(), depth)
                elif etype == 2:
                    if sf_instance is None:
                        if not self.stockfish_path:
                            self.error.emit("Stockfish path not configured.")
                            return
                        try:
                            sf_instance = SyncUCI(self.stockfish_path)
                        except Exception as e:
                            self.error.emit(f"Failed to start Stockfish: {e}")
                            return
                    engines[color] = ("stockfish", sf_instance, depth)

            self.board.reset()

            while not self.board.is_game_over() and not self._stop:
                current_color = self.board.turn
                color_key = 0 if current_color == chess.WHITE else 1
                engine_type, engine, depth = engines[color_key]

                if engine_type == "stockfish":
                    bm, sc = engine.analyse(self.board.fen(), depth=depth)
                    if bm:
                        move = chess.Move.from_uci(bm)
                    else:
                        self.error.emit("Stockfish returned no move.")
                        break
                    eval_cp, nodes, policy = sc, 0, {}
                elif engine_type == "minimax":
                    move, eval_score, nodes, policy = engine.search(self.board, depth)
                    eval_cp = eval_score
                elif engine_type == "mcts":
                    move, eval_score, nodes, policy = engine.search(
                        self.board, iterations=depth * 100)
                    eval_cp = eval_score
                else:
                    break

                if move is None or move not in self.board.legal_moves:
                    logger.warning("Engine returned illegal/None move, stopping.")
                    break

                self.board.push(move)
                game_state, result, detail = self._detect_game_state()

                self.move_made.emit(
                    self.board.copy(), move, eval_cp, nodes, policy,
                    game_state, result, detail,
                )

                if game_state != GAME_NORMAL:
                    self.game_over.emit(game_state, result, detail)
                    break

                time.sleep(self._move_delay / 1000.0)

        except Exception as e:
            logger.exception("Game thread error")
            self.error.emit(str(e))
        finally:
            if sf_instance:
                try:
                    sf_instance.close()
                except Exception:
                    pass
            self.finished.emit()

    def _detect_game_state(self):
        if self.board.is_checkmate():
            r = "1-0" if self.board.turn == chess.BLACK else "0-1"
            return GAME_CHECKMATE, r, "Checkmate"
        if self.board.is_stalemate():
            return GAME_STALEMATE, "½-½", "Stalemate"
        if self.board.is_insufficient_material():
            return GAME_INSUFFICIENT, "½-½", "Insufficient Material"
        if self.board.is_repetition(3):
            return GAME_DRAW, "½-½", "Threefold Repetition"
        if self.board.is_fifty_moves():
            return GAME_DRAW, "½-½", "50-Move Rule"
        if self.board.is_game_over():
            return GAME_DRAW, "½-½", "Draw"
        return GAME_NORMAL, "", ""


class ExportWorker(QObject):
    progress = Signal(int)
    finished = Signal(str)
    error = Signal(str)

    def __init__(self, pgn_text, save_path, resolution_key, fps,
                 board_theme, white_name, black_name,
                 white_engine_info, black_engine_info,
                 eval_history, move_qualities,
                 move_duration=DEFAULT_MOVE_DURATION,
                 anim_duration=DEFAULT_ANIM_DURATION,
                 title_duration=DEFAULT_TITLE_DURATION,
                 result_duration=DEFAULT_RESULT_DURATION,
                 show_title=True, show_result=True,
                 sound_engine=None):
        super().__init__()
        self.pgn_text = pgn_text
        self.save_path = save_path
        self.resolution_key = resolution_key
        self.fps = fps
        self.board_theme = board_theme
        self.white_name = white_name
        self.black_name = black_name
        self.white_engine_info = white_engine_info
        self.black_engine_info = black_engine_info
        self.eval_history = eval_history
        self.move_qualities = move_qualities
        self.move_duration = move_duration
        self.anim_duration = anim_duration
        self.title_duration = title_duration
        self.result_duration = result_duration
        self.show_title = show_title
        self.show_result = show_result
        self.sound_engine = sound_engine
        self._stop = False

    def stop(self):
        self._stop = True

    def run(self):
        if not HAS_CV2:
            self.error.emit("opencv-python is required.\npip install opencv-python")
            return
        try:
            game = None
            if hasattr(chess.pgn, 'read_gameFromString'):
                try:
                    game = chess.pgn.read_gameFromString(self.pgn_text)
                except Exception:
                    pass
            if game is None:
                io = StringIO(self.pgn_text)
                game = chess.pgn.read_game(io)
            if game is None:
                self.error.emit("Invalid PGN.")
                return

            w, h = RESOLUTION_SIZES.get(self.resolution_key, (1920, 1080))
            fps = max(1, self.fps)

            moves = list(game.mainline_moves())
            total_moves = len(moves)
            if total_moves == 0:
                self.error.emit("No moves found in PGN.")
                return
            logger.info("Export starting: %dx%d @ %d fps, %d moves",
                        w, h, fps, total_moves)

            anim_frames = max(1, int(fps * self.anim_duration))
            total_move_frames = max(anim_frames + 1,
                                    int(fps * self.move_duration))
            pause_before = max(0, (total_move_frames - anim_frames) // 2)
            pause_after = total_move_frames - anim_frames - pause_before

            title_frames = int(fps * self.title_duration) if self.show_title else 0
            result_frames = int(fps * self.result_duration) if self.show_result else 0
            total_frames = (title_frames
                            + total_moves * total_move_frames
                            + result_frames)
            if total_frames <= 0:
                total_frames = 1
            frames_done = 0

            fourcc = cv2.VideoWriter_fourcc(*'mp4v')
            tmp_path = self.save_path.replace(".mp4", "_tmp.mp4")
            out = cv2.VideoWriter(tmp_path, fourcc, fps, (w, h))
            if not out.isOpened():
                self.error.emit("Failed to create video writer.")
                return

            board = chess.Board()
            renderer = BoardRenderer(board=board, theme=self.board_theme)
            video = VideoRenderer(renderer, w=w, h=h)
            video.white_name = self.white_name
            video.black_name = self.black_name
            video.white_engine_info = self.white_engine_info
            video.black_engine_info = self.black_engine_info

            frame_buf = np.empty((h, w * 3), dtype=np.uint8)

            # Audio setup
            audio_data = {}
            sr = 44100
            mix = None
            if self.sound_engine and self.sound_engine.enabled:
                sr = self.sound_engine._sr
                for event in [SND_MOVE, SND_CAPTURE, SND_CHECK, SND_CASTLE,
                              SND_CHECKMATE, SND_STALEMATE, SND_DRAW, SND_GAME_START]:
                    fp = self.sound_engine.get_sound_path(event)
                    if fp and os.path.exists(fp):
                        try:
                            with wave.open(fp, 'rb') as wf:
                                n = wf.getnframes()
                                raw = wf.readframes(n)
                                audio_data[event] = np.frombuffer(raw, dtype=np.int16).astype(np.float64) / 32767.0
                        except Exception:
                            pass

                if audio_data:
                    total_samples = int(sr * (total_frames / fps)) + sr * 2
                    mix = np.zeros(total_samples, dtype=np.float64)
                    if SND_GAME_START in audio_data and title_frames > 0:
                        self._add_audio(mix, 0, audio_data[SND_GAME_START], sr, fps)

            # Title screen
            if self.show_title and title_frames > 0:
                title_img = video.render_title_screen()
                title_bgr = self._qimage_to_bgr_numpy(title_img, frame_buf)
                if title_bgr is not None:
                    for _ in range(title_frames):
                        if self._stop:
                            break
                        out.write(title_bgr)
                        frames_done += 1
                    self.progress.emit(int(frames_done / total_frames * 100))

            # Game frames
            move_list_text = []

            for i, move in enumerate(moves):
                if self._stop:
                    logger.info("Export stopped at move %d/%d", i + 1, total_moves)
                    break

                san = board.san(move)
                move_list_text.append(san)

                quality = (self.move_qualities[i]
                           if i < len(self.move_qualities) else MQ_GOOD)
                eval_cp = (self.eval_history[i]
                           if i < len(self.eval_history) else 0.0)

                video.move_list_text = list(move_list_text)
                video.current_move_index = i
                video.move_qualities = self.move_qualities[:i + 1]
                video.eval_cp = eval_cp
                video.eval_history = self.eval_history[:i + 1]

                rook_move = None
                piece = board.piece_at(move.from_square)
                if (piece and piece.piece_type == chess.KING and
                        abs(chess.square_file(move.from_square) -
                            chess.square_file(move.to_square)) == 2):
                    rank = chess.square_rank(move.from_square)
                    if chess.square_file(move.to_square) > chess.square_file(move.from_square):
                        rook_move = (chess.square(7, rank), chess.square(5, rank))
                    else:
                        rook_move = (chess.square(0, rank), chess.square(3, rank))

                is_cap = board.is_capture(move)
                is_castle = rook_move is not None
                gives_check = board.gives_check(move)

                # Pre-move pause
                renderer.board = board
                renderer.last_move = (moves[i - 1] if i > 0 else None)
                renderer.move_quality = (self.move_qualities[i - 1]
                                         if i > 0 and i - 1 < len(self.move_qualities)
                                         else MQ_GOOD)
                renderer.anim_move = None
                renderer.anim_rook_move = None
                renderer.anim_progress = 1.0

                if pause_before > 0:
                    pause_img = video.render()
                    pause_bgr = self._qimage_to_bgr_numpy(pause_img, frame_buf)
                    if pause_bgr is not None:
                        for _ in range(pause_before):
                            if self._stop:
                                break
                            out.write(pause_bgr)
                            frames_done += 1

                # Animation frames
                board.push(move)

                if mix is not None:
                    is_mate = board.is_checkmate()
                    is_stale = board.is_stalemate()
                    is_draw = board.is_game_over() and not is_mate and not is_stale

                    if is_mate:       snd_event = SND_CHECKMATE
                    elif is_stale:    snd_event = SND_STALEMATE
                    elif is_draw:     snd_event = SND_DRAW
                    elif gives_check: snd_event = SND_CHECK
                    elif is_castle:   snd_event = SND_CASTLE
                    elif is_cap:      snd_event = SND_CAPTURE
                    else:             snd_event = SND_MOVE

                    if snd_event in audio_data:
                        self._add_audio(mix, frames_done, audio_data[snd_event], sr, fps)

                renderer.board = board
                renderer.last_move = move
                renderer.move_quality = quality
                renderer.anim_move = move
                renderer.anim_rook_move = rook_move

                anim_rgb_frames = []
                for f_idx in range(anim_frames):
                    if self._stop:
                        break
                    t = f_idx / max(1, anim_frames - 1)
                    renderer.anim_progress = _ease_out_quint(t)
                    img = video.render()
                    rgb = self._qimage_to_rgb_numpy(img, frame_buf)
                    if rgb is not None:
                        anim_rgb_frames.append(rgb)
                    frames_done += 1

                if anim_rgb_frames:
                    anim_bgr_frames = rgb_to_bgr_batch(anim_rgb_frames)
                    for bgr in anim_bgr_frames:
                        out.write(bgr)

                # Post-move settle
                renderer.anim_move = None
                renderer.anim_rook_move = None
                renderer.anim_progress = 1.0

                game_state, result, detail = self._detect_game_state(board)
                if game_state != GAME_NORMAL:
                    video.game_state = game_state
                    video.game_result = result
                    video.game_detail = detail

                if pause_after > 0:
                    settle_img = video.render()
                    settle_bgr = self._qimage_to_bgr_numpy(settle_img, frame_buf)
                    if settle_bgr is not None:
                        for _ in range(pause_after):
                            if self._stop:
                                break
                            out.write(settle_bgr)
                            frames_done += 1

                pct = int(frames_done / max(1, total_frames) * 100)
                self.progress.emit(min(95, pct))

            # Result screen
            if self.show_result and result_frames > 0 and not self._stop:
                result_img = video.render_result_screen()
                result_bgr = self._qimage_to_bgr_numpy(result_img, frame_buf)
                if result_bgr is not None:
                    for _ in range(result_frames):
                        if self._stop:
                            break
                        out.write(result_bgr)
                        frames_done += 1

            out.release()
            logger.info("Raw video written: %s", tmp_path)

            # Export Audio
            audio_tmp_path = None
            if mix is not None:
                actual_samples = int(sr * (frames_done / fps)) + sr
                mix = mix[:actual_samples]
                max_val = np.max(np.abs(mix))
                if max_val > 0:
                    mix = mix / max(max_val * 1.1, 1.0)
                mix_int16 = (mix * 32767).astype(np.int16)

                audio_tmp_path = tmp_path.replace(".mp4", "_audio.wav")
                try:
                    with wave.open(audio_tmp_path, 'wb') as wf:
                        wf.setnchannels(1)
                        wf.setsampwidth(2)
                        wf.setframerate(sr)
                        wf.writeframes(mix_int16.tobytes())
                    logger.info("Audio track generated: %s", audio_tmp_path)
                except Exception as e:
                    logger.warning("Failed to write audio track: %s", e)
                    audio_tmp_path = None

            # H.264 re-encode
            final_path = self._reencode_h264(tmp_path, self.save_path, audio_tmp_path)
            if final_path:
                logger.info("Export complete: %s", final_path)
                self.progress.emit(100)
                self.finished.emit(final_path)
            else:
                if os.path.exists(tmp_path):
                    os.replace(tmp_path, self.save_path)
                    logger.info("Export complete (no re-encode): %s", self.save_path)
                    self.progress.emit(100)
                    self.finished.emit(self.save_path)
                else:
                    self.finished.emit("")

                if audio_tmp_path and os.path.exists(audio_tmp_path):
                    try:
                        os.remove(audio_tmp_path)
                    except OSError:
                        pass

        except Exception as e:
            logger.exception("Export failed")
            self.error.emit(str(e))

    @staticmethod
    def _add_audio(mix, frame_idx, sound_arr, sr, fps):
        if sound_arr is None or len(mix) == 0:
            return
        start_sample = int(sr * frame_idx / fps)
        end_sample = start_sample + len(sound_arr)
        if end_sample > len(mix):
            end_sample = len(mix)
            sound_arr = sound_arr[:end_sample - start_sample]
        if start_sample < len(mix):
            mix[start_sample:end_sample] += sound_arr

    @staticmethod
    def _detect_game_state(board):
        if board.is_checkmate():
            r = "1-0" if board.turn == chess.BLACK else "0-1"
            return GAME_CHECKMATE, r, "Checkmate"
        if board.is_stalemate():
            return GAME_STALEMATE, "½-½", "Stalemate"
        if board.is_insufficient_material():
            return GAME_INSUFFICIENT, "½-½", "Insufficient Material"
        if board.is_repetition(3):
            return GAME_DRAW, "½-½", "Threefold Repetition"
        if board.is_fifty_moves():
            return GAME_DRAW, "½-½", "50-Move Rule"
        if board.is_game_over():
            return GAME_DRAW, "½-½", "Draw"
        return GAME_NORMAL, "", ""

    @staticmethod
    def _reencode_h264(tmp_path, final_path, audio_path=None):
        ffmpeg = shutil.which("ffmpeg")
        if not ffmpeg:
            logger.info("ffmpeg not found — skipping H.264 re-encode")
            return None

        if not os.path.exists(tmp_path):
            return None

        cmd = [ffmpeg, "-y", "-i", tmp_path]

        if audio_path and os.path.exists(audio_path):
            cmd.extend(["-i", audio_path])
            cmd.extend([
                "-map", "0:v", "-map", "1:a",
                "-c:v", "libx264", "-preset", "medium", "-crf", "18",
                "-pix_fmt", "yuv420p",
                "-c:a", "aac", "-b:a", "192k",
            ])
        else:
            cmd.extend([
                "-c:v", "libx264", "-preset", "medium", "-crf", "18",
                "-pix_fmt", "yuv420p",
            ])

        cmd.extend(["-movflags", "+faststart", final_path])

        logger.info("Re-encoding to H.264: %s", " ".join(cmd))
        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=600
            )
            if result.returncode == 0:
                try:
                    os.remove(tmp_path)
                except OSError:
                    pass
                if audio_path:
                    try:
                        os.remove(audio_path)
                    except OSError:
                        pass
                logger.info("H.264 re-encode successful")
                return final_path
            else:
                logger.warning("ffmpeg failed (rc=%d): %s",
                               result.returncode, result.stderr[:500])
                return None
        except FileNotFoundError:
            logger.warning("ffmpeg not found at runtime")
            return None
        except subprocess.TimeoutExpired:
            logger.warning("ffmpeg timed out")
            return None
        except Exception as e:
            logger.warning("ffmpeg error: %s", e)
            return None

    @staticmethod
    def _qimage_to_bgr_numpy(qimg, buf=None):
        img = qimg.convertToFormat(QImage.Format_RGB888)
        w, h = img.width(), img.height()
        if w == 0 or h == 0:
            return None
        bpl = img.bytesPerLine()
        ptr = img.bits()

        if hasattr(ptr, 'setsize'):
            ptr.setsize(bpl * h)
            if buf is not None and buf.shape == (h, bpl):
                np.copyto(buf, np.frombuffer(ptr, dtype=np.uint8)[:h * bpl].reshape(h, bpl))
                arr = buf
            else:
                arr = np.array(ptr, dtype=np.uint8).reshape((h, bpl))
        else:
            raw = np.frombuffer(ptr, dtype=np.uint8)
            arr = raw[:h * bpl].reshape((h, bpl))
            if buf is not None and buf.shape == (h, bpl):
                np.copyto(buf, arr)
                arr = buf

        if bpl != w * 3:
            arr = arr[:, :w * 3]

        arr3 = arr[:, :w * 3].reshape((h, w, 3))
        return cv2.cvtColor(arr3, cv2.COLOR_RGB2BGR)

    @staticmethod
    def _qimage_to_rgb_numpy(qimg, buf=None):
        img = qimg.convertToFormat(QImage.Format_RGB888)
        w, h = img.width(), img.height()
        if w == 0 or h == 0:
            return None
        bpl = img.bytesPerLine()
        ptr = img.bits()

        if hasattr(ptr, 'setsize'):
            ptr.setsize(bpl * h)
            arr = np.array(ptr, dtype=np.uint8).reshape((h, bpl))
        else:
            arr = np.frombuffer(ptr, dtype=np.uint8).reshape((h, bpl))

        if bpl != w * 3:
            arr = arr[:, :w * 3]

        return arr.reshape((h, w, 3)).copy()


# ════════════════════════════════════════════════════════════════════
#  MAIN WINDOW & APP
# ════════════════════════════════════════════════════════════════════

_SETTINGS_GROUP_SS = """
QGroupBox {
    font-weight: 600; font-size: 10px; color: #58586a;
    border: none; border-left: 2px solid #2a2a30;
    border-radius: 0; margin-top: 14px;
    padding: 16px 12px 8px 14px; background-color: transparent;
}
QGroupBox::title {
    subcontrol-origin: margin; left: 14px; padding: 0 8px;
    color: #58586a; font-size: 9px; text-transform: uppercase;
    letter-spacing: 1.5px;
}
"""

_SETTINGS_CONTROL_SS = """
QSpinBox, QDoubleSpinBox, QComboBox, QLineEdit {
    background-color: #1c1c20; border: none;
    border-radius: 4px;
    padding: 7px 8px; color: #c8c8d0; min-height: 24px;
    font-size: 12px;
}
QSpinBox:focus, QDoubleSpinBox:focus, QComboBox:focus, QLineEdit:focus {
    background-color: #202026;
}
QComboBox::drop-down { border: none; width: 20px; }
QComboBox QAbstractItemView {
    background-color: #1c1c20; border: 1px solid #2a2a30;
    border-radius: 4px; color: #c8c8d0;
    selection-background-color: #5b8fd4; selection-color: #fff;
    outline: none;
}
QCheckBox { color: #888898; spacing: 8px; font-size: 11px; }
QCheckBox::indicator {
    width: 16px; height: 16px; border-radius: 4px;
    border: none; background-color: #1c1c20;
}
QCheckBox::indicator:hover { background-color: #242428; }
QCheckBox::indicator:checked { background-color: #5b8fd4; }
QCheckBox::indicator:checked:hover { background-color: #6fa0e4; }
QSlider::groove:horizontal {
    height: 3px; background: #2a2a30; border-radius: 1.5px;
}
QSlider::sub-page:horizontal {
    background: #5b8fd4; border-radius: 1.5px;
}
QSlider::handle:horizontal {
    background: #5b8fd4; width: 12px; height: 12px;
    margin: -5px 0; border-radius: 6px;
}
QSlider::handle:horizontal:hover { background: #6fa0e4; }
QLabel { color: #888898; font-size: 11px; }
QPushButton {
    background: transparent; color: #888898; border: none;
    padding: 4px 2px; font-size: 11px;
}
QPushButton:hover { color: #c8c8d0; }
QToolTip {
    background-color: #1c1c20; color: #c8c8d0; border: none;
    padding: 8px 10px; font-size: 11px; border-radius: 6px;
}
QScrollBar:vertical {
    background: transparent; width: 6px; margin: 0;
}
QScrollBar::handle:vertical {
    background: #3a3a44; border-radius: 3px; min-height: 30px;
}
QScrollBar::handle:vertical:hover { background: #4a4a54; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
    height: 0;
}
QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {
    background: transparent;
}
"""

_BTN_CONTROL_SS = """
QPushButton {
    background-color: #1c1c20; color: #c8c8d0;
    border: none; border-radius: 4px;
    padding: 8px 14px; font-size: 12px; font-weight: 600;
}
QPushButton:hover { background-color: #303036; }
QPushButton:pressed { background-color: #18181c; }
QPushButton:disabled { color: #3a3a44; background-color: #1a1a1e; }
"""

_BTN_BROWSE_SS = """
QPushButton {
    background: transparent; color: #888898;
    border: 1px solid #2a2a30; border-radius: 4px;
    padding: 5px 10px; font-size: 10px;
}
QPushButton:hover {
    color: #c8c8d0; border-color: #3a3a44; background-color: #1c1c20;
}
"""

_BTN_EXPORT_SS = """
QPushButton {
    background: #5b8fd4; color: #fff; border: none;
    border-radius: 6px; font-size: 13px; font-weight: bold;
    padding: 10px 20px;
}
QPushButton:hover { background: #6fa0e4; }
QPushButton:pressed { background: #4a7cc4; }
QPushButton:disabled { background: #2a2a30; color: #4a4a54; }
"""

_LABEL_VALUE_SS = "color:#5b8fd4; font-weight:600; font-size:11px;"


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("AI vs AI → MP4  ·  Chess Battle")
        self.resize(1200, 800)

        self._game_thread = None
        self._game_worker = None
        self._export_thread = None
        self._export_worker = None

        self._board = chess.Board()
        self._move_list = []
        self._move_qualities = []
        self._eval_cp = 0.0
        self._game_state = GAME_NORMAL
        self._game_result = ""
        self._game_detail = ""

        self._analyzer = MoveAnalyzer()
        self.sound_engine = SoundEngine(self)
        self._stockfish_path = find_stockfish()

        logger.info("Stockfish path: %s", self._stockfish_path or "NOT FOUND")

        self._init_ui()
        self._apply_tab_style()
        self._reset_game()

        logger.info("Application initialized")

    # ── Player names & info ───────────────────────────────────
    def _get_player_names(self):
        wt = AI_SHORT_NAMES.get(self.white_ai_combo.currentData(), "AI")
        bt = AI_SHORT_NAMES.get(self.black_ai_combo.currentData(), "AI")
        wc = self.white_name_edit.text().strip() if hasattr(self, 'white_name_edit') else ""
        bc = self.black_name_edit.text().strip() if hasattr(self, 'black_name_edit') else ""
        wn = f"{wc} ({wt})" if wc else f"White ({wt})"
        bn = f"{bc} ({bt})" if bc else f"Black ({bt})"
        return wn, bn

    def _get_player_info(self):
        wt = AI_SHORT_NAMES.get(self.white_ai_combo.currentData(), "AI")
        wd = self.white_depth_spin.value() if hasattr(self, 'white_depth_spin') else 1
        bt = AI_SHORT_NAMES.get(self.black_ai_combo.currentData(), "AI")
        bd = self.black_depth_spin.value() if hasattr(self, 'black_depth_spin') else 1
        return f"{wt} (Depth {wd})", f"{bt} (Depth {bd})"

    def _update_player_labels(self):
        wn, bn = self._get_player_names()
        self.black_info_label.setText(f"♚ {bn}")
        self.white_info_label.setText(f"♔ {wn}")

    # ── Dynamic Depth / Tooltip Logic ─────────────────────────
    def _on_engine_changed(self, combo, spin):
        engine_type = combo.currentData()

        if engine_type == 0:  # Minimax
            spin.setRange(1, 8)
            spin.setValue(min(max(spin.value(), 1), 8))
            if spin.value() < 3:
                spin.setValue(4)
            spin.setToolTip(
                "Minimax Search Depth (half-moves ahead)\n\n"
                "• 1-3: Fast, beginner play\n"
                "• 4-5: Intermediate, slower\n"
                "• 6-8: Strong, VERY slow (Python limits)"
            )
        elif engine_type == 1:  # MCTS
            spin.setRange(1, 50)
            spin.setValue(min(max(spin.value(), 1), 50))
            if spin.value() < 5:
                spin.setValue(15)
            spin.setToolTip(
                "MCTS Simulations (value × 100)\n\n"
                "• 5-10: Fast, weak play (500-1000 sims)\n"
                "• 15-25: Moderate strength\n"
                "• 30+: Stronger, linear slowdown"
            )
        elif engine_type == 2:  # Stockfish
            spin.setRange(1, 30)
            spin.setValue(min(max(spin.value(), 1), 30))
            if spin.value() < 5:
                spin.setValue(18)
            spin.setToolTip(
                "Stockfish Search Depth (plies)\n\n"
                "• 1-8: Fast, beginner play\n"
                "• 10-15: Advanced play\n"
                "• 18+: Master level, very fast (C++ engine)"
            )

        self._update_player_labels()

    # ── UI ────────────────────────────────────────────────────
    def _init_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QHBoxLayout(central)
        main_layout.setContentsMargins(12, 12, 12, 12)
        main_layout.setSpacing(12)

        # Left: player bars + board + eval bar
        left_outer = QVBoxLayout()
        left_outer.setSpacing(4)

        self.black_info_label = QLabel("♚ Black")
        self.black_info_label.setStyleSheet(
            "font-size:12px; font-weight:600; color:#888898; padding:2px 4px;"
        )
        left_outer.addWidget(self.black_info_label)

        left_layout = QHBoxLayout()
        left_layout.setSpacing(6)
        self.eval_bar = EvalBarWidget()
        self.board_widget = BoardPreviewWidget()
        left_layout.addWidget(self.eval_bar)
        left_layout.addWidget(self.board_widget, 1)
        left_outer.addLayout(left_layout)

        self.white_info_label = QLabel("♔ White")
        self.white_info_label.setStyleSheet(
            "font-size:12px; font-weight:600; color:#888898; padding:2px 4px;"
        )
        left_outer.addWidget(self.white_info_label)

        main_layout.addLayout(left_outer, 5)

        # Right: move list + tabs
        right_layout = QVBoxLayout()
        right_layout.setSpacing(8)

        self.move_list_widget = MoveListWidget()
        right_layout.addWidget(self.move_list_widget, 1)

        # Tabs
        self.tab_widget = QTabWidget()
        self.tab_widget.setDocumentMode(True)

        # ──────── Tab 1: Game ─────────────────────────────────
        game_tab = QWidget()
        game_tab.setStyleSheet(_SETTINGS_CONTROL_SS)
        gl = QVBoxLayout(game_tab)
        gl.setContentsMargins(16, 20, 16, 16)
        gl.setSpacing(14)

        # White
        wg = QGroupBox("WHITE")
        wg.setStyleSheet(_SETTINGS_GROUP_SS)
        wf = QFormLayout(wg)
        wf.setContentsMargins(14, 16, 14, 8)
        wf.setSpacing(8)
        self.white_ai_combo = QComboBox()
        self.white_depth_spin = QSpinBox()
        for k, v in AI_MAP.items():
            self.white_ai_combo.addItem(v, k)
        wf.addRow("Engine", self.white_ai_combo)
        wf.addRow("Depth", self.white_depth_spin)
        gl.addWidget(wg)

        # Black
        bg = QGroupBox("BLACK")
        bg.setStyleSheet(_SETTINGS_GROUP_SS)
        bf = QFormLayout(bg)
        bf.setContentsMargins(14, 16, 14, 8)
        bf.setSpacing(8)
        self.black_ai_combo = QComboBox()
        self.black_depth_spin = QSpinBox()
        for k, v in AI_MAP.items():
            self.black_ai_combo.addItem(v, k)
        self.black_ai_combo.setCurrentIndex(1)
        bf.addRow("Engine", self.black_ai_combo)
        bf.addRow("Depth", self.black_depth_spin)
        gl.addWidget(bg)

        self.white_ai_combo.currentIndexChanged.connect(
            lambda _idx, c=self.white_ai_combo, s=self.white_depth_spin:
                self._on_engine_changed(c, s)
        )
        self.black_ai_combo.currentIndexChanged.connect(
            lambda _idx, c=self.black_ai_combo, s=self.black_depth_spin:
                self._on_engine_changed(c, s)
        )
        self.white_depth_spin.valueChanged.connect(self._update_player_labels)
        self.black_depth_spin.valueChanged.connect(self._update_player_labels)

        # Controls
        btn_layout = QHBoxLayout()
        btn_layout.setSpacing(8)
        self.start_btn = QPushButton("▶  Start")
        self.stop_btn = QPushButton("■  Stop")
        self.reset_btn = QPushButton("↺  Reset")
        self.stop_btn.setEnabled(False)
        for b in (self.start_btn, self.stop_btn, self.reset_btn):
            b.setMinimumHeight(34)
            b.setStyleSheet(_BTN_CONTROL_SS)
        self.start_btn.clicked.connect(self._start_game)
        self.stop_btn.clicked.connect(self._stop_game)
        self.reset_btn.clicked.connect(self._reset_game)
        btn_layout.addWidget(self.start_btn, 1)
        btn_layout.addWidget(self.stop_btn, 1)
        btn_layout.addWidget(self.reset_btn, 1)
        gl.addLayout(btn_layout)

        # Last-move quality indicator
        self.quality_label = QLabel("")
        self.quality_label.setAlignment(Qt.AlignCenter)
        self.quality_label.setStyleSheet(
            "font-size:13px; font-weight:bold; padding:4px;"
        )
        gl.addWidget(self.quality_label)

        gl.addStretch()
        self.tab_widget.addTab(game_tab, "♟  Game")

        # ──────── Tab 2: Settings (minimalist) ────────────────
        settings_scroll = QScrollArea()
        settings_scroll.setWidgetResizable(True)
        settings_scroll.setFrameShape(QFrame.NoFrame)
        settings_scroll.setStyleSheet(
            "QScrollArea{background:transparent;border:none;}"
        )

        sc = QWidget()
        sc.setStyleSheet(_SETTINGS_CONTROL_SS)
        sl = QVBoxLayout(sc)
        sl.setContentsMargins(6, 14, 6, 14)
        sl.setSpacing(16)

        # Appearance
        ag = QGroupBox("APPEARANCE")
        ag.setStyleSheet(_SETTINGS_GROUP_SS)
        af = QFormLayout(ag)
        af.setContentsMargins(14, 16, 14, 8)
        af.setSpacing(8)
        self.theme_combo = QComboBox()
        self.theme_combo.addItems(THEMES.keys())
        self.theme_combo.currentTextChanged.connect(self._change_theme)
        af.addRow("Theme", self.theme_combo)
        self.flip_check = QCheckBox("Flip board")
        self.flip_check.toggled.connect(self.board_widget.set_flipped)
        af.addRow("", self.flip_check)
        self.show_coords_check = QCheckBox("Coordinates")
        self.show_coords_check.setChecked(True)
        self.show_coords_check.toggled.connect(self.board_widget.set_show_coords)
        af.addRow("", self.show_coords_check)
        self.anim_speed_slider = QSlider(Qt.Horizontal)
        self.anim_speed_slider.setRange(50, 800)
        self.anim_speed_slider.setValue(300)
        self.anim_speed_lbl = QLabel("300 ms")
        self.anim_speed_lbl.setFixedWidth(48)
        self.anim_speed_lbl.setStyleSheet(_LABEL_VALUE_SS)
        self.anim_speed_slider.valueChanged.connect(self._on_anim_speed)
        ar = QHBoxLayout()
        ar.addWidget(self.anim_speed_slider, 1)
        ar.addWidget(self.anim_speed_lbl)
        af.addRow("Anim", ar)
        sl.addWidget(ag)

        # Sound
        sg = QGroupBox("SOUND")
        sg.setStyleSheet(_SETTINGS_GROUP_SS)
        sf = QFormLayout(sg)
        sf.setContentsMargins(14, 16, 14, 8)
        sf.setSpacing(8)
        self.sound_theme_combo = QComboBox()
        if self.sound_engine.enabled:
            self.sound_theme_combo.addItems(self.sound_engine.available_themes)
            self.sound_theme_combo.currentTextChanged.connect(self.sound_engine.set_theme)
        else:
            self.sound_theme_combo.setEnabled(False)
        sf.addRow("Theme", self.sound_theme_combo)
        self.volume_slider = QSlider(Qt.Horizontal)
        self.volume_slider.setRange(0, 100)
        self.volume_slider.setValue(70)
        self.vol_lbl = QLabel("70%")
        self.vol_lbl.setFixedWidth(32)
        self.vol_lbl.setStyleSheet(_LABEL_VALUE_SS)
        self.volume_slider.valueChanged.connect(self._on_volume)
        vr = QHBoxLayout()
        vr.addWidget(self.volume_slider, 1)
        vr.addWidget(self.vol_lbl)
        sf.addRow("Vol", vr)
        self.mute_check = QCheckBox("Mute")
        self.mute_check.toggled.connect(self.sound_engine.set_muted)
        sf.addRow("", self.mute_check)
        sl.addWidget(sg)

        # Game
        gg = QGroupBox("GAME")
        gg.setStyleSheet(_SETTINGS_GROUP_SS)
        gf = QFormLayout(gg)
        gf.setContentsMargins(14, 16, 14, 8)
        gf.setSpacing(8)
        self.move_delay_spin = QSpinBox()
        self.move_delay_spin.setRange(0, 5000)
        self.move_delay_spin.setValue(100)
        self.move_delay_spin.setSuffix(" ms")
        self.move_delay_spin.setToolTip(
            "Delay between moves during live play\n"
            "(does not affect video export)"
        )
        gf.addRow("Delay", self.move_delay_spin)
        sl.addWidget(gg)

        # Names
        ng = QGroupBox("NAMES")
        ng.setStyleSheet(_SETTINGS_GROUP_SS)
        nf = QFormLayout(ng)
        nf.setContentsMargins(14, 16, 14, 8)
        nf.setSpacing(8)
        self.white_name_edit = QLineEdit()
        self.white_name_edit.setPlaceholderText("White player")
        self.white_name_edit.textChanged.connect(self._update_player_labels)
        nf.addRow("♔", self.white_name_edit)
        self.black_name_edit = QLineEdit()
        self.black_name_edit.setPlaceholderText("Black player")
        self.black_name_edit.textChanged.connect(self._update_player_labels)
        nf.addRow("♚", self.black_name_edit)
        sl.addWidget(ng)

        # Stockfish
        sfg = QGroupBox("STOCKFISH")
        sfg.setStyleSheet(_SETTINGS_GROUP_SS)
        sff = QFormLayout(sfg)
        sff.setContentsMargins(14, 16, 14, 8)
        sff.setSpacing(8)
        self.sf_path_label = QLabel(self._stockfish_path or "Not found")
        self.sf_path_label.setWordWrap(True)
        self.sf_path_label.setTextInteractionFlags(Qt.TextSelectableByMouse)
        self.sf_path_label.setStyleSheet(
            f"color:{'#5eb85e' if self._stockfish_path else '#d04848'};"
            "font-size:11px;"
        )
        sff.addRow("Path", self.sf_path_label)
        self.sf_browse_btn = QPushButton("Browse…")
        self.sf_browse_btn.setFixedWidth(70)
        self.sf_browse_btn.setStyleSheet(_BTN_BROWSE_SS)
        self.sf_browse_btn.clicked.connect(self._browse_stockfish)
        sff.addRow("", self.sf_browse_btn)
        sl.addWidget(sfg)

        # Output
        og = QGroupBox("OUTPUT")
        og.setStyleSheet(_SETTINGS_GROUP_SS)
        of = QFormLayout(og)
        of.setContentsMargins(14, 16, 14, 8)
        of.setSpacing(8)
        self.output_folder_edit = QLineEdit(DEFAULT_OUTPUT_DIR)
        out_row = QHBoxLayout()
        out_row.addWidget(self.output_folder_edit, 1)
        self.output_browse_btn = QPushButton("Browse…")
        self.output_browse_btn.setFixedWidth(70)
        self.output_browse_btn.setStyleSheet(_BTN_BROWSE_SS)
        self.output_browse_btn.clicked.connect(self._browse_output_folder)
        out_row.addWidget(self.output_browse_btn)
        of.addRow("Folder", out_row)
        sl.addWidget(og)

        sl.addStretch()
        settings_scroll.setWidget(sc)
        self.tab_widget.addTab(settings_scroll, "⚙  Settings")

        # ──────── Tab 3: Export ───────────────────────────────
        export_scroll = QScrollArea()
        export_scroll.setWidgetResizable(True)
        export_scroll.setFrameShape(QFrame.NoFrame)
        export_scroll.setStyleSheet(
            "QScrollArea{background:transparent;border:none;}"
        )

        export_tab = QWidget()
        export_tab.setStyleSheet(_SETTINGS_CONTROL_SS)
        el = QVBoxLayout(export_tab)
        el.setContentsMargins(16, 20, 16, 16)
        el.setSpacing(14)

        # Video settings
        eg = QGroupBox("VIDEO")
        eg.setStyleSheet(_SETTINGS_GROUP_SS)
        ef = QFormLayout(eg)
        ef.setContentsMargins(14, 16, 14, 8)
        ef.setSpacing(8)
        self.resolution_combo = QComboBox()
        self.resolution_combo.addItems(RESOLUTION_LIST)
        self.fps_spin = QSpinBox()
        self.fps_spin.setRange(1, 60)
        self.fps_spin.setValue(DEFAULT_VIDEO_FPS)
        self.fps_spin.setSuffix(" fps")
        ef.addRow("Resolution", self.resolution_combo)
        ef.addRow("Frame rate", self.fps_spin)
        el.addWidget(eg)

        # Timing
        tg = QGroupBox("TIMING")
        tg.setStyleSheet(_SETTINGS_GROUP_SS)
        tf = QFormLayout(tg)
        tf.setContentsMargins(14, 16, 14, 8)
        tf.setSpacing(8)
        self.move_duration_spin = QDoubleSpinBox()
        self.move_duration_spin.setRange(0.5, 15.0)
        self.move_duration_spin.setValue(DEFAULT_MOVE_DURATION)
        self.move_duration_spin.setSuffix(" s")
        self.move_duration_spin.setSingleStep(0.5)
        self.move_duration_spin.setDecimals(1)
        tf.addRow("Per move", self.move_duration_spin)

        self.anim_duration_spin = QDoubleSpinBox()
        self.anim_duration_spin.setRange(0.1, 3.0)
        self.anim_duration_spin.setValue(DEFAULT_ANIM_DURATION)
        self.anim_duration_spin.setSuffix(" s")
        self.anim_duration_spin.setSingleStep(0.1)
        self.anim_duration_spin.setDecimals(1)
        tf.addRow("Animation", self.anim_duration_spin)

        self.title_duration_spin = QDoubleSpinBox()
        self.title_duration_spin.setRange(0.0, 10.0)
        self.title_duration_spin.setValue(DEFAULT_TITLE_DURATION)
        self.title_duration_spin.setSuffix(" s")
        self.title_duration_spin.setSingleStep(0.5)
        self.title_duration_spin.setDecimals(1)
        tf.addRow("Title card", self.title_duration_spin)

        self.result_duration_spin = QDoubleSpinBox()
        self.result_duration_spin.setRange(0.0, 15.0)
        self.result_duration_spin.setValue(DEFAULT_RESULT_DURATION)
        self.result_duration_spin.setSuffix(" s")
        self.result_duration_spin.setSingleStep(0.5)
        self.result_duration_spin.setDecimals(1)
        tf.addRow("Result card", self.result_duration_spin)
        el.addWidget(tg)

        # Features
        fg = QGroupBox("FEATURES")
        fg.setStyleSheet(_SETTINGS_GROUP_SS)
        ff = QFormLayout(fg)
        ff.setContentsMargins(14, 16, 14, 8)
        ff.setSpacing(8)
        self.show_title_check = QCheckBox("Title screen")
        self.show_title_check.setChecked(True)
        ff.addRow("", self.show_title_check)
        self.show_result_check = QCheckBox("Result screen")
        self.show_result_check.setChecked(True)
        ff.addRow("", self.show_result_check)
        el.addWidget(fg)

        # Estimated duration
        self.estimate_label = QLabel("")
        self.estimate_label.setStyleSheet(
            "color:#5b8fd4; font-size:11px; font-weight:600; padding:4px;"
        )
        self._update_export_estimate()
        self.move_duration_spin.valueChanged.connect(self._update_export_estimate)
        self.title_duration_spin.valueChanged.connect(self._update_export_estimate)
        self.result_duration_spin.valueChanged.connect(self._update_export_estimate)
        self.show_title_check.toggled.connect(self._update_export_estimate)
        self.show_result_check.toggled.connect(self._update_export_estimate)
        el.addWidget(self.estimate_label)

        # Export button
        self.export_btn = QPushButton("🎬  Export to MP4")
        self.export_btn.setMinimumHeight(42)
        self.export_btn.setStyleSheet(_BTN_EXPORT_SS)
        self.export_btn.clicked.connect(self._export_mp4)
        el.addWidget(self.export_btn)

        self.export_progress_label = QLabel("")
        self.export_progress_label.setAlignment(Qt.AlignCenter)
        self.export_progress_label.setStyleSheet(
            "color:#58586a; font-size:11px;"
        )
        el.addWidget(self.export_progress_label)

        el.addStretch()
        export_scroll.setWidget(export_tab)
        self.tab_widget.addTab(export_scroll, "🎬  Export")

        right_layout.addWidget(self.tab_widget)

        # Status
        sep = QFrame()
        sep.setFrameShape(QFrame.HLine)
        sep.setStyleSheet("color:#2a2a30;")
        right_layout.addWidget(sep)
        self.status_label = QLabel("Ready")
        self.status_label.setStyleSheet(
            "padding:4px 2px; color:#58586a; font-size:11px;"
        )
        right_layout.addWidget(self.status_label)

        main_layout.addLayout(right_layout, 2)

        # Initialize ranges/tooltips on startup
        self._on_engine_changed(self.white_ai_combo, self.white_depth_spin)
        self._on_engine_changed(self.black_ai_combo, self.black_depth_spin)

        self._update_player_labels()

    def _update_export_estimate(self):
        n = len(self._move_list)
        move_dur = self.move_duration_spin.value()
        title_dur = self.title_duration_spin.value() if self.show_title_check.isChecked() else 0
        result_dur = self.result_duration_spin.value() if self.show_result_check.isChecked() else 0
        total = title_dur + n * move_dur + result_dur
        mins = int(total // 60)
        secs = int(total % 60)
        self.estimate_label.setText(
            f"⏱  Estimated duration: {mins}:{secs:02d}  ({n} moves × {move_dur:.1f}s)"
        )

    def _apply_tab_style(self):
        self.tab_widget.setStyleSheet("""
            QTabWidget::pane {
                border: none; border-radius: 8px;
                background-color: #262628;
            }
            QTabBar::tab {
                background: transparent; color: #58586a;
                border: none; border-bottom: 2px solid transparent;
                padding: 8px 18px; margin-right: 2px;
                font-size: 11px; font-weight: 600;
            }
            QTabBar::tab:selected {
                color: #c8c8d0; border-bottom-color: #5b8fd4;
            }
            QTabBar::tab:hover:!selected {
                color: #888898; border-bottom-color: #3a3a44;
            }
        """)

    # ── Settings callbacks ────────────────────────────────────
    def _on_volume(self, v):
        self.vol_lbl.setText(f"{v}%")
        self.sound_engine.set_volume(v / 100.0)

    def _on_anim_speed(self, v):
        self.anim_speed_lbl.setText(f"{v} ms")
        self.board_widget.set_anim_duration(v)

    def _browse_stockfish(self):
        filt = (
            "Executables (*.exe);;All Files (*)"
            if sys.platform == "win32" else "All Files (*)"
        )
        path, _ = QFileDialog.getOpenFileName(self, "Stockfish", "", filt)
        if path:
            self._stockfish_path = path
            self.sf_path_label.setText(path)
            self.sf_path_label.setStyleSheet(
                "color:#5eb85e; font-size:11px;"
            )

    def _browse_output_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Output Folder")
        if folder:
            self.output_folder_edit.setText(folder)

    # ── Game controls ─────────────────────────────────────────
    def _start_game(self):
        if self._game_thread and self._game_thread.isRunning():
            return

        # Validate Stockfish selection
        w_type = self.white_ai_combo.currentData()
        b_type = self.black_ai_combo.currentData()
        if (w_type == 2 or b_type == 2) and not self._stockfish_path:
            QMessageBox.warning(
                self, "Stockfish Not Found",
                "Stockfish is selected but the path is not configured.\n"
                "Please browse to the Stockfish executable in Settings."
            )
            return

        self._reset_game()
        self.status_label.setText("Game running…")
        self.start_btn.setEnabled(False)
        self.stop_btn.setEnabled(True)

        wt = AI_SHORT_NAMES.get(self.white_ai_combo.currentData(), "AI")
        bt = AI_SHORT_NAMES.get(self.black_ai_combo.currentData(), "AI")
        wd = self.white_depth_spin.value()
        bd = self.black_depth_spin.value()
        logger.info("Starting game: White=%s (depth %d) vs Black=%s (depth %d)",
                     wt, wd, bt, bd)

        self._game_thread = QThread()
        self._game_worker = GameWorker(
            white_type=self.white_ai_combo.currentData(),
            white_depth=self.white_depth_spin.value(),
            black_type=self.black_ai_combo.currentData(),
            black_depth=self.black_depth_spin.value(),
            stockfish_path=self._stockfish_path,
            move_delay=self.move_delay_spin.value(),
        )
        self._game_worker.moveToThread(self._game_thread)
        self._game_thread.started.connect(self._game_worker.run)
        self._game_worker.move_made.connect(self._on_move_made)
        self._game_worker.game_over.connect(self._on_game_over)
        self._game_worker.error.connect(self._on_error)
        self._game_worker.finished.connect(self._on_game_finished)
        self._game_thread.start()

    def _stop_game(self):
        if self._game_worker:
            self._game_worker.stop()
        self.status_label.setText("Stopped.")

    def _reset_game(self):
        if self._game_worker:
            self._game_worker.stop()
            try:
                self._game_worker.move_made.disconnect(self._on_move_made)
                self._game_worker.game_over.disconnect(self._on_game_over)
                self._game_worker.error.disconnect(self._on_error)
                self._game_worker.finished.disconnect(self._on_game_finished)
            except RuntimeError:
                pass
        if self._game_thread and self._game_thread.isRunning():
            self._game_thread.quit()
            self._game_thread.wait(3000)
        self._game_thread = None
        self._game_worker = None

        self._board.reset()
        self._move_list.clear()
        self._move_qualities.clear()
        self._eval_cp = 0.0
        self._game_state = GAME_NORMAL
        self._game_result = ""
        self._game_detail = ""
        self._analyzer.reset()

        self.board_widget.set_board(self._board)
        self.board_widget.set_move_quality(MQ_GOOD)
        self.move_list_widget.clear()
        self.eval_bar.set_eval(0.0)
        self.eval_bar.reset_game_state()
        self.quality_label.setText("")
        self.quality_label.setStyleSheet("")
        self.status_label.setText("Ready")
        self.start_btn.setEnabled(True)
        self.stop_btn.setEnabled(False)
        self._update_export_estimate()

    # ── Game callbacks ────────────────────────────────────────
    def _on_move_made(self, board, move, eval_cp, nodes, policy,
                      game_state, result, detail):
        self._board = board
        self._game_state = game_state
        self._game_result = result
        self._game_detail = detail

        prev_board = board.copy()
        prev_board.pop()
        is_white = (prev_board.turn == chess.WHITE)
        quality = self._analyzer.push(eval_cp, is_white, prev_board, move)
        self._move_qualities.append(quality)
        self._eval_cp = eval_cp

        san = prev_board.san(move)
        self._move_list.append(san)

        self.board_widget.animate_move(move)
        QTimer.singleShot(
            350,
            lambda b=self._board.copy(), m=move: self.board_widget.set_board(b, m),
        )
        self.board_widget.set_move_quality(quality)

        self.move_list_widget.add_move(san, quality)
        self.eval_bar.set_eval(eval_cp)

        if game_state != GAME_NORMAL:
            self.eval_bar.set_game_state(game_state, result, detail)

        self.sound_engine.play_move_sound(prev_board, move)

        # ── Dramatic quality label ────────────────────────────
        icon = MQ_ICONS.get(quality, "")
        lbl = MQ_LABELS.get(quality, "")
        color = MQ_COLORS.get(quality, QColor(150, 150, 150)).name()

        if quality in MQ_SHOW_BADGE:
            # Brilliant or Blunder — dramatic display
            quality_txt = f"{icon}  {lbl}" if icon else lbl
            self.quality_label.setText(f"  {quality_txt}  ")
            self.quality_label.setStyleSheet(
                f"font-size:15px; font-weight:bold; padding:6px 12px; "
                f"color:white; background-color:{color}; "
                f"border-radius:6px; border:2px solid rgba(255,255,255,60);"
            )
        elif quality == MQ_MISTAKE:
            quality_txt = f"{icon}  {lbl}" if icon else lbl
            self.quality_label.setText(f"  {quality_txt}  ")
            self.quality_label.setStyleSheet(
                f"font-size:13px; font-weight:bold; padding:4px 10px; "
                f"color:{color}; "
                f"background-color:rgba(230,140,30,30); "
                f"border-radius:4px; border:1px solid {color};"
            )
        elif quality == MQ_GREAT:
            quality_txt = f"{icon}  {lbl}" if icon else lbl
            self.quality_label.setText(f"  {quality_txt}  ")
            self.quality_label.setStyleSheet(
                f"font-size:13px; font-weight:bold; padding:4px 10px; "
                f"color:{color}; "
                f"background-color:rgba(50,170,80,25); "
                f"border-radius:4px; border:1px solid {color};"
            )
        else:
            # Good/Best/Inaccuracy/Book
            if quality == MQ_INACCURACY:
                quality_txt = f"{icon}  {lbl}" if icon else lbl
                self.quality_label.setText(quality_txt)
                self.quality_label.setStyleSheet(
                    f"font-size:11px; font-weight:600; padding:4px; "
                    f"color:{color};"
                )
            else:
                self.quality_label.setText("")
                self.quality_label.setStyleSheet("")

        # Status
        eval_str = (
            f"M{int(abs(eval_cp) - 10000)}" if abs(eval_cp) > 9000
            else f"{eval_cp / 100.0:+.2f}"
        )
        icon_str = f" {icon}" if icon else ""
        self.status_label.setText(
            f"Move {len(self._move_list)}: {san}{icon_str}  |  Eval: {eval_str}"
        )

        self._update_export_estimate()

    def _on_game_over(self, state, result, detail):
        self.status_label.setText(f"Game Over: {detail} ({result})")
        self.sound_engine.play_game_end(state)
        self._update_export_estimate()

    def _on_error(self, msg):
        logger.error("Error: %s", msg)
        self.status_label.setText(f"Error: {msg}")
        self.start_btn.setEnabled(True)
        self.stop_btn.setEnabled(False)

    def _on_game_finished(self):
        if self._game_thread:
            self._game_thread.quit()
            self._game_thread.wait()
        self.start_btn.setEnabled(True)
        self.stop_btn.setEnabled(False)

    # ── Theme ─────────────────────────────────────────────────
    def _change_theme(self, name):
        t = THEMES.get(name)
        if t:
            self.board_widget.set_theme(t)

    # ── Export ────────────────────────────────────────────────
    def _export_mp4(self):
        if not self._move_list:
            self.status_label.setText("No moves to export.")
            return

        output_dir = self.output_folder_edit.text().strip() or DEFAULT_OUTPUT_DIR
        try:
            os.makedirs(output_dir, exist_ok=True)
        except OSError as e:
            self.status_label.setText(f"Cannot create folder: {e}")
            return

        default_path = os.path.join(output_dir, "chess_game.mp4")
        save_path, _ = QFileDialog.getSaveFileName(
            self, "Save Video", default_path, "MP4 (*.mp4);;All (*)"
        )
        if not save_path:
            return

        pgn = self._generate_pgn()
        wn, bn = self._get_player_names()
        wi, bi = self._get_player_info()

        res = self.resolution_combo.currentText()
        fps = self.fps_spin.value()
        logger.info("Exporting MP4: path=%s, resolution=%s, fps=%d, moves=%d",
                     save_path, res, fps, len(self._move_list))

        self._export_thread = QThread()
        self._export_worker = ExportWorker(
            pgn_text=pgn,
            save_path=save_path,
            resolution_key=res,
            fps=fps,
            board_theme=THEMES.get(self.theme_combo.currentText()),
            white_name=wn,
            black_name=bn,
            white_engine_info=wi,
            black_engine_info=bi,
            eval_history=self._analyzer.evals,
            move_qualities=self._move_qualities,
            move_duration=self.move_duration_spin.value(),
            anim_duration=self.anim_duration_spin.value(),
            title_duration=self.title_duration_spin.value(),
            result_duration=self.result_duration_spin.value(),
            show_title=self.show_title_check.isChecked(),
            show_result=self.show_result_check.isChecked(),
            sound_engine=self.sound_engine,
        )
        self._export_worker.moveToThread(self._export_thread)
        self._export_thread.started.connect(self._export_worker.run)
        self._export_worker.progress.connect(self._on_export_progress)
        self._export_worker.finished.connect(self._on_export_finished)
        self._export_worker.error.connect(self._on_error)

        self.export_btn.setEnabled(False)
        self.export_progress_label.setText("Preparing…")
        self._export_thread.start()

    def _on_export_progress(self, v):
        self.export_progress_label.setText(f"Rendering… {v}%")
        self.status_label.setText(f"Exporting… {v}%")

    def _on_export_finished(self, path):
        self.export_btn.setEnabled(True)
        self.export_progress_label.setText("")
        if self._export_thread:
            self._export_thread.quit()
            self._export_thread.wait()
        self._export_worker = None
        if path:
            self.status_label.setText(f"✓ Export complete: {path}")
            logger.info("Export complete: %s", path)
        else:
            self.status_label.setText("Export cancelled.")

    def _generate_pgn(self):
        wn, bn = self._get_player_names()
        game = chess.pgn.Game()
        game.headers["White"] = wn
        game.headers["Black"] = bn
        game.headers["Result"] = self._game_result or "*"
        node = game
        tb = chess.Board()
        for san in self._move_list:
            move = tb.parse_san(san)
            node = node.add_variation(move)
            tb.push(move)
        return str(game)


# ════════════════════════════════════════════════════════════════════
#  Entry Point
# ════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    app = QApplication(sys.argv)

    pal = QPalette()
    pal.setColor(QPalette.Window,          QColor(38, 38, 40))
    pal.setColor(QPalette.WindowText,      QColor(200, 200, 208))
    pal.setColor(QPalette.Base,            QColor(28, 28, 32))
    pal.setColor(QPalette.AlternateBase,   QColor(38, 38, 40))
    pal.setColor(QPalette.ToolTipBase,     QColor(28, 28, 32))
    pal.setColor(QPalette.ToolTipText,     QColor(200, 200, 208))
    pal.setColor(QPalette.Text,            QColor(200, 200, 208))
    pal.setColor(QPalette.Button,          QColor(38, 38, 40))
    pal.setColor(QPalette.ButtonText,      QColor(200, 200, 208))
    pal.setColor(QPalette.BrightText,      QColor(255, 55, 55))
    pal.setColor(QPalette.Link,            QColor(91, 143, 212))
    pal.setColor(QPalette.Highlight,       QColor(91, 143, 212))
    pal.setColor(QPalette.HighlightedText, QColor(0, 0, 0))
    app.setPalette(pal)

    window = MainWindow()
    window.show()
    logger.info("Window shown — entering main event loop")
    sys.exit(app.exec())