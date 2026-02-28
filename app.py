#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PDF / 画像 OCR 付加バッチ（日本語向け / NDLOCR-Lite版）
[v62 original-PDF overlay fix: detach shared /Contents before per-page invisible-text merge]
- 指定ファイルまたは指定フォルダ内の PDF / 画像ファイルを処理
- PDF は既にテキスト層がある場合スキップ
- PDF はページ画像へ分解し、NDLOCR-Lite を --sourcedir で実行
- 画像も一時フォルダへ集約し、NDLOCR-Lite を --sourcedir で実行
- OCR 結果（JSON / XML / TXT を優先的に探索）から検索可能 PDF を再生成
- PDF入力は元PDFを保持し、不可視OCRテキストのみを重畳
- 同名のOCR出力がある場合は、設定に応じて上書きまたは `_ocr_001.pdf` のように連番保存

想定コマンドテンプレート既定値:
    --sourcedir "{input_dir}" --output "{output_dir}"

プレースホルダ:
    {input}       : 単一ページ時の画像パス（互換用）
    {input_dir}   : NDLOCR-Lite に渡す画像格納フォルダ
    {output_dir}  : NDLOCR-Lite の出力先フォルダ
    {output_pdf}  : 最終的にアプリが生成する PDF パス（NDLOCR 側では通常未使用）
    {output_stem} : 出力 PDF の拡張子抜きパス
"""

from __future__ import annotations

import csv
import io
import os
import queue
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
except Exception as e:  # pragma: no cover
    raise SystemExit(f"Tkinter の読み込みに失敗しました: {e}")

try:
    from PIL import Image
except Exception:
    Image = None  # type: ignore

try:
    import pypdfium2 as pdfium
except Exception:
    pdfium = None  # type: ignore

try:
    from pypdf import PdfReader, PdfWriter
    from pypdf.generic import DecodedStreamObject, NameObject
except Exception:
    PdfReader = None  # type: ignore
    DecodedStreamObject = None  # type: ignore
    NameObject = None  # type: ignore

try:
    from reportlab.lib.utils import ImageReader
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.cidfonts import UnicodeCIDFont
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.pdfgen import canvas
except Exception:
    ImageReader = None  # type: ignore
    pdfmetrics = None  # type: ignore
    UnicodeCIDFont = None  # type: ignore
    TTFont = None  # type: ignore
    canvas = None  # type: ignore

APP_TITLE = "PDF / 画像 OCR 付加バッチ（日本語 / NDLOCR-Lite）"
PYTHON_EXECUTABLE_LABEL = "Python実行ファイル"
NDLOCR_COMMAND_LABEL = "NDLOCR-Lite起動コマンド"
OUTPUT_SUFFIX = "_ocr"
GENERATED_INPUT_NAME_RE = re.compile(rf"{re.escape(OUTPUT_SUFFIX)}(?:_\d{{3,}})?$", re.IGNORECASE)
DEFAULT_NDLOCR_TIMEOUT_SEC = 60 * 60
DEFAULT_COMMAND_TEMPLATE = '--sourcedir "{input_dir}" --output "{output_dir}"'
DEFAULT_PDF_RENDER_DPI = 200
DEFAULT_IMAGE_DPI = 150
# PDF入力時の既定は「元PDF保持 + 不可視テキスト重畳」。
# ただし従来の「複数ページの重畳PDFを一括 merge」では、環境によって
# 同一OCR層が全ページへ重なる事例があったため、現在は「1ページずつ重畳PDFを生成し、
# そのページだけへ merge する」方式に変更している。
# 必要時のみ安全側の画像背景再構築へ切り替えられるよう、定数は残す。
PREFER_IMAGE_REBUILD_FOR_PDF = False
MIN_TEXT_LAYER_CHARS = 10
DEFAULT_TEXT_LAYER_CHECK_PAGES = 20
MIN_TEXT_SHOW_OPS = 1
SUPPORTED_IMAGE_SUFFIXES = {".png", ".jpg", ".jpeg", ".bmp", ".tif", ".tiff", ".webp"}
SUPPORTED_INPUT_SUFFIXES = {".pdf", *SUPPORTED_IMAGE_SUFFIXES}
INPUT_KIND_PDF = "pdf"
INPUT_KIND_IMAGE = "image"
JSON_EXTS = {".json", ".jsonl"}
XML_EXTS = {".xml", ".alto", ".page.xml"}
TEXT_EXTS = {".txt"}
DEFAULT_CJK_FONT = "HeiseiKakuGo-W5"
DEFAULT_WINDOW_GEOMETRY = "1060x580"
DEFAULT_STATUS_TEXT = "待機中"
DEFAULT_PROGRESS_TEXT = "0 / 0"
DEFAULT_RUNTIME_NOTICE_TEXT = ""
DEFAULT_PROGRESS_MAX = 100
DEFAULT_UI_PAD_X = 8
DEFAULT_UI_PAD_Y = 6
DEFAULT_LOG_TEXT_HEIGHT = 8
DEFAULT_RUNTIME_NOTICE_WRAPLENGTH = 760
DEFAULT_RUN_SUMMARY_TEXT = "まだ実行していません。\n設定を確認してから「OCR処理を開始」を押してください。"
DEFAULT_DETAIL_TOGGLE_SHOW_TEXT = "詳細設定を開く"
DEFAULT_DETAIL_TOGGLE_HIDE_TEXT = "詳細設定を閉じる"
DEFAULT_LOG_PUMP_INTERVAL_MS = 100
DEFAULT_STARTUP_DEP_CHECK_DELAY_MS = 200
DEFAULT_RUNTIME_NOTICE_COLOR = "#8a5a00"
DEFAULT_LOG_COLORS = {
    "INFO": "#000000",
    "WARN": "#b36b00",
    "ERROR": "#b00020",
    "DONE": "#006400",
}

SETTING_SOURCE_SAVED = "saved"
SETTING_SOURCE_MANUAL = "manual"
SETTING_SOURCE_AUTO = "auto"
SETTING_SOURCE_DEFAULT = "default"

OUTPUT_MODE_SAME_FOLDER = "same_folder"
OUTPUT_MODE_INPUT_FOLDER = "input_folder"
OUTPUT_MODE_CUSTOM_FOLDER = "custom_folder"
OUTPUT_CONFLICT_RENAME = "rename_with_number"
OUTPUT_CONFLICT_OVERWRITE = "overwrite_existing_ocr_output"


CLI_SCRIPT_CANDIDATES = (
    Path(r"C:/ndlocr-lite/src/ocr.py"),
    Path.cwd() / "ndlocr-lite" / "src" / "ocr.py",
    Path(__file__).resolve().parent / "ndlocr-lite" / "src" / "ocr.py",
)


def normalize_output_conflict_mode(mode: str) -> str:
    normalized = (mode or "").strip().lower()
    if normalized == OUTPUT_CONFLICT_OVERWRITE:
        return OUTPUT_CONFLICT_OVERWRITE
    return OUTPUT_CONFLICT_RENAME


def describe_output_conflict_mode(mode: str) -> str:
    normalized = normalize_output_conflict_mode(mode)
    if normalized == OUTPUT_CONFLICT_OVERWRITE:
        return "既存のOCR出力を上書き"
    return "連番を付けて保存"


def determine_default_engine_and_template() -> tuple[str, str]:
    for script_path in CLI_SCRIPT_CANDIDATES:
        try:
            if script_path.exists() and script_path.is_file():
                return str(Path(sys.executable)), f'{script_path} --sourcedir {{input_dir}} --output {{output_dir}}'
        except Exception:
            continue

    for name in RuntimeSupport.LAUNCHER_BASENAMES:  # type: ignore[name-defined]
        try:
            hit = shutil.which(name)
        except Exception:
            hit = None
        if hit:
            return hit, DEFAULT_COMMAND_TEMPLATE

    return "", DEFAULT_COMMAND_TEMPLATE


@dataclass
class ProcessResult:
    total: int = 0
    skipped_has_text: int = 0
    skipped_name_rule: int = 0
    processed: int = 0
    errors: int = 0


@dataclass(frozen=True)
class RunExecutionSettings:
    ndlocr_timeout_sec: int = DEFAULT_NDLOCR_TIMEOUT_SEC
    render_dpi: int = DEFAULT_PDF_RENDER_DPI


@dataclass(frozen=True)
class RunConfig:
    folder: Path
    recursive: bool
    overwrite: bool
    output_conflict_mode: str
    output_mode: str
    custom_output_dir: Optional[Path]
    write_csv_log: bool
    engine_path: str
    command_template: str
    execution: RunExecutionSettings = field(default_factory=RunExecutionSettings)


@dataclass(frozen=True)
class RunSummary:
    started_at: datetime
    ended_at: datetime
    result: ProcessResult
    was_stopped: bool


@dataclass(frozen=True)
class BatchRunOutcome:
    final_status: str
    ui_current: int
    ui_total: int


@dataclass(frozen=True)
class FinishUiState:
    status: str
    current: int
    total: int


@dataclass(frozen=True)
class ProgressUiState:
    status: str
    current: int
    total: int


@dataclass(frozen=True)
class StartupDependencyPresentation:
    notice: str
    log_entries: tuple[LogEntry, ...]


@dataclass(frozen=True)
class BatchCompletionPresentation:
    final_log_kind: str
    final_log_message: str
    outcome: BatchRunOutcome


@dataclass(frozen=True)
class LogEntry:
    kind: str
    message: str


@dataclass(frozen=True)
class StartRunPlan:
    run_config: RunConfig
    startup_log_message: str
    pre_logs: tuple[LogEntry, ...]
    launcher_display: str


@dataclass(frozen=True)
class GuiTextInputState:
    current_value: str
    baseline_value: str
    baseline_source: str


@dataclass(frozen=True)
class StartRunRequest:
    folder_str: str
    recursive: bool
    output_conflict_mode: str
    output_mode: str
    custom_output_folder_str: str
    write_csv_log: bool
    engine_path_input: GuiTextInputState
    command_template_input: GuiTextInputState


@dataclass(frozen=True)
class ResolvedTextSetting:
    value: str
    source: str


@dataclass(frozen=True)
class ResolvedStartRunSettings:
    folder: Path
    recursive: bool
    overwrite: bool
    output_conflict_mode: str
    output_mode: str
    custom_output_folder: Optional[Path]
    write_csv_log: bool
    engine_path_input: ResolvedTextSetting
    command_template: ResolvedTextSetting


@dataclass(frozen=True)
class PreparationIssue:
    user_message: str
    detail: str


@dataclass(frozen=True)
class StartRunPreparationResult:
    ok: bool
    plan: Optional[StartRunPlan] = None
    issue: Optional[PreparationIssue] = None


@dataclass(frozen=True)
class RuntimeIssue:
    user_message: str
    log_detail: str


@dataclass(frozen=True)
class StartUiState:
    status: str
    current: int
    total: int


@dataclass
class CsvLogRow:
    timestamp: str
    input: str
    output: str = ""
    action: str = ""
    detail: str = ""
    engine_path: str = ""
    command_template: str = ""
    seconds: str = ""

    def to_csv_record(self, headers: Iterable[str]) -> list[str]:
        return [str(getattr(self, header, "")) for header in headers]


class SettingPrecedencePolicy:
    TEXT_INPUT_PRIORITY = (
        SETTING_SOURCE_MANUAL,
        SETTING_SOURCE_SAVED,
        SETTING_SOURCE_AUTO,
        SETTING_SOURCE_DEFAULT,
    )

    @classmethod
    def normalize_source(cls, source: str) -> str:
        normalized = (source or "").strip().lower()
        if normalized in cls.TEXT_INPUT_PRIORITY:
            return normalized
        return SETTING_SOURCE_DEFAULT


class TextSettingResolver:
    def resolve(self, input_state: GuiTextInputState) -> ResolvedTextSetting:
        current_value = (input_state.current_value or "").strip()
        baseline_value = (input_state.baseline_value or "").strip()
        baseline_source = SettingPrecedencePolicy.normalize_source(input_state.baseline_source)

        if current_value:
            if current_value == baseline_value:
                return ResolvedTextSetting(value=current_value, source=baseline_source)
            return ResolvedTextSetting(value=current_value, source=SETTING_SOURCE_MANUAL)

        if baseline_value:
            return ResolvedTextSetting(value=baseline_value, source=baseline_source)

        return ResolvedTextSetting(value="", source=baseline_source)


class LogMessageBuilder:
    @staticmethod
    def tagged(tag: str, message: str) -> str:
        return f"[{tag}] {message}"

    @classmethod
    def dependency_ok(cls) -> str:
        return "依存関係チェック: OK（NDLOCR-Lite / PDF・画像対応）"

    @staticmethod
    def _source_label(source: str) -> str:
        normalized = SettingPrecedencePolicy.normalize_source(source)
        labels = {
            SETTING_SOURCE_SAVED: "保存値",
            SETTING_SOURCE_MANUAL: "手動指定",
            SETTING_SOURCE_AUTO: "自動決定",
            SETTING_SOURCE_DEFAULT: "既定値",
        }
        return labels.get(normalized, "既定値")

    @classmethod
    def engine_selection(cls, launcher_display: str, *, source: str) -> LogEntry:
        return LogEntry("INFO", f"{PYTHON_EXECUTABLE_LABEL}（{cls._source_label(source)}）: {launcher_display}")

    @classmethod
    def command_template(cls, command_template: str, *, source: str) -> LogEntry:
        return LogEntry("INFO", f"{NDLOCR_COMMAND_LABEL}（{cls._source_label(source)}）: {command_template}")

    @classmethod
    def output_destination(cls, output_mode: str, custom_output_dir: Optional[Path] = None) -> LogEntry:
        return LogEntry("INFO", f"出力先: {describe_output_destination(output_mode, custom_output_dir)}")

    @classmethod
    def input_formats(cls) -> LogEntry:
        return LogEntry("INFO", f"入力対象: PDF / 画像 ({', '.join(sorted(SUPPORTED_INPUT_SUFFIXES))})")

    @classmethod
    def run_option_output_conflict(cls, output_conflict_mode: str) -> LogEntry:
        message = f"OCR出力の競合時の動作: {describe_output_conflict_mode(output_conflict_mode)}"
        return LogEntry("INFO", message)

    @classmethod
    def processing_start(cls, launcher_display: str) -> str:
        return f"処理を開始します。（エンジン: NDLOCR-Lite / {PYTHON_EXECUTABLE_LABEL}: {launcher_display}）"

    @classmethod
    def skip_name(cls, file_name: str) -> LogEntry:
        return LogEntry("INFO", cls.tagged("SKIP:name", file_name))

    @classmethod
    def skip_has_text(cls, file_name: str) -> LogEntry:
        return LogEntry("INFO", cls.tagged("SKIP:text", f"既にテキスト層あり: {file_name}"))

    @classmethod
    def overwrite(cls, output_name: str) -> LogEntry:
        return LogEntry("WARN", cls.tagged("OVERWRITE", f"既存のOCR出力を上書き: {output_name}"))

    @classmethod
    def rename(cls, output_name: str) -> LogEntry:
        return LogEntry("INFO", cls.tagged("RENAME", f"既存のOCR出力があるため連番保存: {output_name}"))

    @classmethod
    def ocr_start(cls, source_name: str, output_name: str) -> str:
        return cls.tagged("OCR", f"{source_name} -> {output_name}")

    @classmethod
    def output_done(cls, output_path: Path) -> str:
        return cls.tagged("DONE", str(output_path))

    @classmethod
    def stopped(cls, source_name: str, detail: str) -> str:
        return cls.tagged("STOPPED", f"{source_name}: {detail}")

    @classmethod
    def item_error(cls, source_name: str, detail: str) -> str:
        return cls.tagged("ERROR", f"{source_name}: {detail}")

    @classmethod
    def csv_path(cls, csv_path: Path) -> str:
        return cls.tagged("LOG", f"CSVログ出力: {csv_path}")

    @classmethod
    def csv_done(cls, csv_path: Path) -> str:
        return cls.tagged("LOG", str(csv_path))

    @classmethod
    def csv_error(cls, detail: str) -> str:
        return cls.tagged("LOG-ERROR", f"CSVログ出力に失敗: {detail}")

    @classmethod
    def no_inputs_found(cls) -> str:
        return "PDF / 画像ファイルが見つかりませんでした。"

    @classmethod
    def target_count(cls, total: int, *, recursive: bool, target_kind: str) -> str:
        recursive_label = "有効" if recursive else "無効"
        return f"対象ファイル数: {total}（対象種別: {target_kind} / 再帰: {recursive_label}）"

    @classmethod
    def input_scope(cls, *, target_kind: str, recursive: bool) -> str:
        if target_kind == "file":
            return cls.tagged("INPUT", "単一ファイル指定（再帰設定は無効）")
        recursive_label = "有効" if recursive else "無効"
        return cls.tagged("INPUT", f"フォルダ指定（再帰: {recursive_label}）")

    @classmethod
    def stop_requested(cls) -> str:
        return "停止要求を受け付けました（可能な範囲で速やかに停止します）。"

    @classmethod
    def stop_interrupted(cls) -> str:
        return "停止要求により処理を中断しました。"

    @classmethod
    def prep_pdf_split(cls, pdf_name: str, page_count: int) -> str:
        return cls.tagged("PREP", f"PDF分解: {pdf_name} -> {page_count}ページ")

    @classmethod
    def prep_image_input(cls, image_name: str) -> str:
        return cls.tagged("PREP", f"画像入力: {image_name}")

    @classmethod
    def command_line(cls, command_line: str) -> str:
        return cls.tagged("CMD", command_line)

    @classmethod
    def ndlocr_output_count(cls, file_count: int) -> str:
        return cls.tagged("NDLOCR", f"出力生成物数: {file_count}")

    @classmethod
    def parse_warning(cls, path_name: str, detail: str) -> str:
        return cls.tagged("PARSE", f"{path_name}: {detail}")

    @classmethod
    def parse_low_coverage(cls) -> str:
        return cls.tagged("PARSE", "OCR結果の取り込み量が少なすぎます。NDLOCR-Lite の出力形式とパーサの対応不足の可能性があります。")

    @classmethod
    def parse_summary(cls, *, total_tokens: int, total_texts: int, structured_hits: int, text_hits: int) -> str:
        return cls.tagged(
            "PARSE",
            f"tokens={total_tokens} / text_blocks={total_texts} / structured_files={structured_hits} / txt_files={text_hits}",
        )

    @classmethod
    def font_embedded(cls, font_name: str) -> str:
        return cls.tagged("FONT", f"埋め込みフォント: {font_name}")

    @classmethod
    def font_cid(cls, font_name: str) -> str:
        return cls.tagged("FONT", f"CID フォントを使用: {font_name}")

    @classmethod
    def pdf_rebuild(cls, pdf_name: str) -> str:
        return cls.tagged("PDF", f"検索可能PDFを再生成: {pdf_name}")

    @classmethod
    def pdf_overlay_rebuild(cls, pdf_name: str) -> str:
        return cls.tagged("PDF", f"元PDF保持 + 不可視テキスト重畳で出力: {pdf_name}")

    @classmethod
    def pdf_check_encrypted_fail(cls, pdf_name: str, detail: str) -> str:
        return cls.tagged("PDF-CHECK", f"暗号化PDFの判定失敗: {pdf_name} ({detail})")

    @classmethod
    def start_precheck_failed(cls, detail: str) -> str:
        return cls.tagged("CHECK", f"実行前チェック失敗: {detail}")

    @classmethod
    def startup_missing_engine_notice(cls) -> str:
        return (
            f"起動時点では {PYTHON_EXECUTABLE_LABEL} を確認できませんでした。 "
            f"必要に応じて『{PYTHON_EXECUTABLE_LABEL}』と『{NDLOCR_COMMAND_LABEL}』を確認してください。"
        )

    @classmethod
    def pdf_text_check_summary(
        cls,
        pdf_name: str,
        *,
        checked_pages: int,
        total_pages: int,
        total_chars: int,
        total_text_ops: int,
        judged_has_text: bool,
        reasons: list[str],
        page_details: list[str],
    ) -> str:
        reasons_text = ", ".join(reasons) if reasons else "判定根拠なし"
        pages_text = " / ".join(page_details) if page_details else "ページ詳細なし"
        verdict = "OCRあり" if judged_has_text else "OCRなし"
        return cls.tagged(
            "PDF-CHECK",
            f"{pdf_name}: {verdict} | pages={checked_pages}/{total_pages} | chars={total_chars} | text_ops={total_text_ops} | reasons={reasons_text} | {pages_text}",
        )

    @classmethod
    def startup_dependency_detail(cls, detail: str) -> str:
        return cls.tagged("CHECK", f"起動時依存関係チェック: {detail}")

    @classmethod
    def final_summary(cls, summary: RunSummary) -> str:
        result = summary.result
        state = "停止" if summary.was_stopped else "完了"
        return (
            f"{state}  対象:{result.total} / OCR実行:{result.processed} / "
            f"スキップ(既存テキスト):{result.skipped_has_text} / "
            f"スキップ(名前):{result.skipped_name_rule} / エラー:{result.errors}"
        )


class ProgressStatusBuilder:
    @staticmethod
    def checking(file_name: str) -> str:
        return f"判定中: {file_name}"

    @staticmethod
    def skipped_name(file_name: str) -> str:
        return f"スキップ（出力名）: {file_name}"

    @staticmethod
    def skipped_has_text(file_name: str) -> str:
        return f"スキップ（OCRあり）: {file_name}"

    @staticmethod
    def preparing(file_name: str) -> str:
        return f"前処理中: {file_name}"

    @staticmethod
    def running_ocr(file_name: str) -> str:
        return f"OCR実行中: {file_name}"

    @staticmethod
    def parsing(file_name: str) -> str:
        return f"結果解析中: {file_name}"

    @staticmethod
    def rebuilding_pdf(file_name: str) -> str:
        return f"PDF再生成中: {file_name}"

    @staticmethod
    def done(file_name: str) -> str:
        return f"完了: {file_name}"

    @staticmethod
    def stopped(file_name: str) -> str:
        return f"停止: {file_name}"

    @staticmethod
    def error(file_name: str) -> str:
        return f"エラー: {file_name}"

    @staticmethod
    def batch_running() -> str:
        return "処理中..."


class RuntimeIssueResolver:
    def resolve_stop(self, exc: OCRStopRequested) -> RuntimeIssue:
        detail = self._normalize_detail(str(exc))
        return RuntimeIssue(
            user_message="停止要求により中断しました。",
            log_detail=(detail or "停止要求により中断しました。"),
        )

    def resolve_error(self, exc: Exception) -> RuntimeIssue:
        detail = self._normalize_detail(str(exc) or exc.__class__.__name__)
        return RuntimeIssue(
            user_message=self._build_user_message(detail),
            log_detail=detail,
        )

    @staticmethod
    def _normalize_detail(detail: str) -> str:
        normalized = (detail or "").strip()
        if not normalized:
            return "詳細不明"
        return normalized[:2000] if len(normalized) > 2000 else normalized

    @classmethod
    def _build_user_message(cls, detail: str) -> str:
        message = (detail or "").strip()
        if not message:
            return "処理中にエラーが発生しました。"
        if "タイムアウト" in message:
            return "NDLOCR-Lite の実行がタイムアウトしました。"
        if "暗号化PDF" in message:
            return "暗号化PDFのため処理できませんでした。"
        if "OCR 文字情報" in message:
            return "OCR結果から文字情報を取得できませんでした。"
        if "出力ファイルが確認できませんでした" in message:
            return "OCR実行後の出力ファイルを確認できませんでした。"
        if "既存出力ファイル削除失敗" in message:
            return "既存の出力ファイルを削除できませんでした。"
        if cls._is_ndlocr_failure(message):
            return cls._build_ndlocr_failure_message(message)
        first_line = message.splitlines()[0].strip()
        return first_line or "処理中にエラーが発生しました。"

    @staticmethod
    def _is_ndlocr_failure(message: str) -> bool:
        return "NDLOCR-Lite 失敗" in (message or "")

    @classmethod
    def _build_ndlocr_failure_message(cls, detail: str) -> str:
        message = (detail or "").strip()
        lowered = message.lower()
        if "not found" in lowered or "見つかりません" in message:
            return "NDLOCR-Lite の実行に必要なファイルが見つかりませんでした。"
        if "permission denied" in lowered or "アクセスが拒否" in message:
            return "NDLOCR-Lite の実行権限を確認してください。"
        if "modulenotfounderror" in lowered or "no module named" in lowered:
            return "NDLOCR-Lite の依存モジュールが不足している可能性があります。"
        if "cuda" in lowered:
            return "NDLOCR-Lite の実行に失敗しました。CUDA / 実行環境設定を確認してください。"
        code = cls._extract_return_code(message)
        if code is not None:
            return f"NDLOCR-Lite の実行に失敗しました。終了コード: {code}"
        return "NDLOCR-Lite の実行に失敗しました。ログ詳細を確認してください。"

    @staticmethod
    def _extract_return_code(detail: str) -> Optional[int]:
        match = re.search(r"NDLOCR-Lite 失敗 \(code=(\d+)\)", detail or "")
        if not match:
            return None
        try:
            return int(match.group(1))
        except Exception:
            return None


def normalize_output_mode(output_mode: str) -> str:
    normalized = (output_mode or "").strip().lower()
    if normalized in {OUTPUT_MODE_SAME_FOLDER, OUTPUT_MODE_INPUT_FOLDER, OUTPUT_MODE_CUSTOM_FOLDER}:
        return normalized
    return OUTPUT_MODE_SAME_FOLDER


def describe_output_destination(output_mode: str, custom_output_dir: Optional[Path] = None) -> str:
    normalized = normalize_output_mode(output_mode)
    if normalized == OUTPUT_MODE_SAME_FOLDER:
        return "入力ファイルと同じフォルダ"
    if normalized == OUTPUT_MODE_INPUT_FOLDER:
        return '対象の親フォルダ直下の "ocr_output"'
    if custom_output_dir is not None:
        return f"指定フォルダ: {custom_output_dir}"
    return "指定フォルダ"


class StartRunRequestResolver:
    def __init__(self, *, text_setting_resolver: Optional[TextSettingResolver] = None) -> None:
        self._text_setting_resolver = text_setting_resolver or TextSettingResolver()

    def resolve_text_input(self, input_state: GuiTextInputState) -> ResolvedTextSetting:
        return self._text_setting_resolver.resolve(input_state)

    def resolve(self, request: StartRunRequest) -> tuple[Optional[ResolvedStartRunSettings], Optional[PreparationIssue]]:
        folder_str = (request.folder_str or "").strip()
        if not folder_str:
            return None, PreparationIssue(
                user_message="対象ファイルまたはフォルダを選択してください。",
                detail=LogMessageBuilder.start_precheck_failed("対象ファイルまたはフォルダが未指定です。"),
            )

        folder = Path(folder_str)
        if not folder.exists():
            return None, PreparationIssue(
                user_message="指定ファイルまたはフォルダが存在しません。",
                detail=LogMessageBuilder.start_precheck_failed(f"指定ファイルまたはフォルダが存在しません: {folder}"),
            )
        if not (folder.is_file() or folder.is_dir()):
            return None, PreparationIssue(
                user_message="指定パスはファイルまたはフォルダではありません。",
                detail=LogMessageBuilder.start_precheck_failed(f"指定パスはファイルまたはフォルダではありません: {folder}"),
            )
        if folder.is_file() and folder.suffix.lower() not in SUPPORTED_INPUT_SUFFIXES:
            return None, PreparationIssue(
                user_message="対応しているファイルを指定してください。",
                detail=LogMessageBuilder.start_precheck_failed(f"非対応ファイル形式です: {folder}"),
            )

        output_mode = normalize_output_mode(request.output_mode)
        custom_output_dir: Optional[Path] = None
        if output_mode == OUTPUT_MODE_CUSTOM_FOLDER:
            custom_output_folder_str = (request.custom_output_folder_str or "").strip()
            if not custom_output_folder_str:
                return None, PreparationIssue(
                    user_message="出力先フォルダを選択してください。",
                    detail=LogMessageBuilder.start_precheck_failed("指定フォルダ出力が選択されていますが、出力先フォルダが未指定です。"),
                )
            custom_output_dir = Path(custom_output_folder_str)
            try:
                custom_output_dir.mkdir(parents=True, exist_ok=True)
            except Exception as e:
                return None, PreparationIssue(
                    user_message="出力先フォルダを作成できません。",
                    detail=LogMessageBuilder.start_precheck_failed(f"出力先フォルダを作成できません: {custom_output_dir} ({e})"),
                )
            if not custom_output_dir.is_dir():
                return None, PreparationIssue(
                    user_message="出力先にフォルダを指定してください。",
                    detail=LogMessageBuilder.start_precheck_failed(f"出力先がフォルダではありません: {custom_output_dir}"),
                )

        resolved = ResolvedStartRunSettings(
            folder=folder,
            recursive=bool(request.recursive),
            overwrite=normalize_output_conflict_mode(request.output_conflict_mode) == OUTPUT_CONFLICT_OVERWRITE,
            output_conflict_mode=normalize_output_conflict_mode(request.output_conflict_mode),
            output_mode=output_mode,
            custom_output_folder=custom_output_dir,
            write_csv_log=bool(request.write_csv_log),
            engine_path_input=self.resolve_text_input(request.engine_path_input),
            command_template=self.resolve_text_input(request.command_template_input),
        )
        return resolved, None


class StartupDependencyPresentationBuilder:
    def build(self, *, ok: bool, detail: str) -> StartupDependencyPresentation:
        if ok:
            return StartupDependencyPresentation(
                notice="",
                log_entries=(LogEntry("INFO", LogMessageBuilder.dependency_ok()),),
            )
        notice = LogMessageBuilder.startup_missing_engine_notice()
        entries: list[LogEntry] = [LogEntry("WARN", notice)]
        normalized_detail = (detail or "").strip()
        if normalized_detail:
            entries.append(LogEntry("WARN", LogMessageBuilder.startup_dependency_detail(normalized_detail)))
        return StartupDependencyPresentation(notice=notice, log_entries=tuple(entries))


@dataclass(frozen=True)
class AppUiConfig:
    window_geometry: str = DEFAULT_WINDOW_GEOMETRY
    status_text: str = DEFAULT_STATUS_TEXT
    progress_text: str = DEFAULT_PROGRESS_TEXT
    runtime_notice_text: str = DEFAULT_RUNTIME_NOTICE_TEXT
    progress_max: int = DEFAULT_PROGRESS_MAX
    pad_x: int = DEFAULT_UI_PAD_X
    pad_y: int = DEFAULT_UI_PAD_Y
    log_text_height: int = DEFAULT_LOG_TEXT_HEIGHT
    runtime_notice_wraplength: int = DEFAULT_RUNTIME_NOTICE_WRAPLENGTH
    log_pump_interval_ms: int = DEFAULT_LOG_PUMP_INTERVAL_MS
    startup_dependency_check_delay_ms: int = DEFAULT_STARTUP_DEP_CHECK_DELAY_MS
    runtime_notice_color: str = DEFAULT_RUNTIME_NOTICE_COLOR


@dataclass(frozen=True)
class RuntimeDefaults:
    recursive: bool = False
    output_conflict_mode: str = OUTPUT_CONFLICT_RENAME
    output_mode: str = OUTPUT_MODE_SAME_FOLDER
    custom_output_folder: str = ""
    write_csv_log: bool = True
    engine_path: str = ""
    engine_path_source: str = SETTING_SOURCE_AUTO
    command_template: str = DEFAULT_COMMAND_TEMPLATE
    command_template_source: str = SETTING_SOURCE_DEFAULT
    execution: RunExecutionSettings = field(default_factory=RunExecutionSettings)


class RuntimeDefaultsResolver:
    def resolve(self) -> RuntimeDefaults:
        engine_path, command_template = determine_default_engine_and_template()
        command_template_source = (
            SETTING_SOURCE_AUTO
            if command_template != DEFAULT_COMMAND_TEMPLATE
            else SETTING_SOURCE_DEFAULT
        )
        return RuntimeDefaults(
            engine_path=engine_path,
            engine_path_source=SETTING_SOURCE_AUTO,
            command_template=command_template,
            command_template_source=command_template_source,
        )


class GuiRunSettingsSnapshotBuilder:
    def __init__(self, runtime_defaults: RuntimeDefaults) -> None:
        self._runtime_defaults = runtime_defaults

    def build(
        self,
        *,
        folder_str: str,
        recursive: bool,
        output_conflict_mode: str,
        output_mode: str,
        custom_output_folder_str: str,
        write_csv_log: bool,
        engine_path_str: str,
        command_template_str: str,
    ) -> StartRunRequest:
        return StartRunRequest(
            folder_str=folder_str,
            recursive=recursive,
            output_conflict_mode=normalize_output_conflict_mode(output_conflict_mode),
            output_mode=normalize_output_mode(output_mode),
            custom_output_folder_str=custom_output_folder_str,
            write_csv_log=write_csv_log,
            engine_path_input=GuiTextInputState(
                current_value=engine_path_str,
                baseline_value=self._runtime_defaults.engine_path,
                baseline_source=self._runtime_defaults.engine_path_source,
            ),
            command_template_input=GuiTextInputState(
                current_value=command_template_str,
                baseline_value=self._runtime_defaults.command_template,
                baseline_source=self._runtime_defaults.command_template_source,
            ),
        )


@dataclass(frozen=True)
class FileSkipDecision:
    action: str
    detail: str
    progress_status: str
    log_entry: LogEntry
    csv_detail: Optional[str] = None


@dataclass(frozen=True)
class FileOutputPlan:
    output_path: Path
    pre_logs: tuple[LogEntry, ...] = ()
    csv_detail_suffix: str = ""


@dataclass(frozen=True)
class PreparedPage:
    index: int
    image_path: Path
    width_px: int
    height_px: int
    width_pt: float
    height_pt: float
    source_label: str
    rotation_deg: int = 0
    media_width_pt: float = 0.0
    media_height_pt: float = 0.0
    crop_width_pt: float = 0.0
    crop_height_pt: float = 0.0


@dataclass
class PreparedDocument:
    source_path: Path
    page_count: int
    input_dir: Path
    pages: List[PreparedPage]
    input_kind: str = INPUT_KIND_IMAGE
    original_pdf_path: Optional[Path] = None
    temp_root: Optional[tempfile.TemporaryDirectory[str]] = None

    def cleanup(self) -> None:
        if self.temp_root is not None:
            try:
                self.temp_root.cleanup()
            except Exception:
                pass
            self.temp_root = None


@dataclass
class OCRToken:
    text: str
    x1: float
    y1: float
    x2: float
    y2: float


@dataclass
class PageOcrData:
    tokens: List[OCRToken] = field(default_factory=list)
    text_blocks: List[str] = field(default_factory=list)

    def has_any_text(self) -> bool:
        if self.tokens:
            return True
        return any(bool((t or "").strip()) for t in self.text_blocks)


class OCRStopRequested(RuntimeError):
    """停止要求によりOCR実行を中断したことを表す例外。"""


class LogQueue:
    def __init__(self) -> None:
        self.q: "queue.Queue[LogEntry]" = queue.Queue()

    def put(self, kind: str, msg: str) -> None:
        self.put_entry(LogEntry(kind, msg))

    def put_entry(self, entry: LogEntry) -> None:
        self.q.put(entry)

    def get_nowait(self) -> LogEntry:
        return self.q.get_nowait()

    def drain_nowait(self) -> list[LogEntry]:
        entries: list[LogEntry] = []
        while True:
            try:
                entries.append(self.q.get_nowait())
            except queue.Empty:
                return entries


class StartRunCoordinator:
    def __init__(
        self,
        *,
        request_resolver: StartRunRequestResolver,
        validate_runtime_settings: Callable[[str], tuple[bool, str]],
        check_dependencies: Callable[[bool, str], tuple[bool, str]],
        resolve_launcher: Callable[[str], list[str]],
        execution_defaults: RunExecutionSettings,
    ) -> None:
        self._request_resolver = request_resolver
        self._validate_runtime_settings = validate_runtime_settings
        self._check_dependencies = check_dependencies
        self._resolve_launcher = resolve_launcher
        self._execution_defaults = execution_defaults

    def prepare(self, request: StartRunRequest) -> StartRunPreparationResult:
        resolved, issue = self._request_resolver.resolve(request)
        if issue is not None or resolved is None:
            return StartRunPreparationResult(ok=False, issue=issue)

        ok, msg = self._validate_runtime_settings(resolved.command_template.value)
        if not ok:
            return StartRunPreparationResult(
                ok=False,
                issue=PreparationIssue(
                    user_message=msg,
                    detail=LogMessageBuilder.start_precheck_failed(msg),
                ),
            )

        deps_ok, dep_msg = self._check_dependencies(True, resolved.engine_path_input.value)
        if not deps_ok:
            return StartRunPreparationResult(
                ok=False,
                issue=PreparationIssue(
                    user_message="依存関係チェックに失敗しました。ログを確認してください。",
                    detail=LogMessageBuilder.start_precheck_failed(dep_msg),
                ),
            )

        try:
            launcher = self._resolve_launcher(resolved.engine_path_input.value)
        except Exception as e:
            detail = f"{PYTHON_EXECUTABLE_LABEL} を特定できません: {e}"
            return StartRunPreparationResult(
                ok=False,
                issue=PreparationIssue(
                    user_message=f"{PYTHON_EXECUTABLE_LABEL} を確認できません。設定を見直してください。",
                    detail=LogMessageBuilder.start_precheck_failed(detail),
                ),
            )

        launcher_display = launcher[0] if launcher else resolved.engine_path_input.value
        pre_logs: list[LogEntry] = []
        pre_logs.append(
            LogMessageBuilder.engine_selection(
                launcher_display,
                source=resolved.engine_path_input.source,
            )
        )
        pre_logs.append(
            LogMessageBuilder.command_template(
                resolved.command_template.value,
                source=resolved.command_template.source,
            )
        )
        pre_logs.append(LogMessageBuilder.output_destination(resolved.output_mode, resolved.custom_output_folder))
        pre_logs.append(LogMessageBuilder.input_formats())
        pre_logs.append(LogMessageBuilder.run_option_output_conflict(resolved.output_conflict_mode))

        run_config = RunConfig(
            folder=resolved.folder,
            recursive=resolved.recursive,
            overwrite=resolved.overwrite,
            output_conflict_mode=resolved.output_conflict_mode,
            output_mode=resolved.output_mode,
            custom_output_dir=resolved.custom_output_folder,
            write_csv_log=resolved.write_csv_log,
            engine_path=launcher_display,
            command_template=resolved.command_template.value,
            execution=self._execution_defaults,
        )

        startup_log_message = LogMessageBuilder.processing_start(launcher_display)
        plan = StartRunPlan(
            run_config=run_config,
            startup_log_message=startup_log_message,
            pre_logs=tuple(pre_logs),
            launcher_display=launcher_display,
        )
        return StartRunPreparationResult(ok=True, plan=plan)


class CsvLogger:
    HEADERS = [
        "timestamp",
        "input",
        "output",
        "action",
        "detail",
        "engine_path",
        "command_template",
        "seconds",
    ]

    def __init__(self) -> None:
        self._rows: list[CsvLogRow] = []

    def reset(self) -> None:
        self._rows.clear()

    def new_row(self, source_path: Path, run_config: RunConfig) -> CsvLogRow:
        return CsvLogRow(
            timestamp=datetime.now().isoformat(timespec="seconds"),
            input=str(source_path),
            engine_path=run_config.engine_path,
            command_template=run_config.command_template,
        )

    def append_row(self, row: CsvLogRow) -> None:
        self._rows.append(CsvLogRow(**row.__dict__))

    def write(self, csv_path: Path, run_config: RunConfig, summary: RunSummary) -> None:
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        result = summary.result
        with csv_path.open("w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(["meta", "app_title", APP_TITLE])
            w.writerow(["meta", "target_path", str(run_config.folder)])
            w.writerow(["meta", "target_kind", "folder" if run_config.folder.is_dir() else "file"])
            w.writerow(["meta", "started_at", summary.started_at.isoformat(timespec="seconds")])
            w.writerow(["meta", "ended_at", summary.ended_at.isoformat(timespec="seconds")])
            w.writerow(["meta", "engine_path", run_config.engine_path])
            w.writerow(["meta", "command_template", run_config.command_template])
            w.writerow(["meta", "recursive", str(run_config.recursive)])
            w.writerow(["meta", "output_conflict_mode", run_config.output_conflict_mode])
            w.writerow(["meta", "output_conflict_label", describe_output_conflict_mode(run_config.output_conflict_mode)])
            w.writerow(["meta", "overwrite", str(run_config.overwrite)])
            w.writerow(["meta", "output_mode", run_config.output_mode])
            w.writerow(["meta", "output_destination", describe_output_destination(run_config.output_mode, run_config.custom_output_dir)])
            w.writerow(["meta", "stopped", str(bool(summary.was_stopped))])
            w.writerow(["meta", "total", result.total])
            w.writerow(["meta", "processed", result.processed])
            w.writerow(["meta", "skipped_has_text", result.skipped_has_text])
            w.writerow(["meta", "skipped_name_rule", result.skipped_name_rule])
            w.writerow(["meta", "errors", result.errors])
            w.writerow([])
            w.writerow(self.HEADERS)
            for row in self._rows:
                w.writerow(row.to_csv_record(self.HEADERS))

class InputCollector:
    def collect_inputs(self, target_path: Path, recursive: bool) -> List[Path]:
        if target_path.is_file():
            return [target_path] if target_path.suffix.lower() in SUPPORTED_INPUT_SUFFIXES else []
        if recursive:
            files = [p for p in target_path.rglob("*") if p.is_file() and p.suffix.lower() in SUPPORTED_INPUT_SUFFIXES]
        else:
            files = [p for p in target_path.iterdir() if p.is_file() and p.suffix.lower() in SUPPORTED_INPUT_SUFFIXES]
        return sorted(set(files), key=lambda p: str(p).lower())


class PdfInspector:
    _TEXT_SHOW_OPERATOR_RE = re.compile(rb'(?<![A-Za-z])(Tj|TJ|\'|")(?=[^A-Za-z]|$)')

    def __init__(self, *, pdf_reader_cls: Any, log: Callable[[str, str], None]) -> None:
        self._pdf_reader_cls = pdf_reader_cls
        self._log = log

    def has_text_layer(
        self,
        pdf_path: Path,
        pages_to_check: int = DEFAULT_TEXT_LAYER_CHECK_PAGES,
        min_chars: int = MIN_TEXT_LAYER_CHARS,
        min_text_ops: int = MIN_TEXT_SHOW_OPS,
    ) -> bool:
        if self._pdf_reader_cls is None:
            raise RuntimeError("pypdf が利用できません")

        try:
            reader = self._pdf_reader_cls(str(pdf_path))
        except Exception as e:
            raise RuntimeError(f"PDF 読み込み失敗: {e}")

        try:
            if getattr(reader, "is_encrypted", False):
                try:
                    dec_result = reader.decrypt("")
                except Exception as e:
                    self._log("WARN", LogMessageBuilder.pdf_check_encrypted_fail(pdf_path.name, str(e)))
                    raise RuntimeError("暗号化PDFのため判定できません（パスワード解除後に再実行してください）")
                if not dec_result:
                    raise RuntimeError("暗号化PDFのため判定できません（パスワード解除後に再実行してください）")
        except RuntimeError:
            raise
        except Exception as e:
            raise RuntimeError(f"PDFテキスト層判定中にエラー: {e}")

        total_pages = len(reader.pages)
        check_pages = min(total_pages, max(1, int(pages_to_check or DEFAULT_TEXT_LAYER_CHECK_PAGES)))
        total_chars = 0
        total_text_ops = 0
        reasons: list[str] = []
        page_details: list[str] = []

        for i in range(check_pages):
            page = reader.pages[i]
            extracted_variants: list[str] = []
            page_chars = 0
            for extraction_mode in (None, "layout"):
                try:
                    if extraction_mode is None:
                        txt = page.extract_text() or ""
                    else:
                        txt = page.extract_text(extraction_mode=extraction_mode) or ""
                except TypeError:
                    if extraction_mode is None:
                        try:
                            txt = page.extract_text() or ""
                        except Exception:
                            txt = ""
                    else:
                        txt = ""
                except Exception:
                    txt = ""
                txt = re.sub(r"\s+", "", txt)
                if txt:
                    extracted_variants.append(txt)
            if extracted_variants:
                page_chars = max(len(v) for v in extracted_variants)
            total_chars += page_chars

            page_text_ops = self._count_text_show_ops(page)
            total_text_ops += page_text_ops
            page_details.append(f"p{i+1}:chars={page_chars},ops={page_text_ops}")

            if page_chars >= min_chars and "extract_text" not in reasons:
                reasons.append("extract_text")
            if page_text_ops >= min_text_ops and "text_operators" not in reasons:
                reasons.append("text_operators")

            if total_chars >= min_chars or total_text_ops >= min_text_ops:
                self._log(
                    "INFO",
                    LogMessageBuilder.pdf_text_check_summary(
                        pdf_path.name,
                        checked_pages=i + 1,
                        total_pages=total_pages,
                        total_chars=total_chars,
                        total_text_ops=total_text_ops,
                        judged_has_text=True,
                        reasons=reasons,
                        page_details=page_details,
                    ),
                )
                return True

        self._log(
            "INFO",
            LogMessageBuilder.pdf_text_check_summary(
                pdf_path.name,
                checked_pages=check_pages,
                total_pages=total_pages,
                total_chars=total_chars,
                total_text_ops=total_text_ops,
                judged_has_text=False,
                reasons=reasons,
                page_details=page_details,
            ),
        )
        return False

    def _count_text_show_ops(self, page: Any) -> int:
        try:
            contents = page.get_contents()
            if contents is None:
                return 0
            if isinstance(contents, list):
                data = b"".join((item.get_data() or b"") for item in contents)
            else:
                data = contents.get_data() or b""
            if not data:
                return 0
            return len(self._TEXT_SHOW_OPERATOR_RE.findall(data))
        except Exception:
            return 0


class CsvLogPathResolver:
    def make_path(self, folder: Path) -> Path:
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        base = folder / f"ocr_batch_log_{ts}.csv"
        if not base.exists():
            return base
        for i in range(1, 1000):
            cand = folder / f"ocr_batch_log_{ts}_{i:03d}.csv"
            if not cand.exists():
                return cand
        return folder / f"ocr_batch_log_{ts}_{int(time.time())}.csv"


class InputFilePlanner:
    def __init__(
        self,
        *,
        pdf_has_text_layer: Callable[[Path], bool],
        make_output_path: Callable[[Path, Path, str, Optional[Path], bool], Path],
        default_output_path: Callable[[Path, Path, str, Optional[Path]], Path],
    ) -> None:
        self._pdf_has_text_layer = pdf_has_text_layer
        self._make_output_path = make_output_path
        self._default_output_path = default_output_path

    def detect_skip(self, source_path: Path) -> Optional[FileSkipDecision]:
        if GENERATED_INPUT_NAME_RE.search(source_path.stem):
            return FileSkipDecision(
                action="skip_name",
                detail="出力ファイル名規則に一致（再処理防止）",
                progress_status=ProgressStatusBuilder.skipped_name(source_path.name),
                log_entry=LogMessageBuilder.skip_name(source_path.name),
            )

        if source_path.suffix.lower() == ".pdf" and self._pdf_has_text_layer(source_path):
            return FileSkipDecision(
                action="skip_has_text",
                detail="既にテキスト層あり",
                progress_status=ProgressStatusBuilder.skipped_has_text(source_path.name),
                log_entry=LogMessageBuilder.skip_has_text(source_path.name),
                csv_detail="既にテキスト層あり（PDF判定でスキップ）",
            )
        return None

    def plan_output(
        self,
        source_path: Path,
        *,
        input_root_folder: Path,
        output_mode: str,
        custom_output_dir: Optional[Path],
        overwrite: bool,
    ) -> FileOutputPlan:
        output_path = self._make_output_path(source_path, input_root_folder, output_mode, custom_output_dir, overwrite)
        default_output_path = self._default_output_path(source_path, input_root_folder, output_mode, custom_output_dir)
        pre_logs: list[LogEntry] = []
        csv_detail_suffix = "新規のOCR出力を作成"
        if output_path.exists() and overwrite:
            pre_logs.append(LogMessageBuilder.overwrite(output_path.name))
            csv_detail_suffix = "既存のOCR出力（*_ocr.pdf）を上書き"
        elif output_path.name != default_output_path.name:
            pre_logs.append(LogMessageBuilder.rename(output_path.name))
            csv_detail_suffix = "既存のOCR出力があるため連番保存"
        return FileOutputPlan(output_path=output_path, pre_logs=tuple(pre_logs), csv_detail_suffix=csv_detail_suffix)


class DocumentPreparer:
    def __init__(self, *, log: Callable[[str, str], None]) -> None:
        self._log = log

    def prepare(self, source_path: Path, *, render_dpi: int) -> PreparedDocument:
        suffix = source_path.suffix.lower()
        if suffix == ".pdf":
            return self._prepare_pdf(source_path, render_dpi=render_dpi)
        if suffix in SUPPORTED_IMAGE_SUFFIXES:
            return self._prepare_image(source_path)
        raise RuntimeError(f"未対応の入力形式です: {source_path.suffix}")

    def _prepare_pdf(self, pdf_path: Path, *, render_dpi: int) -> PreparedDocument:
        if pdfium is None:
            raise RuntimeError("pypdfium2 が利用できません（`py -m pip install pypdfium2`）")
        if Image is None:
            raise RuntimeError("Pillow が利用できません（`py -m pip install pillow`）")

        temp_root = tempfile.TemporaryDirectory(prefix="ndlocr_input_pdf_")
        temp_dir = Path(temp_root.name)
        pages_dir = temp_dir / "pages"
        pages_dir.mkdir(parents=True, exist_ok=True)

        pdf_page_infos: list[dict[str, float | int]] = []
        if PdfReader is not None:
            try:
                reader = PdfReader(str(pdf_path))
                if getattr(reader, "is_encrypted", False):
                    try:
                        reader.decrypt("")
                    except Exception:
                        pass
                for src_page in reader.pages:
                    try:
                        rotation_deg = int(getattr(src_page, "rotation", 0) or 0) % 360
                    except Exception:
                        rotation_deg = 0
                    try:
                        media_width_pt = float(src_page.mediabox.width)
                        media_height_pt = float(src_page.mediabox.height)
                    except Exception:
                        media_width_pt = 0.0
                        media_height_pt = 0.0
                    try:
                        crop_width_pt = float(src_page.cropbox.width)
                        crop_height_pt = float(src_page.cropbox.height)
                    except Exception:
                        crop_width_pt = media_width_pt
                        crop_height_pt = media_height_pt
                    pdf_page_infos.append(
                        {
                            "rotation_deg": rotation_deg,
                            "media_width_pt": media_width_pt,
                            "media_height_pt": media_height_pt,
                            "crop_width_pt": crop_width_pt,
                            "crop_height_pt": crop_height_pt,
                        }
                    )
            except Exception:
                pdf_page_infos = []

        try:
            doc = pdfium.PdfDocument(str(pdf_path))
        except Exception as e:
            temp_root.cleanup()
            raise RuntimeError(f"PDF のレンダリング準備に失敗しました: {e}")

        normalized_render_dpi = max(72, int(render_dpi))
        scale = normalized_render_dpi / 72.0
        pages: list[PreparedPage] = []
        try:
            page_count = len(doc)
            for i in range(page_count):
                page = doc[i]
                pil_img = page.render(scale=scale).to_pil()
                if pil_img.mode not in ("RGB", "L"):
                    pil_img = pil_img.convert("RGB")
                out_img = pages_dir / f"page_{i+1:04d}.png"
                pil_img.save(out_img, format="PNG")
                width_px, height_px = pil_img.size
                width_pt = width_px * 72.0 / normalized_render_dpi
                height_pt = height_px * 72.0 / normalized_render_dpi
                page_info = pdf_page_infos[i] if i < len(pdf_page_infos) else {}
                pages.append(
                    PreparedPage(
                        index=i,
                        image_path=out_img,
                        width_px=width_px,
                        height_px=height_px,
                        width_pt=width_pt,
                        height_pt=height_pt,
                        source_label=f"{pdf_path.name} / page {i+1}",
                        rotation_deg=int(page_info.get("rotation_deg", 0) or 0),
                        media_width_pt=float(page_info.get("media_width_pt", width_pt) or width_pt),
                        media_height_pt=float(page_info.get("media_height_pt", height_pt) or height_pt),
                        crop_width_pt=float(page_info.get("crop_width_pt", width_pt) or width_pt),
                        crop_height_pt=float(page_info.get("crop_height_pt", height_pt) or height_pt),
                    )
                )
        except Exception as e:
            temp_root.cleanup()
            raise RuntimeError(f"PDF をページ画像へ分解できませんでした: {e}")
        finally:
            try:
                doc.close()
            except Exception:
                pass

        if not pages:
            temp_root.cleanup()
            raise RuntimeError("PDF のページを画像化できませんでした")

        self._log("INFO", LogMessageBuilder.prep_pdf_split(pdf_path.name, len(pages)))
        return PreparedDocument(
            source_path=pdf_path,
            page_count=len(pages),
            input_dir=pages_dir,
            pages=pages,
            input_kind=INPUT_KIND_PDF,
            original_pdf_path=pdf_path,
            temp_root=temp_root,
        )

    def _prepare_image(self, image_path: Path) -> PreparedDocument:
        if Image is None:
            raise RuntimeError("Pillow が利用できません（`py -m pip install pillow`）")

        temp_root = tempfile.TemporaryDirectory(prefix="ndlocr_input_img_")
        temp_dir = Path(temp_root.name)
        pages_dir = temp_dir / "pages"
        pages_dir.mkdir(parents=True, exist_ok=True)

        try:
            with Image.open(image_path) as im:
                dpi_info = im.info.get("dpi", (DEFAULT_IMAGE_DPI, DEFAULT_IMAGE_DPI))
                dpi_x = _normalize_dpi_value(dpi_info[0] if isinstance(dpi_info, (tuple, list)) else dpi_info)
                dpi_y = _normalize_dpi_value(dpi_info[1] if isinstance(dpi_info, (tuple, list)) and len(dpi_info) > 1 else dpi_x)
                working = im.copy()
                if working.mode not in ("RGB", "L"):
                    working = working.convert("RGB")
                out_img = pages_dir / "page_0001.png"
                working.save(out_img, format="PNG")
                width_px, height_px = working.size
                width_pt = width_px * 72.0 / dpi_x
                height_pt = height_px * 72.0 / dpi_y
        except Exception as e:
            temp_root.cleanup()
            raise RuntimeError(f"画像の読み込みに失敗しました: {e}")

        self._log("INFO", LogMessageBuilder.prep_image_input(image_path.name))
        return PreparedDocument(
            source_path=image_path,
            page_count=1,
            input_dir=pages_dir,
            pages=[
                PreparedPage(
                    index=0,
                    image_path=out_img,
                    width_px=width_px,
                    height_px=height_px,
                    width_pt=width_pt,
                    height_pt=height_pt,
                    source_label=image_path.name,
                    rotation_deg=0,
                    media_width_pt=width_pt,
                    media_height_pt=height_pt,
                    crop_width_pt=width_pt,
                    crop_height_pt=height_pt,
                )
            ],
            input_kind=INPUT_KIND_IMAGE,
            temp_root=temp_root,
        )


class NDLOCRLiteRunner:
    def __init__(
        self,
        *,
        resolve_launcher: Callable[[str], list[str]],
        log: Callable[[str, str], None],
        is_stop_requested: Callable[[], bool],
        terminate_process: Callable[[Any], None],
        set_active_process: Callable[[Any], None],
        quote_for_log: Callable[[str], str],
    ) -> None:
        self._resolve_launcher = resolve_launcher
        self._log = log
        self._is_stop_requested = is_stop_requested
        self._terminate_process = terminate_process
        self._set_active_process = set_active_process
        self._quote_for_log = quote_for_log

    def build_cmd(
        self,
        *,
        input_dir: Path,
        single_input: Optional[Path],
        outdir: Path,
        out_pdf: Path,
        command_template: str,
        launcher: Optional[list[str]] = None,
    ) -> list[str]:
        launcher_resolved = list(launcher or self._resolve_launcher(""))
        template = (command_template or "").strip() or DEFAULT_COMMAND_TEMPLATE
        formatted = template.format(
            input=str(single_input or ""),
            input_dir=str(input_dir),
            output_dir=str(outdir),
            output_pdf=str(out_pdf),
            output_stem=str(out_pdf.with_suffix("")),
        )
        try:
            args = shlex.split(formatted, posix=(os.name != "nt"))
        except Exception as e:
            raise RuntimeError(f"{NDLOCR_COMMAND_LABEL} の解析に失敗しました: {e}")
        if not args:
            raise RuntimeError(f"{NDLOCR_COMMAND_LABEL} が空です")
        return launcher_resolved + args

    def run_subprocess_with_polling(self, cmd: list[str], timeout_sec: int) -> tuple[int, str, str]:
        popen_kwargs: dict[str, Any] = dict(
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="ignore",
        )
        if os.name == "nt":
            creationflags = getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)
            if creationflags:
                popen_kwargs["creationflags"] = creationflags
        else:
            popen_kwargs["start_new_session"] = True

        proc = subprocess.Popen(cmd, **popen_kwargs)
        self._set_active_process(proc)
        started = time.monotonic()

        try:
            while True:
                if self._is_stop_requested():
                    self._terminate_process(proc)
                    try:
                        proc.communicate(timeout=2)
                    except Exception:
                        pass
                    raise OCRStopRequested("停止要求によりOCR実行を中断しました")

                rc = proc.poll()
                if rc is not None:
                    stdout, stderr = proc.communicate()
                    return rc, (stdout or ""), (stderr or "")

                if timeout_sec > 0 and (time.monotonic() - started) > timeout_sec:
                    self._terminate_process(proc)
                    try:
                        proc.communicate(timeout=2)
                    except Exception:
                        pass
                    raise RuntimeError(f"NDLOCR-Lite 実行がタイムアウトしました（>{timeout_sec}秒）")

                time.sleep(0.2)
        finally:
            self._set_active_process(None)

    def run(
        self,
        *,
        input_dir: Path,
        single_input: Optional[Path],
        outdir: Path,
        out_pdf: Path,
        command_template: str,
        engine_path: str,
        timeout_sec: int,
    ) -> None:
        launcher = self._resolve_launcher(engine_path)
        cmd = self.build_cmd(
            input_dir=input_dir,
            single_input=single_input,
            outdir=outdir,
            out_pdf=out_pdf,
            command_template=command_template,
            launcher=launcher,
        )
        self._log("INFO", LogMessageBuilder.command_line(" ".join(self._quote_for_log(x) for x in cmd)))

        rc, stdout, stderr = self.run_subprocess_with_polling(cmd, timeout_sec=timeout_sec)
        if rc != 0:
            detail = ((stderr or "") + "\n" + (stdout or "")).strip()
            detail = (detail[:2000] + "...") if len(detail) > 2000 else detail
            raise RuntimeError(f"NDLOCR-Lite 失敗 (code={rc}) {detail}")

        file_count = sum(1 for _ in outdir.rglob("*") if _.is_file())
        self._log("INFO", LogMessageBuilder.ndlocr_output_count(file_count))
        if file_count == 0:
            raise RuntimeError("NDLOCR-Lite 実行は成功しましたが、出力ファイルが見つかりませんでした")


class OCRResultParser:
    def __init__(self, *, log: Callable[[str, str], None]) -> None:
        self._log = log

    def parse(self, output_dir: Path, prepared: PreparedDocument) -> Dict[int, PageOcrData]:
        result: dict[int, PageOcrData] = {p.index: PageOcrData() for p in prepared.pages}
        structured_hits = 0
        text_hits = 0

        files = [p for p in output_dir.rglob("*") if p.is_file()]
        files.sort(key=lambda p: str(p).lower())
        json_files = [p for p in files if p.suffix.lower() in JSON_EXTS]
        xml_files = [p for p in files if (p.suffix.lower() in XML_EXTS or p.name.lower().endswith(".page.xml"))]
        text_files = [p for p in files if p.suffix.lower() in TEXT_EXTS]

        # 同一OCR結果が json / xml / txt に重複出力される環境があるため、
        # まず構造化度の高い形式を優先し、未充足ページのみを下位形式で補完する。
        # これにより、全文コピー時に同一文が重複抽出されるのを抑える。
        for path in json_files:
            try:
                assignments, texts = self._parse_json_file(path, prepared)
                structured_hits += self._merge_assignments(result, assignments, texts, path, prepared, only_empty_pages=True)
            except Exception as e:
                self._log("WARN", LogMessageBuilder.parse_warning(path.name, str(e)))

        for path in xml_files:
            if self._all_pages_have_any_text(result, prepared):
                break
            try:
                assignments, texts = self._parse_xml_file(path, prepared)
                structured_hits += self._merge_assignments(result, assignments, texts, path, prepared, only_empty_pages=True)
            except Exception as e:
                self._log("WARN", LogMessageBuilder.parse_warning(path.name, str(e)))

        for path in text_files:
            if self._all_pages_have_any_text(result, prepared):
                break
            try:
                text_hits += self._merge_text_file(result, path, prepared, only_empty_pages=True)
            except Exception as e:
                self._log("WARN", LogMessageBuilder.parse_warning(path.name, str(e)))

        result = self._postprocess_pages(result)
        total_tokens = sum(len(v.tokens) for v in result.values())
        total_texts = sum(len(v.text_blocks) for v in result.values())
        self._log(
            "INFO",
            LogMessageBuilder.parse_summary(
                total_tokens=total_tokens,
                total_texts=total_texts,
                structured_hits=structured_hits,
                text_hits=text_hits,
            ),
        )
        if len(prepared.pages) > 1 and total_tokens <= 1 and total_texts <= 1:
            self._log("WARN", LogMessageBuilder.parse_low_coverage())
        return result

    def _postprocess_pages(self, result: Dict[int, PageOcrData]) -> Dict[int, PageOcrData]:
        for page_data in result.values():
            if page_data.tokens:
                deduped: list[OCRToken] = []
                seen: set[tuple[str, int, int, int, int]] = set()
                for token in sorted(page_data.tokens, key=lambda t: (round(t.y1, 1), round(t.x1, 1), round(t.y2 - t.y1, 1), t.text)):
                    text_key = _normalize_ocr_text(token.text)
                    if not text_key:
                        continue
                    key = (
                        text_key,
                        int(round(token.x1)),
                        int(round(token.y1)),
                        int(round(token.x2)),
                        int(round(token.y2)),
                    )
                    if key in seen:
                        continue
                    seen.add(key)
                    deduped.append(OCRToken(text=text_key, x1=token.x1, y1=token.y1, x2=token.x2, y2=token.y2))
                page_data.tokens = deduped
            if page_data.text_blocks:
                blocks: list[str] = []
                seen_blocks: set[str] = set()
                for block in page_data.text_blocks:
                    cleaned = _normalize_ocr_text(block)
                    if not cleaned or cleaned in seen_blocks:
                        continue
                    seen_blocks.add(cleaned)
                    blocks.append(cleaned)
                page_data.text_blocks = blocks
        return result

    @staticmethod
    def _all_pages_have_any_text(result: Dict[int, PageOcrData], prepared: PreparedDocument) -> bool:
        return all(result.get(page.index, PageOcrData()).has_any_text() for page in prepared.pages)

    def _merge_assignments(
        self,
        result: Dict[int, PageOcrData],
        assignments: Dict[int, List[OCRToken]],
        texts: Dict[int, List[str]],
        src_path: Path,
        prepared: PreparedDocument,
        *,
        only_empty_pages: bool = False,
    ) -> int:
        hit = 0
        target_page = self._guess_page_index_from_name(src_path, prepared)
        generic_tokens = assignments.pop(-1, []) if -1 in assignments else []
        generic_texts = texts.pop(-1, []) if -1 in texts else []

        for page_index, tokens in assignments.items():
            if page_index in result and tokens:
                # 下位形式からの補完時でも、既存が text_blocks のみなら
                # 座標付き tokens で上書き的に強化する価値があるため許可する。
                if only_empty_pages and result[page_index].tokens:
                    continue
                result[page_index].tokens.extend(tokens)
                hit += 1
        for page_index, blocks in texts.items():
            if page_index in result:
                if only_empty_pages and result[page_index].has_any_text():
                    continue
                cleaned = [b for b in blocks if (b or "").strip()]
                if cleaned:
                    result[page_index].text_blocks.extend(cleaned)
                    hit += 1

        if generic_tokens:
            if target_page is None and len(prepared.pages) == 1:
                target_page = prepared.pages[0].index
            if target_page is not None:
                if (not only_empty_pages) or (not result[target_page].tokens):
                    result[target_page].tokens.extend(generic_tokens)
                    hit += 1
        if generic_texts:
            if target_page is None and len(prepared.pages) == 1:
                target_page = prepared.pages[0].index
            if target_page is not None:
                if (not only_empty_pages) or (not result[target_page].has_any_text()):
                    result[target_page].text_blocks.extend([b for b in generic_texts if (b or "").strip()])
                    hit += 1
        return hit

    def _merge_text_file(self, result: Dict[int, PageOcrData], txt_path: Path, prepared: PreparedDocument, *, only_empty_pages: bool = False) -> int:
        try:
            text = txt_path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            text = txt_path.read_text(encoding="utf-8", errors="ignore")
        except Exception as e:
            raise RuntimeError(f"TXT 読み込み失敗: {e}")

        text = text.replace("\r\n", "\n").strip()
        if not text:
            return 0

        pages = [t.strip() for t in re.split(r"\f+", text) if t.strip()]
        if len(pages) == len(prepared.pages):
            hit = 0
            for page, block in zip(prepared.pages, pages):
                if only_empty_pages and result[page.index].has_any_text():
                    continue
                result[page.index].text_blocks.append(block)
                hit += 1
            return hit

        target_page = self._guess_page_index_from_name(txt_path, prepared)
        if target_page is None:
            if len(prepared.pages) == 1:
                target_page = prepared.pages[0].index
            elif len(pages) == 1:
                target_page = prepared.pages[0].index
        if target_page is None:
            return 0
        if only_empty_pages and result[target_page].has_any_text():
            return 0
        result[target_page].text_blocks.append(text)
        return 1

    def _parse_json_file(self, path: Path, prepared: PreparedDocument) -> tuple[Dict[int, List[OCRToken]], Dict[int, List[str]]]:
        import json

        try:
            content = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            content = path.read_text(encoding="utf-8", errors="ignore")

        data = json.loads(content)
        token_map: dict[int, list[OCRToken]] = {}
        text_map: dict[int, list[str]] = {}
        valid_pages = {p.index for p in prepared.pages}

        def add_token(page_hint: Optional[int], token: OCRToken) -> None:
            normalized = _normalize_ocr_text(token.text)
            if not normalized:
                return
            page_index = page_hint if page_hint in valid_pages else -1
            token_map.setdefault(page_index, []).append(OCRToken(text=normalized, x1=token.x1, y1=token.y1, x2=token.x2, y2=token.y2))

        def add_text(page_hint: Optional[int], text: str) -> None:
            cleaned = _normalize_ocr_text(text)
            if not cleaned:
                return
            page_index = page_hint if page_hint in valid_pages else -1
            text_map.setdefault(page_index, []).append(cleaned)

        # NDLOCR-Lite系の典型: {"contents": [[{boundingBox,text,...}, ...], ...], "imginfo": {...}}
        if isinstance(data, dict) and isinstance(data.get("contents"), list):
            contents = data.get("contents") or []
            img_page_hint = None
            imginfo = data.get("imginfo")
            if isinstance(imginfo, dict):
                img_name = imginfo.get("img_name") or imginfo.get("img_path") or imginfo.get("img")
                if isinstance(img_name, str) and img_name.strip():
                    img_page_hint = self._guess_page_index_from_name(Path(img_name), prepared)

            if contents and all(isinstance(item, list) for item in contents):
                if len(contents) == len(prepared.pages):
                    for idx, lines in enumerate(contents):
                        for entry in lines:
                            if not isinstance(entry, dict):
                                continue
                            text = _extract_text_from_mapping(entry)
                            bbox = _extract_bbox_from_mapping(entry)
                            if text and bbox is not None:
                                add_token(idx, OCRToken(text=text, x1=bbox[0], y1=bbox[1], x2=bbox[2], y2=bbox[3]))
                            elif text:
                                add_text(idx, text)
                    return token_map, text_map
                if len(contents) == 1 and img_page_hint is not None:
                    for entry in contents[0]:
                        if not isinstance(entry, dict):
                            continue
                        text = _extract_text_from_mapping(entry)
                        bbox = _extract_bbox_from_mapping(entry)
                        if text and bbox is not None:
                            add_token(img_page_hint, OCRToken(text=text, x1=bbox[0], y1=bbox[1], x2=bbox[2], y2=bbox[3]))
                        elif text:
                            add_text(img_page_hint, text)
                    return token_map, text_map

        def visit(node: Any, inherited_page_hint: Optional[int] = None) -> None:
            if isinstance(node, dict):
                page_hint = _extract_page_hint(node, inherited_page_hint, len(prepared.pages))
                text = _extract_text_from_mapping(node)
                bbox = _extract_bbox_from_mapping(node)
                if text and bbox is not None:
                    token = OCRToken(text=_normalize_ocr_text(text), x1=bbox[0], y1=bbox[1], x2=bbox[2], y2=bbox[3])
                    add_token(page_hint, token)
                    return
                elif text and _looks_like_text_leaf(node):
                    add_text(page_hint, text)
                    return

                for value in node.values():
                    visit(value, page_hint)
            elif isinstance(node, list):
                for item in node:
                    visit(item, inherited_page_hint)
            elif isinstance(node, str):
                pass

        visit(data)
        return token_map, text_map

    def _parse_xml_file(self, path: Path, prepared: PreparedDocument) -> tuple[Dict[int, List[OCRToken]], Dict[int, List[str]]]:
        try:
            tree = ET.parse(path)
        except Exception as e:
            raise RuntimeError(f"XML 読み込み失敗: {e}")
        root = tree.getroot()
        token_map: dict[int, list[OCRToken]] = {}
        text_map: dict[int, list[str]] = {}
        valid_pages = {p.index for p in prepared.pages}

        def add_token(page_hint: Optional[int], token: OCRToken) -> None:
            normalized = _normalize_ocr_text(token.text)
            if not normalized:
                return
            page_index = page_hint if page_hint in valid_pages else -1
            token_map.setdefault(page_index, []).append(OCRToken(text=normalized, x1=token.x1, y1=token.y1, x2=token.x2, y2=token.y2))

        def add_text(page_hint: Optional[int], text: str) -> None:
            cleaned = _normalize_ocr_text(text)
            if cleaned:
                page_index = page_hint if page_hint in valid_pages else -1
                text_map.setdefault(page_index, []).append(cleaned)

        # NDLOCR-Lite系 XML: <PAGE ...><LINE X= Y= WIDTH= HEIGHT= STRING=... /></PAGE>
        pages = [elem for elem in root.iter() if _local_xml_tag(elem.tag) == "PAGE"]
        if pages:
            for idx, page_elem in enumerate(pages):
                attrib_page = page_elem.attrib or {}
                page_hint = _extract_page_hint(attrib_page, None, len(prepared.pages))
                if page_hint is None:
                    img_name = attrib_page.get("IMAGENAME") or attrib_page.get("imageName") or attrib_page.get("IMG_NAME")
                    if img_name:
                        page_hint = self._guess_page_index_from_name(Path(img_name), prepared)
                if page_hint is None and idx < len(prepared.pages):
                    page_hint = idx

                page_texts: list[str] = []
                for line_elem in page_elem.iter():
                    if _local_xml_tag(line_elem.tag) != "LINE":
                        continue
                    attrib = line_elem.attrib or {}
                    text = attrib.get("STRING") or attrib.get("string") or _extract_xml_text(line_elem)
                    bbox = _extract_bbox_from_mapping(attrib)
                    if text and bbox is not None:
                        add_token(page_hint, OCRToken(text=text, x1=bbox[0], y1=bbox[1], x2=bbox[2], y2=bbox[3]))
                        page_texts.append(text)
                    elif text:
                        add_text(page_hint, text)
                        page_texts.append(text)
                if page_texts and page_hint is not None and page_hint in valid_pages and not text_map.get(page_hint):
                    text_map.setdefault(page_hint, []).append("\n".join(page_texts))
            if token_map or text_map:
                return token_map, text_map

        # ALTO / PAGE XML 系の汎用処理
        # 親領域(TextRegion/TextBlock)と子要素(Word/String/TextLine)を同時採用すると、
        # 全文コピー時に同一文が重複しやすい。細かい粒度を優先して1段階だけ読む。
        candidate_tags_by_priority = [
            {"String"},
            {"Word"},
            {"LINE"},
            {"TextLine"},
            {"TextRegion"},
            {"TextBlock"},
        ]
        available_tags = {_local_xml_tag(elem.tag) for elem in root.iter()}
        selected_tags: set[str] = set()
        for candidate_tags in candidate_tags_by_priority:
            if available_tags & candidate_tags:
                selected_tags = candidate_tags
                break

        for elem in root.iter():
            tag = _local_xml_tag(elem.tag)
            if selected_tags and tag not in selected_tags:
                continue
            attrib = elem.attrib or {}
            page_hint = _extract_page_hint(attrib, None, len(prepared.pages))

            if tag == "String":
                text = attrib.get("CONTENT") or attrib.get("content") or attrib.get("TEXT")
                bbox = _extract_bbox_from_mapping(attrib)
                if text and bbox is not None:
                    add_token(page_hint, OCRToken(text=text, x1=bbox[0], y1=bbox[1], x2=bbox[2], y2=bbox[3]))
                    continue
                if text:
                    add_text(page_hint, text)
                    continue

            if tag in {"Word", "TextLine", "TextRegion", "TextBlock", "LINE"}:
                text = attrib.get("STRING") or attrib.get("string") or _extract_xml_text(elem)
                coords = self._extract_xml_coords(elem)
                if text and coords is not None:
                    add_token(page_hint, OCRToken(text=text, x1=coords[0], y1=coords[1], x2=coords[2], y2=coords[3]))
                    continue
                if text:
                    add_text(page_hint, text)

        if not token_map and not text_map:
            whole_text = _normalize_space(" ".join(t for t in root.itertext() if (t or "").strip()))
            if whole_text:
                text_map.setdefault(-1, []).append(whole_text)
        return token_map, text_map

    @staticmethod
    def _extract_xml_coords(elem: ET.Element) -> Optional[tuple[float, float, float, float]]:
        # PAGE XML style: <Coords points="x1,y1 x2,y2 ..."/>
        for child in list(elem):
            if _local_xml_tag(child.tag) == "Coords":
                pts = _parse_points_string(child.attrib.get("points") or child.attrib.get("POINTS") or "")
                if pts:
                    return _bbox_from_points(pts)
        return _extract_bbox_from_mapping(elem.attrib)

    @staticmethod
    def _guess_page_index_from_name(path: Path, prepared: PreparedDocument) -> Optional[int]:
        name = path.stem.lower()
        page_count = len(prepared.pages)
        exact_num = _extract_page_number_from_name(name)
        if exact_num is not None and 1 <= exact_num <= page_count:
            return exact_num - 1
        if page_count == 1:
            return prepared.pages[0].index

        best: tuple[int, int] | None = None
        for page in prepared.pages:
            candidates = {
                page.image_path.stem.lower(),
                f"p{page.index+1:04d}",
                f"page{page.index+1}",
                f"_{page.index+1:04d}",
            }
            score = 0
            for c in candidates:
                if c and c in name:
                    score += len(c)
            overlap = len(_tokenize_name(name) & _tokenize_name(page.image_path.stem.lower()))
            score += overlap
            if score > 0 and (best is None or score > best[0]):
                best = (score, page.index)
        return best[1] if best else None


class SearchablePdfBuilderBase:
    def __init__(self, *, log: Callable[[str, str], None]) -> None:
        self._log = log
        self._font_name = self._register_font()

    def _register_font(self) -> str:
        if pdfmetrics is None:
            raise RuntimeError("reportlab が利用できません（`py -m pip install reportlab`）")

        windir = os.environ.get("WINDIR", r"C:\Windows")
        fonts_dir = Path(windir) / "Fonts"
        # TrueType / TrueType Collection を優先。ToUnicode を持ちやすく、
        # 日本語抽出時の不自然な空白が CID フォントより出にくい。
        candidates = [
            (fonts_dir / "msgothic.ttc", 0, "NDLOCRWinMSGothic"),
            (fonts_dir / "meiryo.ttc", 0, "NDLOCRWinMeiryo"),
            (fonts_dir / "YuGothM.ttc", 0, "NDLOCRWinYuGothicM"),
            (fonts_dir / "yugothm.ttc", 0, "NDLOCRWinYuGothicM2"),
            (fonts_dir / "msmincho.ttc", 0, "NDLOCRWinMSMincho"),
        ]
        if TTFont is not None:
            for font_path, subfont_index, font_name in candidates:
                try:
                    if not font_path.exists():
                        continue
                    try:
                        pdfmetrics.getFont(font_name)
                    except Exception:
                        pdfmetrics.registerFont(TTFont(font_name, str(font_path), subfontIndex=subfont_index, validate=0))
                    self._log("INFO", LogMessageBuilder.font_embedded(font_path.name))
                    return font_name
                except Exception:
                    continue

        if UnicodeCIDFont is None:
            raise RuntimeError("reportlab の日本語フォント登録に失敗しました")
        try:
            pdfmetrics.getFont(DEFAULT_CJK_FONT)
        except Exception:
            pdfmetrics.registerFont(UnicodeCIDFont(DEFAULT_CJK_FONT))
        self._log("INFO", LogMessageBuilder.font_cid(DEFAULT_CJK_FONT))
        return DEFAULT_CJK_FONT

    def _draw_overlay_page(self, c: Any, page: PreparedPage, ocr: PageOcrData) -> None:
        if ocr.tokens:
            self._draw_invisible_tokens(c, page, ocr.tokens)
        elif ocr.text_blocks:
            self._draw_invisible_text_blocks(c, page, ocr.text_blocks)

    def _draw_invisible_tokens(self, c: Any, page: PreparedPage, tokens: List[OCRToken]) -> None:
        sx = page.width_pt / max(page.width_px, 1)
        sy = page.height_pt / max(page.height_px, 1)
        if _is_vertical_page(tokens):
            self._draw_invisible_vertical_columns(c, page, tokens, sx, sy)
            return
        for line_tokens in _group_tokens_into_lines(tokens):
            line_text = _join_tokens_for_hidden_line(line_tokens)
            if not line_text:
                continue
            min_x = min(float(t.x1) for t in line_tokens)
            max_x = max(float(t.x2) for t in line_tokens)
            max_y = max(float(t.y2) for t in line_tokens)
            avg_h_px = sum(_token_height(t) for t in line_tokens) / max(1, len(line_tokens))

            bbox_w_pt = max(1.0, (max_x - min_x) * sx)
            bbox_h_pt = max(1.0, avg_h_px * sy)
            x_pt = max(0.0, min_x * sx)
            baseline = page.height_pt - (max_y * sy) + max(0.5, bbox_h_pt * 0.15)
            font_size = max(4.0, min(72.0, bbox_h_pt * 0.85))

            try:
                width_now = pdfmetrics.stringWidth(line_text, self._font_name, font_size)
            except Exception:
                width_now = 0.0
            # 横書き行では、文字列幅がそのまま選択帯の横方向長さになりやすい。
            # 行高に合わせたフォントサイズは維持しつつ、必要に応じて水平方向スケールで
            # 行幅へ寄せて、選択帯の長さ不足/過剰を抑える。
            horiz_scale = 100.0
            if width_now > 0:
                horiz_scale = max(70.0, min(170.0, (bbox_w_pt / width_now) * 100.0))
                if horiz_scale < 85.0:
                    font_size = max(3.0, font_size * (horiz_scale / 100.0))
                    horiz_scale = 100.0
                    try:
                        width_now = pdfmetrics.stringWidth(line_text, self._font_name, font_size)
                    except Exception:
                        width_now = 0.0
                    if width_now > 0:
                        horiz_scale = max(70.0, min(170.0, (bbox_w_pt / width_now) * 100.0))

            text_obj = c.beginText()
            text_obj.setTextRenderMode(3)
            try:
                text_obj.setCharSpace(0)
            except Exception:
                pass
            text_obj.setFont(self._font_name, font_size)
            try:
                text_obj.setHorizScale(horiz_scale)
            except Exception:
                pass
            text_obj.setTextOrigin(x_pt, max(0.0, min(page.height_pt - font_size, baseline)))
            text_obj.textOut(line_text)
            c.drawText(text_obj)

    def _draw_invisible_vertical_columns(self, c: Any, page: PreparedPage, tokens: List[OCRToken], sx: float, sy: float) -> None:
        for column_tokens in _group_tokens_into_vertical_columns(tokens):
            column_text = _join_tokens_for_vertical_hidden_column(column_tokens)
            if not column_text:
                continue

            min_x = min(float(t.x1) for t in column_tokens)
            max_x = max(float(t.x2) for t in column_tokens)
            min_y = min(float(t.y1) for t in column_tokens)
            max_y = max(float(t.y2) for t in column_tokens)
            avg_w_px = sum(_token_width(t) for t in column_tokens) / max(1, len(column_tokens))

            bbox_w_pt = max(1.0, max((max_x - min_x) * sx, avg_w_px * sx))
            bbox_h_pt = max(1.0, (max_y - min_y) * sy)
            x_left_pt = max(0.0, min_x * sx)
            y_top_pt = max(0.0, page.height_pt - (min_y * sy))

            font_size = max(4.0, min(72.0, bbox_w_pt * 0.92))
            try:
                width_now = pdfmetrics.stringWidth(column_text, self._font_name, font_size)
            except Exception:
                width_now = 0.0
            # 縦書き列は回転後、文字列の advance 幅がそのまま縦方向の選択長さになる。
            # フォントサイズだけで合わせると列の横幅を崩しやすいため、まずは列幅に合わせた
            # フォントサイズを維持し、必要に応じて水平方向スケールで縦方向の長さを補正する。
            horiz_scale = 100.0
            if width_now > 0:
                horiz_scale = max(70.0, min(170.0, (bbox_h_pt / width_now) * 100.0))
                if horiz_scale < 85.0:
                    font_size = max(3.0, font_size * (horiz_scale / 100.0))
                    horiz_scale = 100.0
                    try:
                        width_now = pdfmetrics.stringWidth(column_text, self._font_name, font_size)
                    except Exception:
                        width_now = 0.0
                    if width_now > 0:
                        horiz_scale = max(70.0, min(170.0, (bbox_h_pt / width_now) * 100.0))

            try:
                ascent, descent = pdfmetrics.getAscentDescent(self._font_name, font_size)
            except Exception:
                ascent, descent = font_size * 0.88, -font_size * 0.12
            glyph_band_w = max(1.0, float(ascent) - float(descent))
            left_pad = max(0.0, (bbox_w_pt - glyph_band_w) / 2.0)
            translate_x = x_left_pt + left_pad - float(descent)
            translate_y = y_top_pt

            c.saveState()
            try:
                # 回転後の glyph band を列幅の中央に置き、列の上端を文頭に合わせる。
                c.translate(translate_x, translate_y)
                c.rotate(-90)
                text_obj = c.beginText()
                text_obj.setTextRenderMode(3)
                try:
                    text_obj.setCharSpace(0)
                except Exception:
                    pass
                text_obj.setFont(self._font_name, font_size)
                try:
                    text_obj.setHorizScale(horiz_scale)
                except Exception:
                    pass
                text_obj.setTextOrigin(0, 0)
                text_obj.textOut(column_text)
                c.drawText(text_obj)
            finally:
                c.restoreState()

    def _draw_invisible_text_blocks(self, c: Any, page: PreparedPage, text_blocks: List[str]) -> int:
        margin_x = 12.0
        top_y = page.height_pt - 18.0
        line_height = 10.0
        current_y = top_y
        written = 0
        for block in text_blocks:
            wrapped = _wrap_for_hidden_text(block, 60)
            if not wrapped:
                continue
            for line in wrapped:
                if current_y < 12.0:
                    return written
                text_obj = c.beginText()
                text_obj.setTextRenderMode(3)
                try:
                    text_obj.setCharSpace(0)
                except Exception:
                    pass
                text_obj.setFont(self._font_name, 8.0)
                text_obj.setTextOrigin(margin_x, current_y)
                text_obj.textLine(line)
                c.drawText(text_obj)
                written += 1
                current_y -= line_height
            current_y -= 4.0
        return written


class SearchablePdfBuilderForImages(SearchablePdfBuilderBase):
    def build(self, prepared: PreparedDocument, ocr_pages: Dict[int, PageOcrData], out_pdf: Path) -> None:
        if canvas is None or ImageReader is None or pdfmetrics is None:
            raise RuntimeError("reportlab が利用できません（`py -m pip install reportlab`）")

        if out_pdf.exists():
            try:
                out_pdf.unlink()
            except Exception as e:
                raise RuntimeError(f"既存出力ファイル削除失敗: {e}")
        out_pdf.parent.mkdir(parents=True, exist_ok=True)

        tmp_pdf = out_pdf.with_suffix(out_pdf.suffix + ".tmp.pdf")
        if tmp_pdf.exists():
            try:
                tmp_pdf.unlink()
            except Exception:
                pass

        c = canvas.Canvas(str(tmp_pdf), pagesize=(prepared.pages[0].width_pt, prepared.pages[0].height_pt))
        try:
            for page in prepared.pages:
                c.setPageSize((page.width_pt, page.height_pt))
                c.drawImage(
                    ImageReader(str(page.image_path)),
                    0,
                    0,
                    width=page.width_pt,
                    height=page.height_pt,
                    preserveAspectRatio=False,
                    mask="auto",
                )
                self._draw_overlay_page(c, page, ocr_pages.get(page.index, PageOcrData()))
                c.showPage()
            c.save()
            tmp_pdf.replace(out_pdf)
        except Exception:
            try:
                c.save()
            except Exception:
                pass
            try:
                if tmp_pdf.exists():
                    tmp_pdf.unlink()
            except Exception:
                pass
            raise
        self._log("INFO", LogMessageBuilder.pdf_rebuild(out_pdf.name))


class SearchablePdfOverlayBuilderForPdf(SearchablePdfBuilderBase):
    def build(self, prepared: PreparedDocument, ocr_pages: Dict[int, PageOcrData], out_pdf: Path) -> None:
        if canvas is None or pdfmetrics is None:
            raise RuntimeError("reportlab が利用できません（`py -m pip install reportlab`）")
        if PdfReader is None or PdfWriter is None or DecodedStreamObject is None or NameObject is None:
            raise RuntimeError("pypdf が利用できません（`py -m pip install pypdf`）")
        if prepared.input_kind != INPUT_KIND_PDF or prepared.original_pdf_path is None:
            raise RuntimeError("PDF重畳ビルダーは PDF入力専用です")

        if out_pdf.exists():
            try:
                out_pdf.unlink()
            except Exception as e:
                raise RuntimeError(f"既存出力ファイル削除失敗: {e}")
        out_pdf.parent.mkdir(parents=True, exist_ok=True)

        tmp_pdf = out_pdf.with_suffix(out_pdf.suffix + ".tmp.pdf")
        if tmp_pdf.exists():
            try:
                tmp_pdf.unlink()
            except Exception:
                pass

        try:
            reader = PdfReader(str(prepared.original_pdf_path))
            if getattr(reader, "is_encrypted", False):
                try:
                    dec_result = reader.decrypt("")
                except Exception as e:
                    raise RuntimeError(f"暗号化PDFのため出力できません: {e}")
                if not dec_result:
                    raise RuntimeError("暗号化PDFのため出力できません（パスワード解除後に再実行してください）")

            writer = PdfWriter()
            writer.clone_document_from_reader(reader)
            if len(writer.pages) != len(prepared.pages):
                raise RuntimeError("出力用PDFのページ数が一致しません")

            # 一部のPDFでは複数ページが同じ /Contents オブジェクトを共有している。
            # その状態で merge_page() すると、あるページへ重ねた OCR テキストが
            # 他ページにも漏れて、全文コピー時に「全ページ同じ文が重なる」現象が起きる。
            # 先に各ページの /Contents を独立したストリームへ張り替えてから merge する。
            self._detach_shared_contents_per_page(writer)

            for page_index, page in enumerate(writer.pages):
                try:
                    rotation = int(getattr(page, "rotation", 0) or 0) % 360
                except Exception:
                    rotation = 0
                if rotation:
                    page.transfer_rotation_to_content()

                overlay_bytes = self._build_single_overlay_pdf_bytes(
                    prepared.pages[page_index],
                    ocr_pages.get(page_index, PageOcrData()),
                )
                if overlay_bytes:
                    overlay_reader = PdfReader(io.BytesIO(overlay_bytes))
                    if len(overlay_reader.pages) != 1:
                        raise RuntimeError("ページ単位のOCR重畳PDF生成に失敗しました")
                    overlay_page = overlay_reader.pages[0]
                    self._merge_overlay_page(page, overlay_page)
                try:
                    page.compress_content_streams()
                except Exception:
                    pass

            try:
                writer.compress_identical_objects(remove_identicals=True, remove_orphans=True)
            except Exception:
                pass

            with tmp_pdf.open("wb") as fp:
                writer.write(fp)
            tmp_pdf.replace(out_pdf)
        except Exception:
            try:
                if tmp_pdf.exists():
                    tmp_pdf.unlink()
            except Exception:
                pass
            raise
        self._log("INFO", LogMessageBuilder.pdf_overlay_rebuild(out_pdf.name))

    @staticmethod
    def _detach_shared_contents_per_page(writer: Any) -> None:
        for page in writer.pages:
            try:
                contents = page.get_contents()
            except Exception:
                contents = None
            try:
                data = contents.get_data() if contents is not None else b""
            except Exception:
                data = b""
            new_stream = DecodedStreamObject()
            try:
                new_stream.set_data(data)
            except Exception:
                new_stream.set_data(b"")
            page[NameObject("/Contents")] = writer._add_object(new_stream)

    def _build_single_overlay_pdf_bytes(self, page: PreparedPage, ocr: PageOcrData) -> bytes | None:
        if not ocr.tokens and not ocr.text_blocks:
            return None
        buffer = io.BytesIO()
        c = canvas.Canvas(buffer, pagesize=(page.width_pt, page.height_pt))
        try:
            c.setPageSize((page.width_pt, page.height_pt))
            self._draw_overlay_page(c, page, ocr)
            c.showPage()
            c.save()
        except Exception:
            try:
                c.save()
            except Exception:
                pass
            raise
        return buffer.getvalue()

    @staticmethod
    def _merge_overlay_page(base_page: Any, overlay_page: Any) -> None:
        try:
            base_w = float(base_page.cropbox.width)
            base_h = float(base_page.cropbox.height)
        except Exception:
            base_w = float(base_page.mediabox.width)
            base_h = float(base_page.mediabox.height)
        overlay_w = float(overlay_page.mediabox.width)
        overlay_h = float(overlay_page.mediabox.height)

        if abs(base_w - overlay_w) <= 0.5 and abs(base_h - overlay_h) <= 0.5:
            base_page.merge_page(overlay_page, over=True)
            return

        scale_x = base_w / max(overlay_w, 1.0)
        scale_y = base_h / max(overlay_h, 1.0)
        from pypdf import Transformation

        base_page.merge_transformed_page(
            overlay_page,
            Transformation().scale(scale_x, scale_y),
            over=True,
            expand=False,
        )


class SearchablePdfBuildCoordinator:
    def __init__(
        self,
        *,
        image_builder: SearchablePdfBuilderForImages,
        pdf_overlay_builder: SearchablePdfOverlayBuilderForPdf,
    ) -> None:
        self._image_builder = image_builder
        self._pdf_overlay_builder = pdf_overlay_builder

    def build(self, prepared: PreparedDocument, ocr_pages: Dict[int, PageOcrData], out_pdf: Path) -> None:
        if prepared.input_kind == INPUT_KIND_PDF and prepared.original_pdf_path is not None and not PREFER_IMAGE_REBUILD_FOR_PDF:
            self._pdf_overlay_builder.build(prepared, ocr_pages, out_pdf)
            return
        self._image_builder.build(prepared, ocr_pages, out_pdf)


class OutputPathResolver:
    def _resolve_output_dir(
        self,
        *,
        source_path: Path,
        input_root_folder: Path,
        output_mode: str,
        custom_output_dir: Optional[Path],
    ) -> Path:
        normalized = normalize_output_mode(output_mode)
        if normalized == OUTPUT_MODE_SAME_FOLDER:
            return source_path.parent
        if normalized == OUTPUT_MODE_INPUT_FOLDER:
            input_base = input_root_folder if input_root_folder.is_dir() else input_root_folder.parent
            out_dir = input_base / "ocr_output"
        elif normalized == OUTPUT_MODE_CUSTOM_FOLDER:
            if custom_output_dir is None:
                raise RuntimeError("指定フォルダ出力が選択されていますが、出力先フォルダが未設定です。")
            out_dir = custom_output_dir
        else:
            out_dir = source_path.parent
        out_dir.mkdir(parents=True, exist_ok=True)
        return out_dir

    def default_output_path(
        self,
        source_path: Path,
        input_root_folder: Path,
        output_mode: str,
        custom_output_dir: Optional[Path],
    ) -> Path:
        out_name = source_path.stem + OUTPUT_SUFFIX + ".pdf"
        out_dir = self._resolve_output_dir(
            source_path=source_path,
            input_root_folder=input_root_folder,
            output_mode=output_mode,
            custom_output_dir=custom_output_dir,
        )
        return out_dir / out_name

    def make_output_path(
        self,
        source_path: Path,
        input_root_folder: Path,
        output_mode: str,
        custom_output_dir: Optional[Path],
        overwrite: bool,
    ) -> Path:
        base = self.default_output_path(source_path, input_root_folder, output_mode, custom_output_dir)
        if overwrite or (not base.exists()):
            return base
        parent = base.parent
        stem = base.stem
        suffix = base.suffix
        for i in range(1, 10000):
            cand = parent / f"{stem}_{i:03d}{suffix}"
            if not cand.exists():
                return cand
        raise RuntimeError("連番出力先を確保できませんでした（_001〜_9999 が埋まっています）")


class RuntimeSupport:
    LAUNCHER_BASENAMES = (
        "ndlocr-lite",
        "ndlocr-lite.exe",
        "ndlocr_lite",
        "ndlocr_lite.exe",
        "NDLOCR-Lite.exe",
        "NDLOCR-Lite",
        "ndlocr_lite_gui.exe",
        "ndlocr_lite_gui",
        "ndlocr-lite-gui.exe",
        "ndlocr-lite-gui",
        "NDLOCR_Lite_GUI.exe",
        "NDLOCR_Lite_GUI",
    )

    def __init__(self, *, has_pypdf: bool, has_pillow: bool, has_pdfium: bool, has_reportlab: bool) -> None:
        self._has_pypdf = bool(has_pypdf)
        self._has_pillow = bool(has_pillow)
        self._has_pdfium = bool(has_pdfium)
        self._has_reportlab = bool(has_reportlab)

    def reset_ndlocr_launcher_cache(self) -> None:
        return

    def validate_runtime_settings(self, command_template: str) -> tuple[bool, str]:
        template = (command_template or "").strip()
        if not template:
            return False, f"{NDLOCR_COMMAND_LABEL} を指定してください。"
        if ("{input_dir}" not in template) and ("{input}" not in template):
            return False, f"{NDLOCR_COMMAND_LABEL} には {{input_dir}} または {{input}} を含めてください。"
        if "{output_dir}" not in template:
            return False, f"{NDLOCR_COMMAND_LABEL} には {{output_dir}} を含めてください。"
        try:
            _ = template.format(
                input="INPUT.png",
                input_dir="INPUT_DIR",
                output_dir="OUTDIR",
                output_pdf="OUT.pdf",
                output_stem="OUT",
            )
        except KeyError as e:
            return False, f"{NDLOCR_COMMAND_LABEL} に未対応のプレースホルダがあります: {e}"
        except Exception as e:
            return False, f"{NDLOCR_COMMAND_LABEL} の検証に失敗しました: {e}"
        return True, ""

    def check_dependencies(self, return_message: bool = False, engine_path: str = "") -> tuple[bool, str]:
        problems: List[str] = []
        if not self._has_pypdf:
            problems.append("- Python ライブラリ `pypdf` が見つかりません（`py -m pip install pypdf`）")
        if not self._has_pillow:
            problems.append("- Python ライブラリ `pillow` が見つかりません（`py -m pip install pillow`）")
        if not self._has_pdfium:
            problems.append("- Python ライブラリ `pypdfium2` が見つかりません（`py -m pip install pypdfium2`）")
        if not self._has_reportlab:
            problems.append("- Python ライブラリ `reportlab` が見つかりません（`py -m pip install reportlab`）")
        try:
            _ = self.resolve_ndlocr_launcher(engine_path)
        except Exception as e:
            if engine_path:
                problems.append(f"- 指定された {PYTHON_EXECUTABLE_LABEL} を利用できません: {e}")
            else:
                problems.append(
                    "- {PYTHON_EXECUTABLE_LABEL} が見つかりません。"
                    " 実行ファイルパスを指定するか、PATH の通った場所に配置してください。"
                    f" ({e})"
                )
        ok = len(problems) == 0
        msg = "\n".join(problems) if problems else "OK"
        if return_message:
            return ok, msg
        return ok, ""

    def find_local_ndlocr_script(self) -> Optional[list[str]]:
        candidates: list[Path] = []
        py = Path(sys.executable)
        search_dirs = [py.parent, py.parent / "Scripts", py.parent.parent / "bin", Path.cwd()]
        for base in search_dirs:
            for name in self.LAUNCHER_BASENAMES:
                candidates.append(base / name)
        for c in candidates:
            try:
                if c.exists() and c.is_file():
                    return [str(c)]
            except Exception:
                continue
        return None

    def resolve_ndlocr_launcher(self, engine_path: str = "") -> list[str]:
        user_path = (engine_path or "").strip()
        if user_path:
            p = Path(user_path)
            if not p.exists():
                raise RuntimeError(f"指定ファイルが存在しません: {user_path}")
            if not p.is_file():
                raise RuntimeError(f"指定パスはファイルではありません: {user_path}")
            return [str(p)]
        for name in self.LAUNCHER_BASENAMES:
            hit = shutil.which(name)
            if hit:
                return [hit]
        local_script = self.find_local_ndlocr_script()
        if local_script:
            return local_script
        raise RuntimeError("候補なし")


class BatchProcessor:
    def __init__(
        self,
        *,
        csv_logger: CsvLogger,
        file_planner: InputFilePlanner,
        runtime_issue_resolver: RuntimeIssueResolver,
        prepare_document: Callable[[Path, RunConfig], PreparedDocument],
        run_ocr_engine: Callable[..., None],
        parse_ocr_results: Callable[[Path, PreparedDocument], Dict[int, PageOcrData]],
        build_searchable_pdf: Callable[[PreparedDocument, Dict[int, PageOcrData], Path], None],
        update_progress_ui: Callable[[int, int, str], None],
        log: Callable[[str, str], None],
        completion_resolver: Optional[BatchCompletionResolver] = None,
    ) -> None:
        self._csv_logger = csv_logger
        self._file_planner = file_planner
        self._runtime_issue_resolver = runtime_issue_resolver
        self._prepare_document = prepare_document
        self._run_ocr_engine = run_ocr_engine
        self._parse_ocr_results = parse_ocr_results
        self._build_searchable_pdf = build_searchable_pdf
        self._update_progress_ui = update_progress_ui
        self._log = log
        self._completion_resolver = completion_resolver or BatchCompletionResolver()

    def _apply_skip_decision(
        self,
        *,
        idx: int,
        total: int,
        row: CsvLogRow,
        result: ProcessResult,
        skip_decision: FileSkipDecision,
    ) -> None:
        if skip_decision.action == "skip_name":
            result.skipped_name_rule += 1
        elif skip_decision.action == "skip_has_text":
            result.skipped_has_text += 1
        row.action = skip_decision.action
        row.detail = skip_decision.csv_detail or skip_decision.detail
        self._log(skip_decision.log_entry.kind, skip_decision.log_entry.message)
        self._update_progress_ui(idx, total, skip_decision.progress_status)

    def _run_pipeline(
        self,
        *,
        idx: int,
        total: int,
        source_path: Path,
        row: CsvLogRow,
        run_config: RunConfig,
    ) -> tuple[PreparedDocument, Path, str]:
        output_plan = self._file_planner.plan_output(
            source_path,
            input_root_folder=run_config.folder,
            output_mode=run_config.output_mode,
            custom_output_dir=run_config.custom_output_dir,
            overwrite=run_config.overwrite,
        )
        out_path = output_plan.output_path
        row.output = str(out_path)
        for entry in output_plan.pre_logs:
            self._log(entry.kind, entry.message)

        self._log("INFO", LogMessageBuilder.ocr_start(source_path.name, out_path.name))
        self._update_progress_ui(idx - 1, total, ProgressStatusBuilder.preparing(source_path.name))
        prepared = self._prepare_document(source_path, run_config)

        with tempfile.TemporaryDirectory(prefix="ndlocr_out_") as td:
            ndlocr_outdir = Path(td)
            single_input = prepared.pages[0].image_path if prepared.page_count == 1 else None
            self._update_progress_ui(idx - 1, total, ProgressStatusBuilder.running_ocr(source_path.name))
            self._run_ocr_engine(
                input_dir=prepared.input_dir,
                single_input=single_input,
                outdir=ndlocr_outdir,
                out_pdf=out_path,
                command_template=run_config.command_template,
                engine_path=run_config.engine_path,
                timeout_sec=run_config.execution.ndlocr_timeout_sec,
            )
            self._update_progress_ui(idx - 1, total, ProgressStatusBuilder.parsing(source_path.name))
            ocr_pages = self._parse_ocr_results(ndlocr_outdir, prepared)
            if not any(v.has_any_text() for v in ocr_pages.values()):
                raise RuntimeError(
                    "NDLOCR-Lite の出力から OCR 文字情報（JSON/XML/TXT）を取得できませんでした。"
                    " CLI 側の出力設定を確認してください。"
                )
            self._update_progress_ui(idx - 1, total, ProgressStatusBuilder.rebuilding_pdf(source_path.name))
            self._build_searchable_pdf(prepared, ocr_pages, out_path)

        if not (out_path.exists() and out_path.stat().st_size > 0):
            raise RuntimeError("OCR 実行後に出力ファイルが確認できませんでした")
        return prepared, out_path, output_plan.csv_detail_suffix

    def _mark_success(
        self,
        *,
        idx: int,
        total: int,
        source_path: Path,
        prepared: PreparedDocument,
        out_path: Path,
        row: CsvLogRow,
        result: ProcessResult,
        output_conflict_detail: str,
    ) -> None:
        result.processed += 1
        row.action = "ocr_done"
        if prepared.input_kind == INPUT_KIND_PDF and not PREFER_IMAGE_REBUILD_FOR_PDF:
            output_route = "元PDF保持 + 不可視テキスト重畳"
        else:
            output_route = "画像背景 + 不可視テキスト重畳"
        row.detail = f"OK ({prepared.page_count}ページ / {output_route} / {output_conflict_detail})"
        self._log("DONE", LogMessageBuilder.output_done(out_path))
        self._update_progress_ui(idx, total, ProgressStatusBuilder.done(source_path.name))

    def _mark_stopped(
        self,
        *,
        idx: int,
        total: int,
        source_path: Path,
        row: CsvLogRow,
        exc: OCRStopRequested,
    ) -> None:
        issue = self._runtime_issue_resolver.resolve_stop(exc)
        row.action = "stopped"
        row.detail = issue.user_message
        self._log("WARN", LogMessageBuilder.stopped(source_path.name, issue.log_detail))
        self._update_progress_ui(idx - 1, total, ProgressStatusBuilder.stopped(source_path.name))

    def _mark_error(
        self,
        *,
        idx: int,
        total: int,
        source_path: Path,
        row: CsvLogRow,
        result: ProcessResult,
        exc: Exception,
    ) -> None:
        issue = self._runtime_issue_resolver.resolve_error(exc)
        result.errors += 1
        row.action = "error"
        row.detail = issue.user_message
        self._log("ERROR", LogMessageBuilder.item_error(source_path.name, issue.log_detail))
        self._update_progress_ui(idx, total, ProgressStatusBuilder.error(source_path.name))

    def process_one(
        self,
        *,
        idx: int,
        total: int,
        source_path: Path,
        run_config: RunConfig,
        result: ProcessResult,
    ) -> bool:
        t0 = time.perf_counter()
        row = self._csv_logger.new_row(source_path, run_config)
        prepared: Optional[PreparedDocument] = None

        try:
            self._update_progress_ui(idx - 1, total, ProgressStatusBuilder.checking(source_path.name))

            skip_decision = self._file_planner.detect_skip(source_path)
            if skip_decision is not None:
                self._apply_skip_decision(
                    idx=idx,
                    total=total,
                    row=row,
                    result=result,
                    skip_decision=skip_decision,
                )
                return False

            prepared, out_path, output_conflict_detail = self._run_pipeline(
                idx=idx,
                total=total,
                source_path=source_path,
                row=row,
                run_config=run_config,
            )
            self._mark_success(
                idx=idx,
                total=total,
                source_path=source_path,
                prepared=prepared,
                out_path=out_path,
                row=row,
                result=result,
                output_conflict_detail=output_conflict_detail,
            )
            return False

        except OCRStopRequested as e:
            self._mark_stopped(
                idx=idx,
                total=total,
                source_path=source_path,
                row=row,
                exc=e,
            )
            return True
        except Exception as e:
            self._mark_error(
                idx=idx,
                total=total,
                source_path=source_path,
                row=row,
                result=result,
                exc=e,
            )
            return False
        finally:
            if prepared is not None:
                prepared.cleanup()
            row.seconds = f"{time.perf_counter() - t0:.2f}"
            self._csv_logger.append_row(row)


class BatchCompletionResolver:
    @staticmethod
    def build_final_message(summary: RunSummary) -> str:
        return LogMessageBuilder.final_summary(summary)

    @staticmethod
    def build_final_outcome(summary: RunSummary) -> BatchRunOutcome:
        result = summary.result
        if result.total == 0:
            return BatchRunOutcome(final_status="完了（対象なし）", ui_current=0, ui_total=0)
        processed_count = result.processed + result.skipped_has_text + result.skipped_name_rule + result.errors
        return BatchRunOutcome(
            final_status="停止済み" if summary.was_stopped else "完了",
            ui_current=min(processed_count, max(result.total, 1)),
            ui_total=max(result.total, 1),
        )

    @classmethod
    def build_presentation(cls, summary: RunSummary) -> BatchCompletionPresentation:
        return BatchCompletionPresentation(
            final_log_kind=("WARN" if summary.was_stopped else "DONE"),
            final_log_message=cls.build_final_message(summary),
            outcome=cls.build_final_outcome(summary),
        )


class BatchRunCoordinator:
    def __init__(
        self,
        *,
        collect_inputs: Callable[[Path, bool], List[Path]],
        make_csv_log_path: Callable[[Path], Path],
        csv_logger: CsvLogger,
        batch_processor: BatchProcessor,
        is_stop_requested: Callable[[], bool],
        update_progress_ui: Callable[[int, int, str], None],
        log: Callable[[str, str], None],
        completion_resolver: Optional[BatchCompletionResolver] = None,
    ) -> None:
        self._collect_inputs = collect_inputs
        self._make_csv_log_path = make_csv_log_path
        self._csv_logger = csv_logger
        self._batch_processor = batch_processor
        self._is_stop_requested = is_stop_requested
        self._update_progress_ui = update_progress_ui
        self._log = log
        self._completion_resolver = completion_resolver or BatchCompletionResolver()

    def _write_csv_if_needed(
        self,
        *,
        csv_log_path: Optional[Path],
        run_config: RunConfig,
        summary: RunSummary,
    ) -> None:
        if not csv_log_path:
            return
        try:
            self._csv_logger.write(csv_log_path, run_config, summary)
            self._log("DONE", LogMessageBuilder.csv_done(csv_log_path))
        except Exception as e:
            self._log("ERROR", LogMessageBuilder.csv_error(str(e)))

    def run(self, run_config: RunConfig) -> BatchRunOutcome:
        folder = run_config.folder
        recursive = run_config.recursive
        started_at = datetime.now()
        csv_log_path: Optional[Path] = None
        result = ProcessResult()
        was_stopped = False

        inputs = self._collect_inputs(folder, recursive)
        result.total = len(inputs)
        total = result.total

        csv_base_dir = folder if folder.is_dir() else folder.parent
        if run_config.write_csv_log:
            csv_log_path = self._make_csv_log_path(csv_base_dir)
            self._log("INFO", LogMessageBuilder.csv_path(csv_log_path))

        if total == 0:
            self._log("WARN", LogMessageBuilder.no_inputs_found())
            summary = RunSummary(started_at=started_at, ended_at=datetime.now(), result=result, was_stopped=False)
            self._write_csv_if_needed(csv_log_path=csv_log_path, run_config=run_config, summary=summary)
            return self._completion_resolver.build_final_outcome(summary)

        target_kind = "folder" if folder.is_dir() else "file"
        self._log("INFO", LogMessageBuilder.input_scope(target_kind=target_kind, recursive=recursive))
        self._log("INFO", LogMessageBuilder.target_count(total, recursive=recursive, target_kind=target_kind))
        self._update_progress_ui(0, total, ProgressStatusBuilder.batch_running())

        for idx, source_path in enumerate(inputs, start=1):
            if self._is_stop_requested():
                was_stopped = True
                self._log("WARN", LogMessageBuilder.stop_interrupted())
                break

            stopped_in_item = self._batch_processor.process_one(
                idx=idx,
                total=total,
                source_path=source_path,
                run_config=run_config,
                result=result,
            )
            if stopped_in_item:
                was_stopped = True
                break

        summary = RunSummary(started_at=started_at, ended_at=datetime.now(), result=result, was_stopped=was_stopped)
        presentation = self._completion_resolver.build_presentation(summary)
        self._log(presentation.final_log_kind, presentation.final_log_message)
        self._write_csv_if_needed(csv_log_path=csv_log_path, run_config=run_config, summary=summary)
        return presentation.outcome


class RunUiStateCoordinator:
    def __init__(
        self,
        *,
        root: tk.Tk,
        progress: Any,
        status_var: tk.StringVar,
        progress_text_var: tk.StringVar,
        btn_start: Any,
        btn_stop: Any,
        set_runtime_controls_enabled: Callable[[bool], None],
        reset_run_state: Callable[[], None],
    ) -> None:
        self._root = root
        self._progress = progress
        self._status_var = status_var
        self._progress_text_var = progress_text_var
        self._btn_start = btn_start
        self._btn_stop = btn_stop
        self._set_runtime_controls_enabled = set_runtime_controls_enabled
        self._reset_run_state = reset_run_state

    @staticmethod
    def _calc_progress_pct(current: int, total: int) -> float:
        return _calculate_progress_pct(current, total)

    @staticmethod
    def _format_progress_text(current: int, total: int) -> str:
        return f"{min(current, total)} / {total}"

    def _apply_progress_core(self, *, current: int, total: int, status: str) -> None:
        pct = self._calc_progress_pct(current, total)
        self._progress.configure(value=pct, maximum=DEFAULT_PROGRESS_MAX)
        self._status_var.set(status)
        self._progress_text_var.set(self._format_progress_text(current, total))

    def apply_started(self, state: StartUiState) -> None:
        self._apply_progress_core(current=state.current, total=state.total, status=state.status)
        self._btn_start.configure(state="disabled")
        self._btn_stop.configure(state="normal")
        self._set_runtime_controls_enabled(False)

    def apply_progress(self, state: ProgressUiState) -> None:
        self._apply_progress_core(current=state.current, total=state.total, status=state.status)

    def schedule_progress(self, state: ProgressUiState) -> None:
        self._root.after(0, lambda: self.apply_progress(state))

    def apply_finished(self, state: FinishUiState) -> None:
        self._apply_progress_core(current=state.current, total=state.total, status=state.status)
        self._btn_start.configure(state="normal")
        self._btn_stop.configure(state="disabled")
        self._set_runtime_controls_enabled(True)
        self._reset_run_state()

    def schedule_finished(self, state: FinishUiState) -> None:
        self._root.after(0, lambda: self.apply_finished(state))


class LogPumpCoordinator:
    def __init__(
        self,
        *,
        root: tk.Tk,
        log_queue: LogQueue,
        text_widget: tk.Text,
        interval_ms: int,
    ) -> None:
        self._root = root
        self._log_queue = log_queue
        self._text_widget = text_widget
        self._interval_ms = interval_ms

    def schedule(self) -> None:
        self._root.after(self._interval_ms, self._pump_once)

    def _pump_once(self) -> None:
        for entry in self._log_queue.drain_nowait():
            self._append_entry(entry)
        self.schedule()

    def _append_entry(self, entry: LogEntry) -> None:
        self._text_widget.insert("end", entry.message + "\n", entry.kind)
        self._text_widget.see("end")


class OCRBatchApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self._ui_config = AppUiConfig()
        self._runtime_defaults = RuntimeDefaultsResolver().resolve()
        self.root.title(APP_TITLE)
        self.root.geometry(self._ui_config.window_geometry)

        self.logq = LogQueue()
        self.worker_thread: Optional[threading.Thread] = None
        self.stop_requested = False
        self._runtime_support = RuntimeSupport(
            has_pypdf=(PdfReader is not None),
            has_pillow=(Image is not None),
            has_pdfium=(pdfium is not None),
            has_reportlab=(canvas is not None and pdfmetrics is not None and UnicodeCIDFont is not None),
        )
        self._csv_logger = CsvLogger()
        self._runtime_issue_resolver = RuntimeIssueResolver()
        self._startup_dependency_presentation_builder = StartupDependencyPresentationBuilder()
        self._input_collector = InputCollector()
        self._pdf_inspector = PdfInspector(pdf_reader_cls=PdfReader, log=self._log)
        self._output_path_resolver = OutputPathResolver()
        self._csv_log_path_resolver = CsvLogPathResolver()
        self._runtime_control_containers: list[Any] = []
        self._active_process: Any = None
        self._current_run_config: Optional[RunConfig] = None
        self._document_preparer = DocumentPreparer(log=self._log)
        self._ocr_result_parser = OCRResultParser(log=self._log)
        self._searchable_pdf_builder = SearchablePdfBuildCoordinator(
            image_builder=SearchablePdfBuilderForImages(log=self._log),
            pdf_overlay_builder=SearchablePdfOverlayBuilderForPdf(log=self._log),
        )
        self._input_file_planner = InputFilePlanner(
            pdf_has_text_layer=self._pdf_has_text_layer,
            make_output_path=self._make_output_path,
            default_output_path=self._default_output_path,
        )
        self._ndlocr_runner = NDLOCRLiteRunner(
            resolve_launcher=self._resolve_ndlocr_launcher,
            log=self._log,
            is_stop_requested=self._is_stop_requested,
            terminate_process=self._terminate_active_process,
            set_active_process=self._set_active_process,
            quote_for_log=self._quote_for_log,
        )
        self._batch_processor = BatchProcessor(
            csv_logger=self._csv_logger,
            file_planner=self._input_file_planner,
            runtime_issue_resolver=self._runtime_issue_resolver,
            prepare_document=self._prepare_document,
            run_ocr_engine=self._run_ocr_engine,
            parse_ocr_results=self._parse_ocr_results,
            build_searchable_pdf=self._build_searchable_pdf,
            update_progress_ui=self._update_progress_ui,
            log=self._log,
        )
        self._batch_completion_resolver = BatchCompletionResolver()
        self._batch_run_coordinator = BatchRunCoordinator(
            collect_inputs=self._collect_inputs,
            make_csv_log_path=self._make_csv_log_path,
            csv_logger=self._csv_logger,
            batch_processor=self._batch_processor,
            is_stop_requested=self._is_stop_requested,
            update_progress_ui=self._update_progress_ui,
            log=self._log,
            completion_resolver=self._batch_completion_resolver,
        )
        self._gui_run_settings_snapshot_builder = GuiRunSettingsSnapshotBuilder(self._runtime_defaults)
        self._start_run_request_resolver = StartRunRequestResolver()
        self._start_run_coordinator = StartRunCoordinator(
            request_resolver=self._start_run_request_resolver,
            validate_runtime_settings=self._validate_runtime_settings,
            check_dependencies=self._check_dependencies,
            resolve_launcher=self._resolve_ndlocr_launcher,
            execution_defaults=self._runtime_defaults.execution,
        )

        self._initialize_runtime_variables()
        self._build_ui()
        self._bind_main_mousewheel_support()
        self._run_ui_state_coordinator = RunUiStateCoordinator(
            root=self.root,
            progress=self.progress,
            status_var=self.status_var,
            progress_text_var=self.progress_text_var,
            btn_start=self.btn_start,
            btn_stop=self.btn_stop,
            set_runtime_controls_enabled=self._set_runtime_controls_enabled,
            reset_run_state=self._reset_run_state_after_finish,
        )
        self._log_pump_coordinator = LogPumpCoordinator(
            root=self.root,
            log_queue=self.logq,
            text_widget=self.txt_log,
            interval_ms=self._ui_config.log_pump_interval_ms,
        )
        self._schedule_log_pump()
        self.root.after(self._ui_config.startup_dependency_check_delay_ms, self._startup_dependency_check)

    def _initialize_runtime_variables(self) -> None:
        self.folder_var = tk.StringVar()
        self.recursive_var = tk.BooleanVar(value=self._runtime_defaults.recursive)
        self.output_conflict_mode_var = tk.StringVar(value=self._runtime_defaults.output_conflict_mode)
        self.output_mode_var = tk.StringVar(value=self._runtime_defaults.output_mode)
        self.custom_output_folder_var = tk.StringVar(value=self._runtime_defaults.custom_output_folder)
        self.write_csv_log_var = tk.BooleanVar(value=self._runtime_defaults.write_csv_log)
        self.engine_path_var = tk.StringVar(value="")
        self.command_template_var = tk.StringVar(value=self._runtime_defaults.command_template)
        self.status_var = tk.StringVar(value=self._ui_config.status_text)
        self.progress_text_var = tk.StringVar(value=self._ui_config.progress_text)
        self.runtime_notice_var = tk.StringVar(value=self._ui_config.runtime_notice_text)
        self.recursive_notice_var = tk.StringVar(value="※ 再帰はフォルダ指定時のみ有効です。")
        self.input_state_var = tk.StringVar(value="入力状態: 未選択")
        self.output_folder_notice_var = tk.StringVar(value="指定フォルダを選ぶと、入力欄と「参照...」が有効になります。")
        self.run_summary_var = tk.StringVar(value=DEFAULT_RUN_SUMMARY_TEXT)
        self.detail_toggle_text_var = tk.StringVar(value=DEFAULT_DETAIL_TOGGLE_SHOW_TEXT)
        self.detail_section_expanded_var = tk.BooleanVar(value=False)

    def _build_ui(self) -> None:
        self._build_scrollable_root_container()
        self._build_input_section()
        self._build_output_section()
        self._build_conflict_section()
        self._build_detail_section()
        self._build_action_section()
        self._build_progress_section()
        self._build_log_section()
        self._configure_log_tags()
        self.folder_var.trace_add("write", lambda *_: self._update_target_input_ui_state())
        self.output_mode_var.trace_add("write", lambda *_: self._update_output_folder_ui_state())
        self._update_target_input_ui_state()
        self._update_output_folder_ui_state()
        self._update_detail_section_visibility()

    def _build_scrollable_root_container(self) -> None:
        self._outer_frame = ttk.Frame(self.root)
        self._outer_frame.pack(fill="both", expand=True)

        self._main_canvas = tk.Canvas(self._outer_frame, highlightthickness=0)
        self._main_canvas.pack(side="left", fill="both", expand=True)

        self._main_vscrollbar = ttk.Scrollbar(self._outer_frame, orient="vertical", command=self._main_canvas.yview)
        self._main_vscrollbar.pack(side="right", fill="y")
        self._main_canvas.configure(yscrollcommand=self._main_vscrollbar.set)

        self._content_frame = ttk.Frame(self._main_canvas)
        self._content_window_id = self._main_canvas.create_window((0, 0), window=self._content_frame, anchor="nw")

        self._content_frame.bind("<Configure>", self._on_content_frame_configure)
        self._main_canvas.bind("<Configure>", self._on_main_canvas_configure)

    def _on_content_frame_configure(self, _event: tk.Event) -> None:
        self._main_canvas.configure(scrollregion=self._main_canvas.bbox("all"))

    def _on_main_canvas_configure(self, event: tk.Event) -> None:
        self._main_canvas.itemconfigure(self._content_window_id, width=event.width)

    def _bind_main_mousewheel_support(self) -> None:
        self.root.bind_all("<MouseWheel>", self._on_global_mousewheel, add="+")
        self.root.bind_all("<Button-4>", self._on_global_mousewheel_linux_up, add="+")
        self.root.bind_all("<Button-5>", self._on_global_mousewheel_linux_down, add="+")

    def _on_global_mousewheel(self, event: tk.Event) -> Optional[str]:
        if not self._should_scroll_main_canvas(event.widget):
            return None
        delta = int(getattr(event, "delta", 0) or 0)
        if delta == 0:
            return None
        steps = max(1, abs(delta) // 120)
        units = -steps if delta > 0 else steps
        self._main_canvas.yview_scroll(units, "units")
        return "break"

    def _on_global_mousewheel_linux_up(self, event: tk.Event) -> Optional[str]:
        if not self._should_scroll_main_canvas(event.widget):
            return None
        self._main_canvas.yview_scroll(-1, "units")
        return "break"

    def _on_global_mousewheel_linux_down(self, event: tk.Event) -> Optional[str]:
        if not self._should_scroll_main_canvas(event.widget):
            return None
        self._main_canvas.yview_scroll(1, "units")
        return "break"

    def _should_scroll_main_canvas(self, widget: Any) -> bool:
        try:
            if widget is None or widget.winfo_toplevel() != self.root:
                return False
        except Exception:
            return False
        if self._is_widget_descendant_of(widget, self.txt_log):
            return False
        return self._is_widget_descendant_of(widget, self._content_frame) or widget == self._main_canvas

    def _is_widget_descendant_of(self, widget: Any, ancestor: Any) -> bool:
        current = widget
        while current is not None:
            if current == ancestor:
                return True
            try:
                parent_name = current.winfo_parent()
            except Exception:
                return False
            if not parent_name:
                return False
            try:
                current = current.nametowidget(parent_name)
            except Exception:
                return False
        return False

    def _section_pad(self) -> dict[str, int]:
        return {"padx": self._ui_config.pad_x, "pady": self._ui_config.pad_y}

    def _build_input_section(self) -> None:
        frm_input = ttk.LabelFrame(self._content_frame, text="入力対象")
        self._runtime_control_containers.append(frm_input)
        frm_input.pack(fill="x", **self._section_pad())

        ttk.Label(frm_input, text="対象ファイルまたはフォルダ:").grid(row=0, column=0, sticky="w", padx=(8, 6), pady=(8, 4))
        button_frame = ttk.Frame(frm_input)
        button_frame.grid(row=0, column=1, sticky="w", padx=(0, 6), pady=(8, 4))
        ttk.Button(button_frame, text="ファイル...", command=self.on_browse_file).grid(row=0, column=0, sticky="w")
        ttk.Button(button_frame, text="フォルダ...", command=self.on_browse_folder).grid(row=0, column=1, sticky="w", padx=(6, 0))

        self.ent_folder = ttk.Entry(frm_input, textvariable=self.folder_var)
        self.ent_folder.grid(row=0, column=2, sticky="ew", padx=(0, 8), pady=(8, 4))

        ttk.Label(
            frm_input,
            text="対応形式: PDF / PNG / JPG / JPEG / BMP / TIF / TIFF / WEBP",
            foreground="#666666",
        ).grid(row=1, column=0, columnspan=3, sticky="w", padx=8, pady=(0, 4))

        options_frame = ttk.Frame(frm_input)
        options_frame.grid(row=2, column=0, columnspan=3, sticky="ew", padx=8, pady=(0, 2))
        self.chk_recursive = ttk.Checkbutton(options_frame, text="サブフォルダも処理する（再帰）", variable=self.recursive_var)
        self.chk_recursive.grid(row=0, column=0, sticky="w")
        self.chk_csv_log = ttk.Checkbutton(options_frame, text="CSVログを出力する", variable=self.write_csv_log_var)
        self.chk_csv_log.grid(row=0, column=1, sticky="w", padx=(20, 0))

        ttk.Label(
            frm_input,
            textvariable=self.recursive_notice_var,
            foreground="#666666",
        ).grid(row=3, column=0, columnspan=3, sticky="w", padx=8, pady=(0, 2))
        ttk.Label(
            frm_input,
            textvariable=self.input_state_var,
            foreground="#666666",
        ).grid(row=4, column=0, columnspan=3, sticky="w", padx=8, pady=(0, 8))
        frm_input.columnconfigure(2, weight=1)

    def _build_output_section(self) -> None:
        frm_output = ttk.LabelFrame(self._content_frame, text="出力設定")
        self._runtime_control_containers.append(frm_output)
        frm_output.pack(fill="x", **self._section_pad())

        ttk.Label(frm_output, text="出力先:").grid(row=0, column=0, sticky="nw", padx=(8, 6), pady=(8, 4))
        output_frame = ttk.Frame(frm_output)
        output_frame.grid(row=0, column=1, sticky="ew", padx=(0, 8), pady=(6, 4))

        self._create_clickable_radiobutton_row(
            output_frame,
            text="入力ファイルと同じフォルダ",
            variable=self.output_mode_var,
            value=OUTPUT_MODE_SAME_FOLDER,
            row=0,
            command=self._update_output_folder_ui_state,
        )
        self._create_clickable_radiobutton_row(
            output_frame,
            text='対象の親フォルダ直下の "ocr_output" フォルダ',
            variable=self.output_mode_var,
            value=OUTPUT_MODE_INPUT_FOLDER,
            row=1,
            command=self._update_output_folder_ui_state,
        )

        custom_row = ttk.Frame(output_frame, padding=(6, 4))
        custom_row.grid(row=2, column=0, sticky="ew", pady=(2, 2))
        custom_row.columnconfigure(1, weight=1)
        custom_row.bind("<Button-1>", lambda _e: self._select_output_mode(OUTPUT_MODE_CUSTOM_FOLDER))
        ttk.Radiobutton(
            custom_row,
            text="指定フォルダ",
            value=OUTPUT_MODE_CUSTOM_FOLDER,
            variable=self.output_mode_var,
            command=self._update_output_folder_ui_state,
        ).grid(row=0, column=0, sticky="w")
        self.ent_custom_output = ttk.Entry(custom_row, textvariable=self.custom_output_folder_var)
        self.ent_custom_output.grid(row=0, column=1, sticky="ew", padx=(6, 6))
        self.btn_browse_output = ttk.Button(custom_row, text="参照...", command=self.on_browse_output_folder)
        self.btn_browse_output.grid(row=0, column=2, sticky="w")

        ttk.Label(
            frm_output,
            textvariable=self.output_folder_notice_var,
            foreground="#666666",
        ).grid(row=1, column=1, sticky="w", padx=(0, 8), pady=(0, 2))
        ttk.Label(
            frm_output,
            text="通常は、入力ファイル名の末尾に _ocr を付けた PDF を作成します。",
            foreground="#666666",
        ).grid(row=2, column=1, sticky="w", padx=(0, 8), pady=(0, 2))
        ttk.Label(
            frm_output,
            text="入力ファイル自体は上書きしません。",
            foreground="#666666",
        ).grid(row=3, column=1, sticky="w", padx=(0, 8), pady=(0, 8))
        frm_output.columnconfigure(1, weight=1)
        output_frame.columnconfigure(0, weight=1)

    def _build_conflict_section(self) -> None:
        frm_conflict = ttk.LabelFrame(self._content_frame, text="同名のOCR出力がある場合")
        self._runtime_control_containers.append(frm_conflict)
        frm_conflict.pack(fill="x", **self._section_pad())

        conflict_frame = ttk.Frame(frm_conflict)
        conflict_frame.pack(fill="x", padx=8, pady=(6, 4))
        self._create_clickable_radiobutton_row(
            conflict_frame,
            text="連番を付けて保存する",
            variable=self.output_conflict_mode_var,
            value=OUTPUT_CONFLICT_RENAME,
            row=0,
        )
        self._create_clickable_radiobutton_row(
            conflict_frame,
            text="既存のOCR出力（*_ocr.pdf）を上書きする",
            variable=self.output_conflict_mode_var,
            value=OUTPUT_CONFLICT_OVERWRITE,
            row=1,
        )
        ttk.Label(
            frm_conflict,
            text="※ 対象になるのは、既存の OCR 出力（*_ocr.pdf）です。",
            foreground="#666666",
        ).pack(anchor="w", padx=8, pady=(0, 8))

    def _build_detail_section(self) -> None:
        frm_detail = ttk.LabelFrame(self._content_frame, text="詳細設定")
        self._runtime_control_containers.append(frm_detail)
        frm_detail.pack(fill="x", **self._section_pad())

        header = ttk.Frame(frm_detail)
        header.pack(fill="x", padx=8, pady=(6, 4))
        ttk.Label(
            header,
            text="通常は変更不要です。必要な場合のみ開いてください。",
            foreground="#666666",
        ).pack(side="left")
        self.btn_toggle_detail = ttk.Button(
            header,
            textvariable=self.detail_toggle_text_var,
            command=self._toggle_detail_section,
            width=18,
        )
        self.btn_toggle_detail.pack(side="right")

        self._detail_body = ttk.Frame(frm_detail)
        ttk.Label(self._detail_body, text=f"{PYTHON_EXECUTABLE_LABEL}:").grid(row=0, column=0, sticky="e", padx=(8, 4), pady=(8, 4))
        self.ent_engine = ttk.Entry(self._detail_body, textvariable=self.engine_path_var)
        self.ent_engine.grid(row=0, column=1, sticky="ew", padx=(0, 6), pady=(8, 4))
        ttk.Button(self._detail_body, text="参照...", command=self.on_browse_engine).grid(row=0, column=2, sticky="w", padx=(0, 8), pady=(8, 4))
        ttk.Label(
            self._detail_body,
            text="未指定時は自動検出します。通常は空欄のままで構いません。",
            foreground="#666666",
        ).grid(row=1, column=1, columnspan=2, sticky="w", padx=(0, 8), pady=(0, 2))
        ttk.Label(
            self._detail_body,
            textvariable=self.runtime_notice_var,
            foreground=self._ui_config.runtime_notice_color,
            justify="left",
            wraplength=self._ui_config.runtime_notice_wraplength,
        ).grid(row=2, column=1, columnspan=2, sticky="w", padx=(0, 8), pady=(0, 6))

        ttk.Label(self._detail_body, text=f"{NDLOCR_COMMAND_LABEL}:").grid(row=3, column=0, sticky="e", padx=(8, 4), pady=4)
        self.ent_template = ttk.Entry(self._detail_body, textvariable=self.command_template_var)
        self.ent_template.grid(row=3, column=1, columnspan=2, sticky="ew", padx=(0, 8), pady=4)
        ttk.Label(
            self._detail_body,
            text='使用可能: {input} / {input_dir} / {output_dir} / {output_pdf} / {output_stem}',
            foreground="#666666",
        ).grid(row=4, column=1, columnspan=2, sticky="w", padx=(0, 8), pady=(0, 2))
        ttk.Label(
            self._detail_body,
            text='既定: --sourcedir "{input_dir}" --output "{output_dir}"',
            foreground="#666666",
        ).grid(row=5, column=1, columnspan=2, sticky="w", padx=(0, 8), pady=(0, 2))
        ttk.Label(
            self._detail_body,
            text="入力形式: PDF / PNG / JPG / JPEG / BMP / TIF / TIFF / WEBP / 出力形式: 検索可能PDF",
            foreground="#666666",
        ).grid(row=6, column=1, columnspan=2, sticky="w", padx=(0, 8), pady=(0, 8))
        self._detail_body.columnconfigure(1, weight=1)

    def _create_clickable_radiobutton_row(
        self,
        parent: ttk.Frame,
        *,
        text: str,
        variable: tk.StringVar,
        value: str,
        row: int,
        command: Optional[Callable[[], None]] = None,
    ) -> ttk.Frame:
        row_frame = ttk.Frame(parent, padding=(6, 4))
        row_frame.grid(row=row, column=0, sticky="ew", pady=(2, 2))
        row_frame.columnconfigure(0, weight=1)

        def _on_select(_event: Optional[tk.Event] = None) -> None:
            variable.set(value)
            if command is not None:
                command()

        radio = ttk.Radiobutton(
            row_frame,
            text=text,
            value=value,
            variable=variable,
            command=command,
        )
        radio.grid(row=0, column=0, sticky="w")
        row_frame.bind("<Button-1>", _on_select)
        radio.bind("<Button-1>", _on_select, add="+")
        return row_frame

    def _select_output_mode(self, value: str) -> None:
        self.output_mode_var.set(value)
        self._update_output_folder_ui_state()

    def _toggle_detail_section(self) -> None:
        self.detail_section_expanded_var.set(not bool(self.detail_section_expanded_var.get()))
        self._update_detail_section_visibility()

    def _update_detail_section_visibility(self) -> None:
        if bool(self.detail_section_expanded_var.get()):
            self.detail_toggle_text_var.set(DEFAULT_DETAIL_TOGGLE_HIDE_TEXT)
            self._detail_body.pack(fill="x", padx=0, pady=(0, 0))
        else:
            self.detail_toggle_text_var.set(DEFAULT_DETAIL_TOGGLE_SHOW_TEXT)
            self._detail_body.pack_forget()

    def _set_run_summary(self, message: str) -> None:
        self.run_summary_var.set((message or "").strip() or DEFAULT_RUN_SUMMARY_TEXT)

    def _format_run_summary(self, run_config: RunConfig) -> str:
        target_kind = "単一ファイル" if run_config.folder.is_file() else "フォルダ"
        if run_config.folder.is_dir():
            target_kind = f"{target_kind} / 再帰: {'有効' if run_config.recursive else '無効'}"
        output_text = describe_output_destination(run_config.output_mode, run_config.custom_output_dir)
        conflict_text = describe_output_conflict_mode(run_config.output_conflict_mode)
        csv_text = "出力する" if run_config.write_csv_log else "出力しない"
        return "\n".join([
            f"対象: {target_kind}",
            f"出力先: {output_text}",
            f"競合時の動作: {conflict_text}",
            f"CSVログ: {csv_text}",
        ])

    def _build_action_section(self) -> None:
        frm_buttons = ttk.LabelFrame(self._content_frame, text="実行操作")
        frm_buttons.pack(fill="x", **self._section_pad())

        ttk.Label(
            frm_buttons,
            text="設定を確認してから開始してください。処理の詳細は下のログに表示されます。",
            foreground="#666666",
        ).pack(anchor="w", padx=8, pady=(6, 4))

        button_row = ttk.Frame(frm_buttons)
        button_row.pack(fill="x", padx=8, pady=(0, 8))
        self.btn_start = ttk.Button(button_row, text="OCR処理を開始", command=self.on_start)
        self.btn_start.pack(side="left", padx=(0, 6))
        self.btn_stop = ttk.Button(button_row, text="停止", command=self.on_stop, state="disabled")
        self.btn_stop.pack(side="left")
        ttk.Button(button_row, text="ログを消去", command=self.clear_log).pack(side="left", padx=(12, 0))

    def _build_progress_section(self) -> None:
        frm_progress = ttk.LabelFrame(self._content_frame, text="実行状況")
        frm_progress.pack(fill="x", **self._section_pad())

        summary_row = ttk.Frame(frm_progress)
        summary_row.pack(fill="x", padx=8, pady=(6, 2))
        ttk.Label(summary_row, text="状態:").pack(side="left")
        ttk.Label(summary_row, textvariable=self.status_var).pack(side="left", padx=(6, 18))
        ttk.Label(summary_row, text="進捗:").pack(side="left")
        ttk.Label(summary_row, textvariable=self.progress_text_var).pack(side="left", padx=(6, 0))

        self.progress = ttk.Progressbar(frm_progress, mode="determinate", maximum=self._ui_config.progress_max)
        self.progress.pack(fill="x", padx=8, pady=(0, 4))

        ttk.Label(
            frm_progress,
            text="実行条件の要約",
            foreground="#666666",
        ).pack(anchor="w", padx=8, pady=(0, 2))
        ttk.Label(
            frm_progress,
            textvariable=self.run_summary_var,
            foreground="#666666",
            justify="left",
            wraplength=self._ui_config.runtime_notice_wraplength,
        ).pack(fill="x", padx=8, pady=(0, 8))

    def _build_log_section(self) -> None:
        frm_log = ttk.LabelFrame(self._content_frame, text="処理ログ（詳細）")
        frm_log.pack(fill="both", expand=True, **self._section_pad())

        self.txt_log = tk.Text(frm_log, height=self._ui_config.log_text_height, wrap="none")
        self.txt_log.pack(side="left", fill="both", expand=True)
        ysb = ttk.Scrollbar(frm_log, orient="vertical", command=self.txt_log.yview)
        ysb.pack(side="right", fill="y")
        xsb = ttk.Scrollbar(frm_log, orient="horizontal", command=self.txt_log.xview)
        xsb.pack(fill="x", padx=0, pady=(6, 0))
        self.txt_log.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)

    def _configure_log_tags(self) -> None:
        for tag_name, color in DEFAULT_LOG_COLORS.items():
            self.txt_log.tag_configure(tag_name, foreground=color)

    def on_browse_folder(self) -> None:
        d = filedialog.askdirectory(title="処理対象フォルダを選択")
        if d:
            self.folder_var.set(d)

    def on_browse_file(self) -> None:
        f = filedialog.askopenfilename(
            title="処理対象ファイルを選択",
            filetypes=[
                ("対応ファイル", "*.pdf *.png *.jpg *.jpeg *.bmp *.tif *.tiff *.webp"),
                ("PDF", "*.pdf"),
                ("画像", "*.png *.jpg *.jpeg *.bmp *.tif *.tiff *.webp"),
                ("すべてのファイル", "*.*"),
            ],
        )
        if f:
            self.folder_var.set(f)

    def on_browse_engine(self) -> None:
        f = filedialog.askopenfilename(title=f"{PYTHON_EXECUTABLE_LABEL}を選択")
        if f:
            self.engine_path_var.set(f)

    def on_browse_output_folder(self) -> None:
        d = filedialog.askdirectory(title="出力先フォルダを選択")
        if d:
            self.custom_output_folder_var.set(d)
            self.output_mode_var.set(OUTPUT_MODE_CUSTOM_FOLDER)
            self._update_output_folder_ui_state()

    def _update_target_input_ui_state(self) -> None:
        path_str = (self.folder_var.get() or "").strip()
        target_path = Path(path_str) if path_str else None
        path_exists = bool(target_path and target_path.exists())
        is_single_file = bool(target_path and path_exists and target_path.is_file())
        is_folder = bool(target_path and path_exists and target_path.is_dir())
        try:
            if is_single_file:
                self.chk_recursive.configure(state="disabled")
            else:
                self.chk_recursive.configure(state="normal")
        except Exception:
            pass
        if is_single_file:
            self.recursive_notice_var.set("※ 単一ファイルを選択中のため、再帰は無効です。")
            self.input_state_var.set("入力状態: 単一ファイルを選択中")
        elif is_folder:
            self.recursive_notice_var.set("※ 再帰はフォルダ選択時のみ有効です。")
            self.input_state_var.set("入力状態: フォルダを選択中")
        elif path_str:
            self.recursive_notice_var.set("※ 再帰はフォルダ選択時のみ有効です。")
            self.input_state_var.set("入力状態: パスを確認できません")
        else:
            self.recursive_notice_var.set("※ 再帰はフォルダ選択時のみ有効です。")
            self.input_state_var.set("入力状態: 未選択")

    def _update_output_folder_ui_state(self) -> None:
        is_custom = normalize_output_mode(self.output_mode_var.get()) == OUTPUT_MODE_CUSTOM_FOLDER
        state = "normal" if is_custom else "disabled"
        try:
            self.ent_custom_output.configure(state=state)
            self.btn_browse_output.configure(state=state)
        except Exception:
            pass
        if is_custom:
            self.output_folder_notice_var.set("指定フォルダを選択中です。入力欄または「参照...」で出力先を指定してください。")
        else:
            self.output_folder_notice_var.set("指定フォルダを選ぶと、入力欄と「参照...」が有効になります。")

    def clear_log(self) -> None:
        self.txt_log.delete("1.0", "end")

    def on_stop(self) -> None:
        self._request_stop()

    def on_start(self) -> None:
        if self._has_running_worker():
            messagebox.showinfo(APP_TITLE, "処理中です。完了または停止後に再実行してください。")
            return
        plan = self._prepare_start_run_plan()
        if plan is None:
            return
        self._begin_run(plan)

    def _build_start_run_request(self) -> StartRunRequest:
        return self._gui_run_settings_snapshot_builder.build(
            folder_str=self.folder_var.get(),
            recursive=bool(self.recursive_var.get()),
            output_conflict_mode=self.output_conflict_mode_var.get(),
            output_mode=self.output_mode_var.get(),
            custom_output_folder_str=self.custom_output_folder_var.get(),
            write_csv_log=bool(self.write_csv_log_var.get()),
            engine_path_str=self.engine_path_var.get(),
            command_template_str=self.command_template_var.get(),
        )

    def _prepare_start_run_plan(self) -> Optional[StartRunPlan]:
        request = self._build_start_run_request()
        preparation = self._start_run_coordinator.prepare(request)
        if not preparation.ok or preparation.plan is None:
            issue = preparation.issue or PreparationIssue(
                user_message="実行前チェックに失敗しました。",
                detail=LogMessageBuilder.start_precheck_failed("詳細不明"),
            )
            if issue.detail:
                self._log("ERROR", issue.detail)
            messagebox.showerror(APP_TITLE, issue.user_message)
            return None
        return preparation.plan

    def _has_running_worker(self) -> bool:
        return bool(self.worker_thread and self.worker_thread.is_alive())

    def _request_stop(self) -> None:
        self.stop_requested = True
        self._log("WARN", LogMessageBuilder.stop_requested())

    def _apply_run_start_state(self, run_config: RunConfig) -> None:
        self._current_run_config = run_config
        self.stop_requested = False
        self._csv_logger.reset()
        self._set_run_summary(self._format_run_summary(run_config))
        self._run_ui_state_coordinator.apply_started(
            StartUiState(status="準備中...", current=0, total=0)
        )

    def _emit_startup_logs(self, plan: StartRunPlan) -> None:
        for entry in plan.pre_logs:
            self._log(entry.kind, entry.message)
        self._log("INFO", plan.startup_log_message)

    def _launch_worker_thread(self, run_config: RunConfig) -> None:
        self.worker_thread = threading.Thread(target=self._run_batch, args=(run_config,), daemon=True)
        self.worker_thread.start()

    def _begin_run(self, plan: StartRunPlan) -> None:
        run_config = plan.run_config
        self._apply_run_start_state(run_config)
        self._emit_startup_logs(plan)
        self._launch_worker_thread(run_config)

    def _schedule_log_pump(self) -> None:
        self._log_pump_coordinator.schedule()

    def _log(self, kind: str, msg: str) -> None:
        self.logq.put(kind, msg)

    def _set_runtime_controls_enabled(self, enabled: bool) -> None:
        state = "normal" if enabled else "disabled"
        for container in self._runtime_control_containers:
            self._apply_state_recursive(container, state)
        if enabled:
            self._update_target_input_ui_state()
            self._update_output_folder_ui_state()

    def _apply_state_recursive(self, widget: Any, state: str) -> None:
        for child in widget.winfo_children():
            self._apply_state_recursive(child, state)
            try:
                child.configure(state=state)
            except Exception:
                pass

    def _is_stop_requested(self) -> bool:
        return bool(self.stop_requested)

    def _set_active_process(self, proc: Any) -> None:
        self._active_process = proc

    def _clear_current_run_context(self) -> None:
        self._current_run_config = None

    def _reset_run_state_after_finish(self) -> None:
        self._clear_current_run_context()
        self.worker_thread = None
        self.stop_requested = False
        self._active_process = None

    def _terminate_active_process(self, proc: Any) -> None:
        if proc is None:
            return
        if proc.poll() is not None:
            return
        try:
            if os.name != "nt":
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                except Exception:
                    proc.terminate()
            else:
                proc.terminate()
        except Exception:
            pass
        try:
            proc.wait(timeout=3)
            return
        except Exception:
            pass
        try:
            if os.name != "nt":
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except Exception:
                    proc.kill()
            else:
                proc.kill()
        except Exception:
            pass
        try:
            proc.wait(timeout=3)
        except Exception:
            pass

    def _set_runtime_notice(self, msg: str = "") -> None:
        self.runtime_notice_var.set(msg.strip())

    def _startup_dependency_check(self) -> None:
        request = self._build_start_run_request()
        resolved_engine = self._start_run_request_resolver.resolve_text_input(request.engine_path_input)
        ok, msg = self._check_dependencies(return_message=True, engine_path=resolved_engine.value)
        presentation = self._startup_dependency_presentation_builder.build(ok=ok, detail=msg)
        self._set_runtime_notice(presentation.notice)
        for entry in presentation.log_entries:
            self._log(entry.kind, entry.message)

    def _validate_runtime_settings(self, command_template: str) -> tuple[bool, str]:
        return self._runtime_support.validate_runtime_settings(command_template)

    def _check_dependencies(self, return_message: bool = False, engine_path: str = "") -> tuple[bool, str]:
        return self._runtime_support.check_dependencies(return_message=return_message, engine_path=engine_path)

    def _resolve_ndlocr_launcher(self, engine_path: str = "") -> list[str]:
        return self._runtime_support.resolve_ndlocr_launcher(engine_path=engine_path)

    def _run_batch(self, run_config: RunConfig) -> None:
        outcome = self._batch_run_coordinator.run(run_config)
        self._finish_ui(outcome.final_status, outcome.ui_current, outcome.ui_total)

    def _collect_inputs(self, target_path: Path, recursive: bool) -> List[Path]:
        return self._input_collector.collect_inputs(target_path=target_path, recursive=recursive)

    def _pdf_has_text_layer(self, pdf_path: Path) -> bool:
        return self._pdf_inspector.has_text_layer(pdf_path=pdf_path)

    def _prepare_document(self, source_path: Path, run_config: RunConfig) -> PreparedDocument:
        return self._document_preparer.prepare(source_path, render_dpi=run_config.execution.render_dpi)

    def _parse_ocr_results(self, output_dir: Path, prepared: PreparedDocument) -> Dict[int, PageOcrData]:
        return self._ocr_result_parser.parse(output_dir, prepared)

    def _build_searchable_pdf(self, prepared: PreparedDocument, ocr_pages: Dict[int, PageOcrData], out_pdf: Path) -> None:
        self._searchable_pdf_builder.build(prepared, ocr_pages, out_pdf)

    def _default_output_path(
        self,
        source_path: Path,
        input_root_folder: Path,
        output_mode: str,
        custom_output_dir: Optional[Path],
    ) -> Path:
        return self._output_path_resolver.default_output_path(source_path, input_root_folder, output_mode, custom_output_dir)

    def _make_output_path(
        self,
        source_path: Path,
        input_root_folder: Path,
        output_mode: str,
        custom_output_dir: Optional[Path],
        overwrite: bool,
    ) -> Path:
        return self._output_path_resolver.make_output_path(source_path, input_root_folder, output_mode, custom_output_dir, overwrite)

    def _run_ocr_engine(
        self,
        *,
        input_dir: Path,
        single_input: Optional[Path],
        outdir: Path,
        out_pdf: Path,
        command_template: str,
        engine_path: str,
        timeout_sec: int,
    ) -> None:
        self._ndlocr_runner.run(
            input_dir=input_dir,
            single_input=single_input,
            outdir=outdir,
            out_pdf=out_pdf,
            command_template=command_template,
            engine_path=engine_path,
            timeout_sec=timeout_sec,
        )

    def _make_csv_log_path(self, folder: Path) -> Path:
        return self._csv_log_path_resolver.make_path(folder)

    @staticmethod
    def _quote_for_log(s: str) -> str:
        if not s:
            return '""'
        if re.search(r"\s", s):
            return '"' + s.replace('"', '\\"') + '"'
        return s

    def _update_progress_ui(self, current: int, total: int, status: str) -> None:
        self._run_ui_state_coordinator.schedule_progress(
            ProgressUiState(status=status, current=current, total=total)
        )

    def _finish_ui(self, status: str, current: int, total: int) -> None:
        summary_text = f"最終結果: {status} / {min(current, total)} / {total}"
        self.root.after(0, lambda msg=summary_text: self._set_run_summary(msg))
        state = FinishUiState(status=status, current=current, total=total)
        self._run_ui_state_coordinator.schedule_finished(state)


# -------------------- Utility functions --------------------

def _calculate_progress_pct(current: int, total: int) -> float:
    total_safe = max(total, 1)
    return max(0.0, min(float(DEFAULT_PROGRESS_MAX), (current / total_safe) * 100.0))


def _normalize_dpi_value(value: Any) -> float:
    try:
        v = float(value)
    except Exception:
        return float(DEFAULT_IMAGE_DPI)
    if v < 20 or v > 1200:
        return float(DEFAULT_IMAGE_DPI)
    return v


def _normalize_space(text: str) -> str:
    return re.sub(r"\s+", " ", (text or "")).strip()


def _normalize_ocr_text(text: str) -> str:
    s = _normalize_space(text)
    if not s:
        return ""
    # 日本語OCRで混入しやすい不要な半角スペースを詰める
    patterns = [
        (r'(?<=[぀-ヿ㐀-䶿一-鿿！-｠　-〿])\s+(?=[぀-ヿ㐀-䶿一-鿿！-｠　-〿])', ''),
        (r'(?<=[A-Za-z])\s+(?=\d)', ''),
        (r'(?<=\d)\s+(?=[A-Za-z])', ''),
        (r'(?<=[\¥￥])\s+(?=\d)', ''),
        (r'(?<=[（\(\[【「『])\s+', ''),
        (r'\s+(?=[）\)\]】」』、。，．,:;])', ''),
        (r'(?<=[●•])\s+', ''),
    ]
    prev = None
    while s != prev:
        prev = s
        for pat, rep in patterns:
            s = re.sub(pat, rep, s)
    return s.strip()


def _contains_japanese(text: str) -> bool:
    return bool(re.search(r'[ぁ-んァ-ヶ一-龯々〆〤ｦ-ﾟ]', text or ''))


def _is_ascii_word_like(text: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z0-9%&/@#_+\-=:;.,]+", text or ""))


def _collapse_spaces_for_japanese_line(text: str) -> str:
    s = _normalize_ocr_text(text)
    if not s:
        return ""
    # 日本語を含む行では、検索結果の自然さを優先し、
    # ASCII語同士のスペース以外はほぼ除去する。
    if not _contains_japanese(s):
        return s.strip()

    placeholder = "\uFFF0"
    s = re.sub(r'(?<=[A-Za-z0-9])\s+(?=[A-Za-z0-9])', placeholder, s)
    s = re.sub(r'\s+', '', s)
    s = s.replace(placeholder, ' ')

    patterns = [
        (r'(?<=[（(\[【「『]) +', ''),
        (r' +(?=[）)\]】」』、。，．・：；！？])', ''),
        (r'(?<=[●•]) +', ''),
        (r'(?<=P) +(?=\d)', ''),
        (r'(?<=\d) +(?=[頁ページ])', ''),
        (r'(?<=\d) +(?=[ぁ-ゖァ-ヺーｦ-ﾟ一-龯々〆〤])', ''),
        (r'(?<=[ぁ-ゖァ-ヺーｦ-ﾟ一-龯々〆〤]) +(?=\d)', ''),
    ]
    prev = None
    while s != prev:
        prev = s
        for pat, rep in patterns:
            s = re.sub(pat, rep, s)
    return s.strip()


def _polish_hidden_line_text(text: str) -> str:
    s = _normalize_ocr_text(text)
    if not s:
        return ""
    if _contains_japanese(s):
        s = _collapse_spaces_for_japanese_line(s)
    return s.strip()


def _normalize_hidden_text(text: str) -> str:
    return _polish_hidden_line_text(text)


def _token_height(token: OCRToken) -> float:
    return max(1.0, float(token.y2) - float(token.y1))


def _token_width(token: OCRToken) -> float:
    return max(1.0, float(token.x2) - float(token.x1))


def _token_center_y(token: OCRToken) -> float:
    return (float(token.y1) + float(token.y2)) / 2.0


def _token_center_x(token: OCRToken) -> float:
    return (float(token.x1) + float(token.x2)) / 2.0




def _join_tokens_for_vertical_hidden_column(tokens: List[OCRToken]) -> str:
    if not tokens:
        return ""
    ordered = sorted(tokens, key=lambda t: (_token_center_y(t), -_token_center_x(t), float(t.y1), float(t.x1)))
    parts: List[str] = []
    for token in ordered:
        txt = _normalize_ocr_text(token.text)
        if txt:
            parts.append(txt)
    return _normalize_hidden_text("".join(parts))
def _group_tokens_into_vertical_columns(tokens: List[OCRToken]) -> List[List[OCRToken]]:
    if not tokens:
        return []
    ordered = sorted(tokens, key=lambda t: (-_token_center_x(t), float(t.y1), float(t.y2)))
    cols: List[List[OCRToken]] = []
    for token in ordered:
        placed = False
        cx = _token_center_x(token)
        tw = _token_width(token)
        for col in reversed(cols[-8:]):
            centers = [_token_center_x(t) for t in col]
            avg_cx = sum(centers) / max(1, len(centers))
            avg_w = sum(_token_width(t) for t in col) / max(1, len(col))
            tolerance = max(4.0, min(avg_w, tw) * 0.9)
            if abs(cx - avg_cx) <= tolerance:
                col.append(token)
                placed = True
                break
        if not placed:
            cols.append([token])
    return [sorted(col, key=lambda t: (float(t.y1), float(t.y2))) for col in cols]


def _is_vertical_page(tokens: List[OCRToken]) -> bool:
    if len(tokens) < 6:
        return False
    tall_ratio = sum(1 for t in tokens if _token_height(t) > _token_width(t) * 1.25) / max(1, len(tokens))
    h_lines = len(_group_tokens_into_lines(tokens))
    v_cols = len(_group_tokens_into_vertical_columns(tokens))
    if tall_ratio >= 0.70:
        return True
    if tall_ratio >= 0.50 and v_cols <= max(1, h_lines):
        return True
    return False


def _group_tokens_into_lines(tokens: List[OCRToken]) -> List[List[OCRToken]]:
    if not tokens:
        return []
    ordered = sorted(tokens, key=lambda t: (_token_center_y(t), float(t.x1), float(t.x2)))
    lines: List[List[OCRToken]] = []
    for token in ordered:
        placed = False
        cy = _token_center_y(token)
        th = _token_height(token)
        for line in reversed(lines[-8:]):
            centers = [_token_center_y(t) for t in line]
            avg_cy = sum(centers) / max(1, len(centers))
            avg_h = sum(_token_height(t) for t in line) / max(1, len(line))
            tolerance = max(4.0, min(avg_h, th) * 0.6)
            if abs(cy - avg_cy) <= tolerance:
                line.append(token)
                placed = True
                break
        if not placed:
            lines.append([token])
    return [sorted(line, key=lambda t: (float(t.x1), float(t.x2))) for line in lines]


def _join_tokens_for_hidden_line(tokens: List[OCRToken]) -> str:
    if not tokens:
        return ''
    pieces: List[str] = []
    prev: Optional[OCRToken] = None
    line_has_japanese = any(_contains_japanese(_normalize_ocr_text(t.text)) for t in tokens)
    for token in tokens:
        cur = _normalize_ocr_text(token.text)
        if not cur:
            continue
        if prev is None:
            pieces.append(cur)
            prev = token
            continue
        prev_text = _normalize_ocr_text(prev.text)
        gap = max(0.0, float(token.x1) - float(prev.x2))
        prev_h = _token_height(prev)
        cur_h = _token_height(token)
        gap_ratio = gap / max(1.0, min(prev_h, cur_h))
        need_space = False
        if line_has_japanese:
            # 日本語を含む行では、ASCII語同士で十分に離れている場合のみ空白を残す。
            if _is_ascii_word_like(prev_text) and _is_ascii_word_like(cur) and gap_ratio >= 0.90:
                need_space = True
        else:
            if gap_ratio >= 0.45:
                need_space = True
        if need_space and pieces:
            pieces.append(' ')
        pieces.append(cur)
        prev = token
    joined = ''.join(pieces)
    if line_has_japanese:
        return _collapse_spaces_for_japanese_line(joined)
    return _polish_hidden_line_text(joined)



def _tokenize_name(name: str) -> set[str]:
    return {t for t in re.split(r"[^a-z0-9]+", (name or "").lower()) if t}



def _extract_page_number_from_name(name: str) -> Optional[int]:
    patterns = [
        r"(?:^|[_\-])p(?:age)?0*(\d{1,5})(?:$|[_\-])",
        r"(?:^|[_\-])0*(\d{1,5})(?:$|[_\-])",
    ]
    for pat in patterns:
        m = re.search(pat, name)
        if m:
            try:
                return int(m.group(1))
            except Exception:
                pass
    return None



def _extract_text_from_mapping(obj: Dict[str, Any]) -> Optional[str]:
    keys = [
        "text",
        "TEXT",
        "content",
        "CONTENT",
        "label",
        "string",
        "STRING",
        "unicode",
        "Unicode",
        "transcription",
        "recognized_text",
        "ocr_text",
        "PlainText",
    ]
    for key in keys:
        value = obj.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return None



def _looks_like_text_leaf(obj: Dict[str, Any]) -> bool:
    if _extract_bbox_from_mapping(obj) is not None:
        return False
    text = _extract_text_from_mapping(obj)
    if not text:
        return False
    scalar_like = 0
    complex_like = 0
    for v in obj.values():
        if isinstance(v, (str, int, float, bool)) or v is None:
            scalar_like += 1
        else:
            complex_like += 1
    return scalar_like >= complex_like



def _extract_page_hint(obj: Dict[str, Any], inherited: Optional[int], page_count: int) -> Optional[int]:
    keys = ["page", "page_no", "page_num", "page_index", "page_id", "pageNumber", "pageIndex"]
    for key in keys:
        if key in obj:
            try:
                value = int(obj[key])
            except Exception:
                continue
            if 0 <= value < page_count:
                return value
            if 1 <= value <= page_count:
                return value - 1
    return inherited



def _extract_bbox_from_mapping(obj: Dict[str, Any]) -> Optional[tuple[float, float, float, float]]:
    if not isinstance(obj, dict):
        return None

    for key in ("bbox", "box", "rect", "boundingBox", "bounding_box"):
        if key in obj:
            value = obj[key]
            bbox = _coerce_bbox_value(value)
            if bbox is not None:
                return bbox

    if all(k in obj for k in ("x", "y", "w", "h")):
        try:
            x = float(obj["x"])
            y = float(obj["y"])
            w = float(obj["w"])
            h = float(obj["h"])
            return (x, y, x + w, y + h)
        except Exception:
            pass
    if all(k in obj for k in ("X", "Y", "WIDTH", "HEIGHT")):
        try:
            x = float(obj["X"])
            y = float(obj["Y"])
            w = float(obj["WIDTH"])
            h = float(obj["HEIGHT"])
            return (x, y, x + w, y + h)
        except Exception:
            pass
    if all(k in obj for k in ("left", "top", "width", "height")):
        try:
            x = float(obj["left"])
            y = float(obj["top"])
            w = float(obj["width"])
            h = float(obj["height"])
            return (x, y, x + w, y + h)
        except Exception:
            pass
    if all(k in obj for k in ("xmin", "ymin", "xmax", "ymax")):
        try:
            return (float(obj["xmin"]), float(obj["ymin"]), float(obj["xmax"]), float(obj["ymax"]))
        except Exception:
            pass
    if all(k in obj for k in ("x1", "y1", "x2", "y2")):
        try:
            return (float(obj["x1"]), float(obj["y1"]), float(obj["x2"]), float(obj["y2"]))
        except Exception:
            pass
    return None



def _coerce_bbox_value(value: Any) -> Optional[tuple[float, float, float, float]]:
    if isinstance(value, dict):
        return _extract_bbox_from_mapping(value)
    if isinstance(value, (list, tuple)):
        if len(value) == 4 and all(isinstance(v, (int, float, str)) for v in value):
            try:
                a, b, c, d = [float(x) for x in value]
            except Exception:
                return None
            if c > a and d > b:
                return (a, b, c, d)
        points = []
        for item in value:
            if isinstance(item, dict):
                x = item.get("x", item.get("X"))
                y = item.get("y", item.get("Y"))
                if x is not None and y is not None:
                    try:
                        points.append((float(x), float(y)))
                    except Exception:
                        pass
            elif isinstance(item, (list, tuple)) and len(item) >= 2:
                try:
                    points.append((float(item[0]), float(item[1])))
                except Exception:
                    pass
        if points:
            return _bbox_from_points(points)
    return None



def _bbox_from_points(points: Iterable[tuple[float, float]]) -> Optional[tuple[float, float, float, float]]:
    pts = list(points)
    if not pts:
        return None
    xs = [p[0] for p in pts]
    ys = [p[1] for p in pts]
    return (min(xs), min(ys), max(xs), max(ys))



def _parse_points_string(value: str) -> list[tuple[float, float]]:
    pts: list[tuple[float, float]] = []
    for part in (value or "").split():
        if "," not in part:
            continue
        xs, ys = part.split(",", 1)
        try:
            pts.append((float(xs), float(ys)))
        except Exception:
            continue
    return pts



def _local_xml_tag(tag: str) -> str:
    if not tag:
        return ""
    if "}" in tag:
        return tag.rsplit("}", 1)[1]
    return tag



def _extract_xml_text(elem: ET.Element) -> str:
    unicode_texts = []
    for child in elem.iter():
        tag = _local_xml_tag(child.tag)
        if tag in {"Unicode", "PlainText"} and child.text and child.text.strip():
            unicode_texts.append(child.text.strip())
    if unicode_texts:
        return _normalize_space(" ".join(unicode_texts))
    joined = _normalize_space(" ".join(t for t in elem.itertext() if (t or "").strip()))
    return joined



def _wrap_for_hidden_text(text: str, width: int) -> List[str]:
    cleaned = _polish_hidden_line_text(text)
    if not cleaned:
        return []
    logical_lines = [seg for seg in re.split(r"\r?\n+", cleaned) if seg.strip()]
    lines: list[str] = []
    for logical in logical_lines:
        logical = _polish_hidden_line_text(logical)
        current = ""
        for ch in logical:
            current += ch
            if len(current) >= width:
                lines.append(_polish_hidden_line_text(current))
                current = ""
        if current:
            lines.append(_polish_hidden_line_text(current))
    return [line for line in lines if line]



def main() -> None:
    root = tk.Tk()
    try:
        style = ttk.Style()
        if "vista" in style.theme_names():
            style.theme_use("vista")
    except Exception:
        pass
    OCRBatchApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
