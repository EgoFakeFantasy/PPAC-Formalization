"""Canonical hashes for locked UTF-8 source text, independent of Git EOL checkout.
Only CRLF becomes LF. Whitespace, lone CR, BOM and all other bytes are retained.
Binary archives must continue to use raw hashlib.sha256, never this function.
"""
import hashlib
from pathlib import Path

POLICY = "sha256/text-crlf-to-lf/v1"
_TEXT_SUFFIXES = {".lean", ".py", ".txt", ".md", ".json", ".toml", ".yml", ".yaml"}
_TEXT_NAMES = {"LICENSE", "NOTICE", "lean-toolchain", ".gitattributes", ".gitignore"}


def source_sha256(path: Path) -> str:
    path = Path(path)
    if path.suffix.lower() not in _TEXT_SUFFIXES and path.name not in _TEXT_NAMES:
        raise ValueError(f"Canonical source hash requires a known text file: {path}")
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
