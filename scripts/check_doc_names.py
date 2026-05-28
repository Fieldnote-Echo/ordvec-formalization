#!/usr/bin/env python3
"""Verify that documented OrdvecFormalization names resolve in Lean."""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOC_PATHS = [
    ROOT / "README.md",
    ROOT / "docs" / "theorem-map.md",
    ROOT / "docs" / "reviewer-brief.md",
    ROOT / "docs" / "proof-spine.md",
]
THEOREM_MAP = ROOT / "docs" / "theorem-map.md"

IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
LEAN_NAME = rf"{IDENT}(?:\.{IDENT})*"

QUALIFIED_RE = re.compile(rf"\bOrdvecFormalization\.({LEAN_NAME})\b")
BACKTICK_NAME_RE = re.compile(rf"`({LEAN_NAME})`")


def markdown_names() -> set[str]:
    names: set[str] = set()
    for path in DOC_PATHS:
        text = path.read_text(encoding="utf-8")
        names.update(QUALIFIED_RE.findall(text))
    return names


def public_surface_names() -> set[str]:
    text = THEOREM_MAP.read_text(encoding="utf-8")
    start_match = re.search(r"^## Public Names\s*$", text, flags=re.MULTILINE)
    if start_match is None:
        raise RuntimeError("Could not find the Public Names section in docs/theorem-map.md")

    block_start = start_match.end()
    next_h2_match = re.search(r"^## ", text[block_start:], flags=re.MULTILINE)
    block_end = block_start + next_h2_match.start() if next_h2_match else len(text)
    block = text[block_start:block_end]
    names = set(BACKTICK_NAME_RE.findall(block))
    if not names:
        raise RuntimeError("Public Names section in docs/theorem-map.md has no backticked names")
    return names


def lean_check(names: list[str]) -> str:
    lines = [
        "import OrdvecFormalization",
        "",
    ]
    lines.extend(f"#check @OrdvecFormalization.{name}" for name in names)
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    names = sorted(markdown_names() | public_surface_names())
    if not names:
        print("No documented OrdvecFormalization names found.", file=sys.stderr)
        return 1

    with tempfile.TemporaryDirectory() as tmpdir:
        temp_path = Path(tmpdir) / "check_doc_names.lean"
        temp_path.write_text(lean_check(names), encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(temp_path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )

    if result.returncode != 0:
        print("Documented Lean name check failed.", file=sys.stderr)
        print("Checked names:", file=sys.stderr)
        for name in names:
            print(f"  {name}", file=sys.stderr)
        print(result.stdout, file=sys.stderr)
        print(result.stderr, file=sys.stderr)
        return result.returncode

    print(f"Verified {len(names)} documented OrdvecFormalization names.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
