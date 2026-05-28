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

QUALIFIED_RE = re.compile(r"\bOrdvecFormalization\.([A-Za-z_][A-Za-z0-9_']*)\b")
BACKTICK_NAME_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*)`")


def markdown_names() -> set[str]:
    names: set[str] = set()
    for path in DOC_PATHS:
        text = path.read_text(encoding="utf-8")
        names.update(QUALIFIED_RE.findall(text))
    return names


def public_surface_names() -> set[str]:
    text = THEOREM_MAP.read_text(encoding="utf-8")
    start = text.find("## Public Names")
    end = text.find("## What Is Not Claimed")
    if start == -1 or end == -1 or end <= start:
        raise RuntimeError("Could not find the Public Names section in docs/theorem-map.md")
    block = text[start:end]
    return set(BACKTICK_NAME_RE.findall(block))


def lean_check(names: list[str]) -> str:
    lines = [
        "import OrdvecFormalization",
        "",
        "namespace OrdvecFormalization",
        "",
    ]
    lines.extend(f"#check @{name}" for name in names)
    lines.extend(["", "end OrdvecFormalization", ""])
    return "\n".join(lines)


def main() -> int:
    names = sorted(markdown_names() | public_surface_names())
    if not names:
        print("No documented OrdvecFormalization names found.", file=sys.stderr)
        return 1

    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as f:
        f.write(lean_check(names))
        temp_path = Path(f.name)

    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(temp_path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
    finally:
        temp_path.unlink(missing_ok=True)

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
