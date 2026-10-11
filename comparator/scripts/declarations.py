#!/usr/bin/env python3
"""Print a Lean file's declarations with every comment and docstring removed.

Line comments (`--` to the end of the line) and block comments (`/- ... -/`, nested, which
includes docstrings `/-- ... -/` and module docstrings `/-! ... -/`) are dropped, trailing
whitespace is stripped and blank lines are removed.  String and character literals are not
treated specially; the reference statement contains no `--` or `/-` inside a literal, and a
change that introduced one would change the printed text, so the comparison in `check.sh`
fails closed.
Usage: declarations.py FILE  (prints the text; `check.sh` compares its SHA-256)
"""

import sys


def strip_comments(text: str) -> str:
    out = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise SystemExit("unterminated block comment")
    lines = (line.rstrip() for line in "".join(out).splitlines())
    return "\n".join(line for line in lines if line) + "\n"


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    with open(sys.argv[1], encoding="utf-8") as f:
        sys.stdout.write(strip_comments(f.read()))
