#!/usr/bin/env python3
"""Remove every Coq comment from .v files (nested comments and string literals
handled), then tidy whitespace: trailing spaces dropped, lines left empty by a
removed comment dropped, and runs of blank lines collapsed to one.

    strip_coq_comments.py FILE...        (rewrites in place)
"""
import re
import sys


def strip(src: str) -> str:
    out, i, n, depth, in_str = [], 0, len(src), 0, False
    while i < n:
        c = src[i]
        if depth == 0 and in_str:
            out.append(c)
            if c == '"':
                if i + 1 < n and src[i + 1] == '"':   # "" escape inside a string
                    out.append('"'); i += 2; continue
                in_str = False
            i += 1
            continue
        if src.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("*)", i):
            depth -= 1; i += 2
            continue
        if depth:
            # keep the newlines a comment spanned, so line structure is sane
            if c == "\n":
                out.append("\x00")
            i += 1
            continue
        if c == '"':
            in_str = True
        out.append(c)
        i += 1
    if depth:
        raise ValueError("unterminated comment")
    text = "".join(out)
    lines = text.split("\n")
    res = []
    for ln in lines:
        had_comment = "\x00" in ln
        ln = ln.replace("\x00", "").rstrip()
        if not ln.strip():
            # a line that only held (part of) a comment disappears entirely;
            # a genuinely blank line is kept (collapsed below)
            if had_comment:
                continue
            ln = ""
        res.append(ln)
    # also drop lines that were whole-line comments without a newline marker
    text = "\n".join(res)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip("\n") + "\n"


def strip_file(path: str) -> None:
    src = open(path, encoding="utf-8").read()
    # mark whole-line comments: a line whose non-space content is entirely a
    # comment should vanish rather than leave a blank line
    new = strip(src)
    open(path, "w", encoding="utf-8").write(new)


if __name__ == "__main__":
    for p in sys.argv[1:]:
        strip_file(p)
