#!/usr/bin/env python3
"""Sync paper Lemma/Theorem numbers from frost.aux into Rocq comments.

Comment format in .v files:
    (** Paper Lemma 3.2 (Soundness of subtyping). [paper-ref: lemma:foo] *)
    (** Paper Theorem 4.5 (Soundness of type inference). [paper-ref: thm:bar] *)
    (** Paper Lemma 3.2 (Soundness of subtyping). [paper-ref: name:"Soundness of subtyping"] *)

The [paper-ref: KEY] marker is stable. The "Lemma N (Name)." portion
before it is rewritten on every run, based on the latest paper/frost.aux.

KEY forms:
- bare LaTeX label (e.g., lemma:general-subsumption) — preferred when
  the paper has a stable [\\label{...}] for the result.
- name:"<exact name>" — falls back to matching the title text. Use
  this for paper [\\restatable[...]{lemma}{}] entries that omit a
  custom command name (and hence don't expose a stable label).

Usage: python3 scripts/sync_paper_refs.py
"""

import re
import sys
from pathlib import Path

PAPER_AUX = Path(__file__).resolve().parents[2] / "paper" / "frost.aux"
ROCQ_ROOT = Path(__file__).resolve().parents[1] / "frost"


def parse_aux(aux_path):
    """Return (label_map, name_map) from a LaTeX .aux file.

    label_map: {LABEL → (Kind, Number, Name)} for entries with stable labels.
    name_map:  {Name → (Kind, Number, Name)} aggregated by visible title,
               used to resolve [paper-ref: name:"..."] references for paper
               restatables that don't expose a custom label.
    """
    if not aux_path.exists():
        sys.exit(f"error: {aux_path} not found. Compile the paper first.")
    text = aux_path.read_text()
    pat = re.compile(
        r"\\newlabel\{([^}]+)\}\{\{([0-9A-Z]+\.[0-9]+)\}\{[^}]*\}\{([^}]*)\}"
        r"\{(lemma|theorem|definition|corollary)\.[0-9A-Z.]+\}\{\}\}"
    )
    label_map = {}
    name_map = {}
    for m in pat.finditer(text):
        label, number, name, kind = m.group(1, 2, 3, 4)
        if not name:
            continue
        entry = (kind.capitalize(), number, name)
        if not label.startswith("thmt@"):
            label_map[label] = entry
        # First occurrence wins for name-based lookup.
        name_map.setdefault(name, entry)
    return label_map, name_map


# Matches:  Paper Lemma 3.2 (Soundness of subtyping). [paper-ref: lemma:foo]
# Also: variants without parentheses, or with multi-word kinds.
REF_PATTERN = re.compile(
    r"Paper\s+(Lemma|Theorem|Definition|Corollary)\s+"
    r"[0-9A-Z]+\.[0-9]+(\s*\([^)]*\))?\.\s*"
    r"\[paper-ref:\s*([^\]]+)\]"
)


NAME_REF_RE = re.compile(r'^name:\s*"([^"]+)"$')


def resolve_ref(key, label_map, name_map):
    """Return (kind, number, name) for a [paper-ref: KEY] value, or None."""
    m = NAME_REF_RE.match(key)
    if m:
        return name_map.get(m.group(1))
    return label_map.get(key)


def rewrite_file(path, label_map, name_map):
    text = path.read_text()
    changed = False

    def replace(match):
        nonlocal changed
        key = match.group(3).strip()
        entry = resolve_ref(key, label_map, name_map)
        if entry is None:
            print(f"  warning: {path.name}: unknown paper-ref [{key}]")
            return match.group(0)
        kind, number, name = entry
        new = f"Paper {kind} {number} ({name}). [paper-ref: {key}]"
        if new != match.group(0):
            changed = True
        return new

    new_text = REF_PATTERN.sub(replace, text)
    if changed:
        path.write_text(new_text)
        print(f"  updated {path.relative_to(path.parent.parent.parent)}")


def main():
    label_map, name_map = parse_aux(PAPER_AUX)
    print(
        f"parsed {len(label_map)} labels + {len(name_map)} titles "
        f"from {PAPER_AUX.name}"
    )
    for v_file in sorted(ROCQ_ROOT.rglob("*.v")):
        rewrite_file(v_file, label_map, name_map)
    print("done.")


if __name__ == "__main__":
    main()
