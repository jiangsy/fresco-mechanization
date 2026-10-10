#!/usr/bin/env python3
"""Build the public README.v from main's README.v: same Check / Print Assumptions
entries, all comments removed, a one-line paper pointer above each entry, and a
short header with the notation legend.

    make_public_readme.py MAIN_README PUBLIC_HEADER_SOURCE OUT
"""
import re
import sys

POINTER = {
    "d_sd_typing_sound": "Lemma B.1 (Soundness of syntax-directed rules)",
    "d_sd_typing_complete": "Lemma B.2 (Completeness of syntax-directed rules)",
    "d_sd_typing_general_subsumption": "General subsumption",
    "d_typing_general_subsumption": "General subsumption, for the declarative typing judgement",
    "a_consis_sound": "Lemma C.6 (Soundness of consistency)",
    "a_consis_complete": "Lemma C.7 (Completeness and optimality of consistency)",
    "a_sub_sound": "Theorem 4.5 (Soundness of subtyping)",
    "a_sub_complete": "Theorem 4.6 (Completeness and optimality of subtyping)",
    "ad_pat_sub_precise_upre_fuel": "Lemma E.14 (Stability of subtyping under more precise substitution)",
    "a_solve_eq_complete_var": "Lemma F.6 (Completeness of consistency constraint collection and solving for variables)",
    "a_lookeq_solve_complete": "Lemma F.5 (Completeness of consistency constraint collection and solving)",
    "a_solve_sub_complete_var": "Lemma E.15 (Completeness of constraint collection and solving for variables)",
    "a_looksub_solve_complete": "Lemma E.16 (Completeness of constraint collection and solving)",
    "a_extract_complete": "Lemma E.17 (Look completeness)",
    "a_pat_sound": "Theorem C.2 (Soundness of skeleton inference)",
    "a_typing_sound": "Theorem 4.2 (Soundness of type inference)",
    "a_typing_sound_infer": "Theorem 4.2 (Soundness of type inference), closed programs, inference mode",
    "a_typing_sound_check": "Theorem 4.2 (Soundness of type inference), closed programs, checking mode",
    "a_pat_complete": "Theorem C.3 (Completeness and optimality of skeleton inference)",
    "a_typing_complete": "Theorem 4.3 (Completeness and optimality of type inference)",
    "a_typing_complete_infer": "Theorem 4.3 (Completeness of type inference), closed programs, inference mode",
    "a_typing_complete_check": "Theorem 4.3 (Completeness of type inference), closed programs, checking mode",
    "a_typing_complete_sd_infer": "Theorem 4.3, closed programs, over syntax-directed typing, inference mode",
    "a_typing_complete_sd_check": "Theorem 4.3, closed programs, over syntax-directed typing, checking mode",
    "a_typing_complete_decl_infer": "Theorem 4.3, closed programs, over declarative typing, inference mode",
    "a_typing_complete_decl_check": "Theorem 4.3, closed programs, over declarative typing, checking mode",
    "ad_precise_extends_pat_sub": "Lemma D.4 (Precision extends skeleton subtyping)",
    "ad_ctx_precise_pat": "Lemma D.7 (Context precision preserves skeleton inference)",
    "d_consis_sub_trans": "Consistency-subtyping transitivity",
    "d_typing_order_irrel": "Order irrelevance of arguments",
    "d_shallow_sub_complete": "Checking-mode subtyping subsumes shallow monotype subtyping",
    "mono_lambda_anno_redundant": "Only polytypes need annotation",
    "e_typing_dec_init": "Decidability of type inference",
    "fresco_infer": "Decidability of type inference: the certified inference function",
}


def strip_comments(src):
    out, i, n, depth, in_str = [], 0, len(src), 0, False
    while i < n:
        c = src[i]
        if not depth and in_str:
            out.append(c)
            if c == '"':
                in_str = False
            i += 1
            continue
        if src.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("*)", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if c == '"':
            in_str = True
        out.append(c); i += 1
    return "".join(out)


def main(main_readme, header_src, out):
    src = open(main_readme, encoding="utf-8").read()
    hdr = open(header_src, encoding="utf-8").read()
    header = hdr[: hdr.index("*)") + 2]          # the public header comment, kept verbatim
    body = strip_comments(src)
    body = "\n".join(l.rstrip() for l in body.splitlines())
    body = re.sub(r"\n{3,}", "\n\n", body).strip("\n")
    # pointer before each entry: an entry starts at "Check NAME" (or a local
    # Theorem/Lemma/Definition that README states itself) and ends at its
    # Print Assumptions.
    lines = body.split("\n")
    res, missing = [], []
    for ln in lines:
        m = re.match(r"(Check|Theorem|Lemma|Corollary|Definition|Example)\s+([A-Za-z0-9_']+)", ln)
        if m and m.group(2) in POINTER:
            if res and res[-1] != "":
                res.append("")
            res.append(f"(* {POINTER[m.group(2)]} *)")
        elif m and m.group(1) == "Check":
            missing.append(m.group(2))
        res.append(ln)
    text = header + "\n\n" + "\n".join(res) + "\n"
    text = re.sub(r"\n{3,}", "\n\n", text)
    open(out, "w", encoding="utf-8").write(text)
    names = re.findall(r"Print Assumptions ([A-Za-z0-9_']+)\.", body)
    print(f"{len(names)} entries; no pointer for: {[n for n in names if n not in POINTER]}; "
          f"unknown Check: {missing}")


if __name__ == "__main__":
    main(*sys.argv[1:])
