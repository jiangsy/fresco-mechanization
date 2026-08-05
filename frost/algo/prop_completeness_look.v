(** * P6 — completeness of the LOOK judgment, the interface module.

    The look judgment [look[N][M]{α}{P}{P'}{Q}[Ξ]] (fig:poly-info-extraction)
    is proved complete by five lemmas plus a shared kit, and they form a
    strict linear chain: each one consumes the previous.  They live in
    [completeness_look/] and this file is their single import point —
    consumers [Require Import src.frost.algo.prop_completeness_look] and get
    all six.

    | file | paper | what it proves |
    |---|---|---|
    | [completeness_look/prop_kit.v] | — | the shared kit: ρ-images, the solve's context/binder transports, the ⊑ᵖ package plumbing |
    | [completeness_look/prop_eq_var.v] | P6-Cv (consistency-proofs.tex:1180) | [a_solve_eq_complete_var] — the EQ collection at a variable |
    | [completeness_look/prop_eq_cstr.v] | P6-Cs (consistency-proofs.tex:920) | [a_lookeq_solve_complete] — EQ collection AND solving |
    | [completeness_look/prop_sub_var.v] | P6-Sv (subtyping-proofs.tex) | [a_solve_sub_complete_var] — the SUB collection at a variable |
    | [completeness_look/prop_sub_cstr.v] | P6-Ss (subtyping-proofs.tex:1696) | [a_looksub_solve_complete] — SUB collection AND solving |
    | [completeness_look/prop_extract.v] | P6-L (subtyping-proofs.tex:2730) | [a_extract_complete] — the look itself, wrapping P6-Ss and supplying [guess^N] |

    ⚠️ The chain is linear, so the directory buys no build parallelism — it
    is organisational.  Each file still rebuilds on its own, which is why the
    six were NOT concatenated: editing P6-L costs 43 s here rather than the
    ~174 s a single fused file would.  (NB [decl/] was deliberately FLATTENED
    out of subdirectories earlier; this cluster is the one place where the
    chain is long enough that a directory + facade reads better.)

    ⚠️⚠️ **DO NOT point an existing consumer at this file yet.**  [Require
    Export] brings all six modules' names into scope at once, and the algo
    layer currently has **20 names defined both inside this cluster and
    outside it** — 4 exact duplicates, ~9 alpha-variants, and ~5 that
    GENUINELY DIVERGE ([msubst_pskl_subst_var] takes its image side condition
    curried in [prop_completeness_consis.v] but paired here;
    [a_wf_pskl_all_of_one] carries a different side condition;
    [pskl_to_bskl_inh_tophole_inv] has a weaker conclusion here;
    [binds_weaken_mid] and [a_non_flex_rename] have different shapes).
    Consumers that import PIECES today therefore resolve some unqualified
    names to the OUTSIDE copy; importing this facade silently flips them.
    [prop_completeness_sub_gen.v] broke exactly that way and is kept on
    piecewise imports.  The duplicates are a PRE-EXISTING hazard this facade
    only exposed — dedupe them (and rename the divergent ones) and this
    becomes the single import point it is meant to be. *)

Require Export src.frost.algo.completeness_look.prop_kit.
Require Export src.frost.algo.completeness_look.prop_eq_var.
Require Export src.frost.algo.completeness_look.prop_eq_cstr.
Require Export src.frost.algo.completeness_look.prop_sub_var.
Require Export src.frost.algo.completeness_look.prop_sub_cstr.
Require Export src.frost.algo.completeness_look.prop_extract.
