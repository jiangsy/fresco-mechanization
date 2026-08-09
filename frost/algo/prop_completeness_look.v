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

    ✅ THE BLOCKER IS CLEARED (2026-08-09, cleanup audit §8.1).  This header
    used to warn "DO NOT point an existing consumer at this file yet", because
    the algo layer had ~20 names defined both inside this cluster and outside
    it, so importing the facade silently flipped which copy an unqualified name
    resolved to.  All 28 such names are gone: 17 duplicate declarations
    deleted, 1 lifted to frost/prop_basic.v, and 10 renamed where the two
    lemmas genuinely differed ([a_guess_mono_wf_pskl], [a_non_flex_subst_var],
    [ad_refine_syn_rename_delta_remove], [binds_weaken_inner],
    [pskl_eq_var_dec], [a_binds_tvar_strengthen_kit],
    [a_wf_pskl_all_of_one_delta], [pskl_to_bskl_inh_all_inh_inv_eq],
    [pskl_to_bskl_inh_tophole_inv_eq], [msubst_pskl_subst_var_paired]).
    **Cluster-vs-outside collisions: 0.**

    ✅ [prop_completeness_sub_gen.v] IS FLIPPED onto this facade (2026-08-09,
    audit §8.1d) — its three piecewise imports are one line, and the build is
    green.  The two remaining piecewise importers, [prop_wf_preservation.v] and
    [prop_sub_msubst_equiv.v], are NOT flipped: each wants only one or two
    files, so the facade would buy them nothing but a wider name surface.

    ⚠️ Before flipping any further consumer, run BOTH checks — being
    collision-free tree-wide is not enough:
    1. **Own-name collisions.**  Does the consumer DECLARE a name that any
       newly-exposed cluster file also declares?  ([Require Import] is not
       transitive for name visibility, so only the files the facade adds
       matter.)  Adding one import has silently rerouted four call sites of
       [a_wf_aenv_def_ftv_dom] and broken the build before.
    2. **Cycles.**  The facade pulls in all six.  It is safe for a consumer of
       the LATE chain (the extra files are earlier, hence already required),
       and dangerous for one the cluster itself imports. *)

Require Export src.frost.algo.completeness_look.prop_kit.
Require Export src.frost.algo.completeness_look.prop_eq_var.
Require Export src.frost.algo.completeness_look.prop_eq_cstr.
Require Export src.frost.algo.completeness_look.prop_sub_var.
Require Export src.frost.algo.completeness_look.prop_sub_cstr.
Require Export src.frost.algo.completeness_look.prop_extract.
