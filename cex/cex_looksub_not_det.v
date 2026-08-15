(** ⚠️ SCOUTING EXHIBIT (2026-08-15): the COLLECTION [a_looksub] is NOT
    deterministic up to renaming — its output constraint list depends on
    the ORDER in which the ∀-peeling rules fire, and the two answers
    differ in SHAPE, not just in names.

    WHY THIS MATTERS (campaign §8c.3/§8c.6, level 4 — the EXTRACT level).
    Level 3 (the cstr fold) was closed by the recipe

        runner's run --e_solve_eq_sound--> a-side derivation
                     --a_solve_eq_det----> an aligned renaming ρ
                     --a_solve_cstr_swaps-> transport the tail

    and the scouted plan for the extract level was to repeat it one layer
    up: prove [a_looksub]/[a_lookeq] determinism up to renaming (with a
    [rel_cstrs] congruence over [rel_pskl], since the openers LEAK into
    the collected 𝒞), then transport [a_extract]'s solve premise from
    the derivation's 𝒞 to the runner's.  ⛔ THAT PLAN CANNOT WORK: the
    premise it rests on is false, and this file is the witness.

    THE CONFIGURATION.  Subject [∀_. α] (a vacuous binder over the
    looked-for variable), target [∀_. 1], mode TC.  Two rules can root
    the derivation — LS-ForallL peels the SUBJECT, LS-ForallR peels the
    TARGET — and LS-Var reads the CURRENT target into the constraint it
    emits, so the order decides what gets read:

      LS-ForallL first:  ∀_.α ≼ ∀_.1  ↝  α ≼ ∀_.1  ↝  𝒞 = [ ≼TC ∀_.1 ]
      LS-ForallR first:  ∀_.α ≼ ∀_.1  ↝  ∀_.α ≼ 1  ↝  𝒞 = [ ≼TC 1    ]

    Both lists are CLOSED (no free type variables at all), so no renaming
    — and no swap chain — relates them; they are simply different
    constraints.

    ⚙ THE ALGORITHM IS STILL RIGHT.  Both lists are SOLVABLE, and the
    runner (which commits to ForallR, type.ml:663) collects the second.
    What fails is only the INVARIANT the scouted proof wanted: the two
    collections agree up to fresh renaming.  The honest invariant is
    weaker — the two lists are SOLVE-EQUIVALENT (a fold derivation on
    one yields a fold derivation on the other) — because SS-ForallR
    peels [≼TC ∀_.1] to exactly the [≼TC 1] the other list starts from.
    ⛔ Designing that invariant is the extract level's real work; see
    docs/HANDOFF-extractable-algo-encoding.md §8c.6.

    ⚙ The sort discipline does not rescue it: the paper sorts the
    collection's subject as a TYPE (full-algo-spec.tex:1042-1056), and
    [∀_. α] IS a type. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.def_look.

Open Scope frost_a_scope.

(** The subject, the target, and the two constraint lists. *)
Definition cex_subj (α : atom) : pskl := pskl_all_syn (pskl_var_f α).
Definition cex_tgt : pskl := pskl_all_syn pskl_unit.
Definition cex_C_l : a_cstrs := a_cstr_sub mode_tc cex_tgt :: nil.
Definition cex_C_r : a_cstrs := a_cstr_sub mode_tc pskl_unit :: nil.

(** (1) Peeling the SUBJECT first reads the WHOLE ∀ target into the
    constraint. *)
Lemma cex_looksub_forall_l_first : forall α β,
  β <> α ->
  {{ nil ⊢ (cex_subj α) ≼[ α , mode_tc ] cex_tgt ⤳ nil ⨾ cex_C_l }}a.
Proof.
  intros α β Hβ. unfold cex_subj, cex_tgt, cex_C_l.
  apply a_looksub__forall_l with (β := β).
  - simpl. clear - Hβ. fsetdec.
  - unfold open_pskl_wrt_pskl. simpl.
    apply a_looksub__var.
Qed.

(** (2) Peeling the TARGET first reads only its BODY. *)
Lemma cex_looksub_forall_r_first : forall α β β',
  β <> α -> β' <> α -> β <> β' ->
  {{ nil ⊢ (cex_subj α) ≼[ α , mode_tc ] cex_tgt ⤳ nil ⨾ cex_C_r }}a.
Proof.
  intros α β β' Hβ Hβ' Hne. unfold cex_subj, cex_tgt, cex_C_r.
  apply a_looksub__forall_r with (β := β').
  - simpl. exact I.
  - simpl. clear - Hβ'. fsetdec.
  - unfold open_pskl_wrt_pskl. simpl.
    apply a_looksub__forall_l with (β := β).
    + simpl. clear - Hβ Hne. fsetdec.
    + unfold open_pskl_wrt_pskl. simpl.
      apply a_looksub__var.
Qed.

(** (3) The two answers are CLOSED and DIFFERENT — so no renaming, and in
    particular no swap chain, can relate them. *)
Lemma cex_looksub_cstrs_closed :
  ftvar_in_a_cstrs cex_C_l [=] empty /\ ftvar_in_a_cstrs cex_C_r [=] empty.
Proof. unfold cex_C_l, cex_C_r, cex_tgt. simpl. split; fsetdec. Qed.

Lemma cex_looksub_cstrs_differ : cex_C_l <> cex_C_r.
Proof. unfold cex_C_l, cex_C_r, cex_tgt. discriminate. Qed.

(** ⭐ THE EXHIBIT: one collection judgement, two derivations, two
    constraint lists that no renaming identifies. *)
Theorem cex_looksub_not_det : forall α β β',
  β <> α -> β' <> α -> β <> β' ->
  {{ nil ⊢ (cex_subj α) ≼[ α , mode_tc ] cex_tgt ⤳ nil ⨾ cex_C_l }}a
  /\ {{ nil ⊢ (cex_subj α) ≼[ α , mode_tc ] cex_tgt ⤳ nil ⨾ cex_C_r }}a
  /\ cex_C_l <> cex_C_r
  /\ ftvar_in_a_cstrs cex_C_l [=] empty
  /\ ftvar_in_a_cstrs cex_C_r [=] empty.
Proof.
  intros α β β' Hβ Hβ' Hne.
  pose proof cex_looksub_cstrs_closed as [Hcl Hcr].
  (* ⚠️ explicit nested splits: [repeat split] dives into the [[=]]s *)
  split; [ exact (cex_looksub_forall_l_first α β Hβ) | ].
  split; [ exact (cex_looksub_forall_r_first α β β' Hβ Hβ' Hne) | ].
  split; [ apply cex_looksub_cstrs_differ | ].
  split; [ exact Hcl | exact Hcr ].
Qed.
