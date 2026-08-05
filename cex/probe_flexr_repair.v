(** ⭐⭐⭐ THE REPAIRED [SolE-FlexR] MAKES THE REFUTING CONFIGURATION WORK
    (2026-08-04).

    ⚠️ WHAT THIS FILE ANSWERS.  Two machine-checked refutations —
    [p6l_look_completeness_fails] (the paper's [lemma:complete-look],
    subtyping-proofs.tex:2730) and [thm_complete_subtyping_false]
    (Theorem 4.6) — both bottomed out in ONE row of the constraint solve,

        SolE-FlexR   nonflex(P)  ⟹  solveeq P α̂ ⤳ α̂

    which DISCARDS the pattern the collection has already accumulated
    (docs/refutations.tex).  At the double-occurrence configuration

        Θ0 = f̂ ~ flex        P0 = (∀γ.γ→γ) → f̂       NM = TY, M = FN(TC)
        subject  ∀β.β→β

    the old row overwrote the eq-constraint's yield [∀γ.γ→γ] with the
    flexible, the enclosing SS-ForallL re-bound a VACUOUS binder [∀_.f̂], the
    guess passed that through, and the continuation was scope-stuck — so NO
    [a_sub] run existed there at all ([probe_no_run],
    cex/probe_double_occ_run.v, now RETRACTED).

    ⭐ UNDER THE AUTHORS' REPAIR — the row keeps the pattern, normalized by
    [guess^TY], and emits the fresh block [Ξ] —

        nonflex(P)   nonghost(P)   guess^TY(P) = (Ξ; P')
        ─────────────────────────────────────────────────
                     solveeq P α̂ ⤳ Ξ ⨾ P'

    the SAME configuration goes through, and this file checks it end to end,
    axiom-free:

      · [new_solve]        the solve now yields [∀γ.γ→γ], not [∀_.f̂].  The
                           interesting step is inside SS-ForallL: SS-Check
                           hands [β→β ∼ f̂] to SE-FlexR, and [guess^TY(β→β)]
                           is [(·; β→β)] — no ghosts, so NOTHING is invented
                           and NOTHING is lost.  The close then re-binds a
                           REAL occurrence.
      · [new_extract]      hence the extract returns [∀γ.γ→γ] with an empty
                           suffix — the direct negation of [probe_extract_det],
                           which forced [∀_.f̂].
      · [new_run_exists]   hence a full [a_sub] run EXISTS at the refuting
                           configuration — the direct negation of
                           [probe_no_run].

    ⭐⭐ AND THE RUN IS THE EXPECTED ONE.  ForallL instantiates with exactly
    the guess the declarative side uses ([⌊ψa⌋ˢ = ∀β.β→β]); the domain is
    [ForallInh] at a fresh rigid then [Arrow] of two [Rigid]s; the codomain
    [∀β.β→β ⩽[TC] f̂] goes by ForallL again, whose collection takes LS-Check
    and then LE-FlexR — inventing a fresh [α̂1] — and whose continuation
    [α̂1→α̂1 ⩽[TC] f̂] is Check / FlexR / Assign, setting [f̂ ≔ α̂1 → α̂1].  That
    solution is MORE GENERAL than the declarative one: the declarative
    [κ f̂ = 1→1] factors through it by [α̂1 ↦ 1].

    ⚙️ SELF-CONTAINED BY DESIGN.  The configuration is RE-DECLARED here
    (identical to [Θ0d] / [P0d] of cex/cex_p7_shield_double_occ.v) rather
    than imported, so that this file rests on nothing but [algo/def_extra.v]
    — it must stay checkable while the completeness cluster downstream of it
    is being repaired. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Closing helpers (computational; lngen gives no ready-made equation    *)
(*  for [close] of a concrete term)                                       *)
(* ===================================================================== *)

Lemma close_pskl_arrow_var_same : forall α,
  close_pskl_wrt_pskl α (pskl_arrow (pskl_var_f α) (pskl_var_f α))
  = pskl_arrow (pskl_var_b 0) (pskl_var_b 0).
Proof.
  intros α. unfold close_pskl_wrt_pskl. simpl.
  destruct (α == α) as [_ | Hne]; [ reflexivity | contradiction ].
Qed.

Lemma close_ptyp_arrow_var_same : forall α,
  close_ptyp_wrt_ptyp α (ptyp_arrow (ptyp_var_f α) (ptyp_var_f α))
  = ptyp_arrow (ptyp_var_b 0) (ptyp_var_b 0).
Proof.
  intros α. unfold close_ptyp_wrt_ptyp. simpl.
  destruct (α == α) as [_ | Hne]; [ reflexivity | contradiction ].
Qed.

Section Repair.

Variable f : atom.

(** The refuting configuration, verbatim from cex_p7_shield_double_occ.v. *)
Definition Θ0r : aenv := f ~ abind_flex_mono.
Definition P0r : pskl :=
  pskl_arrow (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
             (pskl_var_f f).

(** [∀β.β→β] — the subject, and (tag-erased) the declarative guess [⌊ψa⌋ˢ]
    the old algorithm could not choose. *)
Definition Pallr : pskl :=
  pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)).

Lemma lc_Pallr : lc_pskl Pallr.
Proof.
  unfold Pallr. apply lc_pskl_all_syn. intros α.
  unfold open_pskl_wrt_pskl; simpl.
  apply lc_pskl_arrow; apply lc_pskl_var_f.
Qed.

(* ------------------------------------------------------------------ *)
(*  The collection is UNCHANGED: LS-Arrow over LE-Var and LS-Var       *)
(* ------------------------------------------------------------------ *)

Lemma new_looksub : forall α,
  Θ0r ⊢ (pskl_arrow (pskl_var_f α) (pskl_var_f α))
      ≼[ α , (mode_fn mode_tc) ] P0r
      ⤳ nil ⨾ (a_cstr_eq Pallr :: a_cstr_sub mode_tc (pskl_var_f f) :: nil).
Proof.
  intros α. unfold P0r, Pallr.
  exact (a_looksub__arrow (a_lookeq__var _ _ _) (a_looksub__var _ _ mode_tc _)).
Qed.

(* ------------------------------------------------------------------ *)
(*  ⭐ THE STEP THAT CHANGED.  SE-GhostL feeds the eq's yield           *)
(*  [∀γ.γ→γ] into the sub-constraint; SS-ForallL opens β and SS-Check   *)
(*  hands [β→β ∼ f̂] to SE-FlexR — which now returns [guess^TY(β→β)]     *)
(*  = [(·; β→β)] instead of [f̂].  The close re-binds a REAL occurrence, *)
(*  so the solve's output is [∀γ.γ→γ], not the vacuous [∀_.f̂].          *)
(* ------------------------------------------------------------------ *)

Lemma new_solve : forall Θ,
  binds f abind_flex_mono Θ ->
  Θ ⊩ (a_cstr_eq Pallr :: a_cstr_sub mode_tc (pskl_var_f f) :: nil)
      ⨾ pskl_hole ⤳ nil ⨾ Pallr.
Proof.
  intros Θ Hb.
  change (@nil (atom * abind))
    with (@nil (atom * abind) ++ @nil (atom * abind)).
  eapply a_solve_cstr__eq; [ apply a_solve_eq__hole_l | ].
  apply a_solve_cstr__sub.
  (* the witness: fresh for everything the ambient context MENTIONS —
     [ftvar_in_aenv], not [dom] (a flexible's payload may name an atom) *)
  destruct (atom_fresh (add f (ftvar_in_aenv (nil ++ Θ)))) as [β Hβ].
  assert (Hne : β <> f) by (intros Heq; subst; clear - Hβ; fsetdec).
  unfold Pallr at 2.
  rewrite <- (close_pskl_arrow_var_same β).
  apply a_solve_sub__forall_l.
  - simpl. clear - Hβ. fsetdec.
  - unfold open_pskl_wrt_pskl; simpl.
    apply a_solve_sub__check.
    + exact I.
    + apply guarded_pskl__arrow; apply lc_pskl_var_f.
    + apply guarded_pskl__var.
    + (* ⭐ SE-FlexR, repaired: the pattern SURVIVES *)
      change (pskl_arrow (pskl_var_f β) (pskl_var_f β))
        with (ptyp_to_pskl (ptyp_arrow (ptyp_var_f β) (ptyp_var_f β))).
      apply a_solve_eq__flex_r.
      * left. unfold binds; simpl; right. exact Hb.
      * split; [ apply lc_pskl_arrow; apply lc_pskl_var_f | ].
        intros Hfl; inversion Hfl.
      * apply nonghost_pskl__arrow.
      * change (@nil (atom * abind))
          with (@nil (atom * abind) ++ @nil (atom * abind)).
        apply a_guess_mono__arrow; apply a_guess_mono__var.
Qed.

(* ------------------------------------------------------------------ *)
(*  The TY guess passes [∀γ.γ→γ] through (no ghosts to fill)            *)
(* ------------------------------------------------------------------ *)

Lemma new_guess : forall Θ,
  a_guess Θ a_sub_mode_ty Pallr nil Pallr.
Proof.
  intros Θ.
  destruct (atom_fresh (ftvar_in_aenv Θ)) as [β Hβ].
  assert (Hm : a_guess_mono Θ Pallr nil
                 (ptyp_all (ptyp_arrow (ptyp_var_b 0) (ptyp_var_b 0)))).
  { rewrite <- (close_ptyp_arrow_var_same β).
    apply a_guess_mono__forall.
    - unfold Pallr; simpl. clear - Hβ. fsetdec.
    - unfold Pallr, open_pskl_wrt_pskl; simpl.
      change (@nil (atom * abind))
        with (@nil (atom * abind) ++ @nil (atom * abind)).
      apply a_guess_mono__arrow; apply a_guess_mono__var. }
  pose proof (a_guess__ty Hm) as Hg. cbn [ptyp_to_pskl] in Hg.
  unfold Pallr. exact Hg.
Qed.

(* ------------------------------------------------------------------ *)
(*  ⭐ THE EXTRACT NOW RETURNS [∀γ.γ→γ] — the direct negation of         *)
(*  [probe_extract_det], which forced the vacuous [∀_.f̂]                *)
(* ------------------------------------------------------------------ *)

Theorem new_extract : forall α,
  Θ0r ⊢ (pskl_arrow (pskl_var_f α) (pskl_var_f α))
      ⊳[ a_sub_mode_ty , α , (mode_fn mode_tc) ] P0r
      ⤳ nil ↪ Pallr.
Proof.
  intros α.
  change (@nil (atom * abind))
    with (@nil (atom * abind) ++ @nil (atom * abind) ++ @nil (atom * abind)).
  eapply a_extract__solve.
  - apply new_looksub.
  - apply new_solve. unfold Θ0r, binds; simpl; auto.
  - apply new_guess.
Qed.

(* ------------------------------------------------------------------ *)
(*  ⭐⭐ AND THEREFORE A FULL RUN EXISTS — the direct negation of         *)
(*  [probe_no_run]                                                     *)
(* ------------------------------------------------------------------ *)

Theorem new_run_exists :
  exists Q Θ1, a_sub a_sub_mode_ty (mode_fn mode_tc) P0r Θ0r Pallr Q Θ1.
Proof.
  destruct (atom_fresh (singleton f)) as [α Hα].
  destruct (atom_fresh (add α (singleton f))) as [α1 Hα1].
  assert (Hαf : α <> f) by (clear - Hα; fsetdec).
  assert (H1f : α1 <> f) by (clear - Hα1; fsetdec).
  eexists. eexists.
  (* ForallL at the RIGHT instantiation — the one the repaired extract
     now computes ([new_extract]) *)
  unfold Pallr at 1.
  eapply a_sub__forall_l with (α := α) (Ξ := (nil : aenv)) (P1 := Pallr).
  { discriminate. }
  { left. unfold P0r. apply guarded_pskl__arrow;
      [ apply lc_Pallr | apply lc_pskl_var_f ]. }
  { unfold Θ0r, P0r; simpl. clear - Hαf. fsetdec. }
  { unfold open_pskl_wrt_pskl; simpl. apply new_extract. }
  { simpl. unfold Θ0r. solve_uniq. }
  { (* the instantiation is wf: [∀γ.γ→γ] over the empty Δ *)
    simpl. unfold Pallr.
    apply a_wf_pskl__all with (L := dom Θ0r); intros β Hβ.
    unfold open_pskl_wrt_pskl; simpl.
    apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec. }
  (* ------- the continuation, at the subject [∀β.β→β → ∀β.β→β] ------- *)
  unfold open_pskl_wrt_pskl; simpl. unfold Θ0r at 1.
  eapply a_sub__arrow.
  { (* DOMAIN: the two ∀s MATCH — ForallInh at a fresh rigid *)
    unfold P0r, Pallr.
    eapply a_consis__forall_inh with (α := α).
    { simpl. clear - Hαf. fsetdec. }
    unfold open_pskl_wrt_pskl; simpl.
    eapply a_consis__arrow;
      apply a_consis__rigid; unfold binds; simpl; auto. }
  (* CODOMAIN: [∀β.β→β ⩽[TC] f̂] — ForallL, whose collection takes
     LS-Check and then LE-FlexR (a FRESH α̂1) *)
  (* here [P0] is the arrow's CODOMAIN face, [f̂] — not [P0r] *)
  unfold Pallr.
  eapply a_sub__forall_l with
    (α := α) (Ξ := (α1 ~ abind_flex_mono)) (P1 := pskl_var_f α1).
  { discriminate. }
  { left. apply guarded_pskl__var. }
  { simpl. clear - Hαf. fsetdec. }
  { unfold open_pskl_wrt_pskl; simpl.
    change (α1 ~ abind_flex_mono)
      with ((α1 ~ abind_flex_mono) ++ (@nil (atom * abind))
              ++ (@nil (atom * abind))).
    eapply a_extract__solve.
    { eapply a_looksub__check.
      { exact I. }
      { discriminate. }
      { apply guarded_pskl__arrow; apply lc_pskl_var_f. }
      { apply guarded_pskl__var. }
      eapply a_lookeq__flex_r with (α1 := α1).
      { simpl. clear - Hα1. fsetdec. }
      { discriminate. }
      { simpl. clear. fsetdec. } }
    { change (@nil (atom * abind))
        with (@nil (atom * abind) ++ @nil (atom * abind)).
      eapply a_solve_cstr__eq;
        [ apply a_solve_eq__hole_l | apply a_solve_cstr__empty ]. }
    { apply a_guess__ty with (A := ptyp_var_f α1).
      apply a_guess_mono__var. } }
  { simpl. solve_uniq. }
  { apply a_wf_pskl__var. right. right. left. unfold binds; simpl; auto. }
  (* CONTINUATION: [α̂1 → α̂1 ⩽[TC] f̂] — Check, FlexR, Depend, SolveM *)
  unfold open_pskl_wrt_pskl; simpl.
  eapply a_sub__check.
  { split; exact I. }
  { exact I. }
  { apply guarded_pskl__arrow; apply lc_pskl_var_f. }
  { apply guarded_pskl__var. }
  unfold a_consis_chk. eexists.
  eapply a_consis__flex_r.
  { split; [ apply lc_pskl_arrow; apply lc_pskl_var_f | ].
    intros Hfl; inversion Hfl; subst;
      match goal with Hb : binds _ _ _ |- _ =>
        unfold binds in Hb; simpl in Hb; destruct Hb as [Hb|Hb];
        [ discriminate Hb | destruct Hb as [Hb|Hb];
          [ discriminate Hb | destruct Hb ] ] end. }
  simpl.
  eapply a_assign__depend.
  { auto. }
  { simpl. clear. fsetdec. }
  simpl. eapply a_assign__solve_m with (βs := (nil : aenv)).
  { simpl. clear - H1f. fsetdec. }
  { apply a_guess_mono__arrow with (Ξ1 := (nil:aenv)) (Ξ2 := (nil:aenv));
      apply a_guess_mono__var. }
  { apply mono_ptyp__arrow; apply mono_ptyp__var. }
  { apply uniq_nil. }
  { intros β Hβ; simpl in Hβ; clear - Hβ; fsetdec. }
Qed.

End Repair.

Print Assumptions new_extract.
Print Assumptions new_run_exists.
