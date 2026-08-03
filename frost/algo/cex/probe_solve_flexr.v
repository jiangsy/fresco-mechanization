(** ⭐⭐⭐ THE FAILURE IS LOCALIZED TO ONE SOLVE ROW (2026-08-04).

    ⚠️ CONTEXT.  At the double-occurrence configuration of
    cex_p7_shield_double_occ.v —

        Θ0 = f̂ ~ flex        P0 = (∀γ.γ→γ) → f̂        NM = TY, M = FN(TC)
        subject ⌈∀β.β→β⌉      declarative solution: κ = f̂ ↦ 1→1,
                              guess ψa = ∀^e β.β→β  ([join_d], [fill_d] Qed)

    — the paper's [lemma:complete-look] (subtyping-proofs.tex:2730) is FALSE
    ([p6l_look_completeness_fails]) and NO [a_sub] run exists at all
    ([probe_no_run]), both machine-checked in probe_double_occ_run.v.

    ⭐ THIS FILE SHOWS THE FAILURE IS NOT STRUCTURAL.  Give the algorithm the
    RIGHT instantiation — [P1 = ∀β.β→β], i.e. exactly the guess ψa with its
    tag erased — and the continuation SUCCEEDS:

        [run_exists_at_correct_instantiation] :
          ∃ Q Θ1,  Θ0 ⊢ₐ[TY | FN(TC) | P0]  (∀β.β→β) → (∀β.β→β)  ⩽ Q ⊣ Θ1

    and the run it builds is the expected one, end to end:

      · DOMAIN — consistency [(∀β.β→β) ∼ (∀γ.γ→γ)] by ForallInh at a fresh
        rigid, then Arrow of two Rigids.
      · CODOMAIN — [∀β.β→β ⩽[TC] f̂] by ForallL, whose extract is the
        interesting part: the look takes LS-Check and then ⭐ **LE-FlexR**,
        which — facing a flexible payload — invents a FRESH flexible α1̂ and
        emits [eq(α1̂)] instead of letting f̂ overwrite anything; the solve
        yields α1̂ and the TY guess passes it through.  The continuation
        [α1̂→α1̂ ⩽[TC] f̂] is Check → FlexR → Assign-Depend → Assign-SolveM,
        which sets [f̂ ≔ α1̂ → α1̂].
      · That solution is MORE GENERAL than the declarative one: the
        declarative [κ f̂ = 1→1] factors through it by [α1̂ ↦ 1].

    ⭐⭐ SO EVERY RULE THE RUN NEEDS ALREADY EXISTS AND ALREADY WORKS.  What
    the algorithm cannot do is CHOOSE [∀β.β→β], and the reason is a single
    row of the solve.  The extract is deterministic there
    ([probe_extract_det]) and forced through

        a_solve_eq__flex_r  (SE-FlexR)   :  Θ ⊢ₑ P ∼ α̂ ⤳ α̂    -- DISCARDS P
      cf. a_solve_eq__hole_r  (SE-VacuousR):  Θ ⊢ₑ P ∼ ◇ ⤳ P    -- KEEPS P
      cf. a_solve_sub__vacuous (SS-Vacuous):  Θ ⊢ₛ P ≼[m] ◇ ⤳ P -- KEEPS P

    The look collects [eq(∀γ.γ→γ); sub_tc(f̂)]; [a_solve_cstr__eq] threads the
    eq's yield [∀γ.γ→γ] into the sub-constraint; SS-ForallL opens β and
    SS-Check hands [β→β ∼ f̂] to SE-FlexR, which replaces the accumulated
    pattern by the flexible — and the close then re-binds a VACUOUS binder,
    [∀_.f̂].  A raw flexible and a ghost are the SAME epistemic situation
    (nothing is known at that position), and the two rows treat the
    already-computed information oppositely.  With SE-FlexR yielding [P] the
    solve returns [∀β.β→β] and this file's run applies.

    ⚠️ NOT DONE HERE, deliberately: the rule is NOT changed.  SE-FlexR is the
    paper's (full-algo-spec.tex:1374) and a repair must be reported, not made
    silently (docs/PAPER-GAPS.md).  Note also that the [P = ◇] case — the one
    that makes returning α̂ useful, since it lets the guess SHARE the flexible
    instead of inventing a fresh one — is already covered by SE-GhostL
    ([a_solve_eq__hole_l] : [◇ ∼ Q ⤳ Q]), so the two readings differ only
    where the pattern already carries information.  DESIGN §14.10a. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.cex.cex_p7_shield_double_occ.

Set Implicit Arguments.

(** The instantiation the DECLARATIVE side uses, tag-erased: [⌊ψa⌋ˢ]. *)
Definition Pallf : pskl :=
  pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)).

(** [P0d]'s subject, ForallL-instantiated with [Pallf] — i.e. the
    continuation [probe_no_run] never reaches, because [probe_extract_det]
    forces the vacuous [∀_.f̂] instead. *)
Theorem run_exists_at_correct_instantiation : forall f,
  exists Q Θ1,
    a_sub a_sub_mode_ty (mode_fn mode_tc) (P0d f) (Θ0d f)
      (pskl_arrow Pallf Pallf) Q Θ1.
Proof.
  intros f.
  destruct (atom_fresh (singleton f)) as [α Hα].
  destruct (atom_fresh (add α (singleton f))) as [α1 Hα1].
  assert (Hαf : α <> f) by (clear - Hα; fsetdec).
  assert (H1f : α1 <> f) by (clear - Hα1; fsetdec).
  assert (H1α : α1 <> α) by (clear - Hα1; fsetdec).
  unfold P0d, Pallf, Θ0d.
  eexists. eexists.
  eapply a_sub__arrow.
  { (* DOMAIN: the two ∀s MATCH — ForallInh at a fresh rigid *)
    eapply a_consis__forall_inh with (α := α).
    { simpl. clear - Hαf. fsetdec. }
    unfold open_pskl_wrt_pskl; simpl.
    eapply a_consis__arrow;
      apply a_consis__rigid; unfold binds; simpl; auto. }
  (* CODOMAIN: [∀β.β→β ⩽[TC] f̂] — ForallL *)
  eapply a_sub__forall_l with
    (α := α) (Ξ := (α1 ~ abind_flex_mono)) (P1 := pskl_var_f α1).
  { discriminate. }
  { left; apply guarded_pskl__var. }
  { simpl. clear - Hαf. fsetdec. }
  { (* THE EXTRACT: LS-Check then ⭐ LE-FlexR (fresh α1̂), solve, TY guess *)
    unfold open_pskl_wrt_pskl; simpl.
    eapply a_extract__solve with
      (Ξ := (α1 ~ abind_flex_mono)) (Ξ' := (nil : aenv)).
    { eapply a_looksub__check.
      { discriminate. }
      { apply guarded_pskl__arrow; apply lc_pskl_var_f. }
      { apply guarded_pskl__var. }
      eapply a_lookeq__flex_r with (α1 := α1).
      { simpl. clear - Hα1. fsetdec. }
      { discriminate. }
      { simpl. clear. fsetdec. } }
    { eapply a_solve_cstr__eq;
        [ apply a_solve_eq__hole_l | apply a_solve_cstr__empty ]. }
    { apply a_guess__ty with (A := ptyp_var_f α1).
      apply a_guess_mono__var. } }
  { simpl. solve_uniq. }
  { apply a_wf_pskl__var. right. right. left. unfold binds; simpl; auto. }
  (* CONTINUATION: [α1̂ → α1̂ ⩽[TC] f̂] — Check, FlexR, Depend, SolveM *)
  unfold open_pskl_wrt_pskl; simpl.
  eapply a_sub__check.
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

Print Assumptions run_exists_at_correct_instantiation.
