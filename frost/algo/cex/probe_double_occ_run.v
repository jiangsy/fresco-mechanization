(** ⚠️⚠️ RESOLVED AND MACHINE-CHECKED (2026-08-03; Coq construction of the
    2026-08-03 rule-level trace): the MECH's [a_sub] has NO run at the
    double-occurrence configuration of cex_p7_shield_double_occ.v, while
    the declarative solution (join + fill) is Qed-inhabited there — so
    [main_forall], the ONE hypothesis of §12's assembly
    ([a_sub_complete_bundle_holds], prop_sub_complete_dispatch.v), is
    FALSE as stated ([probe_main_forall_false] below), and
    thm:complete-subtyping OVER-QUANTIFIES [P0]: it claims completeness
    at payloads the typing never produces, and there the algorithm fails.

    THE RETHINK THAT MOTIVATED THIS FILE (user-directed).  The mode episode
    (docs/PAPER-GAPS.md, retraction note) exposed two blind spots in the
    completeness analysis:

    (1) THE MODE DISCIPLINE IS THE MATCH/INSTANTIATE MAP.  Arrow DOMAINS
        drop into consistency, where quantifiers can only MATCH (and where
        guess-tags are solved); only the fn-spine CODOMAINS remain in the
        SUB judgment where ForallL instantiation exists.  [ss_walk]
        descending only codomains ([sss_arrow_r]) is the same fact stated
        on the shield's side.  Any repaired premise must be derived from
        this map, not bolted on.

    (2) SOURCE PROBES CANNOT REACH THIS PAYLOAD.  met.exe accepts
        [id2 idc] at FN(TC) (docs/repros/..fn_tc_passes.mle), but the
        spine-collection there builds ITS OWN payload (with ghosts); the
        surface language cannot force [P0 = (∀γ.γ→γ) → α̂] directly.  So
        the implementation run does NOT settle whether the ALGORITHMIC
        RULES succeed at the machine-checked join/fill configuration —
        only this file can.

    THE CONFIGURATION (all from cex_p7_shield_double_occ.v, Section
    [DoubleOccurrence] with atoms f e t, e <> t):

      Θ0 = f̂ ~ flex        P0 = (∀γ.γ→γ) → f̂       NM = TY, M = fn tc
      subject P = ∀.(□₀→□₀)   (so the opened body at the marker α is α→α)
      declarative solution: κ = f̂ ↦ unit→unit, guess ψ = ∀^e β.β→β,
      join [join_d] + fill [fill_d] Qed.

    THE FORCED TRACE — every step now a Qed inversion lemma, UNIFORM in
    the fresh names:

      1. looksub is deterministic ([probe_look_det]): LS-Arrow = LE-Var +
         LS-Var ⟹ [nil ⨾ [eq (∀γ.γ→γ); sub tc f̂]] — the only survivors of
         the inversion are LS-Absent (refuted: α occurs in α→α) and
         LS-Check (refuted: the subject IS the looked-for variable).
      2. the solve is deterministic ([probe_solve_det]): the eq runs on
         the HOLE (SE-GhostL) ⟹ P'' = ∀γ.γ→γ; the sub then runs ON P'':
         SS-ForallL is FORCED (a ∀ is not guarded — the SS-Check branch
         dies on [guarded_pskl (pskl_all_syn _)] inversion), opening β
         fresh; [β→β ≼[tc] f̂] goes SS-Check → SE-FlexR, whose output IS
         the flexible ([a_solve_eq__flex_r] : P ∼ α̂ ⤳ α̂), so the close
         re-binds a VACUOUS binder:  Q_solved = ∀_.f̂.  ⭐ The domain's
         ∀γ.γ→γ is DESTROYED by the threading — the eq-constraint's yield
         is overwritten because the sub-constraint solves on the
         accumulated pattern.
      3. the guess (TY) is deterministic ([probe_guess_det]): on the
         vacuous ∀ it is forced through a_guess_mono's forall + var rows,
         and the close is again vacuous: P1 = ∀_.f̂ — INDEPENDENT of every
         fresh name (the vacuous binder swallows them all).
      4. the continuation is STUCK ([probe_continuation_stuck]): subject
         (∀_.f̂) → (∀_.f̂) vs (∀γ.γ→γ) → f̂ forces Arrow, whose domain
         CONSISTENCY [∀_.f̂ ∼ ∀γ.γ→γ] forces ForallInh: at the freshly
         pushed rigid β1 the subject's body is the bare [f̂] facing
         [β1→β1] — only FlexL applies, and its assignment walk meets the
         context HEAD (β1 ~ tvar) with [β1 ∈ ftv(β1→β1)], where the only
         matching rule Assign-SkipRigid refuses
         ([a_assign_rigid_head_occurs_stuck]).  No alternative choice
         point exists upstream (ForallL is the only [a_sub] entry at a ∀
         subject with an arrow [P0] at FN(TC)).

    ⟹ NO [a_sub] run exists ([probe_no_run]), while the join + fill are
    Qed-inhabited.  Wiring in the rest of the completeness-motive premises
    (all Qed in [p7_sub_shield_positional_over_strong]) refutes the motive
    instance ([probe_motive_instance_false]) and hence [main_forall]
    ([probe_main_forall_false]) and the bundle's hypothesis
    ([probe_main_forall_hyp_false]).  ⭐⭐⭐ The failing payload shape is
    EXACTLY the shield saga's residual: a [P0] with a ∀ below its head (at
    a consis-feeding position); prop_sub_shield_supply.v's covered shapes
    (∀-free / mono-counterpart / inh-free / flex-free) delimit the
    COMPLETABLE class.

    ⭕ REACHABILITY IS OPEN.  A same-day claim that this payload class is
    typing-reachable — a [pipe (fun g -> g arg)] program allegedly accepted
    declaratively and rejected by met.exe — is ⚠️⚠️ RETRACTED: the
    DECLARATIVE system rejects that program too, so it is no separation.  A
    polytype instantiation must be PAID FOR by an inherited ∀ in the
    counterpart ([d_sub__forall_l_untagged] runs at [Ψ ∪ Ψ'] with
    [d_tags Ψ' ph]; only [d_consis__forall_inh_tagged] puts a tag INTO Ψ,
    against a [btyp_all_inh]; and [d_sub__infer] demands [Ψ = ∅]) — the
    paper's "never guess polymorphism out of thin air".  There the
    skeleton [⫯(◇ → ◇)] supplies no ∀, which is the paper's own §2.9
    limitations 2 and 3 ("ghosts are nameless", "only flowing back and
    forth once").
    ⭐ THE SHARPENED QUESTION.  This configuration needs BOTH (1) a raw
    Θ0-flexible at the payload's codomain — the algorithm has NO inherited
    information there — and (2) a concrete counterpart at that codomain
    with the guess's tag paid at the DOMAIN, i.e. the declarative side HAS
    information (here: [consis_d] discharges e against [bskl_all_inh]).
    Those pull in opposite directions, so the conjunction may well be
    UNREACHABLE — in which case thm:complete-subtyping is merely
    OVER-QUANTIFIED and the payload side condition
    (docs/HANDOFF-completeness-repair.md TASKS 2–3) is the repair.
    PAPER-GAPS.md (2026-08-03) + DESIGN §14.9. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.prop_basic.
Require Import src.frost.algo.cex.cex_p7_shield_forall_flex.
Require Import src.frost.algo.cex.cex_p7_shield_double_occ.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_sub_complete_thm.
Require Import src.frost.algo.prop_sub_complete_dispatch.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Small computation lemmas: closing over a non-occurring variable       *)
(* ===================================================================== *)

Lemma close_pskl_var_f_neq : forall β α, β <> α ->
  close_pskl_wrt_pskl β (pskl_var_f α) = pskl_var_f α.
Proof.
  intros β α Hne. unfold close_pskl_wrt_pskl. simpl.
  destruct (β == α); [ exfalso; auto | reflexivity ].
Qed.

Lemma close_ptyp_var_f_neq : forall β α, β <> α ->
  close_ptyp_wrt_ptyp β (ptyp_var_f α) = ptyp_var_f α.
Proof.
  intros β α Hne. unfold close_ptyp_wrt_ptyp. simpl.
  destruct (β == α); [ exfalso; auto | reflexivity ].
Qed.

(* ===================================================================== *)
(*  Generic stuck shapes (uniform in every name)                          *)
(* ===================================================================== *)

(** At a rigid head that OCCURS in the assigned skeleton, no walk rule
    fires: Assign-SkipRigid is the only rule matching an [abind_tvar]
    head, and its side condition demands the rigid away from the
    skeleton's ftv. *)
Lemma a_assign_rigid_head_occurs_stuck : forall β Θ Ξ α P Θ1,
  β `in` ftvar_in_pskl P ->
  ~ a_assign ((β ~ abind_tvar) ++ Θ) Ξ α P Θ1.
Proof.
  intros β Θ Ξ α P Θ1 Hin H.
  inversion H; subst;
    match goal with Hni : β `notin` ftvar_in_pskl _ |- _ => exact (Hni Hin) end.
Qed.

(** A VAR subject facing an arrow input built from the context's own head
    rigid: only FlexL applies, and its assignment is stuck above.  The
    subject variable [α] is arbitrary — rigid or flexible. *)
Lemma a_consis_var_vs_head_rigid_arrow_stuck : forall Δ1 Δ2 β Θ α Q Θ1,
  ~ a_consis Δ1 Δ2 ((β ~ abind_tvar) ++ Θ)
      (pskl_arrow (pskl_var_f β) (pskl_var_f β)) (pskl_var_f α) Q Θ1.
Proof.
  intros Δ1 Δ2 β Θ α Q Θ1 H.
  inversion H; subst.
  match goal with Ha : a_assign _ _ _ _ _ |- _ =>
    refine (a_assign_rigid_head_occurs_stuck _ Ha);
    simpl; clear; fsetdec
  end.
Qed.

(** ⭐ The continuation's crux: a VACUOUS-binder ∀ subject cannot meet
    [∀β.β→β] in consistency — ForallInh is forced, the opened input is
    [β1→β1] at the freshly pushed rigid [β1], and the subject's body is a
    bare variable facing it: stuck, for ANY context, ANY variable [α]
    (rigid or flexible), and ANY fresh name. *)
Lemma a_consis_forall_arrow_vs_vacuous_var_stuck : forall Δ1 Δ2 Θ α Q Θ1,
  ~ a_consis Δ1 Δ2 Θ
      (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
      (pskl_all_syn (pskl_var_f α)) Q Θ1.
Proof.
  intros Δ1 Δ2 Θ α Q Θ1 H.
  inversion H; subst.
  match goal with Hp : a_consis _ _ _ _ _ _ _ |- _ => revert Hp end.
  unfold open_pskl_wrt_pskl; simpl.
  apply a_consis_var_vs_head_rigid_arrow_stuck.
Qed.

(* ===================================================================== *)
(*  The probe run, over the double-occ configuration                      *)
(* ===================================================================== *)

Section ProbeRun.

Variable f : atom.

(* ------------------------------------------------------------------ *)
(*  STEP 1 (positive): the looksub derivation — LS-Arrow over LE-Var    *)
(*  and LS-Var, for ANY marker α                                       *)
(* ------------------------------------------------------------------ *)

Lemma probe_looksub : forall α,
  (Θ0d f) ⊢ (pskl_arrow (pskl_var_f α) (pskl_var_f α))
      ≼[ α , (mode_fn mode_tc) ] (P0d f)
      ⤳ nil ⨾ (a_cstr_eq (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
               :: a_cstr_sub mode_tc (pskl_var_f f) :: nil).
Proof.
  intros α. unfold P0d.
  exact (a_looksub__arrow (a_lookeq__var _ _ _) (a_looksub__var _ _ mode_tc _)).
Qed.

(* ------------------------------------------------------------------ *)
(*  STEP 2 (positive): the solve — SE-GhostL feeds the eq's yield into  *)
(*  the sub-constraint, where SS-ForallL / SS-Check / SE-FlexR          *)
(*  OVERWRITE it with the flexible: the output is the vacuous-binder    *)
(*  ∀_.f̂                                                                *)
(* ------------------------------------------------------------------ *)

Lemma probe_solve : forall Θ,
  binds f abind_flex_mono Θ ->
  Θ ⊩ (a_cstr_eq (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
       :: a_cstr_sub mode_tc (pskl_var_f f) :: nil) ⨾ pskl_hole
      ⤳ (pskl_all_syn (pskl_var_f f)).
Proof.
  intros Θ Hb.
  eapply a_solve_cstr__eq; [ apply a_solve_eq__hole_l | ].
  apply a_solve_cstr__sub.
  destruct (atom_fresh (add f (dom Θ))) as [β Hβ].
  assert (Hne : β <> f) by (intros Heq; subst; clear - Hβ; fsetdec).
  replace (pskl_all_syn (pskl_var_f f))
    with (pskl_all_syn (close_pskl_wrt_pskl β (pskl_var_f f)))
    by (rewrite close_pskl_var_f_neq; [ reflexivity | exact Hne ]).
  apply a_solve_sub__forall_l.
  - simpl. clear - Hβ. fsetdec.
  - unfold open_pskl_wrt_pskl; simpl.
    apply a_solve_sub__check.
    + apply guarded_pskl__arrow; apply lc_pskl_var_f.
    + apply guarded_pskl__var.
    + apply a_solve_eq__flex_r.
      * left; exact Hb.
      * split; [ apply lc_pskl_arrow; apply lc_pskl_var_f | ].
        intros Hfl; inversion Hfl.
Qed.

(* ------------------------------------------------------------------ *)
(*  STEP 3 (positive): the guess (TY) on the vacuous ∀ — forced to      *)
(*  ∀_.f̂ again                                                          *)
(* ------------------------------------------------------------------ *)

Lemma probe_guess : forall Θ,
  a_guess Θ a_sub_mode_ty (pskl_all_syn (pskl_var_f f)) nil
    (pskl_all_syn (pskl_var_f f)).
Proof.
  intros Θ.
  destruct (atom_fresh (add f (ftvar_in_aenv Θ))) as [β Hβ].
  assert (Hne : β <> f) by (intros Heq; subst; clear - Hβ; fsetdec).
  assert (Hm : a_guess_mono Θ (pskl_all_syn (pskl_var_f f)) nil
                 (ptyp_all (ptyp_var_f f))).
  { replace (ptyp_all (ptyp_var_f f))
      with (ptyp_all (close_ptyp_wrt_ptyp β (ptyp_var_f f)))
      by (rewrite close_ptyp_var_f_neq; [ reflexivity | exact Hne ]).
    apply a_guess_mono__forall.
    - simpl. clear - Hβ. fsetdec.
    - unfold open_pskl_wrt_pskl; simpl.
      apply a_guess_mono__var. }
  exact (a_guess__ty Hm).
Qed.

(* ------------------------------------------------------------------ *)
(*  STEPS 1–3 assembled: the extract at the opened subject               *)
(* ------------------------------------------------------------------ *)

Lemma probe_extract : forall α,
  (Θ0d f) ⊢ (pskl_arrow (pskl_var_f α) (pskl_var_f α))
      ⊳[ a_sub_mode_ty , α , (mode_fn mode_tc) ] (P0d f)
      ⤳ nil ↪ (pskl_all_syn (pskl_var_f f)).
Proof.
  intros α.
  change (@nil (atom * abind)) with (@nil (atom * abind) ++ @nil (atom * abind)).
  eapply a_extract__solve.
  - apply probe_looksub.
  - apply probe_solve. unfold Θ0d, binds; simpl; auto.
  - apply probe_guess.
Qed.

(* ------------------------------------------------------------------ *)
(*  DETERMINISM: each step is FORCED, uniformly in the fresh names       *)
(* ------------------------------------------------------------------ *)

Lemma probe_look_det : forall α Ξ 𝒞,
  (Θ0d f) ⊢ (pskl_arrow (pskl_var_f α) (pskl_var_f α))
      ≼[ α , (mode_fn mode_tc) ] (P0d f) ⤳ Ξ ⨾ 𝒞 ->
  Ξ = nil /\
  𝒞 = (a_cstr_eq (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
       :: a_cstr_sub mode_tc (pskl_var_f f) :: nil).
Proof.
  intros α Ξ 𝒞 H. unfold P0d in H.
  inversion H; subst.
  - (* LS-Absent: refuted — α occurs in the subject *)
    exfalso.
    match goal with Hni : α `notin` _ |- _ =>
      simpl in Hni; clear - Hni; fsetdec end.
  - (* LS-Arrow — LE-Var and LS-Var forced on the two sides *)
    match goal with
    | HL1 : a_lookeq _ _ (pskl_var_f α) _ _ _ |- _ =>
        inversion HL1; subst;
        try solve [ exfalso;
                    match goal with Hni : α `notin` _ |- _ =>
                      simpl in Hni; clear - Hni; fsetdec end ]
    end.
    match goal with
    | HL2 : a_looksub _ _ _ (pskl_var_f α) _ _ _ |- _ =>
        inversion HL2; subst;
        try solve [ exfalso;
                    match goal with Hni : α `notin` _ |- _ =>
                      simpl in Hni; clear - Hni; fsetdec end
                  | match goal with Hne : ?x <> ?x |- _ =>
                      exfalso; exact (Hne eq_refl) end ]
    end.
    split; reflexivity.
Qed.

Lemma probe_solve_det : forall Θ Q,
  Θ ⊩ (a_cstr_eq (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
       :: a_cstr_sub mode_tc (pskl_var_f f) :: nil) ⨾ pskl_hole ⤳ Q ->
  Q = pskl_all_syn (pskl_var_f f).
Proof.
  intros Θ Q H.
  inversion H; subst.
  match goal with HE : a_solve_eq _ pskl_hole _ _ |- _ =>
    inversion HE; subst end.
  match goal with HC : a_solve_cstr _ (a_cstr_sub _ _ :: nil) _ _ |- _ =>
    inversion HC; subst end.
  match goal with HS : a_solve_sub _ _ (pskl_all_syn _) _ _ |- _ =>
    inversion HS; subst;
    try solve [ match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
                  inversion Hg end ]
  end.
  (* SS-ForallL, at the rule's fresh β *)
  match goal with
  | HS' : a_solve_sub _ _ (open_pskl_wrt_pskl _ _) _ _ |- _ =>
      unfold open_pskl_wrt_pskl in HS'; simpl in HS';
      inversion HS'; subst
  end.
  (* SS-Check *)
  match goal with
  | HE' : a_solve_eq _ (pskl_arrow _ _) _ _ |- _ =>
      inversion HE'; subst
  end.
  (* SE-FlexR: the output IS the flexible; the close is vacuous *)
  rewrite close_pskl_var_f_neq; [ reflexivity | ].
  match goal with Hfr : ?β `notin` _ |- ?β <> f =>
    intros Heq; subst; simpl in Hfr; clear - Hfr; fsetdec end.
Qed.

Lemma probe_guess_det : forall Θ Ξ P1,
  a_guess Θ a_sub_mode_ty (pskl_all_syn (pskl_var_f f)) Ξ P1 ->
  Ξ = nil /\ P1 = pskl_all_syn (pskl_var_f f).
Proof.
  intros Θ Ξ P1 H.
  inversion H; subst.
  match goal with HM : a_guess_mono _ (pskl_all_syn _) _ _ |- _ =>
    inversion HM; subst end.
  match goal with
  | HM' : a_guess_mono _ (open_pskl_wrt_pskl _ _) _ _ |- _ =>
      unfold open_pskl_wrt_pskl in HM'; simpl in HM';
      inversion HM'; subst
  end.
  split; [ reflexivity | ].
  rewrite close_ptyp_var_f_neq; [ reflexivity | ].
  match goal with Hfr : ?β `notin` _ |- ?β <> f =>
    intros Heq; subst; simpl in Hfr; clear - Hfr; fsetdec end.
Qed.

(** ⭐ Steps 1–3 are jointly deterministic: the extract's output is FORCED
    to [(nil, ∀_.f̂)] — independent of the marker AND of every fresh name
    the run picks (the vacuous binder swallows them). *)
Lemma probe_extract_det : forall α Ξ P1,
  (Θ0d f) ⊢ (pskl_arrow (pskl_var_f α) (pskl_var_f α))
      ⊳[ a_sub_mode_ty , α , (mode_fn mode_tc) ] (P0d f) ⤳ Ξ ↪ P1 ->
  Ξ = nil /\ P1 = pskl_all_syn (pskl_var_f f).
Proof.
  intros α Ξ P1 H.
  inversion H; subst.
  match goal with HL : a_looksub _ _ _ _ _ _ _ |- _ =>
    apply probe_look_det in HL as [-> ->] end.
  match goal with HS : a_solve_cstr _ _ _ _ |- _ =>
    apply probe_solve_det in HS as -> end.
  match goal with HG : a_guess _ _ _ _ _ |- _ =>
    apply probe_guess_det in HG as [-> ->] end.
  split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  STEP 4: the continuation is stuck                                   *)
(* ------------------------------------------------------------------ *)

Lemma probe_continuation_stuck : forall Θ Q Θ1,
  ~ a_sub a_sub_mode_ty (mode_fn mode_tc) (P0d f) Θ
      (pskl_arrow (pskl_all_syn (pskl_var_f f)) (pskl_all_syn (pskl_var_f f)))
      Q Θ1.
Proof.
  intros Θ Q Θ1 H.
  unfold P0d in H.
  inversion H; subst.
  match goal with Hc : a_consis _ _ _ _ _ _ _ |- _ =>
    exact (a_consis_forall_arrow_vs_vacuous_var_stuck Hc) end.
Qed.

(* ------------------------------------------------------------------ *)
(*  ⭐⭐ THE HEADLINE ¬∃: no a_sub run exists at the configuration —      *)
(*  ForallL is the only entry at a ∀ subject with an arrow P0 at        *)
(*  FN(TC), its extract is forced to the collapsed guess, and the       *)
(*  continuation is scope-stuck                                         *)
(* ------------------------------------------------------------------ *)

Theorem probe_no_run : forall Q Θ1,
  ~ a_sub a_sub_mode_ty (mode_fn mode_tc) (P0d f) (Θ0d f)
      (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0))) Q Θ1.
Proof.
  intros Q Θ1 H.
  inversion H; subst.
  match goal with Hext : a_extract _ _ _ _ _ _ _ _ |- _ =>
    unfold open_pskl_wrt_pskl in Hext; simpl in Hext;
    apply probe_extract_det in Hext as [-> ->] end.
  match goal with
  | Hcont : a_sub _ _ _ _ (open_pskl_wrt_pskl _ _) _ _ |- _ =>
      unfold open_pskl_wrt_pskl in Hcont; simpl in Hcont;
      exact (probe_continuation_stuck Hcont)
  end.
Qed.

End ProbeRun.

(* ===================================================================== *)
(*  The motive instance is FALSE, hence main_forall is FALSE              *)
(* ===================================================================== *)

Section ProbeMotive.

Variables f e t : atom.
Hypothesis Het : e <> t.

(** Every premise of [sub_complete_concl] holds at the double-occ
    configuration ([p7_sub_shield_positional_over_strong] supplies them
    all), but its conclusion demands the run [probe_no_run] refutes. *)
Theorem probe_motive_instance_false :
  ~ sub_complete_concl 3 a_sub_mode_ty (mode_fn mode_tc)
      (Θ0d f) (P0d f) (Pd t) (Rd t) (Rd t) empty (Θ0d f) (κd f) Qd.
Proof.
  intros Hmc.
  destruct (@p7_sub_shield_positional_over_strong f e t Het)
    as (Hwf0 & HwfP0 & HwfPd & Hmode & _ & Hgf & Herase & Hinc & Hslack
        & HwfQ & Hjoin & _ & _ & _ & _ & _ & Hfill & _).
  unfold sub_complete_concl in Hmc.
  assert (HskC : a_sub_mode_ty = a_sub_mode_sk ->
                 a_sk_mode_compat (mode_fn mode_tc) (P0d f))
    by (intros Hne; discriminate Hne).
  destruct (Hmc Hwf0 Hwf0 HwfP0 HwfPd HskC (fun _ => Hmode)
              Herase Hinc Hslack Hjoin Hfill HwfQ (fun _ => Hgf))
    as [P1 [Θ1 [Hrun _]]].
  exact (@probe_no_run f P1 Θ1 Hrun).
Qed.

End ProbeMotive.

(** ⭐⭐⭐ [main_forall] — the ONE hypothesis of §12's assembly
    ([a_sub_complete_bundle_holds]) — is FALSE as stated: its [R] is the
    ∀-headed [Rd], its [P0]-guard is met ([P0d] is a guarded arrow), and
    the motive instance it then asserts is refuted above.  The bundle and
    [a_sub_complete_thm] are therefore VACUOUS as stated; the repair is a
    payload side condition on the MOTIVE (the typing's P0-invariant),
    docs/HANDOFF-completeness-repair.md TASKS 2–3. *)
Theorem probe_main_forall_false : ~ main_forall 3.
Proof.
  intros Hmf.
  destruct (atom_fresh empty) as [f _].
  destruct (atom_fresh (singleton f)) as [e He].
  destruct (atom_fresh (add e (singleton f))) as [t Ht].
  assert (Het : e <> t) by (intros Heq; subst; clear - Ht; fsetdec).
  apply (@probe_motive_instance_false f e t Het).
  apply Hmf.
  - right; exists t, Rjd; reflexivity.
  - left; apply P0d_guarded.
Qed.

Corollary probe_main_forall_hyp_false : ~ (forall n, main_forall n).
Proof. intros Hmf. exact (probe_main_forall_false (Hmf 3)). Qed.

(* ===================================================================== *)
(*  ⚠️⚠️ THE PAPER'S OWN [lemma:complete-look] FAILS HERE                   *)
(*                                                                        *)
(*  subtyping-proofs.tex:2730.  Its ForallL consumer (:3371) has NO        *)
(*  [sub_shield]-like premise: it invokes look completeness on the mode    *)
(*  compatibility, the erasure, the guess's TAG SORTING, the freshness,    *)
(*  the declarative premise at [Ψ,Ψa], and the FILL — all of which hold    *)
(*  here ([p7_sub_shield_positional_over_strong] + [ψd_tags] +             *)
(*  [join_premise_d] + [fill_d]) — and concludes that the look succeeds    *)
(*  with an output that is PRECISE BELOW the guess's erasure:              *)
(*                                                                        *)
(*      Θ ⊢ precise{θa Pa}{erase ψa}.                                      *)
(*                                                                        *)
(*  That conclusion is FALSE at this configuration, for EVERY extract      *)
(*  output: the extract is deterministic ([probe_extract_det]) and returns *)
(*  the vacuous-binder guess [∀_.f̂], whose κ-image [∀_.(1→1)] cannot       *)
(*  refine [∀β.β→β] — one arrow step leaves [1 ⊳ β], and the only rule     *)
(*  that could refine a unit to a variable ([ad_refine_syn__flex_r])       *)
(*  demands a DEFINED flexible, while [Θ0d] carries an undefined one.      *)
(*                                                                        *)
(*  ⭐ SO THE GAP IS IN THE PAPER'S LOOK-COMPLETENESS LEMMA, not only in    *)
(*  the mech-invented [sub_shield] that stands in for it: [sub_shield] is  *)
(*  the mech's repair OF THIS LEMMA (it is P6-L's premise), and the        *)
(*  configuration refutes the paper's unrepaired statement directly.       *)
(*  The repair must restrict [P0] (reachability) — DESIGN §14.9.           *)
(* ===================================================================== *)

Theorem p6l_look_completeness_fails : forall f e α Ξ Pa,
  (Θ0d f) ⊢ (pskl_arrow (pskl_var_f α) (pskl_var_f α))
      ⊳[ a_sub_mode_ty , α , (mode_fn mode_tc) ] (P0d f) ⤳ Ξ ↪ Pa ->
  ~ (Θ0d f) ⨟ empty ⊢ₚᵣᵃ (msubst_pskl (κd f) Pa) ⊑ (⌊ ψd e ⌋ˢ).
Proof.
  intros f e α Ξ Pa Hext.
  destruct (probe_extract_det Hext) as [_ ->].
  unfold ad_precise, κd, ψd, cexψ; simpl.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [ | congruence ].
  intros H. inversion H; subst.
  pick fresh α0 for L.
  match goal with Hf : forall a, a `notin` L -> _ |- _ =>
    specialize (Hf α0 ltac:(auto)) end.
  unfold open_bskl_wrt_bskl in *; simpl in *.
  match goal with Ha : _ ⨟ _ ⊢ᵣᵃ (bskl_arrow _ _) ⊳ _ |- _ =>
    inversion Ha; subst end.
  match goal with
  | Hu : _ ⨟ _ ⊢ᵣᵃ bskl_unit ⊳ (bskl_var_f _) |- _ => inversion Hu; subst
  end.
  match goal with
  | Hb : binds _ (abind_flex_mono_def _) _ |- _ =>
      unfold Θ0d, binds in Hb; simpl in Hb;
      destruct Hb as [Heq | Hnil]; [ inversion Heq | destruct Hnil ]
  end.
Qed.

Print Assumptions p6l_look_completeness_fails.
Print Assumptions probe_no_run.
Print Assumptions probe_motive_instance_false.
Print Assumptions probe_main_forall_false.
