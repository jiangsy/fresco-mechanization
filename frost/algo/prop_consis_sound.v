(** Appendix B (consistency-proofs.tex), "Soundness of Consistency" —
    support layer for part 1's main induction.

    The paper augments a solution to a consistency problem with four
    components (⊴, declarative consistency, and the two refinement
    directions).  This file provides the pieces the flex-variable cases
    of the main induction need:

    - [a_unify_sound_consis]: part 2's solution restated declaratively
      (the paper's Flex case reads the unification solution as
      [typconsis{Θ1}{α̂}{β̂}]).  Unification subjects are always
      variables ([a_unify_var_inv]), so the conclusion is stated over
      any binds-monotone extension of the output context in which the
      subjects are tvar-ish — exactly how the skip cases re-assemble
      the context around the recursive call.
    - [ad_pat_consis_refine_syn_mono] / [ad_pat_consis_refine_pskl_mono]:
      the paper's "since flexible variables do not depend on the rigid
      type variables in Δ" steps — a consistency derivation against a
      MONOTYPE painting yields both refinement components (FlexL/FlexR/
      Flex cases of part 1).
    - [ad_pat_consis_fold_def_q_mono]: Q-side (painted-side) definition
      folding at monotypes, the missing mirror of
      [ad_pat_consis_fold_def]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Monotype paintings                                                    *)
(* ===================================================================== *)

(** Painted skeletons of monotypes: no quantifiers, no ghosts. *)
Inductive mono_bskl : bskl -> Prop :=
| mono_bskl__unit  : mono_bskl bskl_unit
| mono_bskl__var   : forall X, mono_bskl (bskl_var_f X)
| mono_bskl__arrow : forall Q1 Q2,
    mono_bskl Q1 -> mono_bskl Q2 -> mono_bskl (bskl_arrow Q1 Q2).

Lemma mono_ptyp_to_bskl_syn : forall τ,
  mono_ptyp τ -> mono_bskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; unfold ptyp_to_bskl_syn in *; simpl; constructor; auto.
Qed.

(** On monotypes the two paintings coincide (colours only differ at
    quantifiers). *)
Lemma mono_inh_eq_syn : forall τ,
  mono_ptyp τ ->
  pskl_to_bskl_inh (ptyp_to_pskl τ) = ptyp_to_bskl_syn τ.
Proof.
  induction 1; unfold ptyp_to_bskl_syn in *; simpl; f_equal; auto.
Qed.

Lemma mono_bskl_inh_syn : forall P,
  mono_bskl (pskl_to_bskl_inh P) ->
  pskl_to_bskl_syn P = pskl_to_bskl_inh P.
Proof.
  induction P; intros Hm; simpl in *; try reflexivity;
    inversion Hm; subst; f_equal; auto.
Qed.

(** Erasure is a left inverse of the syn-painted monotype embedding. *)
Lemma uskl_to_pskl_ptyp : forall A,
  uskl_to_pskl (ptyp_to_uskl_syn A) = ptyp_to_pskl A.
Proof.
  intros. rewrite <- pskl_to_uskl_ptyp. apply uskl_to_pskl_pskl_to_uskl.
Qed.

(* ===================================================================== *)
(*  Context bookkeeping                                                   *)
(* ===================================================================== *)

Lemma a_binds_tvar_mon : forall X Θ Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  a_binds_tvar X Θ ->
  a_binds_tvar X Θ'.
Proof.
  intros * Hmon [Hb | [Hb | [τ Hb]]];
    [ left | right; left | right; right; exists τ ]; auto.
Qed.

(** A defined flexible variable's definition is a monotype in any
    well-formed context. *)
Lemma a_wf_aenv_binds_def_mono : forall Θ γ τ,
  a_wf_aenv Θ ->
  binds γ (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ.
Proof.
  intros Θ γ τ Hwf; induction Hwf; intros Hb;
    try solve
      [ inversion Hb
      | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | auto ]
      | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ inversion Heq; subst; auto | auto ] ].
Qed.

(* ===================================================================== *)
(*  Q-side definition folding at monotypes                                *)
(* ===================================================================== *)

(** Well-formedness of a monotype's skeleton is preserved when a
    definition is folded back. *)
Lemma ad_wf_pskl_mono_subst_back : forall Θ γ τ B,
  binds γ (abind_flex_mono_def τ) Θ ->
  mono_ptyp B ->
  ad_wf_pskl Θ empty (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ B)) ->
  ad_wf_pskl Θ empty (ptyp_to_pskl B).
Proof.
  intros * Hb HmB; induction HmB; intros Hwf; simpl in *.
  - apply ad_wf_pskl__unit.
  - destruct (eq_var X γ) as [->|Hne].
    + apply ad_wf_pskl__var. right. right; right; exists τ; auto.
    + exact Hwf.
  - inversion Hwf; subst. apply ad_wf_pskl__arrow; auto.
Qed.

(** Folding a flexible variable's definition on the PAINTED side of a
    consistency derivation, at a monotype: if [S ≈ syn(B[τ/γ̂])] and
    [γ̂ := τ ∈ Θ], then [S ≈ syn B] (rule FlexR reintroduces [γ̂]).
    Mirror of [ad_pat_consis_fold_def]. *)
Lemma ad_pat_consis_fold_def_q_mono : forall Θ γ τ Ψ S Q',
  ad_pat_consis Ψ Θ S Q' ->
  binds γ (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  forall B,
  mono_ptyp B ->
  Q' = ptyp_to_bskl_syn (subst_ptyp_in_ptyp τ γ B) ->
  ad_pat_consis Ψ Θ S (ptyp_to_bskl_syn B).
Proof.
  intros Θ γ τ Ψ S Q' H Hb Hmτ.
  induction H; intros B HmB HeqQ;
    (destruct B as [ | nB | XB | B1 B2 | B0 ];
     simpl in HeqQ;
     (* mono excludes ∀ *)
     try solve [ inversion HmB ];
     (* non-var heads that cannot match *)
     try discriminate HeqQ).
  - (* unit / B unit *)
    apply ad_pat_consis__unit; auto.
  - (* unit / B var *)
    destruct (eq_var XB γ) as [->|Hne].
    + apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb | ].
      rewrite <- HeqQ. apply ad_pat_consis__unit; auto.
    + discriminate HeqQ.
  - (* var / B var *)
    destruct (eq_var XB γ) as [->|Hne].
    + apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb | ].
      rewrite <- HeqQ. apply ad_pat_consis__var; auto.
    + inversion HeqQ; subst. apply ad_pat_consis__var; auto.
  - (* arrow / B var *)
    destruct (eq_var XB γ) as [->|Hne].
    + apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb | ].
      rewrite <- HeqQ. eapply ad_pat_consis__arrow; eauto.
    + discriminate HeqQ.
  - (* arrow / B arrow *)
    inversion HeqQ; subst. inversion HmB; subst.
    eapply ad_pat_consis__arrow; eauto.
  - (* forall_inh_tagged / B var *)
    destruct (eq_var XB γ) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* forall_inh_untagged / B var *)
    destruct (eq_var XB γ) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* forall_syn_tagged / B var *)
    destruct (eq_var XB γ) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* forall_syn / B var *)
    destruct (eq_var XB γ) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* ghostg / B var *)
    destruct (eq_var XB γ) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* topholeg / B var *)
    destruct (eq_var XB γ) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* hole / B unit *)
    assert (HP : P = ptyp_to_pskl (subst_ptyp_in_ptyp τ γ ptyp_unit)).
    { apply (f_equal bskl_to_pskl) in HeqQ.
      rewrite bskl_to_pskl_pskl_to_bskl_inh in HeqQ.
      unfold ptyp_to_bskl_syn in HeqQ.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in HeqQ. exact HeqQ. }
    replace (ptyp_to_bskl_syn ptyp_unit)
      with (pskl_to_bskl_inh (ptyp_to_pskl ptyp_unit)) by reflexivity.
    apply ad_pat_consis__hole; auto.
    apply ad_wf_pskl_mono_subst_back with (γ := γ) (τ := τ); auto.
    rewrite <- HP; auto.
  - (* hole / B var *)
    destruct (eq_var XB γ) as [->|Hne].
    + apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb | ].
      rewrite <- HeqQ. apply ad_pat_consis__hole; auto.
    + assert (HP : P = ptyp_to_pskl (ptyp_var_f XB)).
      { apply (f_equal bskl_to_pskl) in HeqQ.
        rewrite bskl_to_pskl_pskl_to_bskl_inh in HeqQ.
        unfold ptyp_to_bskl_syn in HeqQ.
        rewrite bskl_to_pskl_pskl_to_bskl_syn in HeqQ. exact HeqQ. }
      replace (ptyp_to_bskl_syn (ptyp_var_f XB))
        with (pskl_to_bskl_inh (ptyp_to_pskl (ptyp_var_f XB)))
        by reflexivity.
      apply ad_pat_consis__hole; auto.
      rewrite <- HP; auto.
  - (* hole / B arrow *)
    assert (HP : P = ptyp_to_pskl
                       (subst_ptyp_in_ptyp τ γ (ptyp_arrow B1 B2))).
    { apply (f_equal bskl_to_pskl) in HeqQ.
      rewrite bskl_to_pskl_pskl_to_bskl_inh in HeqQ.
      unfold ptyp_to_bskl_syn in HeqQ.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in HeqQ. exact HeqQ. }
    rewrite <- (mono_inh_eq_syn HmB).
    apply ad_pat_consis__hole; auto.
    apply ad_wf_pskl_mono_subst_back with (γ := γ) (τ := τ); auto.
    rewrite <- HP; auto.
  - (* tophole / B var *)
    destruct (eq_var XB γ) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* tophole_inh / B var *)
    destruct (eq_var XB γ) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* tophole_drop / B unit *)
    apply ad_pat_consis__tophole_drop. apply IHad_pat_consis; auto.
  - (* tophole_drop / B var *)
    apply ad_pat_consis__tophole_drop.
    apply IHad_pat_consis; auto.
  - (* tophole_drop / B arrow *)
    apply ad_pat_consis__tophole_drop. apply IHad_pat_consis; auto.
  - (* flex_l / B unit *)
    eapply ad_pat_consis__flex_l; eauto.
  - (* flex_l / B var *)
    eapply ad_pat_consis__flex_l; eauto.
  - (* flex_l / B arrow *)
    eapply ad_pat_consis__flex_l; eauto.
  - (* flex_r / B var *)
    destruct (eq_var XB γ) as [->|Hne].
    + apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb | ].
      rewrite <- HeqQ. eapply ad_pat_consis__flex_r; eauto.
    + inversion HeqQ; subst. eapply ad_pat_consis__flex_r; eauto.
Qed.

(* ===================================================================== *)
(*  Soundness of variable unification, declaratively                      *)
(*  (thm:sound-consistency part 2, read as the paper's Flex case does)    *)
(* ===================================================================== *)

(** Unification subjects are always variables. *)
Lemma a_unify_var_inv : forall Θ0 A B Θ1,
  Θ0 ⊲ A ≈ᵘ B ⊣ Θ1 ->
  (exists α, A = ptyp_var_f α) /\ (exists β, B = ptyp_var_f β).
Proof.
  intros * Hu; induction Hu;
    try solve [ split; eauto ]; try solve [ exact IHHu ].
  - (* flex_assign: a substituted non-variable stays a non-variable *)
    destruct IHHu as [[α' HA] [β' HB]].
    split.
    + destruct A as [ | n | X | A1 A2 | A0 ]; simpl in HA;
        try discriminate HA; eauto.
    + destruct B as [ | n | X | B1 B2 | B0 ]; simpl in HB;
        try discriminate HB; eauto.
Qed.

(** Part 2, declaratively: the output context equates the two variables
    as skeleton consistency — over any binds-monotone extension [Θ']
    of the output in which the subjects' variables are tvar-ish (the
    skip cases re-assemble the surrounding context around the
    recursive call, so the conclusion must survive that context
    growth). *)
Lemma a_unify_sound_consis : forall Θ0 A B Θ1,
  Θ0 ⊲ A ≈ᵘ B ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  mono_ptyp A ->
  mono_ptyp B ->
  forall Θ',
  (forall x b, binds x b Θ1 -> binds x b Θ') ->
  (forall X, X `in` (ftvar_in_ptyp A `union` ftvar_in_ptyp B) ->
     a_binds_tvar X Θ') ->
  ad_pat_consis empty Θ' (ptyp_to_uskl_syn A) (ptyp_to_bskl_syn B).
Proof.
  intros * Hu; induction Hu; intros Hwf HmA HmB Θ' Hmon Hvis.
  - (* Flex-Flex-Id *)
    apply ad_pat_consis__var; [ fsetdec | ].
    apply Hvis. simpl. fsetdec.
  - (* Flex-Flex-L : α̂ := β̂ *)
    apply ad_pat_consis__flex_l with (τ := ptyp_var_f β).
    { apply Hmon. unfold binds; left; reflexivity. }
    apply ad_pat_consis__var; [ fsetdec | ].
    apply Hvis. simpl. fsetdec.
  - (* Flex-Flex-R : β̂ := α̂ *)
    apply ad_pat_consis__flex_r with (τ := ptyp_var_f α).
    { apply Hmon. unfold binds; left; reflexivity. }
    apply ad_pat_consis__var; [ fsetdec | ].
    apply Hvis. simpl. fsetdec.
  - (* Flex-Flex-Assign *)
    assert (Hwf0 : a_wf_aenv Θ0) by (inversion Hwf; auto).
    assert (Hwfτ : a_wf_ptyp Θ0 τ) by (inversion Hwf; auto).
    assert (Hmτ0 : mono_ptyp τ) by (inversion Hwf; auto).
    assert (HmA' : mono_ptyp (subst_ptyp_in_ptyp τ γ A))
      by (auto using mono_ptyp_subst).
    assert (HmB' : mono_ptyp (subst_ptyp_in_ptyp τ γ B))
      by (auto using mono_ptyp_subst).
    destruct (a_unify_var_inv Hu) as [[α' HA'] [β' HB']].
    assert (Hmon1 : forall x b, binds x b Θ1 -> binds x b Θ').
    { intros x b Hb. apply Hmon. unfold binds; right; exact Hb. }
    assert (Hinc : Θ0 ⊴ Θ1)
      by (destruct (a_unify_sound Hu Hwf0 HmA' HmB') as [Hi _]; exact Hi).
    (* free variables of τ are tvar-ish all the way to Θ' *)
    assert (Hτvis : forall X, X `in` ftvar_in_ptyp τ -> a_binds_tvar X Θ').
    { intros X HX.
      apply a_binds_tvar_mon with (Θ := Θ1); auto.
      eapply a_isub_binds_tvarish; eauto.
      eapply a_wf_ptyp_ftv_tvarish; eauto. }
    (* the substituted subjects' variables are tvar-ish in Θ' *)
    assert (Hvis' : forall X,
               X `in` (ftvar_in_ptyp (subst_ptyp_in_ptyp τ γ A)
                       `union` ftvar_in_ptyp (subst_ptyp_in_ptyp τ γ B)) ->
               a_binds_tvar X Θ').
    { intros X HX.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper A τ γ) as HuA.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper B τ γ) as HuB.
      assert (HX' : X `in` (ftvar_in_ptyp τ
                    `union` remove γ (ftvar_in_ptyp A)
                    `union` remove γ (ftvar_in_ptyp B)))
        by (clear - HX HuA HuB; fsetdec).
      destruct (AtomSetImpl.union_1 HX') as [Hτ | Hrest]; auto.
      apply Hvis. clear - Hrest; fsetdec. }
    (* dispatch on whether each subject is the substituted variable *)
    destruct A as [ | nA | XA | A1 A2 | A0 ]; simpl in HA';
      try discriminate HA'; try solve [ inversion HmA ].
    destruct B as [ | nB | XB | B1 B2 | B0 ]; simpl in HB';
      try discriminate HB'; try solve [ inversion HmB ].
    simpl in IHHu, Hvis'.
    destruct (eq_var XA γ) as [->|HneA]; destruct (eq_var XB γ) as [->|HneB].
    + (* both subjects are γ̂ *)
      apply ad_pat_consis__flex_l with (τ := τ).
      { apply Hmon. unfold binds; left; reflexivity. }
      apply ad_pat_consis__flex_r with (τ := τ).
      { apply Hmon. unfold binds; left; reflexivity. }
      apply IHHu; auto.
    + (* LHS is γ̂ *)
      apply ad_pat_consis__flex_l with (τ := τ).
      { apply Hmon. unfold binds; left; reflexivity. }
      apply IHHu; auto.
    + (* RHS is γ̂ *)
      apply ad_pat_consis__flex_r with (τ := τ).
      { apply Hmon. unfold binds; left; reflexivity. }
      apply IHHu; auto.
    + (* neither is γ̂ *)
      apply IHHu; auto.
  - (* Flex-Flex-Skip *)
    inversion Hwf; subst.
    apply IHHu; auto;
      try (intros x b Hb; apply Hmon; unfold binds; right; exact Hb).
  - (* Flex-Flex-Skip' *)
    destruct H as [-> | [[Q ->] | [Q ->]]]; inversion Hwf; subst;
      (apply IHHu; auto;
       try (intros x b Hb; apply Hmon; unfold binds; right; exact Hb)).
Qed.

(* ===================================================================== *)
(*  Consistency at a monotype painting implies both refinements          *)
(*  (the paper's since-flexible-variables-do-not-depend-on-the-rigid-    *)
(*   type-variables-in-Δ steps, part 1 cases Flex / FlexL / FlexR)       *)
(* ===================================================================== *)

Lemma ad_pat_consis_refine_syn_mono : forall Ψ Θ S Q,
  ad_pat_consis Ψ Θ S Q ->
  a_wf_aenv Θ ->
  mono_bskl Q ->
  forall Δ,
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh (uskl_to_pskl S)) ⊳ Q.
Proof.
  intros Ψ Θ S Q H Hwf; induction H; intros HmQ Δ; simpl;
    try solve [ inversion HmQ ].
  - (* unit *)
    apply ad_refine_syn__unit.
  - (* var (rigid) *)
    apply ad_refine_syn__var; auto.
  - (* arrow *)
    inversion HmQ; subst.
    apply ad_refine_syn__arrow; auto.
  - (* hole : the RHS is the inh painting of a wf skeleton *)
    rewrite <- (mono_bskl_inh_syn P HmQ).
    apply ad_refine_syn__hole; auto.
  - (* tophole_drop *)
    apply ad_refine_syn__tophole_remove; auto.
  - (* flex_l *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_syn__flex_l with (τ := τ); [ exact H | ].
    specialize (IHad_pat_consis Hwf HmQ Δ).
    rewrite uskl_to_pskl_ptyp in IHad_pat_consis.
    rewrite (mono_inh_eq_syn Hmτ) in IHad_pat_consis.
    exact IHad_pat_consis.
  - (* flex_r *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_syn__flex_r with (τ := τ); [ exact H | ].
    apply IHad_pat_consis; auto using mono_ptyp_to_bskl_syn.
Qed.

(* ===================================================================== *)
(*  Fill-hygienic refinement (internal scaffolding)                       *)
(*                                                                        *)
(*  The ∀-cases of the part-1 main induction must move the opened binder  *)
(*  from the algorithmic context (where the ForallInh/ForallSyn premises  *)
(*  bind it rigid) to the refinement judgment's Δ (where the declarative  *)
(*  __all rule wants it).  A naive strip of the [α ~ tvar] entry is       *)
(*  unsound in general — a ghost FILL could mention α — but the           *)
(*  consistency rules' side conditions (Ghost: Δ2 ∩ ftv(P0) = ∅;          *)
(*  GhostR: Δ1 ∩ ftv(P) = ∅) guarantee fills avoid the Δ-variables.       *)
(*  The paper glosses this as "by definition of refinement".  We make it  *)
(*  formal with a variant judgment carrying a set [F] forbidden in ghost  *)
(*  fills: only the hole rules gain a side condition; [F := Δ1 ∪ Δ2] in   *)
(*  the induction; [*_forget] recovers the real judgments at the end.     *)
(* ===================================================================== *)

Inductive ad_refine_syn_f (F : atoms) : aenv -> atoms -> bskl -> bskl -> Prop :=
| ad_refine_syn_f__unit : forall Θ Δ,
    ad_refine_syn_f F Θ Δ bskl_unit bskl_unit
| ad_refine_syn_f__var : forall Θ Δ X,
    X `in` Δ \/ a_binds_tvar X Θ ->
    ad_refine_syn_f F Θ Δ (bskl_var_f X) (bskl_var_f X)
| ad_refine_syn_f__arrow : forall Θ Δ Q1 Q2 P1 P2,
    ad_refine_syn_f F Θ Δ Q1 P1 ->
    ad_refine_syn_f F Θ Δ Q2 P2 ->
    ad_refine_syn_f F Θ Δ (bskl_arrow Q1 Q2) (bskl_arrow P1 P2)
| ad_refine_syn_f__all : forall L Θ Δ Q P,
    (forall X, X `notin` L ->
       ad_refine_syn_f F Θ (add X Δ)
         (open_bskl_wrt_bskl Q (bskl_var_f X))
         (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    ad_refine_syn_f F Θ Δ (bskl_all_inh Q) (bskl_all_inh P)
| ad_refine_syn_f__hole : forall Θ Δ P,
    AtomSetImpl.inter F (ftvar_in_pskl P) [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    ad_refine_syn_f F Θ Δ bskl_hole (pskl_to_bskl_syn P)
| ad_refine_syn_f__tophole_remove : forall Θ Δ Q P,
    ad_refine_syn_f F Θ Δ Q P ->
    ad_refine_syn_f F Θ Δ (bskl_tophole Q) P
| ad_refine_syn_f__tophole_fill : forall L Θ Δ Q P,
    (forall X, X `notin` L ->
       ad_refine_syn_f F ((X ~ abind_tvar) ++ Θ) Δ
         (bskl_tophole Q) (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    ad_refine_syn_f F Θ Δ (bskl_tophole Q) (bskl_all_syn P)
| ad_refine_syn_f__tophole_keep : forall Θ Δ Q P,
    guarded_bskl P ->
    ad_refine_syn_f F Θ Δ Q P ->
    ad_refine_syn_f F Θ Δ (bskl_tophole Q) (bskl_tophole P)
| ad_refine_syn_f__flex_l : forall Θ Δ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_refine_syn_f F Θ Δ (ptyp_to_bskl_syn τ) Q ->
    ad_refine_syn_f F Θ Δ (bskl_var_f α) Q
| ad_refine_syn_f__flex_r : forall Θ Δ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_refine_syn_f F Θ Δ P (ptyp_to_bskl_syn τ) ->
    ad_refine_syn_f F Θ Δ P (bskl_var_f α).

Inductive ad_refine_pskl_f (F : atoms) : aenv -> atoms -> pskl -> pskl -> Prop :=
| ad_refine_pskl_f__unit : forall Θ Δ,
    ad_refine_pskl_f F Θ Δ pskl_unit pskl_unit
| ad_refine_pskl_f__var : forall Θ Δ X,
    X `in` Δ \/ a_binds_tvar X Θ ->
    ad_refine_pskl_f F Θ Δ (pskl_var_f X) (pskl_var_f X)
| ad_refine_pskl_f__arrow : forall Θ Δ P1 P2 Q1 Q2,
    ad_refine_pskl_f F Θ Δ P1 Q1 ->
    ad_refine_pskl_f F Θ Δ P2 Q2 ->
    ad_refine_pskl_f F Θ Δ (pskl_arrow P1 P2) (pskl_arrow Q1 Q2)
| ad_refine_pskl_f__all : forall L Θ Δ P Q,
    (forall X, X `notin` L ->
       ad_refine_pskl_f F Θ (add X Δ)
         (open_pskl_wrt_pskl P (pskl_var_f X))
         (open_pskl_wrt_pskl Q (pskl_var_f X))) ->
    ad_refine_pskl_f F Θ Δ (pskl_all_syn P) (pskl_all_syn Q)
| ad_refine_pskl_f__hole : forall Θ Δ Q,
    AtomSetImpl.inter F (ftvar_in_pskl Q) [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ Q ->
    ad_refine_pskl_f F Θ Δ pskl_hole Q
| ad_refine_pskl_f__tophole_remove : forall Θ Δ P Q,
    ad_refine_pskl_f F Θ Δ P Q ->
    ad_refine_pskl_f F Θ Δ (pskl_tophole P) Q
| ad_refine_pskl_f__tophole_fill : forall L Θ Δ P Q,
    (forall X, X `notin` L ->
       ad_refine_pskl_f F ((X ~ abind_tvar) ++ Θ) Δ
         (pskl_tophole P) (open_pskl_wrt_pskl Q (pskl_var_f X))) ->
    ad_refine_pskl_f F Θ Δ (pskl_tophole P) (pskl_all_syn Q)
| ad_refine_pskl_f__tophole_keep : forall Θ Δ P Q,
    guarded_pskl Q ->
    ad_refine_pskl_f F Θ Δ P Q ->
    ad_refine_pskl_f F Θ Δ (pskl_tophole P) (pskl_tophole Q)
| ad_refine_pskl_f__flex_l : forall Θ Δ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_refine_pskl_f F Θ Δ (ptyp_to_pskl τ) Q ->
    ad_refine_pskl_f F Θ Δ (pskl_var_f α) Q
| ad_refine_pskl_f__flex_r : forall Θ Δ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_refine_pskl_f F Θ Δ P (ptyp_to_pskl τ) ->
    ad_refine_pskl_f F Θ Δ P (pskl_var_f α).

(** Forgetting the hygiene set recovers the declarative judgments. *)
Lemma ad_refine_syn_f_forget : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P.
Proof.
  intros * H; induction H; eauto using ad_refine_syn.
Qed.

Lemma ad_refine_pskl_f_forget : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q.
Proof.
  intros * H; induction H; eauto using ad_refine_pskl.
Qed.

(** Skeleton wf survives removing a rigid entry the skeleton avoids. *)
Lemma ad_wf_pskl_strip_tvar : forall Θ1 α Θ2 Δ P,
  ad_wf_pskl (Θ1 ++ (α ~ abind_tvar) ++ Θ2) Δ P ->
  α `notin` ftvar_in_pskl P ->
  ad_wf_pskl (Θ1 ++ Θ2) Δ P.
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ2) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hfr; simpl in Hfr.
  - apply ad_wf_pskl__unit.
  - apply ad_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; auto | right ].
    eapply a_binds_tvar_strip_mid; eauto;
      try (intro Hc; inversion Hc; subst; fsetdec);
      try (intros τ0 Hc; inversion Hc).
  - apply ad_wf_pskl__arrow; [ apply IHad_wf_pskl1 | apply IHad_wf_pskl2 ];
      auto.
  - apply ad_wf_pskl__all with (L := L `union` singleton α).
    intros X HX. apply H0; auto.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  P (pskl_var_f X)) as Hup.
    simpl in Hup. fsetdec.
  - apply ad_wf_pskl__hole.
  - apply ad_wf_pskl__tophole; auto.
Qed.

(* ===================================================================== *)
(*  Renaming the opened binder (∀-case crux 2: the coloured witness is    *)
(*  obtained at ONE fresh variable and transported to every cofinite      *)
(*  instance).  Helper layer: embeddings vs substitution / free vars.     *)
(* ===================================================================== *)

Lemma binds_insert_mid : forall (b : abind) y Θ1 (e : list (atom * abind)) Θ0,
  binds y b (Θ1 ++ Θ0) ->
  binds y b (Θ1 ++ e ++ Θ0).
Proof.
  intros * Hb; unfold binds in *.
  apply in_app_or in Hb; apply in_or_app.
  destruct Hb; auto. right; apply in_or_app; auto.
Qed.

Lemma a_binds_tvar_insert_mid : forall y Θ1 (e : list (atom * abind)) Θ0,
  a_binds_tvar y (Θ1 ++ Θ0) ->
  a_binds_tvar y (Θ1 ++ e ++ Θ0).
Proof.
  intros * [Hb | [Hb | [τ Hb]]];
    [ left | right; left | right; right; exists τ ];
    auto using binds_insert_mid.
Qed.

(** Free variables of the paintings/readings are those of the skeleton. *)
Lemma ftvar_in_bskl_syn : forall P,
  ftvar_in_bskl (pskl_to_bskl_syn P) [=] ftvar_in_pskl P.
Proof.
  induction P; simpl; try fsetdec.
Qed.

Lemma ftvar_in_bskl_inh : forall P,
  ftvar_in_bskl (pskl_to_bskl_inh P) [=] ftvar_in_pskl P.
Proof.
  induction P; simpl; try fsetdec.
Qed.

Lemma ftvar_in_uskl_pskl : forall P,
  ftvar_in_uskl (pskl_to_uskl P) [=] ftvar_in_pskl P.
Proof.
  induction P; simpl; try fsetdec.
Qed.

(** Variable renaming commutes with the paintings. *)
Lemma subst_var_bskl_syn : forall P α X,
  subst_bskl_in_bskl (bskl_var_f X) α (pskl_to_bskl_syn P)
  = pskl_to_bskl_syn (subst_pskl_in_pskl (pskl_var_f X) α P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var Xps α); reflexivity.
Qed.

Lemma subst_var_bskl_inh : forall P α X,
  subst_bskl_in_bskl (bskl_var_f X) α (pskl_to_bskl_inh P)
  = pskl_to_bskl_inh (subst_pskl_in_pskl (pskl_var_f X) α P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var Xps α); reflexivity.
Qed.

Lemma subst_var_uskl : forall P α X,
  subst_bskl_in_uskl (uskl_var_f X) α (pskl_to_uskl P)
  = pskl_to_uskl (subst_pskl_in_pskl (pskl_var_f X) α P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var Xps α); reflexivity.
Qed.

(** Guardedness survives variable renaming. *)
Lemma guarded_pskl_subst_var : forall P α Y,
  guarded_pskl P ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f Y) α P).
Proof.
  intros * H; inversion H; subst; simpl.
  - constructor.
  - match goal with |- context [ if ?t then _ else _ ] => destruct t end;
      constructor.
  - constructor; apply subst_pskl_in_pskl_lc_pskl; auto.
Qed.

(** Renaming a rigid context entry in skeleton well-formedness. *)
Lemma ad_wf_pskl_rename_tvar : forall Θ1 α Θ0 Δ P Y,
  ad_wf_pskl (Θ1 ++ (α ~ abind_tvar) ++ Θ0) Δ P ->
  α `notin` Δ ->
  ad_wf_pskl (Θ1 ++ (Y ~ abind_tvar) ++ Θ0) Δ
    (subst_pskl_in_pskl (pskl_var_f Y) α P).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros HαΔ; simpl.
  - apply ad_wf_pskl__unit.
  - match goal with |- context [ if ?t then _ else _ ] =>
      destruct t as [->|Hne] end.
    + apply ad_wf_pskl__var. right.
      unfold a_binds_tvar. left.
      unfold binds. apply in_or_app. right. left. reflexivity.
    + apply ad_wf_pskl__var.
      destruct H as [HΔ | Htv]; [ left; auto | right ].
      apply (@a_binds_tvar_insert_mid X Θ1 (Y ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - apply ad_wf_pskl__arrow; auto.
  - apply ad_wf_pskl__all with (L := L `union` singleton α).
    intros Z HZ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var; auto.
  - apply ad_wf_pskl__hole.
  - apply ad_wf_pskl__tophole;
      [ apply guarded_pskl_subst_var; auto
      | apply IHad_wf_pskl; auto; fsetdec ].
Qed.

Lemma ftvar_in_uskl_ptyp_syn : forall A,
  ftvar_in_uskl (ptyp_to_uskl_syn A) [=] ftvar_in_ptyp A.
Proof.
  intros. rewrite <- pskl_to_uskl_ptyp.
  rewrite ftvar_in_uskl_pskl. apply ftvar_in_ptyp_to_pskl.
Qed.

Lemma ftvar_in_bskl_ptyp_syn : forall A,
  ftvar_in_bskl (ptyp_to_bskl_syn A) [=] ftvar_in_ptyp A.
Proof.
  intros. unfold ptyp_to_bskl_syn.
  rewrite ftvar_in_bskl_syn. apply ftvar_in_ptyp_to_pskl.
Qed.

(** Case-split every renaming decision in the goal; contradictory
    branches close by congruence. *)
Ltac destruct_var_eqs :=
  repeat match goal with
  | |- context [ if ?t then _ else _ ] => destruct t
  end; subst; try congruence.

(** Renaming the opened binder in Θ-level skeleton consistency. *)
Lemma ad_pat_consis_rename_tvar : forall Ψ Θ1 α Θ0 S Q Y,
  ad_pat_consis Ψ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) S Q ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_pat_consis Ψ (Θ1 ++ (Y ~ abind_tvar) ++ Θ0)
    (subst_bskl_in_uskl (uskl_var_f Y) α S)
    (subst_bskl_in_bskl (bskl_var_f Y) α Q).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom Hdefs; simpl.
  - (* unit *)
    apply ad_pat_consis__unit; auto.
  - (* var *)
    destruct_var_eqs.
    + apply ad_pat_consis__var; auto.
      unfold a_binds_tvar. left.
      unfold binds. apply in_or_app. right. left. reflexivity.
    + apply ad_pat_consis__var; auto.
      apply (@a_binds_tvar_insert_mid X Θ1 (Y ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - (* arrow *)
    eapply ad_pat_consis__arrow; eauto.
  - (* forall_inh_tagged *)
    eapply ad_pat_consis__forall_inh_tagged
      with (L := L `union` singleton α); eauto.
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : X `notin` L) by fsetdec.
    apply (H0 X HXL ((X ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* forall_inh_untagged *)
    eapply ad_pat_consis__forall_inh_untagged
      with (L := L `union` singleton α); eauto.
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : X `notin` L) by fsetdec.
    apply (H0 X HXL ((X ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* forall_syn_tagged *)
    eapply ad_pat_consis__forall_syn_tagged
      with (L := L `union` singleton α); eauto.
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : X `notin` L) by fsetdec.
    apply (H0 X HXL ((X ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* forall_syn *)
    eapply ad_pat_consis__forall_syn
      with (L := L `union` singleton α); eauto.
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : X `notin` L) by fsetdec.
    apply (H0 X HXL ((X ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* ghostg *)
    apply ad_pat_consis__ghostg; auto.
  - (* topholeg *)
    apply ad_pat_consis__topholeg; auto.
  - (* hole *)
    rewrite subst_var_bskl_inh.
    apply ad_pat_consis__hole; auto.
    apply ad_wf_pskl_rename_tvar; auto.
  - (* tophole *)
    apply ad_pat_consis__tophole; auto.
  - (* tophole_inh *)
    apply ad_pat_consis__tophole_inh
      with (L := L `union` singleton α).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : X `notin` L) by fsetdec.
    apply (H0 X HXL ((X ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* tophole_drop *)
    apply ad_pat_consis__tophole_drop; auto.
  - (* flex_l *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ)).
    { rewrite ftvar_in_uskl_ptyp_syn. eauto. }
    destruct_var_eqs.
    eapply ad_pat_consis__flex_l
      with (τ := τ);
      [ apply (@binds_insert_mid (abind_flex_mono_def τ) α0
                 Θ1 (Y ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_uskl_fresh_eq
                  (ptyp_to_uskl_syn τ) (uskl_var_f Y) α Hfr).
    auto.
  - (* flex_r *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ)).
    { rewrite ftvar_in_bskl_ptyp_syn. eauto. }
    destruct_var_eqs.
    eapply ad_pat_consis__flex_r
      with (τ := τ);
      [ apply (@binds_insert_mid (abind_flex_mono_def τ) α0
                 Θ1 (Y ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f Y) α Hfr).
    auto.
Qed.

(** THE transfer lemmas: with the opened binder [α] recorded in both the
    hygiene set and Δ, its rigid entry can be dropped from the context —
    the fills avoid it (hygiene), the variable occurrences use Δ, and
    context definitions cannot mention it (they sit below it). *)
Lemma ad_refine_syn_f_strip : forall F Θ1 α Θ2 Δ Q P,
  ad_refine_syn_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ2) Δ Q P ->
  α `in` F ->
  α `in` Δ ->
  ad_refine_syn_f F (Θ1 ++ Θ2) Δ Q P.
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ2) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros HαF HαΔ.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Htv]; [ left; auto | ].
    destruct (eq_var X α) as [->|Hne]; [ left; auto | right ].
    eapply a_binds_tvar_strip_mid; eauto;
      try (intro Hc; inversion Hc; subst; congruence);
      try (intros τ0 Hc; inversion Hc).
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L).
    intros X HX. apply H0; auto; try fsetdec.
  - apply ad_refine_syn_f__hole; auto.
    apply ad_wf_pskl_strip_tvar with (α := α); auto.
    clear - H HαF; fsetdec.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L).
    intros X HX.
    apply (H0 X HX ((X ~ abind_tvar) ++ Θ1)); auto.
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l;
      [ eapply binds_strip_mid; eauto; intro Hc; inversion Hc | auto ].
  - eapply ad_refine_syn_f__flex_r;
      [ eapply binds_strip_mid; eauto; intro Hc; inversion Hc | auto ].
Qed.

Lemma ad_refine_pskl_f_strip : forall F Θ1 α Θ2 Δ P Q,
  ad_refine_pskl_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ2) Δ P Q ->
  α `in` F ->
  α `in` Δ ->
  ad_refine_pskl_f F (Θ1 ++ Θ2) Δ P Q.
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ2) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros HαF HαΔ.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Htv]; [ left; auto | ].
    destruct (eq_var X α) as [->|Hne]; [ left; auto | right ].
    eapply a_binds_tvar_strip_mid; eauto;
      try (intro Hc; inversion Hc; subst; congruence);
      try (intros τ0 Hc; inversion Hc).
  - apply ad_refine_pskl_f__arrow; auto.
  - apply ad_refine_pskl_f__all with (L := L).
    intros X HX. apply H0; auto; try fsetdec.
  - apply ad_refine_pskl_f__hole; auto.
    apply ad_wf_pskl_strip_tvar with (α := α); auto.
    clear - H HαF; fsetdec.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - apply ad_refine_pskl_f__tophole_fill with (L := L).
    intros X HX.
    apply (H0 X HX ((X ~ abind_tvar) ++ Θ1)); auto.
  - apply ad_refine_pskl_f__tophole_keep; auto.
  - eapply ad_refine_pskl_f__flex_l;
      [ eapply binds_strip_mid; eauto; intro Hc; inversion Hc | auto ].
  - eapply ad_refine_pskl_f__flex_r;
      [ eapply binds_strip_mid; eauto; intro Hc; inversion Hc | auto ].
Qed.

(* --------------------------------------------------------------------- *)
(*  Δ-monotonicity and Δ-side renaming of the fill-hygienic judgments      *)
(* --------------------------------------------------------------------- *)

Lemma ad_refine_syn_f_delta_mono : forall F Θ Δ0 Q P,
  ad_refine_syn_f F Θ Δ0 Q P ->
  forall Δ, Δ0 [<=] Δ ->
  ad_refine_syn_f F Θ Δ Q P.
Proof.
  intros * H; induction H; intros Δ' Hsub;
    eauto using ad_refine_syn_f.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Htv]; [ left; fsetdec | auto ].
  - apply ad_refine_syn_f__all with (L := L).
    intros X HX. apply H0; auto. fsetdec.
Qed.

Lemma ad_refine_pskl_f_delta_mono : forall F Θ Δ0 P Q,
  ad_refine_pskl_f F Θ Δ0 P Q ->
  forall Δ, Δ0 [<=] Δ ->
  ad_refine_pskl_f F Θ Δ P Q.
Proof.
  intros * H; induction H; intros Δ' Hsub;
    eauto using ad_refine_pskl_f.
  - apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Htv]; [ left; fsetdec | auto ].
  - apply ad_refine_pskl_f__all with (L := L).
    intros X HX. apply H0; auto. fsetdec.
Qed.

Lemma guarded_bskl_subst_var : forall Q α Y,
  guarded_bskl Q ->
  guarded_bskl (subst_bskl_in_bskl (bskl_var_f Y) α Q).
Proof.
  intros * H; inversion H; subst; simpl.
  - constructor.
  - match goal with |- context [ if ?t then _ else _ ] => destruct t end;
      constructor.
  - constructor; apply subst_bskl_in_bskl_lc_bskl;
      auto using lc_bskl_var_f.
Qed.

(** Δ-side renaming: the ∀-cases obtain their per-instance refinement
    components by renaming the one-fresh-α witness.  [α] has already
    been stripped from Θ ([*_f_strip]) and lives in Δ and in the
    hygiene set (so ghost fills avoid it, making the fills invariant). *)
Lemma ad_refine_syn_f_rename : forall F Θ Δ α Q P Y,
  ad_refine_syn_f F Θ Δ Q P ->
  α `in` F ->
  α `notin` dom Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_refine_syn_f F Θ (add Y (remove α Δ))
    (subst_bskl_in_bskl (bskl_var_f Y) α Q)
    (subst_bskl_in_bskl (bskl_var_f Y) α P).
Proof.
  intros * H HαF; induction H; intros Hdom Hdefs; simpl.
  - (* unit *)
    apply ad_refine_syn_f__unit.
  - (* var *)
    destruct_var_eqs.
    + apply ad_refine_syn_f__var. left. fsetdec.
    + apply ad_refine_syn_f__var.
      destruct H as [HΔ | Htv]; [ left; fsetdec | auto ].
  - (* arrow *)
    apply ad_refine_syn_f__arrow; auto.
  - (* all *)
    apply ad_refine_syn_f__all
      with (L := L `union` singleton α `union` singleton Y).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    apply ad_refine_syn_f_delta_mono
      with (Δ0 := add Y (remove α (add X Δ))); [ apply H0; auto | ].
    fsetdec.
  - (* hole: the fill avoids α, so renaming leaves it untouched *)
    assert (Hfr : α `notin` ftvar_in_pskl P)
      by (clear - H HαF; fsetdec).
    rewrite subst_var_bskl_syn.
    rewrite (subst_pskl_in_pskl_fresh_eq P (pskl_var_f Y) α Hfr).
    apply ad_refine_syn_f__hole; auto.
  - (* tophole_remove *)
    apply ad_refine_syn_f__tophole_remove; auto.
  - (* tophole_fill *)
    apply ad_refine_syn_f__tophole_fill
      with (L := L `union` singleton α).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    replace (bskl_tophole (subst_bskl_in_bskl (bskl_var_f Y) α Q))
      with (subst_bskl_in_bskl (bskl_var_f Y) α (bskl_tophole Q))
      by reflexivity.
    apply H0; auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* tophole_keep *)
    apply ad_refine_syn_f__tophole_keep;
      auto using guarded_bskl_subst_var.
  - (* flex_l *)
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in H. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ)).
    { rewrite ftvar_in_bskl_ptyp_syn. eauto. }
    destruct_var_eqs.
    apply ad_refine_syn_f__flex_l with (τ := τ); [ exact H | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f Y) α Hfr).
    auto.
  - (* flex_r *)
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in H. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ)).
    { rewrite ftvar_in_bskl_ptyp_syn. eauto. }
    destruct_var_eqs.
    apply ad_refine_syn_f__flex_r with (τ := τ); [ exact H | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f Y) α Hfr).
    auto.
Qed.

Lemma ad_refine_pskl_f_rename : forall F Θ Δ α P Q Y,
  ad_refine_pskl_f F Θ Δ P Q ->
  α `in` F ->
  α `notin` dom Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_refine_pskl_f F Θ (add Y (remove α Δ))
    (subst_pskl_in_pskl (pskl_var_f Y) α P)
    (subst_pskl_in_pskl (pskl_var_f Y) α Q).
Proof.
  intros * H HαF; induction H; intros Hdom Hdefs; simpl.
  - (* unit *)
    apply ad_refine_pskl_f__unit.
  - (* var *)
    destruct_var_eqs.
    + apply ad_refine_pskl_f__var. left. fsetdec.
    + apply ad_refine_pskl_f__var.
      destruct H as [HΔ | Htv]; [ left; fsetdec | auto ].
  - (* arrow *)
    apply ad_refine_pskl_f__arrow; auto.
  - (* all *)
    apply ad_refine_pskl_f__all
      with (L := L `union` singleton α `union` singleton Y).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    apply ad_refine_pskl_f_delta_mono
      with (Δ0 := add Y (remove α (add X Δ))); [ apply H0; auto | ].
    fsetdec.
  - (* hole *)
    assert (Hfr : α `notin` ftvar_in_pskl Q)
      by (clear - H HαF; fsetdec).
    rewrite (subst_pskl_in_pskl_fresh_eq Q (pskl_var_f Y) α Hfr).
    apply ad_refine_pskl_f__hole; auto.
  - (* tophole_remove *)
    apply ad_refine_pskl_f__tophole_remove; auto.
  - (* tophole_fill *)
    apply ad_refine_pskl_f__tophole_fill
      with (L := L `union` singleton α).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    replace (pskl_tophole (subst_pskl_in_pskl (pskl_var_f Y) α P))
      with (subst_pskl_in_pskl (pskl_var_f Y) α (pskl_tophole P))
      by reflexivity.
    apply H0; auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* tophole_keep *)
    apply ad_refine_pskl_f__tophole_keep;
      auto using guarded_pskl_subst_var.
  - (* flex_l *)
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in H. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_pskl (ptyp_to_pskl τ)).
    { rewrite ftvar_in_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl_f__flex_l with (τ := τ); [ exact H | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f Y) α Hfr).
    auto.
  - (* flex_r *)
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in H. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_pskl (ptyp_to_pskl τ)).
    { rewrite ftvar_in_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl_f__flex_r with (τ := τ); [ exact H | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f Y) α Hfr).
    auto.
Qed.

(* --------------------------------------------------------------------- *)
(*  Reflexivity and ⊴-stability of the fill-hygienic judgments             *)
(*  (ports of prop_refine / prop_stability; hole fills are trivial or     *)
(*   carried verbatim)                                                    *)
(* --------------------------------------------------------------------- *)

Lemma ad_refine_syn_f_refl_inh : forall F Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  ad_refine_syn_f F Θ Δ (pskl_to_bskl_inh P) (pskl_to_bskl_inh P).
Proof.
  intros F Θ Δ P H; induction H; simpl.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; auto.
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L).
    intros X HX.
    repeat rewrite <- pskl_to_bskl_inh_open. auto.
  - replace (pskl_to_bskl_inh pskl_hole)
      with (pskl_to_bskl_syn pskl_hole) at 2 by reflexivity.
    apply ad_refine_syn_f__hole;
      [ simpl; fsetdec | apply ad_wf_pskl__hole ].
  - apply ad_refine_syn_f__tophole_keep;
      auto using guarded_pskl_to_bskl_inh.
    apply ad_refine_syn_f_delta_mono with (Δ0 := empty); auto.
    fsetdec.
Qed.

Lemma ad_refine_pskl_f_refl : forall F Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  ad_refine_pskl_f F Θ Δ P P.
Proof.
  intros F Θ Δ P H; induction H; simpl.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var; auto.
  - apply ad_refine_pskl_f__arrow; auto.
  - apply ad_refine_pskl_f__all with (L := L). auto.
  - apply ad_refine_pskl_f__hole;
      [ simpl; fsetdec | apply ad_wf_pskl__hole ].
  - apply ad_refine_pskl_f__tophole_keep; auto.
    apply ad_refine_pskl_f_delta_mono with (Δ0 := empty); auto.
    fsetdec.
Qed.

Lemma ad_refine_syn_f_isub : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  forall Θ', Θ ⊴ Θ' ->
  ad_refine_syn_f F Θ' Δ Q P.
Proof.
  intros F Θ Δ Q P H; induction H; intros Θ' Hle.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - apply ad_refine_syn_f__arrow; auto.
  - eapply ad_refine_syn_f__all with (L := L); eauto.
  - apply ad_refine_syn_f__hole; eauto using ad_wf_pskl_isub.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - eapply ad_refine_syn_f__tophole_fill with (L := L).
    intros X HX. eauto using a_isub_cons_tvar.
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_refine_syn_f__flex_r; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_refine_pskl_f_isub : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  forall Θ', Θ ⊴ Θ' ->
  ad_refine_pskl_f F Θ' Δ P Q.
Proof.
  intros F Θ Δ P Q H; induction H; intros Θ' Hle.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - apply ad_refine_pskl_f__arrow; auto.
  - eapply ad_refine_pskl_f__all with (L := L); eauto.
  - apply ad_refine_pskl_f__hole; eauto using ad_wf_pskl_isub.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - eapply ad_refine_pskl_f__tophole_fill with (L := L).
    intros X HX. eauto using a_isub_cons_tvar.
  - apply ad_refine_pskl_f__tophole_keep; auto.
  - eapply ad_refine_pskl_f__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_refine_pskl_f__flex_r; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_pat_consis_refine_pskl_mono : forall Ψ Θ S Q,
  ad_pat_consis Ψ Θ S Q ->
  a_wf_aenv Θ ->
  mono_bskl Q ->
  forall Δ,
  Θ ⨟ Δ ⊢ᵣₚᵃ (uskl_to_pskl S) ⊳ (bskl_to_pskl Q).
Proof.
  intros Ψ Θ S Q H Hwf; induction H; intros HmQ Δ; simpl;
    try solve [ inversion HmQ ].
  - (* unit *)
    apply ad_refine_pskl__unit.
  - (* var (rigid) *)
    apply ad_refine_pskl__var; auto.
  - (* arrow *)
    inversion HmQ; subst.
    apply ad_refine_pskl__arrow; auto.
  - (* hole *)
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    apply ad_refine_pskl__hole; auto.
  - (* tophole_drop *)
    apply ad_refine_pskl__tophole_remove; auto.
  - (* flex_l *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_pskl__flex_l with (τ := τ); [ exact H | ].
    specialize (IHad_pat_consis Hwf HmQ Δ).
    rewrite uskl_to_pskl_ptyp in IHad_pat_consis.
    exact IHad_pat_consis.
  - (* flex_r *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_pskl__flex_r with (τ := τ); [ exact H | ].
    specialize (IHad_pat_consis Hwf (mono_ptyp_to_bskl_syn Hmτ) Δ).
    unfold ptyp_to_bskl_syn in IHad_pat_consis.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in IHad_pat_consis.
    exact IHad_pat_consis.
Qed.

(* --------------------------------------------------------------------- *)
(*  Fill-hygienic variants of the consis→refine lemmas (flex cases of     *)
(*  the main induction).  The hygiene condition is inherited from the     *)
(*  painted side and the context's definitions (the problem invariant:    *)
(*  no flexible variable depends on Δ1/Δ2).                               *)
(* --------------------------------------------------------------------- *)

Lemma ad_pat_consis_refine_syn_f_mono : forall Ψ Θ S Q,
  ad_pat_consis Ψ Θ S Q ->
  a_wf_aenv Θ ->
  mono_bskl Q ->
  forall F Δ,
  AtomSetImpl.inter F (ftvar_in_bskl Q) [=] empty ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     AtomSetImpl.inter F (ftvar_in_ptyp τ) [=] empty) ->
  ad_refine_syn_f F Θ Δ (pskl_to_bskl_inh (uskl_to_pskl S)) Q.
Proof.
  intros Ψ Θ S Q H Hwf; induction H; intros HmQ F Δ HFQ HFdefs; simpl;
    try solve [ inversion HmQ ].
  - (* unit *)
    apply ad_refine_syn_f__unit.
  - (* var (rigid) *)
    apply ad_refine_syn_f__var; auto.
  - (* arrow *)
    inversion HmQ; subst.
    simpl in HFQ.
    apply ad_refine_syn_f__arrow;
      [ apply IHad_pat_consis1 | apply IHad_pat_consis2 ];
      auto; clear - HFQ; fsetdec.
  - (* hole *)
    rewrite <- (mono_bskl_inh_syn P HmQ).
    apply ad_refine_syn_f__hole; auto.
    rewrite <- ftvar_in_bskl_inh. exact HFQ.
  - (* tophole_drop *)
    apply ad_refine_syn_f__tophole_remove; auto.
  - (* flex_l *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_syn_f__flex_l with (τ := τ); [ exact H | ].
    specialize (IHad_pat_consis Hwf HmQ F Δ HFQ HFdefs).
    rewrite uskl_to_pskl_ptyp in IHad_pat_consis.
    rewrite (mono_inh_eq_syn Hmτ) in IHad_pat_consis.
    exact IHad_pat_consis.
  - (* flex_r *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_syn_f__flex_r with (τ := τ); [ exact H | ].
    apply IHad_pat_consis; auto using mono_ptyp_to_bskl_syn.
    rewrite ftvar_in_bskl_ptyp_syn. eauto.
Qed.

Lemma ad_pat_consis_refine_pskl_f_mono : forall Ψ Θ S Q,
  ad_pat_consis Ψ Θ S Q ->
  a_wf_aenv Θ ->
  mono_bskl Q ->
  forall F Δ,
  AtomSetImpl.inter F (ftvar_in_bskl Q) [=] empty ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     AtomSetImpl.inter F (ftvar_in_ptyp τ) [=] empty) ->
  ad_refine_pskl_f F Θ Δ (uskl_to_pskl S) (bskl_to_pskl Q).
Proof.
  intros Ψ Θ S Q H Hwf; induction H; intros HmQ F Δ HFQ HFdefs; simpl;
    try solve [ inversion HmQ ].
  - (* unit *)
    apply ad_refine_pskl_f__unit.
  - (* var (rigid) *)
    apply ad_refine_pskl_f__var; auto.
  - (* arrow *)
    inversion HmQ; subst.
    simpl in HFQ.
    apply ad_refine_pskl_f__arrow;
      [ apply IHad_pat_consis1 | apply IHad_pat_consis2 ];
      auto; clear - HFQ; fsetdec.
  - (* hole *)
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    apply ad_refine_pskl_f__hole; auto.
    rewrite <- ftvar_in_bskl_inh. exact HFQ.
  - (* tophole_drop *)
    apply ad_refine_pskl_f__tophole_remove; auto.
  - (* flex_l *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_pskl_f__flex_l with (τ := τ); [ exact H | ].
    specialize (IHad_pat_consis Hwf HmQ F Δ HFQ HFdefs).
    rewrite uskl_to_pskl_ptyp in IHad_pat_consis.
    exact IHad_pat_consis.
  - (* flex_r *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply ad_refine_pskl_f__flex_r with (τ := τ); [ exact H | ].
    specialize (IHad_pat_consis Hwf (mono_ptyp_to_bskl_syn Hmτ) F Δ).
    unfold ptyp_to_bskl_syn in IHad_pat_consis at 2.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in IHad_pat_consis.
    apply IHad_pat_consis; auto.
    rewrite ftvar_in_bskl_ptyp_syn. eauto.
Qed.


(* --------------------------------------------------------------------- *)
(*  Θ-side renaming of the fill-hygienic judgments (ForallSyn/UnivGhost1  *)
(*  cases: the tophole_fill-shaped components keep the binder rigid in    *)
(*  the context, so the per-instance transport renames the Θ entry).      *)
(* --------------------------------------------------------------------- *)

Lemma ad_refine_syn_f_rename_ctx : forall F Θ1 α Θ0 Δ Q P Y,
  ad_refine_syn_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ0) Δ Q P ->
  α `notin` dom (Θ1 ++ Θ0) ->
  α `notin` Δ ->
  Y `notin` F ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_refine_syn_f F (Θ1 ++ (Y ~ abind_tvar) ++ Θ0) Δ
    (subst_bskl_in_bskl (bskl_var_f Y) α Q)
    (subst_bskl_in_bskl (bskl_var_f Y) α P).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom HαΔ HYF Hdefs; simpl.
  - (* unit *)
    apply ad_refine_syn_f__unit.
  - (* var *)
    destruct_var_eqs.
    + apply ad_refine_syn_f__var. right.
      unfold a_binds_tvar. left.
      unfold binds. apply in_or_app. right. left. reflexivity.
    + apply ad_refine_syn_f__var.
      destruct H as [HΔ | Htv]; [ left; auto | right ].
      apply (@a_binds_tvar_insert_mid X Θ1 (Y ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - (* arrow *)
    apply ad_refine_syn_f__arrow; auto.
  - (* all *)
    apply ad_refine_syn_f__all with (L := L `union` singleton α).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
  - (* hole *)
    rewrite subst_var_bskl_syn.
    apply ad_refine_syn_f__hole.
    + pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    P (pskl_var_f Y) α) as Hup.
      simpl in Hup. clear - H HYF Hup. fsetdec.
    + apply ad_wf_pskl_rename_tvar; auto.
  - (* tophole_remove *)
    apply ad_refine_syn_f__tophole_remove; auto.
  - (* tophole_fill *)
    apply ad_refine_syn_f__tophole_fill
      with (L := L `union` singleton α).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    replace (bskl_tophole (subst_bskl_in_bskl (bskl_var_f Y) α Q))
      with (subst_bskl_in_bskl (bskl_var_f Y) α (bskl_tophole Q))
      by reflexivity.
    apply (H0 X ltac:(auto) ((X ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* tophole_keep *)
    apply ad_refine_syn_f__tophole_keep;
      auto using guarded_bskl_subst_var.
  - (* flex_l *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ)).
    { rewrite ftvar_in_bskl_ptyp_syn. eauto. }
    destruct_var_eqs.
    apply ad_refine_syn_f__flex_l with (τ := τ);
      [ apply (@binds_insert_mid (abind_flex_mono_def τ) α0
                 Θ1 (Y ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f Y) α Hfr).
    auto.
  - (* flex_r *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ)).
    { rewrite ftvar_in_bskl_ptyp_syn. eauto. }
    destruct_var_eqs.
    apply ad_refine_syn_f__flex_r with (τ := τ);
      [ apply (@binds_insert_mid (abind_flex_mono_def τ) α0
                 Θ1 (Y ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f Y) α Hfr).
    auto.
Qed.

Lemma ad_refine_pskl_f_rename_ctx : forall F Θ1 α Θ0 Δ P Q Y,
  ad_refine_pskl_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ0) Δ P Q ->
  α `notin` dom (Θ1 ++ Θ0) ->
  α `notin` Δ ->
  Y `notin` F ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_refine_pskl_f F (Θ1 ++ (Y ~ abind_tvar) ++ Θ0) Δ
    (subst_pskl_in_pskl (pskl_var_f Y) α P)
    (subst_pskl_in_pskl (pskl_var_f Y) α Q).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hdom HαΔ HYF Hdefs; simpl.
  - (* unit *)
    apply ad_refine_pskl_f__unit.
  - (* var *)
    destruct_var_eqs.
    + apply ad_refine_pskl_f__var. right.
      unfold a_binds_tvar. left.
      unfold binds. apply in_or_app. right. left. reflexivity.
    + apply ad_refine_pskl_f__var.
      destruct H as [HΔ | Htv]; [ left; auto | right ].
      apply (@a_binds_tvar_insert_mid X Θ1 (Y ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - (* arrow *)
    apply ad_refine_pskl_f__arrow; auto.
  - (* all *)
    apply ad_refine_pskl_f__all with (L := L `union` singleton α).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
  - (* hole *)
    apply ad_refine_pskl_f__hole.
    + pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    Q (pskl_var_f Y) α) as Hup.
      simpl in Hup. clear - H HYF Hup. fsetdec.
    + apply ad_wf_pskl_rename_tvar; auto.
  - (* tophole_remove *)
    apply ad_refine_pskl_f__tophole_remove; auto.
  - (* tophole_fill *)
    apply ad_refine_pskl_f__tophole_fill
      with (L := L `union` singleton α).
    intros X HX.
    assert (Hαx : α <> X) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    replace (pskl_tophole (subst_pskl_in_pskl (pskl_var_f Y) α P))
      with (subst_pskl_in_pskl (pskl_var_f Y) α (pskl_tophole P))
      by reflexivity.
    apply (H0 X ltac:(auto) ((X ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* tophole_keep *)
    apply ad_refine_pskl_f__tophole_keep;
      auto using guarded_pskl_subst_var.
  - (* flex_l *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_pskl (ptyp_to_pskl τ)).
    { rewrite ftvar_in_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl_f__flex_l with (τ := τ);
      [ apply (@binds_insert_mid (abind_flex_mono_def τ) α0
                 Θ1 (Y ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f Y) α Hfr).
    auto.
  - (* flex_r *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_pskl (ptyp_to_pskl τ)).
    { rewrite ftvar_in_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl_f__flex_r with (τ := τ);
      [ apply (@binds_insert_mid (abind_flex_mono_def τ) α0
                 Θ1 (Y ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f Y) α Hfr).
    auto.
Qed.


(* ===================================================================== *)
(*  The part-1 problem invariants and their preservation                  *)
(*                                                                        *)
(*  The paper's augmented solution requires that no flexible variables    *)
(*  in Θ depend on variables in Δ1 and Δ2, and the induction needs it     *)
(*  PRESERVED by every unifyvar/assignvar step.  Preservation rests on    *)
(*  the positional discipline of the algorithm: the Δ-variables are the   *)
(*  derivation's own head-openings, so they sit above every non-rigid     *)
(*  entry ([flex_above_free]); Assign-SkipRigid's occurs condition then   *)
(*  witnesses that assignment payloads avoid them, and Assign-SolveM's    *)
(*  used-name freshness keeps the guessed names off them.                 *)
(* ===================================================================== *)

(** No definition mentions a Δ-variable. *)
Definition no_flex_dep (Δ : atoms) (Θ : aenv) : Prop :=
  forall β τ, binds β (abind_flex_mono_def τ) Θ ->
  AtomSetImpl.inter Δ (ftvar_in_ptyp τ) [=] empty.

(** Δ-names sit above (and differ from) every non-rigid entry. *)
Definition flex_above_free (Δ : atoms) (Θ : aenv) : Prop :=
  forall Θ1 β (b : abind) Θ2, Θ = Θ1 ++ (β, b) :: Θ2 ->
  b <> abind_tvar ->
  AtomSetImpl.inter Δ (add β (dom Θ2)) [=] empty.

Lemma no_flex_dep_cong : forall Δ Δ' Θ,
  Δ [=] Δ' -> no_flex_dep Δ Θ -> no_flex_dep Δ' Θ.
Proof.
  intros Δ Δ' Θ Heq H β τ Hb. pose proof (H β τ Hb) as Hh.
  clear - Heq Hh. fsetdec.
Qed.

Lemma faf_cong : forall Δ Δ' Θ,
  Δ [=] Δ' -> flex_above_free Δ Θ -> flex_above_free Δ' Θ.
Proof.
  intros Δ Δ' Θ Heq H Θ1 β b Θ2 Hsp Hne.
  pose proof (H Θ1 β b Θ2 Hsp Hne) as Hh. clear - Heq Hh. fsetdec.
Qed.

Lemma no_flex_dep_tail : forall Δ (c : atom) (b : abind) Θ,
  no_flex_dep Δ ((c ~ b) ++ Θ) ->
  no_flex_dep Δ Θ.
Proof.
  intros * H β τ Hb. apply (H β τ). unfold binds; right; exact Hb.
Qed.

Lemma faf_tail : forall Δ (c : atom) (b : abind) Θ,
  flex_above_free Δ ((c ~ b) ++ Θ) ->
  flex_above_free Δ Θ.
Proof.
  intros * H Θ1 β b0 Θ2 -> Hne.
  apply (H ((c ~ b) ++ Θ1) β b0 Θ2); auto.
Qed.

Lemma faf_head : forall Δ (c : atom) (b : abind) Θ,
  flex_above_free Δ ((c ~ b) ++ Θ) ->
  b <> abind_tvar ->
  AtomSetImpl.inter Δ (add c (dom Θ)) [=] empty.
Proof.
  intros * H Hne. apply (H nil c b Θ); auto.
Qed.

Lemma faf_cons : forall Δ (c : atom) (b : abind) Θ,
  (b <> abind_tvar -> AtomSetImpl.inter Δ (add c (dom Θ)) [=] empty) ->
  flex_above_free Δ Θ ->
  flex_above_free Δ ((c ~ b) ++ Θ).
Proof.
  intros * Hhd Hin Θ1 β b0 Θ2 Heq Hne.
  destruct Θ1 as [ | [c1 b1] Θ1' ]; simpl in Heq; inversion Heq; subst.
  - auto.
  - eapply Hin; eauto.
Qed.

(** Prepending a block of Δ-free entries preserves the invariant. *)
Lemma faf_app : forall Δ (E : aenv) Θ,
  AtomSetImpl.inter Δ (dom E) [=] empty ->
  AtomSetImpl.inter Δ (dom Θ) [=] empty ->
  flex_above_free Δ Θ ->
  flex_above_free Δ (E ++ Θ).
Proof.
  intros Δ E; induction E as [ | [c b] E' IH ]; intros Θ HE HΘ Hin;
    simpl in *; auto.
  apply faf_cons.
  - intros _. repeat rewrite dom_app in *. clear - HE HΘ. fsetdec.
  - apply IH; auto. clear - HE. fsetdec.
Qed.

(** Opening a fresh binder at the head extends both invariants. *)
Lemma faf_open_tvar : forall Δ α Θ,
  flex_above_free Δ Θ ->
  α `notin` dom Θ ->
  flex_above_free (add α Δ) ((α ~ abind_tvar) ++ Θ).
Proof.
  intros * Hin Hfr Θ1 β b Θ2 Heq Hne.
  destruct Θ1 as [ | [c1 b1] Θ1' ]; simpl in Heq; inversion Heq; subst.
  - congruence.
  - assert (Hβ : AtomSetImpl.inter Δ (add β (dom Θ2)) [=] empty)
      by (eapply Hin; eauto).
    rewrite dom_app in Hfr. simpl in Hfr.
    clear - Hβ Hfr. fsetdec.
Qed.

(** Strip a shared rigid head from an identity information-increase.
    The target's shared [(α, tvar)] head forces the a_inc suffix to be
    empty (its entries are flexible, never rigid), so the increase holds
    at the tails. *)
Lemma a_isub_strip_tvar : forall α Θ0 Θ1,
  ((α ~ abind_tvar) ++ Θ0) ⊴ ((α ~ abind_tvar) ++ Θ1) ->
  Θ0 ⊴ Θ1.
Proof.
  intros α Θ0 Θ1 [[θ [Hid Hinc]] Hdef].
  destruct (a_inc_tvar_inv Hinc) as [Ξ [Θ2 [Heq [Hsuf Hinc']]]].
  destruct Ξ as [ | [γ b] Ξ' ]; simpl in Heq.
  - assert (HΘ : Θ2 = Θ1) by (injection Heq; auto). subst Θ2.
    split.
    + exists θ. auto.
    + intros β τ Hb.
      assert (Hb1 : binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ1))
        by (apply Hdef; unfold binds; right; exact Hb).
      destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[? Heq2] | Hb'];
        [ discriminate | exact Hb' ].
  - inversion Hsuf as [ | ? ? ? Hsuf' Hbind ]; subst.
    inversion Heq; subst. inversion Hbind.
Qed.

(** Strip a shared rigid binder from the problem invariants. *)
Lemma no_flex_dep_strip : forall α Δ Θ,
  no_flex_dep (add α Δ) ((α ~ abind_tvar) ++ Θ) ->
  no_flex_dep Δ Θ.
Proof.
  intros α Δ Θ H β τ Hb.
  assert (Hb1 : binds β (abind_flex_mono_def τ) ((α ~ abind_tvar) ++ Θ))
    by (unfold binds; right; exact Hb).
  pose proof (H β τ Hb1) as Hh. clear - Hh. fsetdec.
Qed.

Lemma faf_strip : forall α Δ Θ,
  flex_above_free (add α Δ) ((α ~ abind_tvar) ++ Θ) ->
  flex_above_free Δ Θ.
Proof.
  intros α Δ Θ H Θ1 β b Θ2 Heq Hne.
  assert (Heq' : (α ~ abind_tvar) ++ Θ
               = ((α ~ abind_tvar) ++ Θ1) ++ (β, b) :: Θ2)
    by (subst; simpl; reflexivity).
  pose proof (H ((α ~ abind_tvar) ++ Θ1) β b Θ2 Heq' Hne) as Hh.
  clear - Hh. fsetdec.
Qed.

(** Definitions in a well-formed context are scoped by it. *)
Lemma a_wf_aenv_def_ftv_dom : forall Θ β τ,
  a_wf_aenv Θ ->
  binds β (abind_flex_mono_def τ) Θ ->
  ftvar_in_ptyp τ [<=] dom Θ.
Proof.
  intros Θ β τ Hwf; induction Hwf; intros Hb;
    try solve
      [ inversion Hb
      | destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate
        | simpl; intros X HX;
          pose proof (IHHwf Hb' X HX); fsetdec ] ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
  - inversion Heq; subst.
    intros X HX. simpl.
    match goal with
    | Hw : a_wf_ptyp _ _ |- _ =>
        pose proof (a_wf_ptyp_ftv_tvarish Hw HX) as Htv
    end.
    destruct Htv as [Hb0 | [Hb0 | [τ1 Hb0]]]; apply binds_In in Hb0;
      fsetdec.
  - simpl. intros X HX.
    pose proof (IHHwf Hb' X HX). fsetdec.
Qed.

Lemma no_flex_dep_open_tvar : forall Δ α Θ,
  a_wf_aenv Θ ->
  no_flex_dep Δ Θ ->
  α `notin` dom Θ ->
  no_flex_dep (add α Δ) ((α ~ abind_tvar) ++ Θ).
Proof.
  intros * Hwf Hnd Hfr β τ Hb.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
    [ discriminate | ].
  assert (Hd : AtomSetImpl.inter Δ (ftvar_in_ptyp τ) [=] empty)
    by (eapply Hnd; eauto).
  assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
    by (eapply a_wf_aenv_def_ftv_dom; eauto).
  clear - Hd Hsc Hfr. fsetdec.
Qed.

(** guess^TY scopes its result by the source and the fresh names. *)
Lemma a_guess_mono_ftv : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  ftvar_in_ptyp τ [<=] (ftvar_in_pskl P `union` dom βs).
Proof.
  intros * H; induction H; simpl; try solve [ fsetdec ].
  - (* arrow *)
    repeat rewrite dom_app. clear - IHa_guess_mono1 IHa_guess_mono2.
    fsetdec.
  - (* forall *)
    pick fresh α for (L `union` ftvar_in_ptyp A `union` ftvar_in_pskl P
                        `union` dom Ξ).
    assert (HL : α `notin` L) by fsetdec.
    specialize (H0 α HL).
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A (ptyp_var_f α))
      as Hlo.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α))
      as Hup.
    simpl in Hup.
    intros X HX.
    assert (HX1 : X `in` ftvar_in_ptyp
                    (open_ptyp_wrt_ptyp A (ptyp_var_f α)))
      by (clear - HX Hlo; fsetdec).
    assert (HX2 : X `in` (ftvar_in_pskl
                    (open_pskl_wrt_pskl P (pskl_var_f α))
                    `union` dom Ξ)) by (clear - HX1 H0; fsetdec).
    assert (Hne : X <> α) by (clear - HX Fr; fsetdec).
    clear - HX2 Hup Hne. fsetdec.
Qed.


Lemma inter_empty_pointwise : forall Δ S,
  (forall X, X `in` Δ -> X `notin` S) ->
  AtomSetImpl.inter Δ S [=] empty.
Proof.
  intros Δ S H X. split; intro HX.
  - assert (H1 := AtomSetImpl.inter_1 HX).
    assert (H2 := AtomSetImpl.inter_2 HX).
    exfalso. apply (H X H1 H2).
  - exfalso. clear - HX. fsetdec.
Qed.

Lemma a_decls_no_def : forall Ξ β τ,
  a_decls Ξ ->
  binds β (abind_flex_mono_def τ) Ξ ->
  False.
Proof.
  intros Ξ β τ H; induction H; intros Hb.
  - inversion Hb.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
    [ inversion H0; subst; discriminate Heq | auto ].
Qed.

(** Preservation of the problem invariants by assignment.  The occurs
    condition of Assign-SkipRigid discharges each Δ-variable as its
    entry is walked; the positional invariant makes every Δ-variable
    walked by the time Assign-SolveM fires; the used-name freshness
    keeps the guessed names off Δ. *)
Lemma a_assign_preserves_inv : forall F Θ0 Ξ α P Θ1 Δ,
  Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
  no_flex_dep Δ (Ξ ++ Θ0) ->
  flex_above_free Δ Θ0 ->
  AtomSetImpl.inter Δ (dom Ξ) [=] empty ->
  Δ [<=] (F `union` dom Θ0 `union` dom Ξ) ->
  (forall X, X `in` Δ -> X `notin` dom Θ0 -> X `notin` ftvar_in_pskl P) ->
  no_flex_dep Δ Θ1 /\
  flex_above_free Δ Θ1 /\
  (forall X, X `in` Δ -> X `in` dom Θ1 -> X `in` (dom Ξ `union` dom Θ0)).
Proof.
  intros * Ha; induction Ha; intros Hnd Hfaf HΔΞ Hcov HP.
  - (* Assign-UnivGhost-Id *)
    split; [ exact Hnd | split; [ exact Hfaf | ] ].
    intros X _ HX. clear - HX. fsetdec.
  - (* Assign-SolveM *)
    assert (Hhd : AtomSetImpl.inter Δ (add α (dom Θ0)) [=] empty)
      by (apply (faf_head Hfaf); discriminate).
    assert (Hft : forall X, X `in` Δ -> X `notin` ftvar_in_pskl P).
    { intros X HXΔ. apply HP; auto. simpl.
      assert (X `notin` add α (dom Θ0)) by (clear - Hhd HXΔ; fsetdec).
      auto. }
    assert (HβΔ : forall X, X `in` Δ -> X `notin` dom βs).
    { intros X HXΔ HXβ.
      assert (HXfr := H3 X HXβ).
      assert (HXcov := Hcov X HXΔ).
      simpl in HXcov. repeat rewrite dom_app in *.
      clear - HXfr HXcov. fsetdec. }
    assert (Hτ : AtomSetImpl.inter Δ (ftvar_in_ptyp τ) [=] empty).
    { apply inter_empty_pointwise. intros X HXΔ HXτ.
      pose proof (a_guess_mono_ftv H0 HXτ) as Hin.
      assert (X `notin` ftvar_in_pskl P) by (apply Hft; auto).
      assert (X `notin` dom βs) by (apply HβΔ; auto).
      clear - Hin H4 H5. fsetdec. }
    assert (Hβsd : a_decls βs) by (eapply a_guess_mono_decls; eauto).
    split; [ | split ].
    + (* no_flex_dep *)
      intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
      { inversion Heq; subst; exact Hτ. }
      apply in_app_or in Hb'. destruct Hb' as [Hbβ | HbΞΘ].
      { exfalso. eapply a_decls_no_def; eauto. }
      apply (Hnd β' τ').
      unfold binds. apply in_app_or in HbΞΘ. apply in_or_app.
      destruct HbΞΘ as [HbΞ | HbΘ]; [ auto | ].
      right. right. exact HbΘ.
    + (* flex_above_free *)
      apply faf_cons.
      { intros _. repeat rewrite dom_app.
        apply inter_empty_pointwise. intros X HXΔ HXin.
        assert (X `notin` add α (dom Θ0)) by (clear - Hhd HXΔ; fsetdec).
        assert (X `notin` dom βs) by auto.
        assert (X `notin` dom Ξ) by (clear - HΔΞ HXΔ; fsetdec).
        clear - HXin H4 H5 H6. fsetdec. }
      apply faf_app.
      { apply inter_empty_pointwise. intros X HXΔ. auto. }
      { rewrite dom_app. apply inter_empty_pointwise.
        intros X HXΔ HXin.
        assert (X `notin` dom Ξ) by (clear - HΔΞ HXΔ; fsetdec).
        assert (X `notin` add α (dom Θ0)) by (clear - Hhd HXΔ; fsetdec).
        clear - HXin H4 H5. fsetdec. }
      apply faf_app.
      { exact HΔΞ. }
      { apply inter_empty_pointwise. intros X HXΔ HXin.
        clear - Hhd HXΔ HXin. fsetdec. }
      eapply faf_tail; eauto.
    + (* dom bookkeeping *)
      intros X HXΔ HXd.
      simpl in HXd. repeat rewrite dom_app in HXd.
      assert (X `notin` dom βs) by auto.
      assert (X `notin` add α (dom Θ0)) by (clear - Hhd HXΔ; fsetdec).
      simpl. clear - HXd H4 H5. fsetdec.
  - (* Assign-Assign *)
    assert (Hhd : AtomSetImpl.inter Δ (add β (dom Θ0)) [=] empty)
      by (apply (faf_head Hfaf); discriminate).
    assert (Hτ0 : AtomSetImpl.inter Δ (ftvar_in_ptyp τ) [=] empty).
    { apply (Hnd β τ). unfold binds.
      apply in_or_app. right. left. reflexivity. }
    destruct IHHa as [IH1 [IH2 IH3]].
    { intros β' τ' Hb. apply (Hnd β' τ').
      apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
               (β ~ abind_flex_mono_def τ) Θ0). exact Hb. }
    { eapply faf_tail; eauto. }
    { exact HΔΞ. }
    { intros X HX. assert (HXc := Hcov X HX).
      simpl in HXc. clear - HXc. fsetdec. }
    { intros X HXΔ HXd.
      assert (HXP : X `notin` ftvar_in_pskl P).
      { apply HP; auto. simpl.
        assert (X `notin` add β (dom Θ0)) by (clear - Hhd HXΔ; fsetdec).
        auto. }
      assert (HXτ : X `notin` ftvar_in_ptyp τ)
        by (clear - Hτ0 HXΔ; fsetdec).
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    P (ptyp_to_pskl τ) β) as Hup.
      pose proof (ftvar_in_ptyp_to_pskl τ) as Hτp.
      intro HXin.
      assert (HXsub : X `in` (ftvar_in_pskl (ptyp_to_pskl τ)
                        `union` remove β (ftvar_in_pskl P)))
        by (clear - HXin Hup; fsetdec).
      clear - HXsub Hτp HXτ HXP. fsetdec. }
    split; [ | split ].
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ inversion Heq; subst; exact Hτ0
        | exact (IH1 β' τ' Hb') ].
    + apply faf_cons; [ | exact IH2 ].
      intros _. apply inter_empty_pointwise.
      intros X HXΔ HXin.
      assert (Hβ : X `notin` add β (dom Θ0))
        by (clear - Hhd HXΔ; fsetdec).
      assert (HΘ1 : X `notin` dom Θ1).
      { intro HXd. specialize (IH3 X HXΔ HXd).
        assert (HXΞ : X `notin` dom Ξ) by (clear - HΔΞ HXΔ; fsetdec).
        clear - IH3 HXΞ Hβ. fsetdec. }
      clear - HXin Hβ HΘ1. fsetdec.
    + intros X HXΔ HXd. simpl in HXd.
      assert (Hnex : X <> β)
        by (intro; subst; clear - Hhd HXΔ; fsetdec).
      assert (HXd1 : X `in` dom Θ1) by (clear - HXd Hnex; fsetdec).
      specialize (IH3 X HXΔ HXd1). simpl.
      clear - IH3. fsetdec.
  - (* Assign-Depend *)
    assert (Hhd : AtomSetImpl.inter Δ (add β (dom Θ0)) [=] empty)
      by (apply (faf_head Hfaf); discriminate).
    destruct IHHa as [IH1 [IH2 IH3]].
    { intros β' τ' Hb. apply (Hnd β' τ').
      apply binds_permute_mid. exact Hb. }
    { eapply faf_tail; eauto. }
    { simpl. apply inter_empty_pointwise. intros X HXΔ HXin.
      assert (HXβ : X `notin` add β (dom Θ0))
        by (clear - Hhd HXΔ; fsetdec).
      assert (HXΞ : X `notin` dom Ξ) by (clear - HΔΞ HXΔ; fsetdec).
      clear - HXin HXβ HXΞ. fsetdec. }
    { intros X HX. assert (HXc := Hcov X HX).
      simpl in *. clear - HXc. fsetdec. }
    { intros X HXΔ HXd. apply HP; auto. simpl.
      assert (X `notin` add β (dom Θ0)) by (clear - Hhd HXΔ; fsetdec).
      auto. }
    split; [ exact IH1 | split; [ exact IH2 | ] ].
    intros X HXΔ HXd.
    specialize (IH3 X HXΔ HXd). simpl in IH3. simpl.
    clear - IH3. fsetdec.
  - (* Assign-Skip *)
    assert (Hhd : AtomSetImpl.inter Δ (add β (dom Θ0)) [=] empty)
      by (apply (faf_head Hfaf); discriminate).
    destruct IHHa as [IH1 [IH2 IH3]].
    { intros β' τ' Hb. apply (Hnd β' τ').
      apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
               (β ~ abind_flex_mono) Θ0). exact Hb. }
    { eapply faf_tail; eauto. }
    { exact HΔΞ. }
    { intros X HX. assert (HXc := Hcov X HX).
      simpl in HXc. clear - HXc. fsetdec. }
    { intros X HXΔ HXd. apply HP; auto. simpl.
      assert (X `notin` add β (dom Θ0)) by (clear - Hhd HXΔ; fsetdec).
      auto. }
    split; [ | split ].
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (IH1 β' τ' Hb') ].
    + apply faf_cons; [ | exact IH2 ].
      intros _. apply inter_empty_pointwise.
      intros X HXΔ HXin.
      assert (Hβ : X `notin` add β (dom Θ0))
        by (clear - Hhd HXΔ; fsetdec).
      assert (HΘ1 : X `notin` dom Θ1).
      { intro HXd. specialize (IH3 X HXΔ HXd).
        assert (HXΞ : X `notin` dom Ξ) by (clear - HΔΞ HXΔ; fsetdec).
        clear - IH3 HXΞ Hβ. fsetdec. }
      clear - HXin Hβ HΘ1. fsetdec.
    + intros X HXΔ HXd. simpl in HXd.
      assert (Hnex : X <> β)
        by (intro; subst; clear - Hhd HXΔ; fsetdec).
      assert (HXd1 : X `in` dom Θ1) by (clear - HXd Hnex; fsetdec).
      specialize (IH3 X HXΔ HXd1). simpl.
      clear - IH3. fsetdec.
  - (* Assign-SkipRigid *)
    destruct IHHa as [IH1 [IH2 IH3]].
    { intros β' τ' Hb. apply (Hnd β' τ').
      apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
               (β ~ abind_tvar) Θ0). exact Hb. }
    { eapply faf_tail; eauto. }
    { exact HΔΞ. }
    { intros X HX. assert (HXc := Hcov X HX).
      simpl in HXc. clear - HXc. fsetdec. }
    { intros X HXΔ HXd.
      destruct (eq_var X β) as [->|Hne]; [ exact H | ].
      apply HP; auto; simpl; auto. }
    split; [ | split ].
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (IH1 β' τ' Hb') ].
    + apply faf_cons; [ intros Hne; congruence | exact IH2 ].
    + intros X HXΔ HXd. simpl in HXd. simpl.
      destruct (eq_var X β) as [->|Hne]; [ fsetdec | ].
      assert (HXd1 : X `in` dom Θ1) by (clear - HXd Hne; fsetdec).
      specialize (IH3 X HXΔ HXd1). clear - IH3. fsetdec.
  - (* Assign-SkipTmVar *)
    assert (Hhd : AtomSetImpl.inter Δ (add x (dom Θ0)) [=] empty)
      by (apply (faf_head Hfaf); discriminate).
    destruct IHHa as [IH1 [IH2 IH3]].
    { intros β' τ' Hb. apply (Hnd β' τ').
      apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
               (x ~ abind_var_typ Q) Θ0). exact Hb. }
    { eapply faf_tail; eauto. }
    { exact HΔΞ. }
    { intros X HX. assert (HXc := Hcov X HX).
      simpl in HXc. clear - HXc. fsetdec. }
    { intros X HXΔ HXd. apply HP; auto. simpl.
      assert (X `notin` add x (dom Θ0)) by (clear - Hhd HXΔ; fsetdec).
      auto. }
    split; [ | split ].
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (IH1 β' τ' Hb') ].
    + apply faf_cons; [ | exact IH2 ].
      intros _. apply inter_empty_pointwise.
      intros X HXΔ HXin.
      assert (Hx : X `notin` add x (dom Θ0))
        by (clear - Hhd HXΔ; fsetdec).
      assert (HΘ1 : X `notin` dom Θ1).
      { intro HXd. specialize (IH3 X HXΔ HXd).
        assert (HXΞ : X `notin` dom Ξ) by (clear - HΔΞ HXΔ; fsetdec).
        clear - IH3 HXΞ Hx. fsetdec. }
      clear - HXin Hx HΘ1. fsetdec.
    + intros X HXΔ HXd. simpl in HXd.
      assert (Hnex : X <> x)
        by (intro; subst; clear - Hhd HXΔ; fsetdec).
      assert (HXd1 : X `in` dom Θ1) by (clear - HXd Hnex; fsetdec).
      specialize (IH3 X HXΔ HXd1). simpl.
      clear - IH3. fsetdec.
  - (* Assign-SkipTmVar (skl) *)
    assert (Hhd : AtomSetImpl.inter Δ (add x (dom Θ0)) [=] empty)
      by (apply (faf_head Hfaf); discriminate).
    destruct IHHa as [IH1 [IH2 IH3]].
    { intros β' τ' Hb. apply (Hnd β' τ').
      apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
               (x ~ abind_var_skl Q) Θ0). exact Hb. }
    { eapply faf_tail; eauto. }
    { exact HΔΞ. }
    { intros X HX. assert (HXc := Hcov X HX).
      simpl in HXc. clear - HXc. fsetdec. }
    { intros X HXΔ HXd. apply HP; auto. simpl.
      assert (X `notin` add x (dom Θ0)) by (clear - Hhd HXΔ; fsetdec).
      auto. }
    split; [ | split ].
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (IH1 β' τ' Hb') ].
    + apply faf_cons; [ | exact IH2 ].
      intros _. apply inter_empty_pointwise.
      intros X HXΔ HXin.
      assert (Hx : X `notin` add x (dom Θ0))
        by (clear - Hhd HXΔ; fsetdec).
      assert (HΘ1 : X `notin` dom Θ1).
      { intro HXd. specialize (IH3 X HXΔ HXd).
        assert (HXΞ : X `notin` dom Ξ) by (clear - HΔΞ HXΔ; fsetdec).
        clear - IH3 HXΞ Hx. fsetdec. }
      clear - HXin Hx HΘ1. fsetdec.
    + intros X HXΔ HXd. simpl in HXd.
      assert (Hnex : X <> x)
        by (intro; subst; clear - Hhd HXΔ; fsetdec).
      assert (HXd1 : X `in` dom Θ1) by (clear - HXd Hnex; fsetdec).
      specialize (IH3 X HXΔ HXd1). simpl.
      clear - IH3. fsetdec.
Qed.


(** Unification preserves the domain (no names are created). *)
Lemma a_unify_dom : forall Θ0 A B Θ1,
  Θ0 ⊲ A ≈ᵘ B ⊣ Θ1 ->
  dom Θ1 [=] dom Θ0.
Proof.
  intros * H; induction H; simpl; try fsetdec.
Qed.

(** Preservation of the problem invariants by variable unification:
    the only new definitions are the (hatted, Δ-free) subjects. *)
Lemma a_unify_preserves_inv : forall Θ0 A B Θ1 Δ,
  Θ0 ⊲ A ≈ᵘ B ⊣ Θ1 ->
  no_flex_dep Δ Θ0 ->
  flex_above_free Δ Θ0 ->
  (forall X, X `in` Δ ->
     X `notin` (ftvar_in_ptyp A `union` ftvar_in_ptyp B)) ->
  no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1.
Proof.
  intros * Hu; induction Hu; intros Hnd Hfaf Hsubj.
  - (* Flex-Flex-Id *)
    auto.
  - (* Flex-Flex-L *)
    split.
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
      * inversion Heq; subst. simpl.
        apply inter_empty_pointwise. intros X HXΔ.
        assert (HX := Hsubj X HXΔ). simpl in HX.
        clear - HX. fsetdec.
      * apply (Hnd β' τ'). unfold binds; right; exact Hb'.
    + apply faf_cons; [ | eapply faf_tail; eauto ].
      intros _. apply (faf_head Hfaf). discriminate.
  - (* Flex-Flex-R *)
    split.
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
      * inversion Heq; subst. simpl.
        apply inter_empty_pointwise. intros X HXΔ.
        assert (HX := Hsubj X HXΔ). simpl in HX.
        clear - HX. fsetdec.
      * apply (Hnd β' τ'). unfold binds; right; exact Hb'.
    + apply faf_cons; [ | eapply faf_tail; eauto ].
      intros _. apply (faf_head Hfaf). discriminate.
  - (* Flex-Flex-Assign *)
    assert (Hτ : AtomSetImpl.inter Δ (ftvar_in_ptyp τ) [=] empty)
      by (apply (Hnd γ τ); unfold binds; left; reflexivity).
    destruct IHHu as [IH1 IH2].
    { eapply no_flex_dep_tail; eauto. }
    { eapply faf_tail; eauto. }
    { intros X HXΔ.
      assert (HX := Hsubj X HXΔ).
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper A τ γ) as HupA.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper B τ γ) as HupB.
      assert (HXτ : X `notin` ftvar_in_ptyp τ)
        by (clear - Hτ HXΔ; fsetdec).
      clear - HX HupA HupB HXτ. fsetdec. }
    assert (Hdom : dom Θ1 [=] dom Θ0) by (eapply a_unify_dom; eauto).
    split.
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ inversion Heq; subst; exact Hτ
        | exact (IH1 β' τ' Hb') ].
    + apply faf_cons; [ | exact IH2 ].
      intros _.
      assert (Hhd : AtomSetImpl.inter Δ (add γ (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      clear - Hhd Hdom. fsetdec.
  - (* Flex-Flex-Skip *)
    destruct IHHu as [IH1 IH2].
    { eapply no_flex_dep_tail; eauto. }
    { eapply faf_tail; eauto. }
    { exact Hsubj. }
    assert (Hdom : dom Θ1 [=] dom Θ0) by (eapply a_unify_dom; eauto).
    split.
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (IH1 β' τ' Hb') ].
    + apply faf_cons; [ | exact IH2 ].
      intros _.
      assert (Hhd : AtomSetImpl.inter Δ (add γ (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      clear - Hhd Hdom. fsetdec.
  - (* Flex-Flex-Skip' *)
    destruct IHHu as [IH1 IH2].
    { eapply no_flex_dep_tail; eauto. }
    { eapply faf_tail; eauto. }
    { exact Hsubj. }
    assert (Hdom : dom Θ1 [=] dom Θ0) by (eapply a_unify_dom; eauto).
    split.
    + intros β' τ' Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ | exact (IH1 β' τ' Hb') ].
      subst.
      destruct H as [H2 | [[Q H2] | [Q H2]]]; discriminate H2.
    + apply faf_cons; [ | exact IH2 ].
      intros Hne.
      assert (Hhd : AtomSetImpl.inter Δ (add c (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); exact Hne).
      clear - Hhd Hdom. fsetdec.
Qed.


(* ===================================================================== *)
(*  Helpers for the main induction                                        *)
(* ===================================================================== *)

(** Erasure commutes with closing a free variable. *)
Lemma bskl_to_pskl_close_rec : forall Q α k,
  bskl_to_pskl (close_bskl_wrt_bskl_rec k α Q)
  = close_pskl_wrt_pskl_rec k α (bskl_to_pskl Q).
Proof.
  induction Q; intros; simpl; f_equal; auto;
    repeat match goal with
    | |- context [ if ?t then _ else _ ] => destruct t
    | |- context [ lt_ge_dec ?a ?b ] => destruct (lt_ge_dec a b)
    end; reflexivity.
Qed.

Lemma bskl_to_pskl_close : forall Q α,
  bskl_to_pskl (close_bskl_wrt_bskl α Q)
  = close_pskl_wrt_pskl α (bskl_to_pskl Q).
Proof. intros; apply bskl_to_pskl_close_rec. Qed.

(** The subject of an assignment is bound (as a flexible or defined
    variable) in the output context. *)
Lemma a_assign_subject_binds : forall F Θ0 Ξ α P Θ1,
  Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
  a_binds_tvar α Θ1.
Proof.
  intros * H; induction H;
    try solve
      [ right; left; unfold binds; left; reflexivity
      | right; right; exists τ; unfold binds; left; reflexivity
      | exact IHa_assign
      | destruct IHa_assign as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        unfold binds; right; auto ].
Qed.

(** Moving a variable from Δ into the context as a rigid (the skeleton
    well-formedness reassociation used to open ∀-binders). *)
Lemma ad_wf_pskl_reassoc : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall α,
  ((α ~ abind_tvar) ++ Θ) ⨟ (remove α Δ) ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H; induction H; intros α0; simpl.
  - apply ad_wf_pskl__unit.
  - apply ad_wf_pskl__var.
    destruct H as [HΔ | Htv].
    + destruct (X == α0) as [->|Hne].
      * right. left. unfold binds; left; reflexivity.
      * left. fsetdec.
    + right. apply (@a_binds_tvar_weaken_cons X (α0 ~ abind_tvar) Θ). exact Htv.
  - apply ad_wf_pskl__arrow; [ apply (IHad_wf_pskl1 α0) | apply (IHad_wf_pskl2 α0) ].
  - apply ad_wf_pskl__all with (L := L `union` singleton α0).
    intros X HX.
    assert (HXL : X `notin` L) by fsetdec.
    eapply ad_wf_pskl_delta_mono; [ apply (H0 X HXL α0) | ].
    fsetdec.
  - apply ad_wf_pskl__hole.
  - apply ad_wf_pskl__tophole; auto.
    eapply ad_wf_pskl_delta_mono; [ apply (IHad_wf_pskl α0) | ].
    fsetdec.
Qed.

(** Rigid membership of the two auxiliary contexts extends when a fresh
    binder is opened. *)
Lemma delta_rigids_open : forall Δ Θ α,
  (forall X, X `in` Δ -> a_binds_tvar X Θ) ->
  (forall X, X `in` (add α Δ) -> a_binds_tvar X ((α ~ abind_tvar) ++ Θ)).
Proof.
  intros * H X HX.
  destruct (X == α) as [->|Hne].
  - left. unfold binds; left; reflexivity.
  - apply (@a_binds_tvar_weaken_cons X (α ~ abind_tvar) Θ).
    apply H. fsetdec.
Qed.


(** F-monotonicity: a proof forbidding MORE names in ghost fills is a
    proof forbidding fewer (fills avoiding the larger set avoid the
    smaller). *)
Lemma ad_refine_syn_f_fmono : forall F F' Θ Δ Q P,
  F [<=] F' ->
  ad_refine_syn_f F' Θ Δ Q P ->
  ad_refine_syn_f F Θ Δ Q P.
Proof.
  intros F F' Θ Δ Q P Hsub H; revert F Hsub; induction H; intros F Hsub;
    eauto using ad_refine_syn_f.
  - apply ad_refine_syn_f__hole; auto. clear - H Hsub. fsetdec.
Qed.

Lemma ad_refine_pskl_f_fmono : forall F F' Θ Δ P Q,
  F [<=] F' ->
  ad_refine_pskl_f F' Θ Δ P Q ->
  ad_refine_pskl_f F Θ Δ P Q.
Proof.
  intros F F' Θ Δ P Q Hsub H; revert F Hsub; induction H; intros F Hsub;
    eauto using ad_refine_pskl_f.
  - apply ad_refine_pskl_f__hole; auto. clear - H Hsub. fsetdec.
Qed.

(** [a_wf_ptyp] transports along [⊴] (only positive tvar-ish lookups). *)
Lemma a_wf_ptyp_isub : forall Θ A,
  a_wf_ptyp Θ A ->
  forall Θ', Θ ⊴ Θ' ->
  a_wf_ptyp Θ' A.
Proof.
  intros Θ A H; induction H; intros Θ' Hle; eauto using a_wf_ptyp.
  - apply a_wf_ptyp__var. eapply a_isub_binds_tvarish; eauto.
  - apply a_wf_ptyp__all with (L := L `union` dom Θ'). intros X HX.
    apply H0; auto. apply a_isub_cons_tvar; auto.
Qed.


(** Removing a declaration-only prefix preserves well-formedness. *)
Lemma a_wf_aenv_strip_prefix : forall Ξ Θ,
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ) ->
  a_wf_aenv Θ.
Proof.
  induction Ξ as [ | [γ b] Ξ' IH ]; intros Θ Hdecl Hwf; simpl in *.
  - exact Hwf.
  - inversion Hdecl; subst; inversion Hwf; subst; eauto.
Qed.

(** Algorithmic skeleton well-formedness transports along [⊴]. *)
Lemma a_wf_pskl_isub : forall Θ P,
  a_wf_pskl Θ P ->
  forall Θ', Θ ⊴ Θ' ->
  a_wf_pskl Θ' P.
Proof.
  intros Θ P H; induction H; intros Θ' Hle; eauto using a_wf_pskl.
  - apply a_wf_pskl__var. eapply a_isub_binds_tvarish; eauto.
  - apply a_wf_pskl__all with (L := L `union` dom Θ'). intros X HX.
    apply H0; auto. apply a_isub_cons_tvar; auto.
Qed.

(** A monotype all of whose free variables are tvar-ish is well-formed. *)
Lemma mono_ptyp_wf : forall Θ τ,
  mono_ptyp τ ->
  (forall X, X `in` ftvar_in_ptyp τ -> a_binds_tvar X Θ) ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ τ H; induction H; intros Hvis; simpl in *.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply Hvis. fsetdec.
  - apply a_wf_ptyp__arrow;
      [ apply IHmono_ptyp1 | apply IHmono_ptyp2 ];
      intros X HX; apply Hvis; fsetdec.
Qed.

(** Context well-formedness gives uniqueness of the domain. *)
Lemma a_wf_aenv_uniq : forall Θ,
  a_wf_aenv Θ -> uniq Θ.
Proof.
  intros Θ H; induction H; solve_uniq.
Qed.

(** Every binding produced by guess^TY is a plain flexible variable. *)
Lemma a_guess_mono_flex_binds : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  forall γ b, binds γ b βs -> b = abind_flex_mono.
Proof.
  intros * H; induction H; intros γ b Hb; simpl in *;
    try solve [ inversion Hb ].
  - (* hole *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ inversion Heq; auto | inversion Hb' ].
  - (* tophole *)
    eauto.
  - (* arrow *)
    unfold binds in Hb. apply in_app_or in Hb.
    destruct Hb as [Hb | Hb];
      [ eapply IHa_guess_mono1 | eapply IHa_guess_mono2 ];
      unfold binds; eauto.
  - (* forall *)
    pick fresh α for L.
    eapply H0; eauto.
Qed.

(** Prepending a fresh, uniform flexible-variable block preserves
    context well-formedness. *)
Lemma a_wf_aenv_prepend_flex : forall E Θ,
  (forall γ b, binds γ b E -> b = abind_flex_mono) ->
  uniq E ->
  (forall γ, γ `in` dom E -> γ `notin` dom Θ) ->
  a_wf_aenv Θ ->
  a_wf_aenv (E ++ Θ).
Proof.
  induction E as [ | [γ b] E' IH ]; intros Θ Hall Huniq Hfresh Hwf; simpl.
  - exact Hwf.
  - assert (Hb : b = abind_flex_mono)
      by (apply (Hall γ); unfold binds; simpl; left; reflexivity).
    subst.
    assert (HuE : uniq E' /\ γ `notin` dom E')
      by (inversion Huniq; subst; auto).
    destruct HuE as [HuE Hγ'].
    apply a_wf_aenv__flex.
    + rewrite dom_app.
      assert (Hγd : γ `notin` dom Θ) by (apply Hfresh; simpl; fsetdec).
      clear - Hγ' Hγd. fsetdec.
    + apply IH; auto.
      * intros γ' b' Hb'. apply (Hall γ'); unfold binds; simpl; right; auto.
      * intros γ' Hγ'2. apply Hfresh. simpl. fsetdec.
Qed.

(** Every variable in an assignment's output is either already present
    or freshly generated (hence outside the used-name set [F]). *)
Lemma a_assign_new_avoids_F : forall F Θ0 Ξ α P Θ1,
  Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
  forall γ, γ `in` dom Θ1 ->
  γ `in` dom (Ξ ++ Θ0) \/ γ `notin` F.
Proof.
  intros * H; induction H; intros γ Hγ;
    repeat rewrite dom_app in *; simpl in *.
  - (* UnivGhost-Id *) left. fsetdec.
  - (* SolveM *)
    destruct (AtomSetImpl.union_1 Hγ) as [Hα | Hrest];
      [ left; fsetdec | ].
    destruct (AtomSetImpl.union_1 Hrest) as [Hβs | Hqt];
      [ | left; fsetdec ].
    right. pose proof (H3 γ Hβs) as Hh. clear - Hh. fsetdec.
  - (* Assign *)
    destruct (AtomSetImpl.union_1 Hγ) as [Hβ | Hrest].
    + left. fsetdec.
    + destruct (IHa_assign γ Hrest) as [Hin | Hout];
        [ left; repeat rewrite dom_app in *; fsetdec
        | right; clear - Hout; fsetdec ].
  - (* Depend *)
    destruct (IHa_assign γ Hγ) as [Hin | Hout];
      [ left; repeat rewrite dom_app in *; simpl in *; fsetdec
      | right; auto ].
  - (* Skip *)
    destruct (AtomSetImpl.union_1 Hγ) as [Hβ | Hrest].
    + left. fsetdec.
    + destruct (IHa_assign γ Hrest) as [Hin | Hout];
        [ left; repeat rewrite dom_app in *; fsetdec
        | right; clear - Hout; fsetdec ].
  - (* SkipRigid *)
    destruct (AtomSetImpl.union_1 Hγ) as [Hβ | Hrest].
    + left. fsetdec.
    + destruct (IHa_assign γ Hrest) as [Hin | Hout];
        [ left; repeat rewrite dom_app in *; fsetdec | right; auto ].
  - (* SkipTmVar *)
    destruct (AtomSetImpl.union_1 Hγ) as [Hx | Hrest].
    + left. fsetdec.
    + destruct (IHa_assign γ Hrest) as [Hin | Hout];
        [ left; repeat rewrite dom_app in *; fsetdec | right; auto ].
  - (* SkipTmVar skl *)
    destruct (AtomSetImpl.union_1 Hγ) as [Hx | Hrest].
    + left. fsetdec.
    + destruct (IHa_assign γ Hrest) as [Hin | Hout];
        [ left; repeat rewrite dom_app in *; fsetdec | right; auto ].
Qed.

(** Clean inversions of context well-formedness. *)
Lemma a_wf_aenv_flex_inv : forall α Θ,
  a_wf_aenv ((α ~ abind_flex_mono) ++ Θ) ->
  α `notin` dom Θ /\ a_wf_aenv Θ.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_aenv_flex_def_inv : forall α τ Θ,
  a_wf_aenv ((α ~ abind_flex_mono_def τ) ++ Θ) ->
  α `notin` dom Θ /\ a_wf_ptyp Θ τ /\ mono_ptyp τ /\ a_wf_aenv Θ.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_aenv_tvar_inv : forall α Θ,
  a_wf_aenv ((α ~ abind_tvar) ++ Θ) ->
  α `notin` dom Θ /\ a_wf_aenv Θ.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_aenv_var_typ_inv : forall x Q Θ,
  a_wf_aenv ((x ~ abind_var_typ Q) ++ Θ) ->
  x `notin` dom Θ /\ a_wf_ptyp Θ Q /\ a_wf_aenv Θ.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_aenv_var_skl_inv : forall x Q Θ,
  a_wf_aenv ((x ~ abind_var_skl Q) ++ Θ) ->
  x `notin` dom Θ /\ a_wf_pskl Θ Q /\ a_wf_aenv Θ.
Proof. intros * H; inversion H; subst; auto. Qed.

(** [a_unify] preserves context well-formedness (the only mutation is
    turning a flexible variable into a definition by a hatted, hence
    well-formed and monotype, payload). *)
Lemma a_unify_preserves_wf : forall Θ0 A B Θ1,
  Θ0 ⊲ A ≈ᵘ B ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  mono_ptyp A ->
  mono_ptyp B ->
  a_wf_aenv Θ1.
Proof.
  intros * Hu; induction Hu; intros Hwf HmA HmB.
  - (* Flex-Flex-Id *) exact Hwf.
  - (* Flex-Flex-L : α̂ := β̂ *)
    apply a_wf_aenv_flex_inv in Hwf. destruct Hwf as [Hfr Hwf0].
    apply a_wf_aenv__flex_def; auto.
    apply a_wf_ptyp__var.
    destruct H0 as [Hb | [τ Hb]];
      [ right; left | right; right; exists τ ]; auto.
  - (* Flex-Flex-R : β̂ := α̂ *)
    apply a_wf_aenv_flex_inv in Hwf. destruct Hwf as [Hfr Hwf0].
    apply a_wf_aenv__flex_def; auto.
    apply a_wf_ptyp__var.
    destruct H0 as [Hb | [τ Hb]];
      [ right; left | right; right; exists τ ]; auto.
  - (* Flex-Flex-Assign *)
    apply a_wf_aenv_flex_def_inv in Hwf.
    destruct Hwf as [Hfr [Hwfτ [Hmτ Hwf0]]].
    assert (Hdom : dom Θ1 [=] dom Θ0) by (eapply a_unify_dom; eauto).
    assert (Hle : Θ0 ⊴ Θ1)
      by (destruct (a_unify_sound Hu Hwf0 (@mono_ptyp_subst A τ γ HmA Hmτ)
                      (@mono_ptyp_subst B τ γ HmB Hmτ)) as [Hi _]; exact Hi).
    apply a_wf_aenv__flex_def; auto.
    + rewrite Hdom; auto.
    + eapply a_wf_ptyp_isub; eauto.
    + apply IHHu; auto using mono_ptyp_subst.
  - (* Flex-Flex-Skip *)
    apply a_wf_aenv_flex_inv in Hwf. destruct Hwf as [Hfr Hwf0].
    assert (Hdom : dom Θ1 [=] dom Θ0) by (eapply a_unify_dom; eauto).
    apply a_wf_aenv__flex; auto.
    rewrite Hdom; auto.
  - (* Flex-Flex-Skip' *)
    assert (Hdom : dom Θ1 [=] dom Θ0) by (eapply a_unify_dom; eauto).
    destruct H as [-> | [[Q ->] | [Q ->]]].
    + apply a_wf_aenv_tvar_inv in Hwf. destruct Hwf as [Hfr Hwf0].
      apply a_wf_aenv__tvar; auto. rewrite Hdom; auto.
    + apply a_wf_aenv_var_typ_inv in Hwf.
      destruct Hwf as [Hfr [Hwfp Hwf0]].
      assert (Hle : Θ0 ⊴ Θ1)
        by (destruct (a_unify_sound Hu Hwf0 HmA HmB) as [Hi _]; exact Hi).
      apply a_wf_aenv__var_typ; auto.
      * rewrite Hdom; auto.
      * eapply a_wf_ptyp_isub; eauto.
    + apply a_wf_aenv_var_skl_inv in Hwf.
      destruct Hwf as [Hfr [Hwfp Hwf0]].
      assert (Hle : Θ0 ⊴ Θ1)
        by (destruct (a_unify_sound Hu Hwf0 HmA HmB) as [Hi _]; exact Hi).
      apply a_wf_aenv__var; auto.
      * rewrite Hdom; auto.
      * eapply a_wf_pskl_isub; eauto.
Qed.

(** Contrapositive of [a_assign_new_avoids_F]: a name in [F] and fresh
    from the input stays fresh in the output. *)
Corollary a_assign_notin : forall F Θ0 Ξ α P Θ1,
  Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
  forall β, β `in` F -> β `notin` dom (Ξ ++ Θ0) -> β `notin` dom Θ1.
Proof.
  intros * Ha β HβF Hβd Hin.
  destruct (a_assign_new_avoids_F Ha Hin) as [Hd | HF]; auto.
Qed.

(** Free variables of a well-formed skeleton are tvar-ish or in Δ. *)
Lemma ad_wf_pskl_ftv_tvarish : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall X, X `in` ftvar_in_pskl P -> X `in` Δ \/ a_binds_tvar X Θ.
Proof.
  intros Θ Δ P H; induction H; intros Y HY; simpl in HY.
  - fsetdec.
  - assert (Y = X) by fsetdec. subst. auto.
  - destruct (AtomSetImpl.union_1 HY); auto.
  - pick fresh Z for (L `union` ftvar_in_pskl P `union` Δ `union` {{Y}}
                        `union` dom Θ).
    assert (HZL : Z `notin` L) by fsetdec.
    assert (HY' : Y `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f Z))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f Z)).
      fsetdec. }
    destruct (H0 Z HZL Y HY') as [HΔ | Htv].
    + left. assert (Y <> Z) by fsetdec. clear - HΔ H1. fsetdec.
    + auto.
  - fsetdec.
  - destruct (IHad_wf_pskl Y HY) as [HΔ | Htv]; [ fsetdec | auto ].
Qed.

(** [a_assign] preserves context well-formedness.  Mirrors
    [a_assign_sound]'s visibility threading; the output is the input
    with a fresh flexible-variable block and one monotype definition
    prepended (SolveM), or an entry re-attached (skip cases). *)
Lemma a_assign_preserves_wf : forall F Θ0 Ξ α P Θ1,
  Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (forall X, X `in` ftvar_in_pskl P -> a_binds_tvar X (Ξ ++ Θ0)) ->
  a_wf_aenv Θ1.
Proof.
  intros * Ha; induction Ha; intros Hdecl Hwf Hvis.
  - (* Assign-UnivGhost-Id *)
    simpl in Hwf. exact Hwf.
  - (* Assign-SolveM *)
    assert (Huniq : uniq (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hαd : α `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (Hβsfr : forall γ, γ `in` dom βs -> γ `notin` dom (Ξ ++ Θ0)).
    { intros γ Hγ. pose proof (H3 γ Hγ) as Hh.
      repeat rewrite dom_app in *. clear - Hh. fsetdec. }
    assert (Hβswf : a_wf_aenv (βs ++ Ξ ++ Θ0)).
    { apply a_wf_aenv_prepend_flex;
        [ intros γ b Hb; eapply a_guess_mono_flex_binds; eauto
        | exact H2
        | intros γ Hγ;
          (assert (Hf : γ `notin` dom (Ξ ++ Θ0)) by (apply Hβsfr; auto));
          repeat rewrite dom_app in *; clear - Hf; fsetdec
        | exact HwfΞΘ ]. }
    assert (Hαβs : α `notin` dom βs).
    { intro Hin. pose proof (H3 α Hin) as Hh. clear - Hh. fsetdec. }
    apply a_wf_aenv__flex_def; [ | | exact H1 | exact Hβswf ].
    { repeat rewrite dom_app in *. clear - Hαd Hαβs. fsetdec. }
    apply mono_ptyp_wf; auto.
    intros X HX.
    pose proof (a_guess_mono_ftv H0 HX) as Hin.
      destruct (AtomSetImpl.union_1 Hin) as [HXP | HXβs].
      * assert (HXα : X <> α) by (intro; subst; auto).
        assert (Htv : a_binds_tvar X (Ξ ++ Θ0)).
        { eapply a_binds_tvar_strip_mid with
            (c := α) (b := abind_flex_mono);
            [ apply Hvis; auto
            | intro Hc; inversion Hc; congruence
            | intro Hc; inversion Hc; congruence
            | intros τ0 Hc; inversion Hc; congruence ]. }
        destruct Htv as [Hb | [Hb | [τ0 Hb]]];
          [ left | right; left | right; right; exists τ0 ];
          unfold binds; apply in_or_app; right; exact Hb.
      * right; left. unfold binds; apply in_or_app; left.
        apply binds_In_inv in HXβs. destruct HXβs as [b Hb].
        assert (Hbf : b = abind_flex_mono)
          by (eapply a_guess_mono_flex_binds; eauto). subst. exact Hb.
  - (* Assign-Assign *)
    assert (Hτ : a_wf_ptyp Θ0 τ /\ mono_ptyp τ)
      by (eapply a_wf_aenv_mid_def_inv; eauto).
    destruct Hτ as [Hτwf Hτm].
    assert (Huniq : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hvis' : forall X, X `in` ftvar_in_pskl
                      (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ->
                    a_binds_tvar X (Ξ ++ Θ0)).
    { intros X HX.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    P (ptyp_to_pskl τ) β) as Hup.
      assert (HX' : X `in` (ftvar_in_pskl (ptyp_to_pskl τ)
                            `union` remove β (ftvar_in_pskl P)))
        by (clear - HX Hup; fsetdec).
      destruct (AtomSetImpl.union_1 HX') as [HXτ | HXP].
      - rewrite ftvar_in_ptyp_to_pskl in HXτ.
        assert (Htv : a_binds_tvar X Θ0)
          by (eapply a_wf_ptyp_ftv_tvarish; eauto).
        destruct Htv as [Hb | [Hb | [τ0 Hb]]];
          [ left | right; left | right; right; exists τ0 ];
          unfold binds; apply in_or_app; right; exact Hb.
      - assert (HXβ : X <> β) by (clear - HXP; fsetdec).
        assert (HXP' : X `in` ftvar_in_pskl P) by (clear - HXP; fsetdec).
        eapply a_binds_tvar_strip_mid with
          (c := β) (b := abind_flex_mono_def τ);
          [ apply Hvis; auto
          | intro Hc; inversion Hc; congruence
          | intro Hc; inversion Hc; congruence
          | intros τ0 Hc; inversion Hc; congruence ]. }
    assert (Hwf1 : a_wf_aenv Θ1) by (apply IHHa; auto).
    assert (Hβ1 : β `notin` dom Θ1)
      by (eapply a_assign_notin; eauto; clear - Hβd; fsetdec).
    assert (Hle : Θ0 ⊴ Θ1)
      by (destruct (a_assign_sound Ha Hdecl HwfΞΘ Hvis') as [Hi _];
          eapply a_isub_strengthen_decls_src; eauto).
    apply a_wf_aenv__flex_def; auto.
    eapply a_wf_ptyp_isub; eauto.
  - (* Assign-Depend *)
    apply IHHa; auto.
    { apply (a_decls__cons β); auto. }
    { eapply a_wf_aenv_move_decl; eauto. }
    { intros X HX.
      apply (a_binds_tvar_permute_mid Ξ (β ~ abind_flex_mono) Θ0); auto. }
  - (* Assign-Skip *)
    assert (Huniq : uniq (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hvis' : forall X, X `in` ftvar_in_pskl P ->
                    a_binds_tvar X (Ξ ++ Θ0)).
    { intros X HX.
      assert (HXβ : X <> β) by (intro; subst; auto).
      eapply a_binds_tvar_strip_mid with (c := β) (b := abind_flex_mono);
        [ apply Hvis; auto
        | intro Hc; inversion Hc; congruence
        | intro Hc; inversion Hc; congruence
        | intros τ0 Hc; inversion Hc; congruence ]. }
    assert (Hwf1 : a_wf_aenv Θ1) by (apply IHHa; auto).
    apply a_wf_aenv__flex; auto.
    eapply a_assign_notin; eauto; clear - Hβd; fsetdec.
  - (* Assign-SkipRigid *)
    assert (Huniq : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hvis' : forall X, X `in` ftvar_in_pskl P ->
                    a_binds_tvar X (Ξ ++ Θ0)).
    { intros X HX.
      assert (HXβ : X <> β) by (intro; subst; auto).
      eapply a_binds_tvar_strip_mid with (c := β) (b := abind_tvar);
        [ apply Hvis; auto
        | intro Hc; inversion Hc; congruence
        | intro Hc; inversion Hc; congruence
        | intros τ0 Hc; inversion Hc; congruence ]. }
    assert (Hwf1 : a_wf_aenv Θ1) by (apply IHHa; auto).
    apply a_wf_aenv__tvar; auto.
    eapply a_assign_notin; eauto; clear - Hβd; fsetdec.
  - (* Assign-SkipTmVar (typ) *)
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_typ Q) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hxwf : a_wf_aenv ((x ~ abind_var_typ Q) ++ Θ0))
      by (eapply a_wf_aenv_strip_prefix; eauto).
    apply a_wf_aenv_var_typ_inv in Hxwf.
    destruct Hxwf as [_ [HQwf _]].
    assert (Hvis' : forall X, X `in` ftvar_in_pskl P ->
                    a_binds_tvar X (Ξ ++ Θ0)).
    { intros X HX.
      eapply a_binds_tvar_strip_mid with (c := x) (b := abind_var_typ Q);
        [ apply Hvis; auto
        | intro Hc; inversion Hc
        | intro Hc; inversion Hc
        | intros τ0 Hc; inversion Hc ]. }
    assert (Hwf1 : a_wf_aenv Θ1) by (apply IHHa; auto).
    assert (Hle : Θ0 ⊴ Θ1)
      by (destruct (a_assign_sound Ha Hdecl HwfΞΘ Hvis') as [Hi _];
          eapply a_isub_strengthen_decls_src; eauto).
    apply a_wf_aenv__var_typ; auto.
    + eapply a_assign_notin; eauto; clear - Hxd; fsetdec.
    + eapply a_wf_ptyp_isub; eauto.
  - (* Assign-SkipTmVar (skl) *)
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_skl Q) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hxwf : a_wf_aenv ((x ~ abind_var_skl Q) ++ Θ0))
      by (eapply a_wf_aenv_strip_prefix; eauto).
    apply a_wf_aenv_var_skl_inv in Hxwf.
    destruct Hxwf as [_ [HQwf _]].
    assert (Hvis' : forall X, X `in` ftvar_in_pskl P ->
                    a_binds_tvar X (Ξ ++ Θ0)).
    { intros X HX.
      eapply a_binds_tvar_strip_mid with (c := x) (b := abind_var_skl Q);
        [ apply Hvis; auto
        | intro Hc; inversion Hc
        | intro Hc; inversion Hc
        | intros τ0 Hc; inversion Hc ]. }
    assert (Hwf1 : a_wf_aenv Θ1) by (apply IHHa; auto).
    assert (Hle : Θ0 ⊴ Θ1)
      by (destruct (a_assign_sound Ha Hdecl HwfΞΘ Hvis') as [Hi _];
          eapply a_isub_strengthen_decls_src; eauto).
    apply a_wf_aenv__var; auto.
    + eapply a_assign_notin; eauto; clear - Hxd; fsetdec.
    + eapply a_wf_pskl_isub; eauto.
Qed.

(** Monotype skeletons are locally closed and guarded. *)
Lemma mono_ptyp_to_pskl_lc : forall τ,
  mono_ptyp τ -> lc_pskl (ptyp_to_pskl τ).
Proof. induction 1; simpl; auto using lc_pskl. Qed.

Lemma mono_ptyp_to_pskl_guarded : forall τ,
  mono_ptyp τ -> guarded_pskl (ptyp_to_pskl τ).
Proof.
  destruct 1 as [ | X | A1 A2 ]; simpl;
    [ apply guarded_pskl__unit | apply guarded_pskl__var
    | apply guarded_pskl__arrow; apply mono_ptyp_to_pskl_lc; auto ].
Qed.

Lemma mono_bskl_lc : forall Q,
  mono_bskl Q -> lc_bskl Q.
Proof. induction 1; auto using lc_bskl. Qed.

Lemma mono_bskl_guarded : forall Q,
  mono_bskl Q -> guarded_bskl Q.
Proof.
  destruct 1 as [ | X | Q1 Q2 ];
    [ apply guarded_bskl__unit | apply guarded_bskl__var
    | apply guarded_bskl__arrow; apply mono_bskl_lc; auto ].
Qed.

(** A non-rigid entry is not among the (rigid) Δ-variables. *)
Lemma faf_flex_notin : forall Δ Θ α b,
  flex_above_free Δ Θ ->
  binds α b Θ ->
  b <> abind_tvar ->
  α `notin` Δ.
Proof.
  intros Δ Θ α b Hfaf Hb Hne.
  apply binds_split in Hb. destruct Hb as [Θ1 [Θ2 Heq]].
  simpl in Heq.
  pose proof (Hfaf _ _ _ _ Heq Hne) as Hh. clear - Hh. fsetdec.
Qed.

(** The subjects of a variable unification are flexible. *)
Lemma a_flex_tvar_weaken_cons : forall α (e : list (atom * abind)) Θ,
  a_flex_tvar Θ α ->
  α `notin` dom e ->
  a_flex_tvar (e ++ Θ) α.
Proof.
  intros α e Θ [Hb | [τ Hb]] Hd;
    [ left | right; exists τ ];
    unfold binds; apply in_or_app; right; exact Hb.
Qed.

Lemma a_unify_subjects_flex : forall Θ0 A B Θ1,
  a_wf_aenv Θ0 ->
  Θ0 ⊲ A ≈ᵘ B ⊣ Θ1 ->
  forall α β, A = ptyp_var_f α -> B = ptyp_var_f β ->
  a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β.
Proof.
  intros Θ0 A B Θ1 Hwf Hu; induction Hu; intros α0 β0 HA HB;
    try (inversion HA; inversion HB; subst).
  - (* flex_id *) split; left; auto.
  - (* flex_l : (α~flex)++Θ0 *)
    split; [ left; unfold binds; left; reflexivity | ].
    apply a_flex_tvar_weaken_cons; [ auto | simpl; fsetdec ].
  - (* flex_r : (β~flex)++Θ0 *)
    split; [ | left; unfold binds; left; reflexivity ].
    apply a_flex_tvar_weaken_cons; [ auto | simpl; fsetdec ].
  - (* flex_assign : (γ~def τ)++Θ0 *)
    apply a_wf_aenv_flex_def_inv in Hwf.
    destruct Hwf as [Hfr [Hwfτ [Hmτ Hwf0]]].
    assert (Hα : a_flex_tvar ((γ ~ abind_flex_mono_def τ) ++ Θ0) α0).
    { destruct (eq_var α0 γ) as [->|HneA].
      - right; exists τ; unfold binds; left; reflexivity.
      - assert (HeqA : subst_ptyp_in_ptyp τ γ (ptyp_var_f α0) = ptyp_var_f α0)
          by (simpl; destruct (eq_var α0 γ); congruence).
        destruct (a_unify_var_inv Hu) as [[α' HA'] [β' HB']].
        rewrite HeqA in HA'. inversion HA'; subst α'.
        destruct (IHHu Hwf0 α0 β') as [Hfα _]; auto.
        apply a_flex_tvar_weaken_cons; [ exact Hfα | simpl; clear - HneA; fsetdec ]. }
    assert (Hβ : a_flex_tvar ((γ ~ abind_flex_mono_def τ) ++ Θ0) β0).
    { destruct (eq_var β0 γ) as [->|HneB].
      - right; exists τ; unfold binds; left; reflexivity.
      - assert (HeqB : subst_ptyp_in_ptyp τ γ (ptyp_var_f β0) = ptyp_var_f β0)
          by (simpl; destruct (eq_var β0 γ); congruence).
        destruct (a_unify_var_inv Hu) as [[α' HA'] [β' HB']].
        rewrite HeqB in HB'. inversion HB'; subst β'.
        destruct (IHHu Hwf0 α' β0) as [_ Hfβ]; auto.
        apply a_flex_tvar_weaken_cons; [ exact Hfβ | simpl; clear - HneB; fsetdec ]. }
    split; auto.
  - (* flex_skip : (γ~flex)++Θ0 *)
    apply a_wf_aenv_flex_inv in Hwf. destruct Hwf as [Hfr Hwf0].
    destruct (IHHu Hwf0 α0 β0) as [Hfα Hfβ]; auto.
    simpl in H.
    assert (Hna : γ <> α0) by (clear - H; fsetdec).
    assert (Hnb : γ <> β0) by (clear - H; fsetdec).
    split; (apply a_flex_tvar_weaken_cons; [ auto | simpl; fsetdec ]).
  - (* skip_other *)
    assert (Hwf0 : a_wf_aenv Θ0 /\ c `notin` dom Θ0).
    { destruct H as [-> | [[Q ->] | [Q ->]]].
      - apply a_wf_aenv_tvar_inv in Hwf; tauto.
      - apply a_wf_aenv_var_typ_inv in Hwf; destruct Hwf as [? [? ?]]; auto.
      - apply a_wf_aenv_var_skl_inv in Hwf; destruct Hwf as [? [? ?]]; auto. }
    destruct Hwf0 as [Hwf0 Hcd].
    destruct (IHHu Hwf0 α0 β0) as [Hfα Hfβ]; auto.
    assert (Hαd : α0 `in` dom Θ0)
      by (destruct Hfα as [Hb | [τ Hb]]; apply binds_In in Hb; auto).
    assert (Hβd : β0 `in` dom Θ0)
      by (destruct Hfβ as [Hb | [τ Hb]]; apply binds_In in Hb; auto).
    split; (apply a_flex_tvar_weaken_cons; [ auto | simpl; fsetdec ]).
Qed.

(** Variable unification is symmetric (the two flex rules swap). *)
Lemma a_unify_sym : forall Θ0 A B Θ1,
  Θ0 ⊲ A ≈ᵘ B ⊣ Θ1 -> Θ0 ⊲ B ≈ᵘ A ⊣ Θ1.
Proof.
  intros Θ0 A B Θ1 H; induction H.
  - apply a_unify__flex_id; auto.
  - apply a_unify__flex_r; auto.
  - apply a_unify__flex_l; auto.
  - apply a_unify__flex_assign; auto.
  - apply a_unify__flex_skip; [ clear - H; fsetdec | assumption ].
  - apply a_unify__skip_other; [ assumption | assumption ].
Qed.

(** [a_flex_tvar] transport under mid-insertion / permutation. *)
Lemma a_flex_tvar_insert_mid : forall α Ξ (e : list (atom * abind)) Θ,
  a_flex_tvar (Ξ ++ Θ) α -> a_flex_tvar (Ξ ++ e ++ Θ) α.
Proof.
  intros * [Hb | [τ Hb]]; [ left | right; exists τ ];
    apply binds_insert_mid; auto.
Qed.

Lemma a_flex_tvar_permute_mid : forall α (e : list (atom * abind)) Ξ Θ,
  a_flex_tvar (e ++ Ξ ++ Θ) α -> a_flex_tvar (Ξ ++ e ++ Θ) α.
Proof.
  intros * H.
  assert (Hb : forall (b : abind), binds α b (e ++ Ξ ++ Θ) ->
                                   binds α b (Ξ ++ e ++ Θ)).
  { intros b Hb0. unfold binds in *.
    apply in_app_or in Hb0. apply in_or_app.
    destruct Hb0 as [Hb0 | Hb0]; [ right; apply in_or_app; auto | ].
    apply in_app_or in Hb0. destruct Hb0 as [Hb0 | Hb0];
      [ auto | right; apply in_or_app; auto ]. }
  destruct H as [H | [τ H]]; [ left | right; exists τ ]; auto.
Qed.

(** The subject of an assignment is flexible in the input context. *)
Lemma a_assign_subject_flex : forall F Θ0 Ξ α P Θ1,
  Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
  a_flex_tvar (Ξ ++ Θ0) α.
Proof.
  intros * H; induction H.
  - (* UnivGhost-Id *)
    left. simpl. unfold binds; left; reflexivity.
  - (* SolveM *)
    left. unfold binds. apply in_or_app. right. left. reflexivity.
  - (* Assign *)
    apply a_flex_tvar_insert_mid; auto.
  - (* Depend *)
    apply a_flex_tvar_permute_mid with (e := (β ~ abind_flex_mono)).
    exact IHa_assign.
  - (* Skip *)
    apply a_flex_tvar_insert_mid; auto.
  - (* SkipRigid *)
    apply a_flex_tvar_insert_mid; auto.
  - (* SkipTmVar (typ) *)
    apply a_flex_tvar_insert_mid; auto.
  - (* SkipTmVar (skl) *)
    apply a_flex_tvar_insert_mid; auto.
Qed.

(** Rigid bindings are preserved exactly along [⊴]. *)
Lemma a_isub_binds_tvar : forall Θ Θ' α,
  Θ ⊴ Θ' -> binds α abind_tvar Θ -> binds α abind_tvar Θ'.
Proof.
  intros Θ Θ' α [[θ [Hid Hinc]] _] Hb.
  eapply a_inc_binds_tvar; eauto.
Qed.

(** A well-formed skeleton is locally closed. *)
Lemma ad_wf_pskl_lc : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P -> lc_pskl P.
Proof.
  intros Θ Δ P H; induction H; eauto using lc_pskl.
Qed.

(** The synthesised painting preserves local closure. *)
Lemma pskl_to_bskl_syn_lc : forall P,
  lc_pskl P -> lc_bskl (pskl_to_bskl_syn P).
Proof.
  intros P H; induction H; simpl;
    try (now eauto using lc_bskl);
    (apply lc_bskl_all_syn; intros X;
     rewrite <- pskl_to_bskl_syn_open; now auto).
Qed.

(** Refinement outputs are locally closed. *)
Lemma ad_refine_pskl_f_lc_r : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q -> lc_pskl Q.
Proof.
  intros F Θ Δ P Q H; induction H;
    try (now eauto using lc_pskl);
    try (now (eapply ad_wf_pskl_lc; eauto));
    (pick fresh X; apply (lc_pskl_all_syn_exists X); auto).
Qed.

Lemma ad_refine_syn_f_lc_r : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P -> lc_bskl P.
Proof.
  intros F Θ Δ Q P H; induction H;
    try (now eauto using lc_bskl);
    try (now (apply pskl_to_bskl_syn_lc; eapply ad_wf_pskl_lc; eauto));
    (pick fresh X; apply (lc_bskl_all_syn_exists X); auto).
Qed.

(** Refinement with a guarded left side yields a guarded right side. *)
Lemma ad_refine_pskl_f_guarded_r : forall F Θ Δ P Q,
  a_wf_aenv Θ ->
  ad_refine_pskl_f F Θ Δ P Q ->
  guarded_pskl P ->
  guarded_pskl Q.
Proof.
  intros F Θ Δ P Q Hwf H; induction H; intros Hg;
    try solve [ inversion Hg ].
  - apply guarded_pskl__unit.
  - apply guarded_pskl__var.
  - apply guarded_pskl__arrow; eapply ad_refine_pskl_f_lc_r; eauto.
  - assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply IHad_refine_pskl_f; auto. apply mono_ptyp_to_pskl_guarded; auto.
  - apply guarded_pskl__var.
Qed.

Lemma ad_refine_syn_f_guarded_r : forall F Θ Δ Q P,
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ Q P ->
  guarded_bskl Q ->
  guarded_bskl P.
Proof.
  intros F Θ Δ Q P Hwf H; induction H; intros Hg;
    try solve [ inversion Hg ].
  - apply guarded_bskl__unit.
  - apply guarded_bskl__var.
  - apply guarded_bskl__arrow; eapply ad_refine_syn_f_lc_r; eauto.
  - assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply IHad_refine_syn_f; auto.
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn; auto.
  - apply guarded_bskl__var.
Qed.

(* ===================================================================== *)
(*  Soundness of consistency, part 1 (thm:sound-consistency)              *)
(* ===================================================================== *)

Lemma a_consis_sound_aux : forall Δ1 Δ2 Θ0 P0 P Q Θ1,
  a_consis Δ1 Δ2 Θ0 P0 P Q Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 ->
  flex_above_free (Δ1 `union` Δ2) Θ0 ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  no_flex_dep (Δ1 `union` Δ2) Θ1 /\ flex_above_free (Δ1 `union` Δ2) Θ1 /\
  (exists Qt, bskl_to_pskl Qt = Q /\
     ad_pat_consis empty Θ1 (pskl_to_uskl P) Qt /\
     ad_refine_syn_f Δ1 Θ1 Δ1 (pskl_to_bskl_inh P0) Qt) /\
  ad_refine_pskl_f Δ2 Θ1 Δ2 P Q.
Proof.
  intros * Hc; induction Hc;
    intros Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
  - (* Ghost *)
    split; [ apply a_isub_refl | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists (pskl_to_bskl_inh P0).
      split; [ apply bskl_to_pskl_pskl_to_bskl_inh | ].
      split.
      * apply ad_pat_consis__hole; [ fsetdec | exact HwfP0 ].
      * apply ad_refine_syn_f_refl_inh.
        eapply ad_wf_pskl_delta_mono; [ exact HwfP0 | fsetdec ].
    + apply ad_refine_pskl_f__hole; [ exact H | exact HwfP0 ].
  - (* Unit *)
    split; [ apply a_isub_refl | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists bskl_unit. split; [ reflexivity | ].
      split; [ apply ad_pat_consis__unit; fsetdec | apply ad_refine_syn_f__unit ].
    + apply ad_refine_pskl_f__unit.
  - (* Rigid *)
    split; [ apply a_isub_refl | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__var; [ fsetdec | left; exact H ].
      * apply ad_refine_syn_f__var. right; left; exact H.
    + apply ad_refine_pskl_f__var. right; left; exact H.
  - (* Arrow *)
    simpl in HwfP0, HwfP.
    inversion HwfP0 as [ | | Θa Δa P0a' P0b' HwfP0a HwfP0b | | | ]; subst.
    inversion HwfP as [ | | Θb Δb P1' P2' HwfP1 HwfP2 | | | ]; subst.
    destruct IHHc1
      as [Hle1 [Hwf1 [Hnfd1 [Hfaf1 [[Qt1 [HeQt1 [Hcons1 Hrs1]]] Hrp1]]]]]; auto.
    destruct IHHc2
      as [Hle2 [Hwf2 [Hnfd2 [Hfaf2 [[Qt2 [HeQt2 [Hcons2 Hrs2]]] Hrp2]]]]]; auto.
    { eapply ad_wf_pskl_isub; eauto. }
    { eapply ad_wf_pskl_isub; eauto. }
    { intros X HX. eapply a_isub_binds_tvar; eauto. }
    split; [ eapply a_isub_trans; eauto | ].
    split; [ exact Hwf2 | ]. split; [ exact Hnfd2 | ]. split; [ exact Hfaf2 | ].
    split.
    + exists (bskl_arrow Qt1 Qt2). split.
      { simpl. rewrite HeQt1, HeQt2. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
          [ eapply ad_pat_consis_isub; eauto | exact Hcons2 | fsetdec ].
      * simpl. apply ad_refine_syn_f__arrow;
          [ eapply ad_refine_syn_f_isub; eauto | exact Hrs2 ].
    + simpl. apply ad_refine_pskl_f__arrow;
        [ eapply ad_refine_pskl_f_isub; eauto | exact Hrp2 ].
  - (* ForallInh : ∀α.P ≈ ∀α.Q against input ∀α.P0 *)
    simpl in HwfP0, HwfP.
    inversion HwfP0 as [ | | | L0 Θa Δa P0a Hbody0 Heqa | | ]; subst.
    inversion HwfP as [ | | | L1 Θb Δb Pa Hbody1 Heqb | | ]; subst.
    pick fresh α for
      (L `union` L0 `union` L1 `union` dom Θ0 `union` dom Θ1
       `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
       `union` Δ1 `union` Δ2).
    assert (HαL : α `notin` L) by auto.
    assert (HwfΘα : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; auto).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                       ⊢ₚₛᵃ (open_pskl_wrt_pskl P0 (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_mono;
        [ apply (ad_wf_pskl_reassoc (Hbody0 α ltac:(auto)) α)
        | clear; fsetdec ]. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                       ⊢ₚₛᵃ (open_pskl_wrt_pskl P (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_mono;
        [ apply (ad_wf_pskl_reassoc (Hbody1 α ltac:(auto)) α)
        | clear; fsetdec ]. }
    assert (Hrigα : forall X, X `in` (add α Δ1 `union` add α Δ2) ->
                    binds X abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros X HX. destruct (X == α) as [->|Hne].
      - unfold binds; left; reflexivity.
      - unfold binds; right. apply Hrig. clear - HX Hne. fsetdec. }
    assert (Hnfdα : no_flex_dep (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ]. }
    assert (Hfafα : flex_above_free (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply faf_open_tvar; auto ]. }
    destruct (H0 α HαL HwfΘα HwfP0α HwfPα Hrigα Hnfdα Hfafα)
      as [Hleα [Hwfα [Hnfdα1 [Hfafα1 [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
    assert (Hwf1 : a_wf_aenv Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Hα1 : α `notin` dom Θ1) by auto.
    assert (Hdefsα : forall β τ, binds β (abind_flex_mono_def τ) Θ1 ->
                     α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      pose proof (@a_wf_aenv_def_ftv_dom Θ1 β τ Hwf1 Hb) as Hsc.
      clear - Hsc Hα1. fsetdec. }
    split; [ eapply a_isub_strip_tvar; eauto | ].
    split; [ exact Hwf1 | ].
    split.
    { apply no_flex_dep_strip with (α := α).
      apply no_flex_dep_cong with (Δ := add α Δ1 `union` add α Δ2);
        [ clear; fsetdec | exact Hnfdα1 ]. }
    split.
    { apply faf_strip with (α := α).
      apply faf_cong with (Δ := add α Δ1 `union` add α Δ2);
        [ clear; fsetdec | exact Hfafα1 ]. }
    split.
    + exists (bskl_all_inh (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; fsetdec ]. }
      split.
      * simpl. apply ad_pat_consis__forall_inh_untagged
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P).
        intros X HX.
        rewrite (subst_bskl_in_uskl_intro α (pskl_to_uskl P) (uskl_var_f X));
          [ | rewrite ftvar_in_uskl_pskl; clear - Fr; fsetdec ].
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f X));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        change ((X ~ abind_tvar) ++ Θ1)
          with (nil ++ (X ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ | exact Hα1 | exact Hdefsα ].
        rewrite <- pskl_to_uskl_open_var. exact Hconsα.
      * change (pskl_to_bskl_inh (pskl_all_syn P0))
          with (bskl_all_inh (pskl_to_bskl_inh P0)).
        apply ad_refine_syn_f__all
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P0).
        intros X HX.
        rewrite <- pskl_to_bskl_inh_open.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f X));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        assert (Hfr0 : α `notin` ftvar_in_pskl P0) by (clear - Fr; fsetdec).
        rewrite (subst_pskl_in_pskl_intro α P0 (pskl_var_f X) Hfr0).
        rewrite <- subst_var_bskl_inh.
        eapply ad_refine_syn_f_fmono with (F' := add α Δ1);
          [ clear; fsetdec | ].
        eapply ad_refine_syn_f_delta_mono;
          [ | instantiate (1 := add X (remove α (add α Δ1)));
              clear - Fr; fsetdec ].
        apply ad_refine_syn_f_rename;
          [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
        exact (ad_refine_syn_f_strip nil Θ1 Hrsα
                 ltac:(clear; fsetdec) ltac:(clear; fsetdec)).
    + simpl. apply ad_refine_pskl_f__all
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_pskl P `union` ftvar_in_pskl Q).
      intros X HX.
      rewrite (subst_pskl_in_pskl_intro α P (pskl_var_f X));
        [ | clear - Fr; fsetdec ].
      rewrite (subst_pskl_in_pskl_intro α Q (pskl_var_f X));
        [ | clear - Fr; fsetdec ].
      eapply ad_refine_pskl_f_fmono with (F' := add α Δ2);
        [ clear; fsetdec | ].
      eapply ad_refine_pskl_f_delta_mono;
        [ | instantiate (1 := add X (remove α (add α Δ2)));
            clear - Fr; fsetdec ].
      apply ad_refine_pskl_f_rename;
        [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
      exact (ad_refine_pskl_f_strip nil Θ1 Hrpα
               ltac:(clear; fsetdec) ltac:(clear; fsetdec)).
  - (* ForallSyn *) admit.
  - (* UnivGhost : ⊤.P ≈ ⊤.Q against input ⊤.P0 *)
    simpl in HwfP0, HwfP.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' ]; subst.
    inversion HwfP as [ | | | | | Θb Δb P' Hg' Hwf' ]; subst.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists (bskl_tophole Qt). split.
      { simpl. rewrite HeQt. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__tophole. exact Hcons.
      * simpl. apply ad_refine_syn_f__tophole_keep; [ | exact Hrs ].
        eapply ad_refine_syn_f_guarded_r;
          [ exact Hwf1 | exact Hrs | apply guarded_pskl_to_bskl_inh; exact Hg0 ].
    + simpl. apply ad_refine_pskl_f__tophole_keep; [ | exact Hrp ].
      eapply ad_refine_pskl_f_guarded_r; [ exact Hwf1 | exact Hrp | exact Hg' ].
  - (* UnivGhost1 *) admit.
  - (* UnivGhost2 *)
    simpl in HwfP.
    inversion HwfP as [ | | | | | Θb Δb P' Hg' Hwf' ]; subst.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists Qt. split; [ exact HeQt | ].
      split; [ simpl; apply ad_pat_consis__tophole_drop; exact Hcons | exact Hrs ].
    + simpl. apply ad_refine_pskl_f__tophole_remove. exact Hrp.
  - (* Flex : α̂ ≈ α̂ against input skel β̂ *)
    assert (Hmα : mono_ptyp (ptyp_var_f α)) by constructor.
    assert (Hmβ : mono_ptyp (ptyp_var_f β)) by constructor.
    assert (Hle : Θ0 ⊴ Θ1)
      by (destruct (a_unify_sound H Hwf Hmα Hmβ) as [Hi _]; exact Hi).
    assert (Hwf1 : a_wf_aenv Θ1) by (eapply a_unify_preserves_wf; eauto).
    destruct (a_unify_subjects_flex Hwf H eq_refl eq_refl) as [Hfα Hfβ].
    assert (HαnΔ : α `notin` (Δ1 `union` Δ2)).
    { destruct Hfα as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (HβnΔ : β `notin` (Δ1 `union` Δ2)).
    { destruct Hfβ as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (Hinv : no_flex_dep (Δ1 `union` Δ2) Θ1 /\
                   flex_above_free (Δ1 `union` Δ2) Θ1).
    { eapply a_unify_preserves_inv; eauto.
      intros X HX. simpl.
      assert (X <> α) by (intro; subst; auto).
      assert (X <> β) by (intro; subst; auto).
      clear - H0 H1. fsetdec. }
    destruct Hinv as [Hnfd1 Hfaf1].
    assert (Hbα1 : a_binds_tvar α Θ1).
    { eapply a_isub_binds_tvarish; eauto.
      destruct Hfα as [Hb | [τ Hb]];
        [ right; left | right; right; exists τ ]; auto. }
    assert (Hbβ1 : a_binds_tvar β Θ1).
    { eapply a_isub_binds_tvarish; eauto.
      destruct Hfβ as [Hb | [τ Hb]];
        [ right; left | right; right; exists τ ]; auto. }
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__var; [ fsetdec | exact Hbα1 ].
      * assert (Hcbα : ad_pat_consis empty Θ1
                  (ptyp_to_uskl_syn (ptyp_var_f β))
                  (ptyp_to_bskl_syn (ptyp_var_f α))).
        { eapply a_unify_sound_consis with (Θ' := Θ1);
            [ apply a_unify_sym; exact H | exact Hwf | exact Hmβ | exact Hmα
            | auto | ].
          intros X HX. simpl in HX.
          destruct (AtomSetImpl.union_1 HX) as [HXβ | HXα];
            [ assert (X = β) by (clear - HXβ; fsetdec); subst; exact Hbβ1
            | assert (X = α) by (clear - HXα; fsetdec); subst; exact Hbα1 ]. }
        replace (pskl_to_bskl_inh (pskl_var_f β))
          with (pskl_to_bskl_inh (uskl_to_pskl (ptyp_to_uskl_syn (ptyp_var_f β))))
          by (rewrite uskl_to_pskl_ptyp; reflexivity).
        replace (bskl_var_f α) with (ptyp_to_bskl_syn (ptyp_var_f α))
          by reflexivity.
        eapply ad_pat_consis_refine_syn_f_mono;
          [ exact Hcbα | exact Hwf1
          | apply mono_ptyp_to_bskl_syn; exact Hmα | | ].
        { rewrite ftvar_in_bskl_ptyp_syn. simpl. clear - HαnΔ. fsetdec. }
        { intros γ τ Hb. eapply (Hnfd1 γ τ) in Hb.
          clear - Hb. fsetdec. }
    + apply ad_refine_pskl_f__var. right. exact Hbα1.
  - (* FlexL : assign α̂ := P0 (the input skeleton) *)
    assert (Hvis : forall X, X `in` ftvar_in_pskl P0 -> a_binds_tvar X Θ0).
    { intros X HX. destruct (ad_wf_pskl_ftv_tvarish HwfP0 HX) as [HΔ | Ht];
        [ clear - HΔ; fsetdec | exact Ht ]. }
    destruct (a_assign_sound H0 a_decls__nil Hwf Hvis) as [Hle Hcons].
    simpl in Hle.
    assert (Hwf1 : a_wf_aenv Θ1)
      by (eapply a_assign_preserves_wf;
          [ exact H0 | apply a_decls__nil | exact Hwf | exact Hvis ]).
    assert (Hfα : a_flex_tvar Θ0 α)
      by (pose proof (a_assign_subject_flex H0) as Hf; simpl in Hf; exact Hf).
    assert (HαnΔ : α `notin` (Δ1 `union` Δ2)).
    { destruct Hfα as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (HΔdom : Δ1 `union` Δ2 [<=] dom Θ0).
    { intros X HX. apply binds_In with (a := abind_tvar). apply Hrig; auto. }
    assert (Hinv : no_flex_dep (Δ1 `union` Δ2) Θ1 /\
                   flex_above_free (Δ1 `union` Δ2) Θ1).
    { destruct (a_assign_preserves_inv (Δ := Δ1 `union` Δ2) H0
                  ltac:(simpl; exact Hnfd) Hfaf
                  ltac:(simpl; fsetdec)
                  ltac:(simpl; rewrite <- HΔdom; fsetdec)
                  ltac:(intros X HX Hnd0; exfalso; apply Hnd0;
                        apply HΔdom; exact HX))
        as [Hnd [Hfaf' _]].
      split; assumption. }
    destruct Hinv as [Hnfd1 Hfaf1].
    assert (Hbα1 : a_binds_tvar α Θ1) by (eapply a_assign_subject_binds; eauto).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__var; [ fsetdec | exact Hbα1 ].
      * replace (pskl_to_bskl_inh P0)
          with (pskl_to_bskl_inh (uskl_to_pskl (pskl_to_uskl P0)))
          by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        eapply ad_pat_consis_refine_syn_f_mono;
          [ exact Hcons | exact Hwf1 | apply mono_bskl__var | | ].
        { simpl. clear - HαnΔ. fsetdec. }
        { intros γ τ Hb. eapply (Hnfd1 γ τ) in Hb. clear - Hb. fsetdec. }
    + apply ad_refine_pskl_f__var. right. exact Hbα1.
  - (* FlexR : assign α̂ := P (the input), output var α̂ *)
    assert (Hvis : forall X, X `in` ftvar_in_pskl P -> a_binds_tvar X Θ0).
    { intros X HX. destruct (ad_wf_pskl_ftv_tvarish HwfP HX) as [HΔ | Ht];
        [ clear - HΔ; fsetdec | exact Ht ]. }
    destruct (a_assign_sound H0 a_decls__nil Hwf Hvis) as [Hle Hcons].
    simpl in Hle.
    assert (Hwf1 : a_wf_aenv Θ1)
      by (eapply a_assign_preserves_wf;
          [ exact H0 | apply a_decls__nil | exact Hwf | exact Hvis ]).
    assert (Hfα : a_flex_tvar Θ0 α)
      by (pose proof (a_assign_subject_flex H0) as Hf; simpl in Hf; exact Hf).
    assert (HαnΔ : α `notin` (Δ1 `union` Δ2)).
    { destruct Hfα as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (HΔdom : Δ1 `union` Δ2 [<=] dom Θ0).
    { intros X HX. apply binds_In with (a := abind_tvar). apply Hrig; auto. }
    assert (Hinv : no_flex_dep (Δ1 `union` Δ2) Θ1 /\
                   flex_above_free (Δ1 `union` Δ2) Θ1).
    { destruct (a_assign_preserves_inv (Δ := Δ1 `union` Δ2) H0
                  ltac:(simpl; exact Hnfd) Hfaf
                  ltac:(simpl; fsetdec)
                  ltac:(simpl; rewrite <- HΔdom; fsetdec)
                  ltac:(intros X HX Hnd0; exfalso; apply Hnd0;
                        apply HΔdom; exact HX))
        as [Hnd [Hfaf' _]].
      split; assumption. }
    destruct Hinv as [Hnfd1 Hfaf1].
    assert (Hbα1 : a_binds_tvar α Θ1) by (eapply a_assign_subject_binds; eauto).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * exact Hcons.
      * replace (pskl_to_bskl_inh (pskl_var_f α)) with (bskl_var_f α)
          by reflexivity.
        apply ad_refine_syn_f__var. right. exact Hbα1.
    + replace (pskl_var_f α) with (bskl_to_pskl (bskl_var_f α)) by reflexivity.
      replace P with (uskl_to_pskl (pskl_to_uskl P)) at 1
        by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      eapply ad_pat_consis_refine_pskl_f_mono;
        [ exact Hcons | exact Hwf1 | apply mono_bskl__var | | ].
      { simpl. clear - HαnΔ. fsetdec. }
      { intros γ τ Hb. eapply (Hnfd1 γ τ) in Hb. clear - Hb. fsetdec. }
  - (* GhostR *)
    split; [ apply a_isub_refl | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists (pskl_to_bskl_syn P).
      split; [ apply bskl_to_pskl_pskl_to_bskl_syn | ].
      split.
      * replace (pskl_to_bskl_syn P)
          with (pskl_to_bskl_syn (uskl_to_pskl (pskl_to_uskl P)))
          by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        apply ad_pat_consis_refl_erase.
        { apply pskl_to_uskl_lc. eapply ad_wf_pskl_lc; eauto. }
        { intros X HX. rewrite ftvar_in_uskl_pskl in HX.
          destruct (ad_wf_pskl_ftv_tvarish HwfP HX) as [HΔ | Htv];
            [ clear - HΔ; fsetdec | exact Htv ]. }
      * replace (pskl_to_bskl_inh pskl_hole) with bskl_hole by reflexivity.
        apply ad_refine_syn_f__hole; [ exact H | exact HwfP ].
    + apply ad_refine_pskl_f_refl.
      eapply ad_wf_pskl_delta_mono; [ exact HwfP | fsetdec ].
  - (* UnivGhostR *)
    simpl in HwfP0.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' ]; subst.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists Qt. split; [ exact HeQt | ]. split; [ exact Hcons | ].
      apply ad_refine_syn_f__tophole_remove. exact Hrs.
    + exact Hrp.
Admitted.