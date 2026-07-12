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
