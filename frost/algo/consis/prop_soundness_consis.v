(** Appendix B (consistency-proofs.tex), "Soundness of Consistency".

    The paper augments a solution to a consistency problem with four
    components (⊴, declarative consistency, and the two refinement
    directions), and proves the theorem "by mutual induction on the
    algorithmic consistency derivation together with the two auxiliary
    judgements of variable unification and assignment"
    (consistency-proofs.tex:1562).  Accordingly:

    - [a_unify_consis_sound]: the MUTUAL soundness bundle over
      [a_unify] + [a_consis] (the corrected [Flex-Flex-Assign] recurses
      into consistency, so the two judgments are mutually inductive).
      [a_assign] stays below the cycle (the mech reads Assign-Assign as
      continuing the assignment, cf. algo/def_extra.v) — its lemmas
      ([a_assign_sound], [a_assign_preserves_wf/_inv], ...) are plain
      inductions consumed by the bundle's FlexL/FlexR cases.
    - [a_consistag_sound_aux]: the DECORATED main induction
      (lemma:sound-decorated-consistency), a plain induction above the
      bundle — [a_consistag] is not in the recursion cycle; its Flex
      case consumes the bundle's [a_unify_sound].
    - [ad_pat_consis_refine_syn_f_mono] / [ad_pat_consis_refine_pskl_f_mono]:
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
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.decorated_algo.prop_decorate.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_mono_bridge.
(* cluster 4: [a_consis_decorate] moved downstream, into §10 there *)
Require Import src.frost.algo.consis.prop_consis_rename.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Monotype paintings                                                    *)
(* ===================================================================== *)

(** Painted skeletons of monotypes: no quantifiers, no ghosts. *)
Inductive mono_bskl : bskl -> Prop :=
| mono_bskl__unit  : mono_bskl bskl_unit
| mono_bskl__var   : forall α, mono_bskl (bskl_var_f α)
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

Lemma a_binds_tvar_mon : forall α Θ Θ',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  a_binds_tvar α Θ ->
  a_binds_tvar α Θ'.
Proof.
  intros * Hmon [Hb | [Hb | [τ Hb]]];
    [ left | right; left | right; right; exists τ ]; auto.
Qed.

(** A defined flexible variable's definition is a monotype in any
    well-formed context. *)
Lemma a_wf_aenv_binds_def_mono : forall Θ α1 τ,
  a_wf_aenv Θ ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ.
Proof.
  intros Θ α1 τ Hwf; induction Hwf; intros Hb;
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
Lemma a_wf_pskl_mono_subst_back : forall Θ α1 τ A,
  binds α1 (abind_flex_mono_def τ) Θ ->
  mono_ptyp A ->
  a_wf_pskl Θ empty (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 A)) ->
  a_wf_pskl Θ empty (ptyp_to_pskl A).
Proof.
  intros * Hb HmB; induction HmB; intros Hwf; simpl in *.
  - apply a_wf_pskl__unit.
  - destruct (eq_var α α1) as [->|Hne].
    + apply a_wf_pskl__var. right. right; right; exists τ; auto.
    + exact Hwf.
  - inversion Hwf; subst. apply a_wf_pskl__arrow; auto.
Qed.

(** Folding a flexible variable's definition on the PAINTED side of a
    consistency derivation, at a monotype: if [R ∼ syn(B[τ/α1̂])] and
    [α1̂ := τ ∈ Θ], then [R ∼ syn B] (rule FlexR reintroduces [α1̂]).
    Mirror of [ad_pat_consis_fold_def]. *)
Lemma ad_pat_consis_fold_def_q_mono : forall Θ α1 τ Ψ R Q',
  ad_pat_consis Ψ Θ R Q' ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  forall A',
  mono_ptyp A' ->
  Q' = ptyp_to_bskl_syn (subst_ptyp_in_ptyp τ α1 A') ->
  ad_pat_consis Ψ Θ R (ptyp_to_bskl_syn A').
Proof.
  intros Θ α1 τ Ψ R Q' H Hb Hmτ.
  induction H; intros A' HmB HeqQ;
    (destruct A' as [ | nB | XB | B1 B2 | B0 ];
     simpl in HeqQ;
     (* mono excludes ∀ *)
     try solve [ inversion HmB ];
     (* non-var heads that cannot match *)
     try discriminate HeqQ).
  - (* unit / A' unit *)
    apply ad_pat_consis__unit; auto.
  - (* unit / A' var *)
    destruct (eq_var XB α1) as [->|Hne].
    + apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb | ].
      rewrite <- HeqQ. apply ad_pat_consis__unit; auto.
    + discriminate HeqQ.
  - (* var / A' var *)
    destruct (eq_var XB α1) as [->|Hne].
    + apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb | ].
      rewrite <- HeqQ. apply ad_pat_consis__var; auto.
    + inversion HeqQ; subst. apply ad_pat_consis__var; auto.
  - (* arrow / A' var *)
    destruct (eq_var XB α1) as [->|Hne].
    + apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb | ].
      rewrite <- HeqQ. eapply ad_pat_consis__arrow; eauto.
    + discriminate HeqQ.
  - (* arrow / A' arrow *)
    inversion HeqQ; subst. inversion HmB; subst.
    eapply ad_pat_consis__arrow; eauto.
  - (* forall_inh_tagged / A' var *)
    destruct (eq_var XB α1) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* forall_inh_untagged / A' var *)
    destruct (eq_var XB α1) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* forall_syn_tagged / A' var *)
    destruct (eq_var XB α1) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* forall_syn / A' var *)
    destruct (eq_var XB α1) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* ghostg / A' var *)
    destruct (eq_var XB α1) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* topholeg / A' var *)
    destruct (eq_var XB α1) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* hole / A' unit *)
    assert (HP : P = ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 ptyp_unit)).
    { apply (f_equal bskl_to_pskl) in HeqQ.
      rewrite bskl_to_pskl_pskl_to_bskl_inh in HeqQ.
      unfold ptyp_to_bskl_syn in HeqQ.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in HeqQ. exact HeqQ. }
    replace (ptyp_to_bskl_syn ptyp_unit)
      with (pskl_to_bskl_inh (ptyp_to_pskl ptyp_unit)) by reflexivity.
    apply ad_pat_consis__hole; auto.
    apply a_wf_pskl_mono_subst_back with (α1 := α1) (τ := τ); auto.
    rewrite <- HP; auto.
  - (* hole / A' var *)
    destruct (eq_var XB α1) as [->|Hne].
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
  - (* hole / A' arrow *)
    assert (HP : P = ptyp_to_pskl
                       (subst_ptyp_in_ptyp τ α1 (ptyp_arrow B1 B2))).
    { apply (f_equal bskl_to_pskl) in HeqQ.
      rewrite bskl_to_pskl_pskl_to_bskl_inh in HeqQ.
      unfold ptyp_to_bskl_syn in HeqQ.
      rewrite bskl_to_pskl_pskl_to_bskl_syn in HeqQ. exact HeqQ. }
    rewrite <- (mono_inh_eq_syn HmB).
    apply ad_pat_consis__hole; auto.
    apply a_wf_pskl_mono_subst_back with (α1 := α1) (τ := τ); auto.
    rewrite <- HP; auto.
  - (* tophole / A' var *)
    destruct (eq_var XB α1) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* tophole_inh / A' var *)
    destruct (eq_var XB α1) as [->|Hne];
      [ unfold ptyp_to_bskl_syn in HeqQ; destruct Hmτ; simpl in HeqQ | ];
      discriminate HeqQ.
  - (* tophole_drop / A' unit *)
    apply ad_pat_consis__tophole_drop. apply IHad_pat_consis; auto.
  - (* tophole_drop / A' var *)
    apply ad_pat_consis__tophole_drop.
    apply IHad_pat_consis; auto.
  - (* tophole_drop / A' arrow *)
    apply ad_pat_consis__tophole_drop. apply IHad_pat_consis; auto.
  - (* flex_l / A' unit *)
    eapply ad_pat_consis__flex_l; eauto.
  - (* flex_l / A' var *)
    eapply ad_pat_consis__flex_l; eauto.
  - (* flex_l / A' arrow *)
    eapply ad_pat_consis__flex_l; eauto.
  - (* flex_r / A' var *)
    destruct (eq_var XB α1) as [->|Hne].
    + apply ad_pat_consis__flex_r with (τ := τ); [ exact Hb | ].
      rewrite <- HeqQ. eapply ad_pat_consis__flex_r; eauto.
    + inversion HeqQ; subst. eapply ad_pat_consis__flex_r; eauto.
Qed.

(* ===================================================================== *)
(*  Soundness of variable unification, declaratively                      *)
(*  (thm:sound-consistency part 2, read as the paper's Flex case does)    *)
(* ===================================================================== *)

(** Unification subjects are always variables. *)
(* [a_unify_var_inv] DELETED.  It said "every derivable [a_unify] has VARIABLE
   subjects" — which read like a theorem but was a SYMPTOM of the bug: the old
   [Flex-Flex-Assign] recursed into [a_unify], so a substituted non-variable
   subject had nowhere to go.  [a_unify]'s subjects are now ATOMS (the paper's
   hatted [unifyvar{α̂}{β̂}]), so the statement is vacuous. *)


(* [a_unify_sound_consis] REPLACED by the mutual soundness bundle
   ([a_unify_consis_sound] below): part 2 now produces a type EQUIVALENCE
   [Θ1 ⊢ α ≡ᵗ β] (subjects are atoms), and the converse bridge
   [tyequiv_mono_consis] (prop_mono_bridge.v) recovers the declarative
   consistency reading where the Flex case of part 1 needs it. *)

(* ===================================================================== *)
(*  Consistency at a monotype painting implies both refinements          *)
(*  (the paper's since-flexible-variables-do-not-depend-on-the-rigid-    *)
(*   type-variables-in-Δ steps, part 1 cases Flex / FlexL / FlexR)       *)
(* ===================================================================== *)

Lemma ad_pat_consis_refine_syn_mono : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  a_wf_aenv Θ ->
  mono_bskl Q ->
  forall Δ,
  Θ ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh (uskl_to_pskl R)) ⊳ Q.
Proof.
  intros Ψ Θ R Q H Hwf; induction H; intros HmQ Δ; simpl;
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
| ad_refine_syn_f__var : forall Θ Δ α,
    α `in` Δ \/ a_binds_tvar α Θ ->
    ad_refine_syn_f F Θ Δ (bskl_var_f α) (bskl_var_f α)
| ad_refine_syn_f__arrow : forall Θ Δ Q1 Q2 P1 P2,
    ad_refine_syn_f F Θ Δ Q1 P1 ->
    ad_refine_syn_f F Θ Δ Q2 P2 ->
    ad_refine_syn_f F Θ Δ (bskl_arrow Q1 Q2) (bskl_arrow P1 P2)
| ad_refine_syn_f__all : forall L Θ Δ Q P,
    (forall α, α `notin` L ->
       ad_refine_syn_f F Θ (add α Δ)
         (open_bskl_wrt_bskl Q (bskl_var_f α))
         (open_bskl_wrt_bskl P (bskl_var_f α))) ->
    ad_refine_syn_f F Θ Δ (bskl_all_inh Q) (bskl_all_inh P)
| ad_refine_syn_f__hole : forall Θ Δ P,
    F ∩ ftvar_in_pskl P [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    ad_refine_syn_f F Θ Δ bskl_hole (pskl_to_bskl_syn P)
| ad_refine_syn_f__tophole_remove : forall Θ Δ Q P,
    ad_refine_syn_f F Θ Δ Q P ->
    ad_refine_syn_f F Θ Δ (bskl_tophole Q) P
| ad_refine_syn_f__tophole_fill : forall L Θ Δ Q P,
    (forall α, α `notin` L ->
       ad_refine_syn_f F ((α ~ abind_tvar) ++ Θ) Δ
         (bskl_tophole Q) (open_bskl_wrt_bskl P (bskl_var_f α))) ->
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
| ad_refine_pskl_f__var : forall Θ Δ α,
    α `in` Δ \/ a_binds_tvar α Θ ->
    ad_refine_pskl_f F Θ Δ (pskl_var_f α) (pskl_var_f α)
| ad_refine_pskl_f__arrow : forall Θ Δ P1 P2 Q1 Q2,
    ad_refine_pskl_f F Θ Δ P1 Q1 ->
    ad_refine_pskl_f F Θ Δ P2 Q2 ->
    ad_refine_pskl_f F Θ Δ (pskl_arrow P1 P2) (pskl_arrow Q1 Q2)
| ad_refine_pskl_f__all : forall L Θ Δ P Q,
    (forall α, α `notin` L ->
       ad_refine_pskl_f F Θ (add α Δ)
         (open_pskl_wrt_pskl P (pskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α))) ->
    ad_refine_pskl_f F Θ Δ (pskl_all_syn P) (pskl_all_syn Q)
| ad_refine_pskl_f__hole : forall Θ Δ Q,
    F ∩ ftvar_in_pskl Q [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ Q ->
    ad_refine_pskl_f F Θ Δ pskl_hole Q
| ad_refine_pskl_f__tophole_remove : forall Θ Δ P Q,
    ad_refine_pskl_f F Θ Δ P Q ->
    ad_refine_pskl_f F Θ Δ (pskl_tophole P) Q
| ad_refine_pskl_f__tophole_fill : forall L Θ Δ P Q,
    (forall α, α `notin` L ->
       ad_refine_pskl_f F ((α ~ abind_tvar) ++ Θ) Δ
         (pskl_tophole P) (open_pskl_wrt_pskl Q (pskl_var_f α))) ->
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
Lemma ad_refine_syn_f_forget : forall F Θ Δ Q Q',
  ad_refine_syn_f F Θ Δ Q Q' ->
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ Q'.
Proof.
  intros * H; induction H; eauto using ad_refine_syn.
Qed.

Lemma ad_refine_pskl_f_forget : forall F Θ Δ P P',
  ad_refine_pskl_f F Θ Δ P P' ->
  Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ P'.
Proof.
  intros * H; induction H; eauto using ad_refine_pskl.
Qed.

(** Skeleton wf survives removing a rigid entry the skeleton avoids. *)
Lemma a_wf_pskl_strip_tvar : forall Θ1 α Θ2 Δ P,
  a_wf_pskl (Θ1 ++ (α ~ abind_tvar) ++ Θ2) Δ P ->
  α `notin` ftvar_in_pskl P ->
  a_wf_pskl (Θ1 ++ Θ2) Δ P.
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ2) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros Hfr; simpl in Hfr.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; auto | right ].
    eapply a_binds_tvar_strip_mid; eauto;
      try (intro Hc; inversion Hc; subst; fsetdec);
      try (intros τ0 Hc; inversion Hc).
  - apply a_wf_pskl__arrow; [ apply IHa_wf_pskl1 | apply IHa_wf_pskl2 ];
      auto.
  - apply a_wf_pskl__all with (L := L `union` singleton α).
    intros α0 Hα0. apply H0; auto.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                  P (pskl_var_f α0)) as Hup.
    simpl in Hup. fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; auto.
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
Lemma subst_var_bskl_syn : forall P α α',
  subst_bskl_in_bskl (bskl_var_f α') α (pskl_to_bskl_syn P)
  = pskl_to_bskl_syn (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var α α0); reflexivity.
Qed.

Lemma subst_var_bskl_inh : forall P α α',
  subst_bskl_in_bskl (bskl_var_f α') α (pskl_to_bskl_inh P)
  = pskl_to_bskl_inh (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var α α0); reflexivity.
Qed.

Lemma subst_var_uskl : forall P α α',
  subst_bskl_in_uskl (uskl_var_f α') α (pskl_to_uskl P)
  = pskl_to_uskl (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  induction P; intros; simpl; f_equal; auto.
  destruct (eq_var α α0); reflexivity.
Qed.

(** Guardedness survives variable renaming. *)
Lemma guarded_pskl_subst_var : forall P α β,
  guarded_pskl P ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros * H; inversion H; subst; simpl.
  - constructor.
  - destruct_if;
      constructor.
  - constructor; apply subst_pskl_in_pskl_lc_pskl; auto.
Qed.

(** Renaming a rigid context entry in skeleton well-formedness. *)
Lemma a_wf_pskl_rename_tvar : forall Θ1 α Θ0 Δ P β,
  a_wf_pskl (Θ1 ++ (α ~ abind_tvar) ++ Θ0) Δ P ->
  α `notin` Δ ->
  a_wf_pskl (Θ1 ++ (β ~ abind_tvar) ++ Θ0) Δ
    (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ0) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros HαΔ; simpl.
  - apply a_wf_pskl__unit.
  - destruct_if as [->|Hne].
    + apply a_wf_pskl__var. right.
      unfold a_binds_tvar. left.
      unfold binds. apply in_or_app. right. left. reflexivity.
    + apply a_wf_pskl__var.
      destruct H as [HΔ | Htv]; [ left; auto | right ].
      apply (@a_binds_tvar_insert_mid α0 Θ1 (β ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L `union` singleton α).
    intros α2 Hα2.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var; auto.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole;
      [ apply guarded_pskl_subst_var; auto
      | apply IHa_wf_pskl; auto; fsetdec ].
Qed.

Lemma ftvar_in_uskl_ptyp_syn : forall A,
  ftvar_in_uskl (ptyp_to_uskl_syn A) [=] ftvar_in_ptyp A.
Proof.
  intros. rewrite <- pskl_to_uskl_ptyp.
  rewrite ftvar_in_uskl_pskl. apply ftvar_ptyp_to_pskl.
Qed.

Lemma ftvar_in_bskl_ptyp_syn : forall A,
  ftvar_in_bskl (ptyp_to_bskl_syn A) [=] ftvar_in_ptyp A.
Proof.
  intros. unfold ptyp_to_bskl_syn.
  rewrite ftvar_in_bskl_syn. apply ftvar_ptyp_to_pskl.
Qed.

(** Case-split every renaming decision in the goal; contradictory
    branches close by congruence. *)
Ltac destruct_var_eqs :=
  repeat destruct_if; subst; try congruence.

(** Renaming the opened binder in Θ-level skeleton consistency. *)
Lemma ad_pat_consis_rename_tvar : forall Ψ Θ1 α Θ0 R Q β',
  ad_pat_consis Ψ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) R Q ->
  α `notin` dom (Θ1 ++ Θ0) ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_pat_consis Ψ (Θ1 ++ (β' ~ abind_tvar) ++ Θ0)
    (subst_bskl_in_uskl (uskl_var_f β') α R)
    (subst_bskl_in_bskl (bskl_var_f β') α Q).
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
      apply (@a_binds_tvar_insert_mid α0 Θ1 (β' ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - (* arrow *)
    eapply ad_pat_consis__arrow; eauto.
  - (* forall_inh_tagged *)
    eapply ad_pat_consis__forall_inh_tagged
      with (L := L `union` singleton α); eauto.
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* forall_inh_untagged *)
    eapply ad_pat_consis__forall_inh_untagged
      with (L := L `union` singleton α); eauto.
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* forall_syn_tagged *)
    eapply ad_pat_consis__forall_syn_tagged
      with (L := L `union` singleton α); eauto.
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
    all: try (simpl; repeat rewrite dom_app in *; fsetdec).
    all: intros β τ Hb;
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | eauto ].
  - (* forall_syn *)
    eapply ad_pat_consis__forall_syn
      with (L := L `union` singleton α); eauto.
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      auto using lc_uskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
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
    apply a_wf_pskl_rename_tvar; auto.
  - (* tophole *)
    apply ad_pat_consis__tophole; auto.
  - (* tophole_inh *)
    apply ad_pat_consis__tophole_inh
      with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    assert (HXL : α0 `notin` L) by fsetdec.
    apply (H0 α0 HXL ((α0 ~ abind_tvar) ++ Θ1)); auto.
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
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_uskl_fresh_eq
                  (ptyp_to_uskl_syn τ) (uskl_var_f β') α Hfr).
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
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α Hfr).
    auto.
Qed.

(** THE transfer lemmas: with the opened binder [α] recorded in both the
    hygiene set and Δ, its rigid entry can be dropped from the context —
    the fills avoid it (hygiene), the variable occurrences use Δ, and
    context definitions cannot mention it (they sit below it). *)
Lemma ad_refine_syn_f_strip : forall F Θ1 α Θ2 Δ Q Q',
  ad_refine_syn_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ2) Δ Q Q' ->
  α `in` F ->
  α `in` Δ ->
  ad_refine_syn_f F (Θ1 ++ Θ2) Δ Q Q'.
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ2) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros HαF HαΔ.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Htv]; [ left; auto | ].
    destruct (eq_var α0 α) as [->|Hne]; [ left; auto | right ].
    eapply a_binds_tvar_strip_mid; eauto;
      try (intro Hc; inversion Hc; subst; congruence);
      try (intros τ0 Hc; inversion Hc).
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L).
    intros α0 Hα0. apply H0; auto; try fsetdec.
  - apply ad_refine_syn_f__hole; auto.
    apply a_wf_pskl_strip_tvar with (α := α); auto.
    clear - H HαF; fsetdec.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L).
    intros α0 Hα0.
    apply (H0 α0 Hα0 ((α0 ~ abind_tvar) ++ Θ1)); auto.
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l;
      [ eapply binds_strip_mid; eauto; intro Hc; inversion Hc | auto ].
  - eapply ad_refine_syn_f__flex_r;
      [ eapply binds_strip_mid; eauto; intro Hc; inversion Hc | auto ].
Qed.

Lemma ad_refine_pskl_f_strip : forall F Θ1 α Θ2 Δ P P',
  ad_refine_pskl_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ2) Δ P P' ->
  α `in` F ->
  α `in` Δ ->
  ad_refine_pskl_f F (Θ1 ++ Θ2) Δ P P'.
Proof.
  intros * H.
  remember (Θ1 ++ (α ~ abind_tvar) ++ Θ2) as Θfull eqn:HeqΘ.
  revert Θ1 HeqΘ.
  induction H; intros Θ1 ->; intros HαF HαΔ.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Htv]; [ left; auto | ].
    destruct (eq_var α0 α) as [->|Hne]; [ left; auto | right ].
    eapply a_binds_tvar_strip_mid; eauto;
      try (intro Hc; inversion Hc; subst; congruence);
      try (intros τ0 Hc; inversion Hc).
  - apply ad_refine_pskl_f__arrow; auto.
  - apply ad_refine_pskl_f__all with (L := L).
    intros α0 Hα0. apply H0; auto; try fsetdec.
  - apply ad_refine_pskl_f__hole; auto.
    apply a_wf_pskl_strip_tvar with (α := α); auto.
    clear - H HαF; fsetdec.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - apply ad_refine_pskl_f__tophole_fill with (L := L).
    intros α0 Hα0.
    apply (H0 α0 Hα0 ((α0 ~ abind_tvar) ++ Θ1)); auto.
  - apply ad_refine_pskl_f__tophole_keep; auto.
  - eapply ad_refine_pskl_f__flex_l;
      [ eapply binds_strip_mid; eauto; intro Hc; inversion Hc | auto ].
  - eapply ad_refine_pskl_f__flex_r;
      [ eapply binds_strip_mid; eauto; intro Hc; inversion Hc | auto ].
Qed.

(* --------------------------------------------------------------------- *)
(*  Δ-monotonicity and Δ-side renaming of the fill-hygienic judgments      *)
(* --------------------------------------------------------------------- *)

Lemma ad_refine_syn_f_delta_mono : forall F Θ Δ0 Q Q',
  ad_refine_syn_f F Θ Δ0 Q Q' ->
  forall Δ, Δ0 [<=] Δ ->
  ad_refine_syn_f F Θ Δ Q Q'.
Proof.
  intros * H; induction H; intros Δ' Hsub;
    eauto using ad_refine_syn_f.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Htv]; [ left; fsetdec | auto ].
  - apply ad_refine_syn_f__all with (L := L).
    intros α Hα. apply H0; auto. fsetdec.
Qed.

Lemma ad_refine_pskl_f_delta_mono : forall F Θ Δ0 P P',
  ad_refine_pskl_f F Θ Δ0 P P' ->
  forall Δ, Δ0 [<=] Δ ->
  ad_refine_pskl_f F Θ Δ P P'.
Proof.
  intros * H; induction H; intros Δ' Hsub;
    eauto using ad_refine_pskl_f.
  - apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Htv]; [ left; fsetdec | auto ].
  - apply ad_refine_pskl_f__all with (L := L).
    intros α Hα. apply H0; auto. fsetdec.
Qed.

Lemma guarded_bskl_subst_var : forall Q α β,
  guarded_bskl Q ->
  guarded_bskl (subst_bskl_in_bskl (bskl_var_f β) α Q).
Proof.
  intros * H; inversion H; subst; simpl.
  - constructor.
  - destruct_if;
      constructor.
  - constructor; apply subst_bskl_in_bskl_lc_bskl;
      auto using lc_bskl_var_f.
Qed.

(** Δ-side renaming: the ∀-cases obtain their per-instance refinement
    components by renaming the one-fresh-α witness.  [α] has already
    been stripped from Θ ([*_f_strip]) and lives in Δ and in the
    hygiene set (so ghost fills avoid it, making the fills invariant). *)
Lemma ad_refine_syn_f_rename : forall F Θ Δ α Q Q' β',
  ad_refine_syn_f F Θ Δ Q Q' ->
  α `in` F ->
  α `notin` dom Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_refine_syn_f F Θ (add β' (remove α Δ))
    (subst_bskl_in_bskl (bskl_var_f β') α Q)
    (subst_bskl_in_bskl (bskl_var_f β') α Q').
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
      with (L := L `union` singleton α `union` singleton β').
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    apply ad_refine_syn_f_delta_mono
      with (Δ0 := add β' (remove α (add α0 Δ))); [ apply H0; auto | ].
    fsetdec.
  (* [P] is the hole rule's OWN fill binder ([ad_refine_syn_f__hole],
     algo/def_decl_algo.v), auto-bound by the induction — not this lemma's Q'. *)
  - (* hole: the fill avoids α, so renaming leaves it untouched *)
    assert (Hfr : α `notin` ftvar_in_pskl P)
      by (clear - H HαF; fsetdec).
    rewrite subst_var_bskl_syn.
    rewrite (subst_pskl_in_pskl_fresh_eq P (pskl_var_f β') α Hfr).
    apply ad_refine_syn_f__hole; auto.
  - (* tophole_remove *)
    apply ad_refine_syn_f__tophole_remove; auto.
  - (* tophole_fill *)
    apply ad_refine_syn_f__tophole_fill
      with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    replace (bskl_tophole (subst_bskl_in_bskl (bskl_var_f β') α Q))
      with (subst_bskl_in_bskl (bskl_var_f β') α (bskl_tophole Q))
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
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α Hfr).
    auto.
  - (* flex_r *)
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in H. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_bskl (ptyp_to_bskl_syn τ)).
    { rewrite ftvar_in_bskl_ptyp_syn. eauto. }
    destruct_var_eqs.
    apply ad_refine_syn_f__flex_r with (τ := τ); [ exact H | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α Hfr).
    auto.
Qed.

Lemma ad_refine_pskl_f_rename : forall F Θ Δ α P P' β',
  ad_refine_pskl_f F Θ Δ P P' ->
  α `in` F ->
  α `notin` dom Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_refine_pskl_f F Θ (add β' (remove α Δ))
    (subst_pskl_in_pskl (pskl_var_f β') α P)
    (subst_pskl_in_pskl (pskl_var_f β') α P').
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
      with (L := L `union` singleton α `union` singleton β').
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    apply ad_refine_pskl_f_delta_mono
      with (Δ0 := add β' (remove α (add α0 Δ))); [ apply H0; auto | ].
    fsetdec.
  (* [Q] is the hole rule's OWN fill binder ([ad_refine_pskl_f__hole]),
     auto-bound by the induction — not this lemma's P'. *)
  - (* hole *)
    assert (Hfr : α `notin` ftvar_in_pskl Q)
      by (clear - H HαF; fsetdec).
    rewrite (subst_pskl_in_pskl_fresh_eq Q (pskl_var_f β') α Hfr).
    apply ad_refine_pskl_f__hole; auto.
  - (* tophole_remove *)
    apply ad_refine_pskl_f__tophole_remove; auto.
  - (* tophole_fill *)
    apply ad_refine_pskl_f__tophole_fill
      with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    replace (pskl_tophole (subst_pskl_in_pskl (pskl_var_f β') α P))
      with (subst_pskl_in_pskl (pskl_var_f β') α (pskl_tophole P))
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
    { rewrite ftvar_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl_f__flex_l with (τ := τ); [ exact H | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f β') α Hfr).
    auto.
  - (* flex_r *)
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in H. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_pskl (ptyp_to_pskl τ)).
    { rewrite ftvar_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl_f__flex_r with (τ := τ); [ exact H | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f β') α Hfr).
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
    intros α Hα.
    repeat rewrite <- pskl_to_bskl_inh_open. auto.
  - replace (pskl_to_bskl_inh pskl_hole)
      with (pskl_to_bskl_syn pskl_hole) at 2 by reflexivity.
    apply ad_refine_syn_f__hole;
      [ simpl; fsetdec | apply a_wf_pskl__hole ].
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
      [ simpl; fsetdec | apply a_wf_pskl__hole ].
  - apply ad_refine_pskl_f__tophole_keep; auto.
    apply ad_refine_pskl_f_delta_mono with (Δ0 := empty); auto.
    fsetdec.
Qed.

Lemma ad_refine_syn_f_isub : forall F Θ Δ Q Q',
  ad_refine_syn_f F Θ Δ Q Q' ->
  forall Θ', Θ ⊴ Θ' ->
  ad_refine_syn_f F Θ' Δ Q Q'.
Proof.
  intros F Θ Δ Q Q' H; induction H; intros Θ' Hle.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - apply ad_refine_syn_f__arrow; auto.
  - eapply ad_refine_syn_f__all with (L := L); eauto.
  - apply ad_refine_syn_f__hole; eauto using a_wf_pskl_isub.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - eapply ad_refine_syn_f__tophole_fill with (L := L).
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_refine_syn_f__flex_r; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_refine_pskl_f_isub : forall F Θ Δ P P',
  ad_refine_pskl_f F Θ Δ P P' ->
  forall Θ', Θ ⊴ Θ' ->
  ad_refine_pskl_f F Θ' Δ P P'.
Proof.
  intros F Θ Δ P P' H; induction H; intros Θ' Hle.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Htv]; eauto using a_isub_binds_tvarish.
  - apply ad_refine_pskl_f__arrow; auto.
  - eapply ad_refine_pskl_f__all with (L := L); eauto.
  - apply ad_refine_pskl_f__hole; eauto using a_wf_pskl_isub.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - eapply ad_refine_pskl_f__tophole_fill with (L := L).
    intros α Hα. eauto using a_isub_cons_tvar.
  - apply ad_refine_pskl_f__tophole_keep; auto.
  - eapply ad_refine_pskl_f__flex_l; eauto using a_isub_binds_flex_def.
  - eapply ad_refine_pskl_f__flex_r; eauto using a_isub_binds_flex_def.
Qed.

Lemma ad_pat_consis_refine_pskl_mono : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  a_wf_aenv Θ ->
  mono_bskl Q ->
  forall Δ,
  Θ ⨟ Δ ⊢ᵣₚᵃ (uskl_to_pskl R) ⊳ (bskl_to_pskl Q).
Proof.
  intros Ψ Θ R Q H Hwf; induction H; intros HmQ Δ; simpl;
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

Lemma ad_pat_consis_refine_syn_f_mono : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  a_wf_aenv Θ ->
  mono_bskl Q ->
  forall F Δ,
  F ∩ ftvar_in_bskl Q [=] empty ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     F ∩ ftvar_in_ptyp τ [=] empty) ->
  ad_refine_syn_f F Θ Δ (pskl_to_bskl_inh (uskl_to_pskl R)) Q.
Proof.
  intros Ψ Θ R Q H Hwf; induction H; intros HmQ F Δ HFQ HFdefs; simpl;
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

Lemma ad_pat_consis_refine_pskl_f_mono : forall Ψ Θ R Q,
  ad_pat_consis Ψ Θ R Q ->
  a_wf_aenv Θ ->
  mono_bskl Q ->
  forall F Δ,
  F ∩ ftvar_in_bskl Q [=] empty ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
     F ∩ ftvar_in_ptyp τ [=] empty) ->
  ad_refine_pskl_f F Θ Δ (uskl_to_pskl R) (bskl_to_pskl Q).
Proof.
  intros Ψ Θ R Q H Hwf; induction H; intros HmQ F Δ HFQ HFdefs; simpl;
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

Lemma ad_refine_syn_f_rename_ctx : forall F Θ1 α Θ0 Δ Q Q' β',
  ad_refine_syn_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ0) Δ Q Q' ->
  α `notin` dom (Θ1 ++ Θ0) ->
  α `notin` Δ ->
  β' `notin` F ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_refine_syn_f F (Θ1 ++ (β' ~ abind_tvar) ++ Θ0) Δ
    (subst_bskl_in_bskl (bskl_var_f β') α Q)
    (subst_bskl_in_bskl (bskl_var_f β') α Q').
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
      apply (@a_binds_tvar_insert_mid α0 Θ1 (β' ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - (* arrow *)
    apply ad_refine_syn_f__arrow; auto.
  - (* all *)
    apply ad_refine_syn_f__all with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
  - (* hole *)
    rewrite subst_var_bskl_syn.
    apply ad_refine_syn_f__hole.
    + pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    P (pskl_var_f β') α) as Hup.
      simpl in Hup. clear - H HYF Hup. fsetdec.
    + apply a_wf_pskl_rename_tvar; auto.
  - (* tophole_remove *)
    apply ad_refine_syn_f__tophole_remove; auto.
  - (* tophole_fill *)
    apply ad_refine_syn_f__tophole_fill
      with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      auto using lc_bskl_var_f.
    replace (bskl_tophole (subst_bskl_in_bskl (bskl_var_f β') α Q))
      with (subst_bskl_in_bskl (bskl_var_f β') α (bskl_tophole Q))
      by reflexivity.
    apply (H0 α0 ltac:(auto) ((α0 ~ abind_tvar) ++ Θ1)); auto.
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
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α Hfr).
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
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_bskl_in_bskl_fresh_eq
                  (ptyp_to_bskl_syn τ) (bskl_var_f β') α Hfr).
    auto.
Qed.

Lemma ad_refine_pskl_f_rename_ctx : forall F Θ1 α Θ0 Δ P P' β',
  ad_refine_pskl_f F (Θ1 ++ (α ~ abind_tvar) ++ Θ0) Δ P P' ->
  α `notin` dom (Θ1 ++ Θ0) ->
  α `notin` Δ ->
  β' `notin` F ->
  (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
     α `notin` ftvar_in_ptyp τ) ->
  ad_refine_pskl_f F (Θ1 ++ (β' ~ abind_tvar) ++ Θ0) Δ
    (subst_pskl_in_pskl (pskl_var_f β') α P)
    (subst_pskl_in_pskl (pskl_var_f β') α P').
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
      apply (@a_binds_tvar_insert_mid α0 Θ1 (β' ~ abind_tvar) Θ0).
      eapply a_binds_tvar_strip_mid; eauto;
        try (intro Hc; inversion Hc; subst; congruence);
        try (intros τ0 Hc; inversion Hc).
  - (* arrow *)
    apply ad_refine_pskl_f__arrow; auto.
  - (* all *)
    apply ad_refine_pskl_f__all with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
  - (* hole *)
    apply ad_refine_pskl_f__hole.
    + pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    Q (pskl_var_f β') α) as Hup.
      simpl in Hup. clear - H HYF Hup. fsetdec.
    + apply a_wf_pskl_rename_tvar; auto.
  - (* tophole_remove *)
    apply ad_refine_pskl_f__tophole_remove; auto.
  - (* tophole_fill *)
    apply ad_refine_pskl_f__tophole_fill
      with (L := L `union` singleton α).
    intros α0 Hα0.
    assert (Hαx : α <> α0) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      auto using lc_pskl_var_f.
    replace (pskl_tophole (subst_pskl_in_pskl (pskl_var_f β') α P))
      with (subst_pskl_in_pskl (pskl_var_f β') α (pskl_tophole P))
      by reflexivity.
    apply (H0 α0 ltac:(auto) ((α0 ~ abind_tvar) ++ Θ1)); auto.
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
    { rewrite ftvar_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl_f__flex_l with (τ := τ);
      [ apply (@binds_insert_mid (abind_flex_mono_def τ) α0
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f β') α Hfr).
    auto.
  - (* flex_r *)
    assert (Hb' : binds α0 (abind_flex_mono_def τ) (Θ1 ++ Θ0)).
    { eapply binds_strip_mid; eauto. intro Hc; inversion Hc. }
    assert (Hαne : α0 <> α).
    { intro; subst. apply binds_In in Hb'. fsetdec. }
    assert (Hfr : α `notin` ftvar_in_pskl (ptyp_to_pskl τ)).
    { rewrite ftvar_ptyp_to_pskl. eauto. }
    destruct_var_eqs.
    apply ad_refine_pskl_f__flex_r with (τ := τ);
      [ apply (@binds_insert_mid (abind_flex_mono_def τ) α0
                 Θ1 (β' ~ abind_tvar) Θ0); auto | ].
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f β') α Hfr).
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
  Δ ∩ ftvar_in_ptyp τ [=] empty.

(** Δ-names sit above (and differ from) every non-rigid entry. *)
Definition flex_above_free (Δ : atoms) (Θ : aenv) : Prop :=
  forall Θ1 β (b : abind) Θ2, Θ = Θ1 ++ (β, b) :: Θ2 ->
  b <> abind_tvar ->
  Δ ∩ (add β (dom Θ2)) [=] empty.

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
  Δ ∩ (add c (dom Θ)) [=] empty.
Proof.
  intros * H Hne. apply (H nil c b Θ); auto.
Qed.

Lemma faf_cons : forall Δ (c : atom) (b : abind) Θ,
  (b <> abind_tvar -> Δ ∩ (add c (dom Θ)) [=] empty) ->
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
  Δ ∩ dom E [=] empty ->
  Δ ∩ dom Θ [=] empty ->
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
  - assert (Hβ : Δ ∩ (add β (dom Θ2)) [=] empty)
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
  intros α Θ0 Θ1 [[κ [Hid Hinc]] Hdef].
  destruct (a_inc_tvar_inv Hinc) as [Ξ [Θ2 [Heq [Hsuf Hinc']]]].
  destruct Ξ as [ | [α1 b] Ξ' ]; simpl in Heq.
  - assert (HΘ : Θ2 = Θ1) by (injection Heq; auto). subst Θ2.
    split.
    + exists κ. auto.
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
        | simpl; intros α0 Hα0;
          pose proof (IHHwf Hb' α0 Hα0); fsetdec ] ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
  - inversion Heq; subst.
    intros α0 Hα0. simpl.
    match goal with
    | Hw : a_wf_ptyp _ _ |- _ =>
        pose proof (a_wf_ptyp_ftv_tvarish Hw Hα0) as Htv
    end.
    destruct Htv as [Hb0 | [Hb0 | [τ1 Hb0]]]; apply binds_In in Hb0;
      fsetdec.
  - simpl. intros α0 Hα0.
    pose proof (IHHwf Hb' α0 Hα0). fsetdec.
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
  assert (Hd : Δ ∩ ftvar_in_ptyp τ [=] empty)
    by (eapply Hnd; eauto).
  assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
    by (eapply a_wf_aenv_def_ftv_dom; eauto).
  clear - Hd Hsc Hfr. fsetdec.
Qed.

(* [a_guess_mono_ftv] MOVED to prop_flex.v by the freshness campaign: the
   guess kit there derives target-side freshness from it instead of
   assuming output-side hypotheses.  prop_flex sits below this file, so
   the name is still in scope here. *)

Lemma inter_empty_pointwise : forall Δ Δ',
  (forall α, α `in` Δ -> α `notin` Δ') ->
  Δ ∩ Δ' [=] empty.
Proof.
  intros Δ Δ' H α. split; intro Hα.
  - assert (H1 := inter_1 Hα).
    assert (H2 := inter_2 Hα).
    exfalso. apply (H α H1 H2).
  - exfalso. clear - Hα. fsetdec.
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

(* [a_assign_preserves_inv] is now the ∀Δ-generalized 5th CONJUNCT of the
   bundle's ASSIGN motive: with the corrected Assign-Assign the proof recurses
   into CONSISTENCY, so it cannot be a standalone induction on [a_assign] any
   more.  Re-exported from the bundle under its original name (with the
   [a_decls] / wf hypotheses the motive carries). *)


(** Unification preserves the domain (no names are created). *)
(* [a_unify_dom] DELETED — it is now FALSE.  It said unification preserves the
   context DOMAIN ([dom Θ1 [=] dom Θ0]).  With [Flex-Flex-Assign] recursing into
   CONSISTENCY, unification can GROW the context: consistency → FlexL/FlexR →
   [a_assign] → [Assign-SolveM] → fresh [β̄] from [guess^TY].  That is CORRECT —
   the paper's part-2 soundness only claims an information INCREASE
   ([⊑{Θ₀}{Θ₁}]), which permits growth.  Uses of it are reworked onto ⊴. *)


(* [a_unify_preserves_inv] is now a CONJUNCT of the mutual soundness bundle
   ([a_unify_consis_sound] below), generalized over the Δ it protects — the
   consistency premise of [Flex-Flex-Assign] runs with [Δ1 = Δ2 = ∅], so a
   fixed-Δ statement would be useless there. *)


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

(* [a_assign_subject_binds] MOVED below the bundle: it needs NO induction any
   more — the increase conjunct plus [a_assign_subject_flex] and
   [a_isub_binds_tvarish] give it directly. *)

(** Moving a variable from Δ into the context as a rigid (the skeleton
    well-formedness reassociation used to open ∀-binders). *)
(* ===================================================================== *)
(*  ∀-wf at a CHOSEN opener (moved here by the freshness campaign's        *)
(*  cluster 4)                                                            *)
(* ===================================================================== *)

(** [a_consis]'s ∀ rows are exists-fresh now, so they hand their consumers
    ONE opener — an atom the cofinite [a_wf_pskl__all] has no reason to have
    avoided.  [a_wf_pskl_all_inv_at] manufactures the wf instance at that
    opener; it and its two supports moved up from prop_completeness_consis.v (PART B),
    which is downstream and still sees them. *)

Lemma a_wf_pskl_ftv_dom : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  ftvar_in_pskl P [<=] (Δ `union` dom Θ).
Proof.
  intros * H; induction H; simpl; try solve [ clear; fsetdec ].
  - (* var *)
    destruct H as [HΔ | Hbt]; [ clear - HΔ; fsetdec | ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]]; apply binds_In in Hb;
      clear - Hb; fsetdec.
  - (* arrow *) clear - IHa_wf_pskl1 IHa_wf_pskl2. fsetdec.
  - (* all *)
    pick fresh α for (L `union` ftvar_in_pskl P `union` Δ
                        `union` dom Θ).
    assert (HXL : α `notin` L) by (clear - Fr; fsetdec).
    pose proof (H0 α HXL) as Hsub.
    intros α2 Hα2.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower
                  P (pskl_var_f α)) as Hlo.
    assert (HZ' : α2 `in` (add α Δ `union` dom Θ))
      by (apply Hsub; clear - Hα2 Hlo; fsetdec).
    assert (Hne : α2 <> α) by (clear - Hα2 Fr; fsetdec).
    clear - HZ' Hne. fsetdec.
  - (* tophole *) clear - IHa_wf_pskl. fsetdec.
Qed.

Lemma a_wf_pskl_rename_delta : forall Θ Δ P β α0,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  β `notin` dom Θ ->
  Θ ⨟ (add α0 (remove β Δ)) ⊢ₚₛᵃ (subst_pskl_in_pskl (pskl_var_f α0) β P).
Proof.
  intros Θ Δ P β α0 H; revert α0; induction H; intros α1 Hβ; cbn.
  - apply a_wf_pskl__unit.
  - destruct_if as [-> | Hne].
    + apply a_wf_pskl__var. left. clear; fsetdec.
    + apply a_wf_pskl__var.
      destruct H as [HΔ | Hbt];
        [ left; clear - HΔ Hne; fsetdec | right; exact Hbt ].
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L `union` singleton β `union` singleton α1).
    intros α2 Hα2.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα2; fsetdec | apply lc_pskl_var_f ].
    eapply a_wf_pskl_delta_mono;
      [ apply H0; [ clear - Hα2; fsetdec | exact Hβ ]
      | clear - Hα2; fsetdec ].
  - apply a_wf_pskl__hole.
  - (* ∀◇ : the body is wf at the CLOSED Δ, so β ∉ ftv it and subst is a no-op *)
    assert (Hfr : β `notin` ftvar_in_pskl P).
    { assert (Hsc : ftvar_in_pskl P [<=] (empty `union` dom Θ))
        by (eapply a_wf_pskl_ftv_dom; exact H0).
      clear - Hβ Hsc; fsetdec. }
    rewrite (subst_pskl_in_pskl_fresh_eq P (pskl_var_f α1) β Hfr).
    apply a_wf_pskl__tophole; [ exact H | exact H0 ].
Qed.

Lemma a_wf_pskl_all_inv_at : forall Θ Δ P β,
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_all_syn P) ->
  β `notin` ftvar_in_pskl P ->
  Θ ⨟ (add β Δ) ⊢ₚₛᵃ (open_pskl_wrt_pskl P (pskl_var_f β)).
Proof.
  intros Θ Δ P β H HβP.
  inversion H as [ | | | L1 ? ? ? Hb | | ]; subst.
  pick fresh α for (L1 `union` dom Θ `union` ftvar_in_pskl P `union` Δ).
  pose proof (Hb α ltac:(clear - Fr; solve_notin_auto)) as Hα.
  pose proof (@a_wf_pskl_rename_delta Θ (add α Δ)
                (open_pskl_wrt_pskl P (pskl_var_f α)) α β Hα
                ltac:(clear - Fr; solve_notin_auto)) as Hr.
  rewrite <- (subst_pskl_in_pskl_intro α P (pskl_var_f β)
                ltac:(clear - Fr; solve_notin_auto)) in Hr.
  eapply a_wf_pskl_delta_mono; [ exact Hr | clear; fsetdec ].
Qed.

Lemma a_wf_pskl_reassoc : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall α,
  ((α ~ abind_tvar) ++ Θ) ⨟ (remove α Δ) ⊢ₚₛᵃ P.
Proof.
  intros Θ Δ P H; induction H; intros α0; simpl.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv].
    + destruct (α == α0) as [->|Hne].
      * right. left. unfold binds; left; reflexivity.
      * left. fsetdec.
    + right. apply (@a_binds_tvar_weaken_cons α (α0 ~ abind_tvar) Θ). exact Htv.
  - apply a_wf_pskl__arrow; [ apply (IHa_wf_pskl1 α0) | apply (IHa_wf_pskl2 α0) ].
  - apply a_wf_pskl__all with (L := L `union` singleton α0).
    intros α Hα.
    assert (HXL : α `notin` L) by fsetdec.
    eapply a_wf_pskl_delta_mono; [ apply (H0 α HXL α0) | ].
    fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; auto.
    eapply a_wf_pskl_delta_mono; [ apply (IHa_wf_pskl α0) | ].
    fsetdec.
Qed.

(** Opening a ∀-body at a GIVEN sufficiently fresh rigid α — the exists-fresh
    form of the ∀-wf inversion (the cofinite rule delivers instances only off
    its own [L], which an exists-fresh consumer does not control).  Pick a
    cofinite instance, reassociate its binder into Θ, and rename it to α. *)
Lemma a_wf_pskl_all_syn_open_tvar : forall Θ Δ B α,
  Θ ⨟ Δ ⊢ₚₛᵃ (pskl_all_syn B) ->
  α `notin` dom Θ `union` ftvar_in_pskl B `union` Δ ->
  ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ₚₛᵃ (open_pskl_wrt_pskl B (pskl_var_f α)).
Proof.
  intros Θ Δ B α Hwf Hα.
  inversion Hwf as [ | | | L Θz Δz Bz Hbody Heq | | ]; subst.
  destruct (atom_fresh (L `union` dom Θ `union` ftvar_in_pskl B
                          `union` singleton α `union` Δ)) as [β Hβ].
  assert (H1 : ((β ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ₚₛᵃ
                 (open_pskl_wrt_pskl B (pskl_var_f β))).
  { eapply a_wf_pskl_delta_mono;
      [ apply (a_wf_pskl_reassoc (Hbody β ltac:(clear - Hβ; solve_notin_auto)) β)
      | clear - Hβ; fsetdec ]. }
  rewrite (subst_pskl_in_pskl_intro β B (pskl_var_f α)
             ltac:(clear - Hβ; solve_notin_auto)).
  apply (@a_wf_pskl_rename_tvar nil β Θ Δ _ α);
    [ simpl; exact H1 | clear - Hβ; fsetdec ].
Qed.

(** Rigid membership of the two auxiliary contexts extends when a fresh
    binder is opened. *)
Lemma delta_rigids_open : forall Δ Θ α,
  (forall α', α' `in` Δ -> a_binds_tvar α' Θ) ->
  (forall α', α' `in` (add α Δ) -> a_binds_tvar α' ((α ~ abind_tvar) ++ Θ)).
Proof.
  intros * H α' Hα.
  destruct (α' == α) as [->|Hne].
  - left. unfold binds; left; reflexivity.
  - apply (@a_binds_tvar_weaken_cons α' (α ~ abind_tvar) Θ).
    apply H. fsetdec.
Qed.


(** F-monotonicity: a proof forbidding MORE names in ghost fills is a
    proof forbidding fewer (fills avoiding the larger set avoid the
    smaller). *)
Lemma ad_refine_syn_f_fmono : forall F F' Θ Δ Q Q',
  F [<=] F' ->
  ad_refine_syn_f F' Θ Δ Q Q' ->
  ad_refine_syn_f F Θ Δ Q Q'.
Proof.
  intros F F' Θ Δ Q Q' Hsub H; revert F Hsub; induction H; intros F Hsub;
    eauto using ad_refine_syn_f.
  - apply ad_refine_syn_f__hole; auto. clear - H Hsub. fsetdec.
Qed.

Lemma ad_refine_pskl_f_fmono : forall F F' Θ Δ P P',
  F [<=] F' ->
  ad_refine_pskl_f F' Θ Δ P P' ->
  ad_refine_pskl_f F Θ Δ P P'.
Proof.
  intros F F' Θ Δ P P' Hsub H; revert F Hsub; induction H; intros F Hsub;
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
  - apply a_wf_ptyp__all with (L := L `union` dom Θ'). intros α Hα.
    apply H0; auto. apply a_isub_cons_tvar; auto.
Qed.


(** Removing a declaration-only prefix preserves well-formedness. *)
Lemma a_wf_aenv_strip_prefix : forall Ξ Θ,
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ) ->
  a_wf_aenv Θ.
Proof.
  induction Ξ as [ | [α1 b] Ξ' IH ]; intros Θ Hdecl Hwf; simpl in *.
  - exact Hwf.
  - inversion Hdecl; subst; inversion Hwf; subst; eauto.
Qed.

(** Algorithmic skeleton well-formedness transports along [⊴]. *)
Lemma a_scope_pskl_isub : forall Θ P,
  a_scope_pskl Θ P ->
  forall Θ', Θ ⊴ Θ' ->
  a_scope_pskl Θ' P.
Proof.
  intros Θ P H; induction H; intros Θ' Hle; eauto using a_scope_pskl.
  - apply a_scope_pskl__var. eapply a_isub_binds_tvarish; eauto.
  - apply a_scope_pskl__all with (L := L `union` dom Θ'). intros α Hα.
    apply H0; auto. apply a_isub_cons_tvar; auto.
Qed.

(** A monotype all of whose free variables are tvar-ish is well-formed. *)
Lemma mono_ptyp_wf : forall Θ τ,
  mono_ptyp τ ->
  (forall α, α `in` ftvar_in_ptyp τ -> a_binds_tvar α Θ) ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ τ H; induction H; intros Hvis; simpl in *.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply Hvis. fsetdec.
  - apply a_wf_ptyp__arrow;
      [ apply IHmono_ptyp1 | apply IHmono_ptyp2 ];
      intros α Hα; apply Hvis; fsetdec.
Qed.

(* [a_wf_aenv_uniq] relocated to prop_flex.v (pure base lemma needed by prop_metasubst). *)

(** Every binding produced by guess^TY is a plain flexible variable. *)
Lemma a_guess_mono_flex_binds : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  forall α1 b, binds α1 b βs -> b = abind_flex_mono.
Proof.
  intros * H; induction H; intros α1 b Hb; simpl in *;
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
  - (* forall — exists-fresh: the single premise IS the instance *)
    eauto.
Qed.

(** Prepending a fresh, uniform flexible-variable block preserves
    context well-formedness. *)
Lemma a_wf_aenv_prepend_flex : forall E Θ,
  (forall α1 b, binds α1 b E -> b = abind_flex_mono) ->
  uniq E ->
  (forall α1, α1 `in` dom E -> α1 `notin` dom Θ) ->
  a_wf_aenv Θ ->
  a_wf_aenv (E ++ Θ).
Proof.
  induction E as [ | [α1 b] E' IH ]; intros Θ Hall Huniq Hfresh Hwf; simpl.
  - exact Hwf.
  - assert (Hb : b = abind_flex_mono)
      by (apply (Hall α1); unfold binds; simpl; left; reflexivity).
    subst.
    assert (HuE : uniq E' /\ α1 `notin` dom E')
      by (inversion Huniq; subst; auto).
    destruct HuE as [HuE Hγ'].
    apply a_wf_aenv__flex.
    + rewrite dom_app.
      assert (Hγd : α1 `notin` dom Θ) by (apply Hfresh; simpl; fsetdec).
      clear - Hγ' Hγd. fsetdec.
    + apply IH; auto.
      * intros α1' b' Hb'. apply (Hall α1'); unfold binds; simpl; right; auto.
      * intros α1' Hγ'2. apply Hfresh. simpl. fsetdec.
Qed.

(* [a_assign_new_avoids_F] is now the 4th CONJUNCT of the bundle's ASSIGN
   motive, re-exported below. *)

(* [a_assign_dom_mono] is now the 3rd CONJUNCT of the bundle's ASSIGN
   motive, re-exported below. *)

(** A visible monotype's skeleton is well-formed (no quantifiers, no
    ghosts — only the var leaves need discharging). *)
Lemma mono_ptyp_wf_pskl : forall Θ τ,
  mono_ptyp τ ->
  (forall α, α `in` ftvar_in_ptyp τ -> a_binds_tvar α Θ) ->
  Θ ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl τ).
Proof.
  intros Θ τ H; induction H; intros Hvis; simpl in *.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. right. apply Hvis. fsetdec.
  - apply a_wf_pskl__arrow;
      [ apply IHmono_ptyp1 | apply IHmono_ptyp2 ];
      intros α Hα; apply Hvis; fsetdec.
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

Lemma a_wf_aenv_var_typ_inv : forall x A Θ,
  a_wf_aenv ((x ~ abind_var_typ A) ++ Θ) ->
  x `notin` dom Θ /\ a_wf_ptyp Θ A /\ a_wf_aenv Θ.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma a_wf_aenv_var_skl_inv : forall x P Θ,
  a_wf_aenv ((x ~ abind_var_skl P) ++ Θ) ->
  x `notin` dom Θ /\ a_scope_pskl Θ P /\ a_wf_aenv Θ.
Proof. intros * H; inversion H; subst; auto. Qed.

(* [a_unify_preserves_wf] is now a CONJUNCT of the mutual soundness bundle
   ([a_unify_consis_sound] below): with the corrected [Flex-Flex-Assign] the
   proof recurses into consistency, so it cannot be a standalone induction
   on [a_unify] any more. *)

(* [a_assign_notin] is a corollary of [a_assign_new_avoids_F]; both are now
   conjuncts of the bundle's ASSIGN motive and re-exported below. *)

(** Free variables of a well-formed skeleton are tvar-ish or in Δ. *)
Lemma a_wf_pskl_ftv_tvarish : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  forall α, α `in` ftvar_in_pskl P -> α `in` Δ \/ a_binds_tvar α Θ.
Proof.
  intros Θ Δ P H; induction H; intros β Hβ; simpl in Hβ.
  - fsetdec.
  - assert (β = α) by fsetdec. subst. auto.
  - destruct (union_1 Hβ); auto.
  - pick fresh α2 for (L `union` ftvar_in_pskl P `union` Δ `union` {{β}}
                        `union` dom Θ).
    assert (HZL : α2 `notin` L) by fsetdec.
    assert (HY' : β `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α2))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α2)).
      fsetdec. }
    destruct (H0 α2 HZL β HY') as [HΔ | Htv].
    + left. assert (β <> α2) by fsetdec. clear - HΔ H1. fsetdec.
    + auto.
  - fsetdec.
  - destruct (IHa_wf_pskl β Hβ) as [HΔ | Htv]; [ fsetdec | auto ].
Qed.

(* [a_assign_preserves_wf] is now the 2nd CONJUNCT of the ASSIGN motive of
   the mutual bundle [a_assign_unify_consis_sound] below (Assign-Assign's
   premise is a CONSISTENCY derivation, so there is no [a_assign] IH for it).
   Re-exported from the bundle under its original name. *)

(** Monotype skeletons are locally closed and guarded. *)
(* [mono_ptyp_to_pskl_guarded] relocated to prop_flex.v (pure base lemma needed by prop_metasubst). *)

Lemma mono_bskl_lc : forall Q,
  mono_bskl Q -> lc_bskl Q.
Proof. induction 1; auto using lc_bskl. Qed.

Lemma mono_bskl_guarded : forall Q,
  mono_bskl Q -> guarded_bskl Q.
Proof.
  destruct 1 as [ | α | Q1 Q2 ];
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

Lemma a_unify_subjects_flex : forall Θ0 α β Θ1,
  a_wf_aenv Θ0 ->
  Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 ->
  a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β.
Proof.
  intros Θ0 α β Θ1 Hwf Hu; induction Hu.
  - (* flex_id : the rule's premise IS the flexibility (defined or not) *)
    split; assumption.
  - (* flex_l : (α~flex)++Θ0 *)
    split; [ left; unfold binds; left; reflexivity | ].
    apply a_flex_tvar_weaken_cons; [ auto | ].
    simpl. destruct H0 as [Hb | [τ Hb]]; apply binds_In in Hb; fsetdec.
  - (* flex_r : (β~flex)++Θ0 *)
    split; [ | left; unfold binds; left; reflexivity ].
    apply a_flex_tvar_weaken_cons; [ auto | ].
    simpl. destruct H0 as [Hb | [τ Hb]]; apply binds_In in Hb; fsetdec.
  - (* flex_assign : the hatted subjects are premises of the rule *)
    split; assumption.
  - (* flex_skip : (α1~flex)++Θ0 *)
    apply a_wf_aenv_flex_inv in Hwf. destruct Hwf as [Hfr Hwf0].
    destruct (IHHu Hwf0) as [Hfα Hfβ].
    split; (apply a_flex_tvar_weaken_cons;
            [ auto | simpl; clear - H H0; fsetdec ]).
  - (* skip_other *)
    assert (Hwf0 : a_wf_aenv Θ0 /\ c `notin` dom Θ0).
    { destruct H as [-> | [[Q ->] | [Q ->]]].
      - apply a_wf_aenv_tvar_inv in Hwf; tauto.
      - apply a_wf_aenv_var_typ_inv in Hwf; destruct Hwf as [? [? ?]]; auto.
      - apply a_wf_aenv_var_skl_inv in Hwf; destruct Hwf as [? [? ?]]; auto. }
    destruct Hwf0 as [Hwf0 Hcd].
    destruct (IHHu Hwf0) as [Hfα Hfβ].
    assert (Hαd : α `in` dom Θ0)
      by (destruct Hfα as [Hb | [τ Hb]]; apply binds_In in Hb; auto).
    assert (Hβd : β `in` dom Θ0)
      by (destruct Hfβ as [Hb | [τ Hb]]; apply binds_In in Hb; auto).
    split; (apply a_flex_tvar_weaken_cons; [ auto | simpl; fsetdec ]).
Qed.

(* [a_unify_sym] DELETED.  With [Flex-Flex-Assign]'s premise read as
   CONSISTENCY (subject vs input, asymmetric), unification is no longer
   syntactically symmetric.  The soundness bundle yields a type EQUIVALENCE
   [Θ1 ⊢ α ≡ᵗ β] instead, and [a_tyequiv__sym] provides the flip. *)

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

(* [a_flex_tvar_weaken_prefix] relocated to prop_inc.v (pure metasubst-base
   lemma; it was the only symbol prop_inc_strengthen borrowed from here, which
   created a prop_inc_strengthen -> prop_consis_sound import cycle). *)

(** The subject of an assignment is flexible in the input context.

    Still a STANDALONE induction after the mutual refactor: no case needs an
    [a_consis] IH.  Assign-Assign reads its conclusion straight off the HATTED
    SUBJECT premise (which is exactly why that premise exists — with an opaque
    consistency premise the old "derive it from the [a_assign] IH" argument
    dies, and [a_consis__rigid] would otherwise admit a RIGID subject).  And
    Assign-Depend gets SIMPLER: the suffix now grows at the tail, so the
    context is already associated the right way and [a_flex_tvar_permute_mid]
    is no longer needed — plain [app_assoc] does it. *)
Lemma a_assign_subject_flex : forall Θ0 Ξ α P Θ1,
  Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 ->
  a_flex_tvar (Ξ ++ Θ0) α.
Proof.
  intros * H; induction H.
  - (* UnivGhost-Id *)
    left. simpl. unfold binds; left; reflexivity.
  - (* SolveM *)
    left. unfold binds. apply in_or_app. right. left. reflexivity.
  - (* Assign : from the hatted-subject premise, not from an IH *)
    apply a_flex_tvar_weaken_prefix. assumption.
  - (* Depend : tail-append ⇒ just reassociate *)
    simpl_env in IHa_assign. exact IHa_assign.
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
  intros Θ Θ' α [[κ [Hid Hinc]] _] Hb.
  eapply a_inc_binds_tvar; eauto.
Qed.

(** A well-formed skeleton is locally closed. *)
Lemma a_wf_pskl_lc : forall Θ Δ P,
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
    (apply lc_bskl_all_syn; intros α;
     rewrite <- pskl_to_bskl_syn_open; now auto).
Qed.

(** Refinement outputs are locally closed. *)
Lemma ad_refine_pskl_f_lc_r : forall F Θ Δ P P',
  ad_refine_pskl_f F Θ Δ P P' -> lc_pskl P'.
Proof.
  intros F Θ Δ P P' H; induction H;
    try (now eauto using lc_pskl);
    try (now (eapply a_wf_pskl_lc; eauto));
    (pick fresh α; apply (lc_pskl_all_syn_exists α); auto).
Qed.

Lemma ad_refine_syn_f_lc_r : forall F Θ Δ Q Q',
  ad_refine_syn_f F Θ Δ Q Q' -> lc_bskl Q'.
Proof.
  intros F Θ Δ Q Q' H; induction H;
    try (now eauto using lc_bskl);
    try (now (apply pskl_to_bskl_syn_lc; eapply a_wf_pskl_lc; eauto));
    (pick fresh α; apply (lc_bskl_all_syn_exists α); auto).
Qed.

(** Refinement with a guarded left side yields a guarded right side. *)
Lemma ad_refine_pskl_f_guarded_r : forall F Θ Δ P P',
  a_wf_aenv Θ ->
  ad_refine_pskl_f F Θ Δ P P' ->
  guarded_pskl P ->
  guarded_pskl P'.
Proof.
  intros F Θ Δ P P' Hwf H; induction H; intros Hg;
    try solve [ inversion Hg ].
  - auto with frost.
  - auto with frost.
  - apply guarded_pskl__arrow; eapply ad_refine_pskl_f_lc_r; eauto.
  - assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply IHad_refine_pskl_f; auto. apply mono_ptyp_to_pskl_guarded; auto.
  - auto with frost.
Qed.

Lemma ad_refine_syn_f_guarded_r : forall F Θ Δ Q Q',
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ Q Q' ->
  guarded_bskl Q ->
  guarded_bskl Q'.
Proof.
  intros F Θ Δ Q Q' Hwf H; induction H; intros Hg;
    try solve [ inversion Hg ].
  - auto with frost.
  - auto with frost.
  - apply guarded_bskl__arrow; eapply ad_refine_syn_f_lc_r; eauto.
  - assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    apply IHad_refine_syn_f; auto.
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn; auto.
  - auto with frost.
Qed.



(* ===================================================================== *)
(*  The two SUBSIDIARY INDUCTIONS that Assign-Assign's soundness needs     *)
(*  (consistency-proofs.tex:1742-1753).  Assign-Assign's premise is a      *)
(*  CONSISTENCY derivation, so the [a_assign] IH hands back a JOIN [Q]     *)
(*  rather than the variable [α̂] the conclusion asks for.  The paper       *)
(*  eliminates [Q] in two steps:                                           *)
(*                                                                         *)
(*    (h)  from  inh(P[τ/β̂]) ⊳ˢʸⁿ Q  and  α̂[τ/β̂] ∼ Q                       *)
(*         conclude  P[τ/β̂] ∼ α̂[τ/β̂]                                       *)
(*    (i)  fold the definition β̂ ≔ τ back in, on BOTH sides.               *)
(*                                                                         *)
(*  Step (h) splits into [refine_inh_mono_consis] (the refinement side —   *)
(*  the join is a MONOTYPE painting, because the subject [α̂[τ/β̂]] is one,  *)
(*  which kills every quantifier/tophole refinement rule) and the Q-SIDE   *)
(*  transport of consistency along [≡ᵗ] (the mirror of                     *)
(*  [tyequiv_mono_consis_transport], prop_mono_bridge.v — the subject-side *)
(*  one — which the [Flex-Flex-Assign] case uses).  Step (i) is            *)
(*  [ad_pat_consis_fold_def] (left) + [ad_pat_consis_fold_def_q_mono]      *)
(*  (right); both already exist.                                           *)
(* ===================================================================== *)

(** A monotype PAINTING is colour-blind: syn = inh (colours differ only at
    quantifiers, and a monotype has none).  Companion of [mono_bskl_inh_syn]. *)
Lemma mono_bskl_syn_inh : forall P,
  mono_bskl (pskl_to_bskl_syn P) ->
  pskl_to_bskl_syn P = pskl_to_bskl_inh P.
Proof.
  induction P; intros Hm; simpl in *; try reflexivity;
    inversion Hm; subst; f_equal; auto.
Qed.

(** Substituting a monotype for a variable commutes with the skeleton
    embedding, on a variable.  (The [α̂ = β̂] branch is REACHABLE — there the
    subject of Assign-Assign is the monotype [τ], not a variable.) *)
Lemma subst_pskl_var_ptyp : forall τ β α,
  subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)
  = ptyp_to_pskl (subst_ptyp_in_ptyp τ β (ptyp_var_f α)).
Proof.
  intros. simpl. destruct (eq_var α β); simpl; reflexivity.
Qed.

(** SUBSIDIARY INDUCTION #1 (the refinement half of the paper's step (h)):
    if the inherited painting of [P0] refines to a join that is a MONOTYPE
    painting, then [⌊P0⌋] is CONSISTENT with that join.  The monotype
    hypothesis is what makes this true: it rules out ForallInh /
    TopholeFill / TopholeKeep (whose outputs are quantifiers or topholes),
    and it forces the ghost-hole fill [pskl_to_bskl_syn P] to be
    colour-blind, so consistency's [hole] rule — which produces the
    INHERITED painting — matches it. *)
Lemma refine_inh_mono_consis : forall Θ Δ Qb Qt,
  Θ ⨟ Δ ⊢ᵣᵃ Qb ⊳ Qt ->
  a_wf_aenv Θ ->
  mono_bskl Qt ->
  forall P0, Qb = pskl_to_bskl_inh P0 ->
  (forall α, α `in` Δ -> a_binds_tvar α Θ) ->
  empty ⨟ Θ ⊢ₛᵃ (pskl_to_uskl P0) ∼ Qt.
Proof.
  intros Θ Δ Qb Qt Hr Hwf; induction Hr; intros Hm P0 Heq Hrig.
  - (* unit *)
    destruct P0; simpl in Heq; try discriminate.
    simpl. apply ad_pat_consis__unit. fsetdec.
  - (* var *)
    destruct P0; simpl in Heq; try discriminate.
    inversion Heq; subst.
    simpl. apply ad_pat_consis__var; [ fsetdec | ].
    destruct H as [HΔ | Ht]; [ apply Hrig; auto | exact Ht ].
  - (* arrow *)
    destruct P0; simpl in Heq; try discriminate.
    inversion Heq; subst. inversion Hm; subst.
    simpl. apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply IHHr1 | apply IHHr2 | fsetdec ]; auto.
  - (* all : the join would be a quantifier, never a monotype *)
    inversion Hm.
  - (* hole : the ghost fill is colour-blind here *)
    destruct P0; simpl in Heq; try discriminate.
    simpl. rewrite (mono_bskl_syn_inh _ Hm).
    apply ad_pat_consis__hole; [ fsetdec | exact H ].
  - (* tophole_remove *)
    destruct P0; simpl in Heq; try discriminate.
    inversion Heq; subst.
    simpl. apply ad_pat_consis__tophole_drop. apply IHHr; auto.
  - (* tophole_fill : the join would be a quantifier *)
    inversion Hm.
  - (* tophole_keep : the join would be a tophole *)
    inversion Hm.
  - (* flex_l : the input is a DEFINED flexible variable *)
    destruct P0; simpl in Heq; try discriminate.
    inversion Heq; subst.
    assert (Hmt : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    simpl. eapply ad_pat_consis__flex_l; [ exact H | ].
    rewrite <- ptyp_to_uskl_syn_eq.
    apply IHHr; auto.
    unfold ptyp_to_bskl_syn. rewrite mono_inh_eq_syn; auto.
  - (* flex_r : the join is a DEFINED flexible variable *)
    assert (Hmt : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_r; [ exact H | ].
    apply IHHr; auto.
    apply mono_ptyp_to_bskl_syn; auto.
Qed.

(** Unfold a DEFINED variable sitting in the JOIN position.  The mirror of
    [consis_unfold_def_subject] (prop_mono_bridge.v): only [var] / [hole] /
    [tophole_drop] / [flex_l] / [flex_r] can have join [α1̂]. *)
Lemma consis_unfold_def_join : forall Ψ Θ R Qt,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Qt ->
  a_wf_aenv Θ ->
  forall α1 τ, Qt = bskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ (ptyp_to_bskl_syn τ).
Proof.
  intros * Hc Hwf; induction Hc; intros α10 τ0 HeqQ Hb;
    try discriminate HeqQ.
  - (* var : the subject is the same variable; unfold it with [flex_l] *)
    inversion HeqQ; subst.
    assert (Hmτ : mono_ptyp τ0) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_pat_consis__flex_l; [ exact Hb | ].
    eapply consis_psi_cong_local;
      [ apply consis_mono_refl | clear - H; fsetdec ]; auto.
    intros α Hα. eapply a_wf_ptyp_ftv_tvarish;
      [ eapply a_wf_aenv_binds_def_wf; eauto | exact Hα ].
  - (* hole : the ghost fill IS the variable *)
    destruct P; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst.
    assert (Hmτ : mono_ptyp τ0) by (eapply a_wf_aenv_binds_def_mono; eauto).
    rewrite <- (mono_inh_eq_syn Hmτ).
    apply ad_pat_consis__hole; [ exact H | ].
    apply a_wf_pskl_mono_ptyp; [ exact Hmτ | ].
    eapply a_wf_aenv_binds_def_wf; eauto.
  - (* tophole_drop *)
    apply ad_pat_consis__tophole_drop. eapply IHHc; eauto.
  - (* flex_l *)
    eapply ad_pat_consis__flex_l; [ eassumption | ]. eapply IHHc; eauto.
  - (* flex_r : the join's own definition is the one we are unfolding *)
    inversion HeqQ; subst.
    assert (Heqτ : τ = τ0)
      by (assert (Hu : uniq Θ) by (apply a_wf_aenv_uniq; auto);
          pose proof (binds_unique _ _ _ _ _ H Hb Hu) as He;
          inversion He; reflexivity).
    subst. exact Hc.
Qed.

(** Congruence of the JOIN at an arrow.  Mirror of
    [consis_arrow_subject_transport]; the [hole] case is why the components
    must be given as concrete MONOTYPES rather than opaque transports (the
    rebuilt ghost fill has to be a well-formed skeleton). *)
Lemma consis_arrow_join_transport : forall Ψ Θ R Qt,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Qt ->
  a_wf_aenv Θ ->
  forall A1' A2' A1 A2,
  Qt = ptyp_to_bskl_syn (ptyp_arrow A1' A2') ->
  mono_ptyp A1 -> mono_ptyp A2 ->
  (forall α, α `in` ftvar_in_ptyp (ptyp_arrow A1 A2) -> a_binds_tvar α Θ) ->
  (forall Ψ' R', Ψ' ⨟ Θ ⊢ₛᵃ R' ∼ (ptyp_to_bskl_syn A1') ->
                 Ψ' ⨟ Θ ⊢ₛᵃ R' ∼ (ptyp_to_bskl_syn A1)) ->
  (forall Ψ' R', Ψ' ⨟ Θ ⊢ₛᵃ R' ∼ (ptyp_to_bskl_syn A2') ->
                 Ψ' ⨟ Θ ⊢ₛᵃ R' ∼ (ptyp_to_bskl_syn A2)) ->
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ (ptyp_to_bskl_syn (ptyp_arrow A1 A2)).
Proof.
  intros Ψ Θ R Qt Hc Hwf; induction Hc;
    intros A1' A2' A1 A2 HeqQ HmA1 HmA2 Hvis Ht1 Ht2;
    unfold ptyp_to_bskl_syn in HeqQ; simpl in HeqQ; try discriminate HeqQ.
  - (* arrow *)
    inversion HeqQ; subst.
    unfold ptyp_to_bskl_syn; simpl.
    apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2).
    { apply Ht1; unfold ptyp_to_bskl_syn; assumption. }
    { apply Ht2; unfold ptyp_to_bskl_syn; assumption. }
    { assumption. }
  - (* hole : rebuild the fill at the transported monotype *)
    assert (Hma : mono_ptyp (ptyp_arrow A1 A2))
      by (apply mono_ptyp__arrow; auto).
    rewrite <- (mono_inh_eq_syn Hma).
    apply ad_pat_consis__hole; [ exact H | ].
    apply mono_ptyp_wf_pskl; [ exact Hma | exact Hvis ].
  - (* tophole_drop *)
    apply ad_pat_consis__tophole_drop.
    apply (IHHc Hwf A1' A2' A1 A2 HeqQ HmA1 HmA2 Hvis Ht1 Ht2).
  - (* flex_l *)
    eapply ad_pat_consis__flex_l; [ eassumption | ].
    apply (IHHc Hwf A1' A2' A1 A2 HeqQ HmA1 HmA2 Hvis Ht1 Ht2).
Qed.

(** SUBSIDIARY INDUCTION #2 (the JOIN-side transport): for [A ≡ᵗ B] on
    monotypes, a consistency derivation whose JOIN is [syn{B}] can be
    re-joined at [syn{A}], and vice versa.  Both directions at once, so
    [sym] swaps and [trans] composes.  The exact mirror of
    [tyequiv_mono_consis_transport] (which transports the SUBJECT). *)
Lemma tyequiv_mono_consis_transport_q : forall Θ A A',
  Θ ⊢ A ≡ᵗ A' ->
  a_wf_aenv Θ ->
  mono_ptyp A ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  (forall Ψ R, Ψ ⨟ Θ ⊢ₛᵃ R ∼ (ptyp_to_bskl_syn A') ->
               Ψ ⨟ Θ ⊢ₛᵃ R ∼ (ptyp_to_bskl_syn A)) /\
  (forall Ψ R, Ψ ⨟ Θ ⊢ₛᵃ R ∼ (ptyp_to_bskl_syn A) ->
               Ψ ⨟ Θ ⊢ₛᵃ R ∼ (ptyp_to_bskl_syn A')).
Proof.
  intros Θ A A' Heq Hwf; induction Heq; intros Hm Hv.
  - (* refl *)
    split; intros Ψ R Hc; exact Hc.
  - (* sym : swap the IH's directions *)
    destruct (a_tyequiv_mono_vis Heq Hwf) as [_ Hback].
    destruct (Hback (conj Hm Hv)) as [HmA HvA].
    destruct (IHHeq Hwf HmA HvA) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - (* trans : compose *)
    destruct (a_tyequiv_mono_vis Heq1 Hwf) as [Hfwd _].
    destruct (Hfwd (conj Hm Hv)) as [HmB HvB].
    destruct (IHHeq1 Hwf Hm Hv) as [H1l H1r].
    destruct (IHHeq2 Hwf HmB HvB) as [H2l H2r].
    split; intros Ψ R Hc; [ apply H1l, H2l, Hc | apply H2r, H1r, Hc ].
  - (* flex_def : α̂ ≡ τ with α̂ ≔ τ *)
    split; intros Ψ R Hc.
    + (* fold the join back to the variable : one lookup rule *)
      unfold ptyp_to_bskl_syn; simpl.
      eapply ad_pat_consis__flex_r; [ eassumption | exact Hc ].
    + (* unfold the join's definition *)
      eapply consis_unfold_def_join;
        [ exact Hc | exact Hwf | | eassumption ].
      unfold ptyp_to_bskl_syn; simpl; reflexivity.
  - (* arrow : componentwise *)
    inversion Hm as [ | | ? ? Hm1 Hm2 ]; subst; simpl in Hv.
    assert (Hv1 : forall α, α `in` ftvar_in_ptyp A1 -> a_binds_tvar α Θ)
      by (intros α Hα; apply Hv; fsetdec).
    assert (Hv2 : forall α, α `in` ftvar_in_ptyp A2 -> a_binds_tvar α Θ)
      by (intros α Hα; apply Hv; fsetdec).
    destruct (a_tyequiv_mono_vis Heq1 Hwf) as [Hf1 _].
    destruct (Hf1 (conj Hm1 Hv1)) as [HmB1 HvB1].
    destruct (a_tyequiv_mono_vis Heq2 Hwf) as [Hf2 _].
    destruct (Hf2 (conj Hm2 Hv2)) as [HmB2 HvB2].
    destruct (IHHeq1 Hwf Hm1 Hv1) as [H1l H1r].
    destruct (IHHeq2 Hwf Hm2 Hv2) as [H2l H2r].
    split; intros Ψ R Hc.
    + eapply consis_arrow_join_transport with (A1' := B1) (A2' := B2);
        [ exact Hc | exact Hwf | reflexivity | exact Hm1 | exact Hm2
        | | exact H1l | exact H2l ].
      intros α Hα; simpl in Hα.
      destruct (union_1 Hα); [ apply Hv1 | apply Hv2 ]; auto.
    + eapply consis_arrow_join_transport with (A1' := A1) (A2' := A2);
        [ exact Hc | exact Hwf | reflexivity | exact HmB1 | exact HmB2
        | | exact H1r | exact H2r ].
      intros α Hα; simpl in Hα.
      destruct (union_1 Hα); [ apply HvB1 | apply HvB2 ]; auto.
  - (* all : a monotype is never a ∀ *)
    inversion Hm.
Qed.

(* ===================================================================== *)
(*  THE MUTUAL SOUNDNESS BUNDLE (thm:sound-consistency parts 1+2)          *)
(*                                                                          *)
(*  [a_unify] and [a_consis] are mutually inductive (the corrected          *)
(*  [Flex-Flex-Assign] recurses into consistency), so — exactly as the      *)
(*  paper organises its own proof (consistency-proofs.tex:1562) — their     *)
(*  soundness is ONE mutual induction.  [a_assign] stays BELOW the cycle    *)
(*  (the mech reads Assign-Assign as continuing the assignment, see the     *)
(*  note in algo/def_extra.v), so its lemmas enter as black boxes.          *)
(*                                                                          *)
(*  Conjuncts, per judgment  Θ0 → Θ1:                                       *)
(*   1. Θ0 ⊴ Θ1                    (information increase)                   *)
(*   2. a_wf_aenv Θ1               (wf preservation)                        *)
(*   3. dom Θ0 ⊆ dom Θ1            (no entry is dropped)                    *)
(*   4. ∀Δ-invariant preservation  (no-flex-dep + flex-above-free +         *)
(*      domain bookkeeping, GENERALIZED over Δ: the consistency premise     *)
(*      of Flex-Flex-Assign runs at Δ1 = Δ2 = ∅, so the fixed-Δ variant     *)
(*      would be useless there.  Its COVERAGE hypothesis is                 *)
(*      OUTPUT-relative, [Δ ∩ dom Θ1 ⊆ dom Θ0], mirroring the walk's own    *)
(*      Barendregt output premises — DESIGN.md §4.3)                        *)
(*   5. the augmented solution     (consistency: join + both refinements;   *)
(*      unification: the type EQUIVALENCE Θ1 ⊢ α ≡ᵗ β)                      *)
(*                                                                          *)
(*  The used-name index [F] and its "new names avoid F" conjunct are GONE   *)
(*  (2026-08-03): the walk's re-attaching rules state the obligation        *)
(*  directly, and completeness carries the matching avoid set on its own    *)
(*  motive (prop_completeness_consis.v (PART B) §2).                                     *)
(* ===================================================================== *)

(* [a_assign_unify_consis_mutind] (+ the per-judgment Induction schemes)
   relocated to def_extra.v, next to the inductives, so prop_inc_strengthen can
   use it without importing this file (cycle break). *)

(** Conclusions of the two motives (hypotheses live in [*_concl] below). *)
Definition unify_sound_post (Θ0 : aenv) (α β : atom)
    (Θ1 : aenv) : Prop :=
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\ dom Θ0 [<=] dom Θ1 /\
  (forall Δ,
     no_flex_dep Δ Θ0 -> flex_above_free Δ Θ0 ->
     Δ ∩ dom Θ1 [<=] dom Θ0 ->
     no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1 /\
     (forall α, α `in` Δ -> α `in` dom Θ1 -> α `in` dom Θ0)) /\
  (Θ1 ⊢ (ptyp_var_f α) ≡ᵗ (ptyp_var_f β)).

Definition consis_sound_post (Δ1 Δ2 : atoms) (Θ0 : aenv)
    (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\ dom Θ0 [<=] dom Θ1 /\
  (forall Δ,
     no_flex_dep Δ Θ0 -> flex_above_free Δ Θ0 ->
     Δ ∩ dom Θ1 [<=] dom Θ0 ->
     (forall α, α `in` Δ -> α `notin` dom Θ0 ->
        α `notin` (ftvar_in_pskl P0 `union` ftvar_in_pskl P)) ->
     no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1 /\
     (forall α, α `in` Δ -> α `in` dom Θ1 -> α `in` dom Θ0)) /\
  (exists Qt, bskl_to_pskl Qt = Q /\
     ad_pat_consis empty Θ1 (pskl_to_uskl P) Qt /\
     ad_refine_syn_f Δ1 Θ1 Δ1 (pskl_to_bskl_inh P0) Qt) /\
  ad_refine_pskl_f Δ2 Θ1 Δ2 P Q.

Definition unify_sound_concl (Θ0 : aenv) (α β : atom)
    (Θ1 : aenv) : Prop :=
  a_wf_aenv Θ0 -> unify_sound_post Θ0 α β Θ1.

Definition consis_sound_concl (Δ1 Δ2 : atoms) (Θ0 : aenv)
    (P0 P Q : pskl) (Θ1 : aenv) : Prop :=
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 ->
  flex_above_free (Δ1 `union` Δ2) Θ0 ->
  consis_sound_post Δ1 Δ2 Θ0 P0 P Q Θ1.

(** The ASSIGN motive.  [Ξ] is the pending suffix, so every context slot is
    the MERGED [Ξ ++ Θ0] (which is exactly the context of Assign-Assign's
    consistency premise).  Conjuncts 1-5 mirror the other two motives;
    conjunct 6 is the paper's part-3 solution: the assigned skeleton is
    declaratively consistent with the subject VARIABLE in the output.

    The wf hypothesis is the FULL [⨟ ∅ ⊢ₚₛᵃ P], not the old "every free
    variable is tvar-ish": the consistency IH of Assign-Assign needs
    [⨟ ∅ ⊢ₚₛᵃ] on BOTH slots, and [a_wf_pskl__tophole] demands
    [guarded_pskl] — strictly stronger than visibility.  Every [a_assign]
    call site (consistency's FlexL/FlexR and their decorated twins) has it. *)
Definition assign_sound_post (Θ0 Ξ : aenv) (α : atom)
    (P : pskl) (Θ1 : aenv) : Prop :=
  (Ξ ++ Θ0) ⊴ Θ1 /\ a_wf_aenv Θ1 /\ dom (Ξ ++ Θ0) [<=] dom Θ1 /\
  (forall Δ,
     no_flex_dep Δ (Ξ ++ Θ0) -> flex_above_free Δ Θ0 ->
     Δ ∩ dom Ξ [=] empty ->
     Δ ∩ dom Θ1 [<=] dom (Ξ ++ Θ0) ->
     (forall α, α `in` Δ -> α `notin` dom Θ0 -> α `notin` ftvar_in_pskl P) ->
     no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1 /\
     (forall α, α `in` Δ -> α `in` dom Θ1 -> α `in` (dom Ξ `union` dom Θ0))) /\
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (bskl_var_f α).

Definition assign_sound_concl (Θ0 Ξ : aenv) (α : atom)
    (P : pskl) (Θ1 : aenv) : Prop :=
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  assign_sound_post Θ0 Ξ α P Θ1.

Theorem a_assign_unify_consis_sound :
  (forall Θ0 Ξ α P Θ1,
     Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 -> assign_sound_concl Θ0 Ξ α P Θ1) /\
  (forall Θ0 α β Θ1,
     Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 -> unify_sound_concl Θ0 α β Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P P3 Θ1,
     Θ0 ⊢ₐ[ Δ1 | Δ2 | P0 ] P ∼ P3 ⊣ Θ1 ->
     consis_sound_concl Δ1 Δ2 Θ0 P0 P P3 Θ1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ => assign_sound_concl Θ0 Ξ α P Θ1)
           (fun Θ0 α β Θ1 _ => unify_sound_concl Θ0 α β Θ1)
           (fun Δ1 Δ2 Θ0 P0 P P3 Θ1 _ =>
              consis_sound_concl Δ1 Δ2 Θ0 P0 P P3 Θ1));
    unfold assign_sound_concl, unify_sound_concl, consis_sound_concl,
           assign_sound_post, unify_sound_post, consis_sound_post.
  - (* Assign-UnivGhost-Id *)
    intros Θ0 α Hdecl Hwf HwfP.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ simpl; clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      split; [ exact Hnd | ]. split; [ exact Hfaf | ].
      intros α0 _ Hα0. simpl in Hα0. simpl. clear - Hα0. fsetdec. }
    replace (pskl_to_uskl (pskl_tophole (pskl_var_f α)))
      with (uskl_tophole (uskl_var_f α)) by reflexivity.
    apply ad_pat_consis__tophole_drop.
    apply ad_pat_consis__var; [ clear; fsetdec | ].
    right; left. unfold binds; left; reflexivity.

  - (* Assign-SolveM *)
    intros Θ0 Ξ α P βs τ Hαn Hg Hmτ Huβs Hfr Hdecl Hwf HwfP.
    assert (Hvis : forall α0, α0 `in` ftvar_in_pskl P ->
                   a_binds_tvar α0 (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)).
    { intros α0 Hα0. destruct (a_wf_pskl_ftv_tvarish HwfP Hα0) as [HΔ | Ht];
        [ clear - HΔ; fsetdec | exact Ht ]. }
    assert (Hβsd : a_decls βs) by (eapply a_guess_mono_decls; eauto).
    assert (Huniq : uniq (Ξ ++ (α ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hαd : α `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (Hle : (Ξ ++ (α ~ abind_flex_mono) ++ Θ0) ⊴
                  ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0)).
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb. right; left.
        unfold binds. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; left. exact Hb. }
      apply a_isub_prepend_decls_src;
        [ apply (a_decls__cons α); constructor
        | intros α1 Hb;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ subst; right; right; exists τ; unfold binds;
            apply in_or_app; left; left; reflexivity
          | inversion Hb' ]
        | ].
      assert (Hs1 : Θ0 ⊴ ((βs ++ Ξ) ++ Θ0)).
      { pose proof (a_wf_aenv_lc_aenv HwfΞΘ) as Hlca.
        apply lc_aenv_app_inv in Hlca as [_ Hlc0].
        apply a_isub_weaken_suffix; [ exact Hlc0 | ].
        apply a_suffix_app; auto using a_decls_suffix. }
      first [ rewrite <- app_assoc in Hs1 | rewrite app_assoc in Hs1 ].
      apply a_isub_target_weaken with (Ξ := (α ~ abind_flex_mono_def τ))
        in Hs1; auto.
      apply (a_suffix__cons α (b := abind_flex_mono_def τ)); constructor. }
    assert (Hβsfr : forall α1, α1 `in` dom βs -> α1 `notin` dom (Ξ ++ Θ0)).
    { intros α1 Hα1. pose proof (Hfr α1 Hα1) as Hh.
      repeat rewrite dom_app in *. clear - Hh. fsetdec. }
    assert (Hβswf : a_wf_aenv (βs ++ Ξ ++ Θ0)).
    { apply a_wf_aenv_prepend_flex;
        [ intros α1 b Hb; eapply a_guess_mono_flex_binds; eauto
        | exact Huβs
        | intros α1 Hα1;
          (assert (Hf : α1 `notin` dom (Ξ ++ Θ0)) by (apply Hβsfr; auto));
          repeat rewrite dom_app in *; clear - Hf; fsetdec
        | exact HwfΞΘ ]. }
    assert (Hαβs : α `notin` dom βs).
    { intro Hin. pose proof (Hfr α Hin) as Hh. clear - Hh. fsetdec. }
    assert (Hwf1 : a_wf_aenv ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0)).
    { apply a_wf_aenv__flex_def; [ | | exact Hmτ | exact Hβswf ].
      { repeat rewrite dom_app in *. clear - Hαd Hαβs. fsetdec. }
      apply mono_ptyp_wf; auto.
      intros α0 Hα0.
      pose proof (a_guess_mono_ftv Hg Hα0) as Hin.
      destruct (union_1 Hin) as [HXP | Hα0βs].
      - assert (Hα0α : α0 <> α) by (intro; subst; auto).
        assert (Htv : a_binds_tvar α0 (Ξ ++ Θ0)).
        { eapply a_binds_tvar_strip_mid with
            (c := α) (b := abind_flex_mono);
            [ apply Hvis; auto
            | intro Hc; inversion Hc; congruence
            | intro Hc; inversion Hc; congruence
            | intros τ0 Hc; inversion Hc; congruence ]. }
        destruct Htv as [Hb | [Hb | [τ0 Hb]]];
          [ left | right; left | right; right; exists τ0 ];
          unfold binds; apply in_or_app; right; exact Hb.
      - right; left. unfold binds; apply in_or_app; left.
        apply binds_In_inv in Hα0βs. destruct Hα0βs as [b Hb].
        assert (Hbf : b = abind_flex_mono)
          by (eapply a_guess_mono_flex_binds; eauto). subst. exact Hb. }
    split; [ exact Hle | ].
    split; [ exact Hwf1 | ].
    split.
    { clear. repeat rewrite dom_app. simpl. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add α (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      assert (Hft : forall α0, α0 `in` Δ -> α0 `notin` ftvar_in_pskl P).
      { intros α0 Hα0Δ. apply HP; auto. simpl.
        assert (α0 `notin` add α (dom Θ0)) by (clear - Hhd Hα0Δ; fsetdec).
        auto. }
      (* the guessed block is excluded by the OUTPUT-relative coverage: a
         Δ-name among the [β̄] would be in the output's domain, hence — by
         [Hcov] — in the merged input's, which the rule's own side condition
         forbids *)
      assert (HβΔ : forall α0, α0 `in` Δ -> α0 `notin` dom βs).
      { intros α0 Hα0Δ Hα0β.
        assert (HXfr := Hfr α0 Hα0β).
        assert (HXcov : α0 `in` dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0)).
        { apply Hcov. apply inter_3; [ exact Hα0Δ | ].
          repeat rewrite dom_app. simpl. clear - Hα0β. fsetdec. }
        repeat rewrite dom_app in *. simpl in *.
        clear - HXfr HXcov. fsetdec. }
      assert (Hτ : Δ ∩ ftvar_in_ptyp τ [=] empty).
      { apply inter_empty_pointwise. intros α0 Hα0Δ Hα0τ.
        pose proof (a_guess_mono_ftv Hg Hα0τ) as Hin.
        assert (HnP : α0 `notin` ftvar_in_pskl P) by (apply Hft; auto).
        assert (Hnβ : α0 `notin` dom βs) by (apply HβΔ; auto).
        clear - Hin HnP Hnβ. fsetdec. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
        { inversion Heq; subst; exact Hτ. }
        apply in_app_or in Hb'. destruct Hb' as [Hbβ | HbΞΘ].
        { exfalso. eapply a_decls_no_def; eauto. }
        apply (Hnd β' τ').
        unfold binds. apply in_app_or in HbΞΘ. apply in_or_app.
        destruct HbΞΘ as [HbΞ | HbΘ]; [ auto | ].
        right. right. exact HbΘ.
      + apply faf_cons.
        { intros _. repeat rewrite dom_app.
          apply inter_empty_pointwise. intros α0 Hα0Δ HXin.
          assert (Hn1 : α0 `notin` add α (dom Θ0))
            by (clear - Hhd Hα0Δ; fsetdec).
          assert (Hn2 : α0 `notin` dom βs) by auto.
          assert (Hn3 : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
          clear - HXin Hn1 Hn2 Hn3. fsetdec. }
        apply faf_app.
        { apply inter_empty_pointwise. intros α0 Hα0Δ. auto. }
        { rewrite dom_app. apply inter_empty_pointwise.
          intros α0 Hα0Δ HXin.
          assert (Hn3 : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
          assert (Hn1 : α0 `notin` add α (dom Θ0))
            by (clear - Hhd Hα0Δ; fsetdec).
          clear - HXin Hn1 Hn3. fsetdec. }
        apply faf_app.
        { exact HΔΞ. }
        { apply inter_empty_pointwise. intros α0 Hα0Δ HXin.
          clear - Hhd Hα0Δ HXin. fsetdec. }
        eapply faf_tail; eauto.
      + intros α0 Hα0Δ HXd.
        simpl in HXd. repeat rewrite dom_app in HXd.
        assert (Hn2 : α0 `notin` dom βs) by auto.
        assert (Hn1 : α0 `notin` add α (dom Θ0))
          by (clear - Hhd Hα0Δ; fsetdec).
        simpl. clear - HXd Hn1 Hn2. fsetdec. }
    apply ad_pat_consis__flex_r with (τ := τ);
      [ unfold binds; left; reflexivity | ].
    eapply a_guess_mono_consis; eauto.
    { intros α0 Hα0. eapply a_isub_binds_tvarish; eauto. }
    { intros α1 Hb. right; left.
      unfold binds. apply in_or_app; right.
      apply in_or_app; left. exact Hb. }

  - (* Assign-Assign : the premise is a CONSISTENCY derivation, so the join
       [P3] must be eliminated — see the two subsidiary inductions above. *)
    intros Θ0 Θ1 Ξ α β τ P P3 Hfl Hbar Hc IHc Hdecl Hwf HwfP.
    assert (Hτ : a_wf_ptyp Θ0 τ /\ mono_ptyp τ)
      by (eapply a_wf_aenv_mid_def_inv; eauto).
    destruct Hτ as [Hτwf Hτm].
    assert (Hlcτ : lc_ptyp τ) by (eapply a_wf_ptyp_lc; eauto).
    assert (Huniq : uniq (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (Hβd0 : β `notin` dom Θ0)
      by (repeat rewrite dom_app in *; clear - Hβd; fsetdec).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hbβ : binds β (abind_flex_mono_def τ)
                    (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ0))
      by (unfold binds; apply in_or_app; right; left; reflexivity).
    (* [τ] avoids [β̂] (it is well-formed strictly below it) *)
    assert (Hτfv : forall α0, α0 `in` ftvar_in_ptyp τ -> α0 `in` dom Θ0).
    { intros α0 Hα0.
      assert (Htv : a_binds_tvar α0 Θ0)
        by (eapply a_wf_ptyp_ftv_tvarish; eauto).
      destruct Htv as [Hb | [Hb | [τ0 Hb]]]; eapply binds_In; eauto. }
    assert (Hβτ : β `notin` ftvar_in_ptyp τ)
      by (intro Hin; apply Hβd0; apply Hτfv; exact Hin).
    (* the SUBSTITUTED SUBJECT is a monotype *)
    assert (Hmsub : mono_ptyp (subst_ptyp_in_ptyp τ β (ptyp_var_f α)))
      by (apply mono_ptyp_subst; [ constructor | exact Hτm ]).
    assert (Hsubvis : forall α0,
        α0 `in` ftvar_in_ptyp (subst_ptyp_in_ptyp τ β (ptyp_var_f α)) ->
        a_binds_tvar α0 (Ξ ++ Θ0)).
    { intros α0 Hα0.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                    (ptyp_var_f α) τ β) as Hup.
      assert (HX' : α0 `in` (ftvar_in_ptyp τ `union`
                            remove β (ftvar_in_ptyp (ptyp_var_f α))))
        by (clear - Hα0 Hup; fsetdec).
      destruct (union_1 HX') as [Hτ | Hα].
      - assert (Htv : a_binds_tvar α0 Θ0)
          by (eapply a_wf_ptyp_ftv_tvarish; eauto).
        destruct Htv as [Hb | [Hb | [τ0 Hb]]];
          [ left | right; left | right; right; exists τ0 ];
          unfold binds; apply in_or_app; right; exact Hb.
      - simpl in Hα.
        assert (Hα0α : α0 = α) by (clear - Hα; fsetdec).
        assert (Hα0β : α0 <> β) by (clear - Hα; fsetdec).
        subst α0.
        destruct Hfl as [Hb | [τ' Hb]];
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx ?] | Hb'];
          try solve [ exfalso; apply Hα0β; exact Heqx ];
          [ right; left | right; right; exists τ' ];
          unfold binds; apply in_or_app; right; exact Hb'. }
    (* the two well-formedness obligations of the consistency IH *)
    assert (HwfP0 : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)).
    { eapply a_wf_pskl_strip_mid with (c := β) (b := abind_flex_mono_def τ).
      - apply a_wf_pskl_mono_subst; auto.
      - pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                      P (ptyp_to_pskl τ) β) as Hup.
        rewrite ftvar_ptyp_to_pskl in Hup.
        clear - Hup Hβτ. fsetdec. }
    assert (HwfS : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                     (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))).
    { rewrite subst_pskl_var_ptyp.
      apply mono_ptyp_wf_pskl; [ exact Hmsub | exact Hsubvis ]. }
    destruct (IHc HwfΞΘ HwfP0 HwfS
                ltac:(intros α0 Hα0; exfalso; clear - Hα0; solve_notin_auto)
                ltac:(intros β' τ' _; clear; solve_notin_auto)
                ltac:(intros Θa βa ba Θb Heq Hne; clear; solve_notin_auto))
      as [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [HconsQ Hrs]]] Hrp]]]]].
    (* the walked head misses the output: the rule says so *)
    assert (Hβ1 : β `notin` dom Θ1) by exact Hbar.
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strengthen_decls_src; eauto).
    assert (HleF : ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊴
                   ((β ~ abind_flex_mono_def τ) ++ Θ1))
      by (apply a_isub_cons_flex_def; auto).
    assert (Hwf1' : a_wf_aenv ((β ~ abind_flex_mono_def τ) ++ Θ1)).
    { apply a_wf_aenv__flex_def; auto.
      eapply a_wf_ptyp_isub; eauto. }
    assert (Hbβ1 : binds β (abind_flex_mono_def τ)
                     ((β ~ abind_flex_mono_def τ) ++ Θ1))
      by (unfold binds; left; reflexivity).
    (* 1. increase *)
    split.
    { apply a_isub_prepend_decls_src; [ exact Hdecl | | exact HleF ].
      intros α1 Hb.
      apply a_binds_tvar_weaken_cons.
      eapply a_isub_binds_flex; [ exact Hle | ].
      unfold binds; apply in_or_app; left; exact Hb. }
    (* 2. well-formedness *)
    split; [ exact Hwf1' | ].
    (* 3. domain *)
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    (* 4. the ∀Δ invariant *)
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add β (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      assert (Hτ0 : Δ ∩ ftvar_in_ptyp τ [=] empty)
        by (apply (Hnd β τ); exact Hbβ).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
                 (β ~ abind_flex_mono_def τ) Θ0). exact Hb. }
      { apply faf_app.
        - exact HΔΞ.
        - clear - Hhd. fsetdec.
        - eapply faf_tail; eauto. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd.
        repeat rewrite dom_app in HXd.
        assert (Hα0β : α0 <> β) by (intro; subst; clear - Hhd Hα0Δ; fsetdec).
        assert (Hα0Θ0 : α0 `notin` dom Θ0) by (clear - HXd; fsetdec).
        assert (Hα0τ : α0 `notin` ftvar_in_ptyp τ)
          by (clear - Hτ0 Hα0Δ; fsetdec).
        assert (HXP : α0 `notin` ftvar_in_pskl P).
        { apply HP;
            [ exact Hα0Δ | simpl; clear - Hα0β Hα0Θ0; fsetdec ]. }
        assert (HXsub : α0 `notin` ftvar_in_pskl
                          (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)).
        { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        P (ptyp_to_pskl τ) β) as Hup.
          rewrite ftvar_ptyp_to_pskl in Hup.
          clear - Hup Hα0τ HXP. fsetdec. }
        assert (Hα0α : α0 <> α).
        { intro; subst α0.
          destruct Hfl as [Hb | [τ' Hb]];
            destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx ?] | Hb'];
            [ apply Hα0β; exact Heqx | | apply Hα0β; exact Heqx | ];
            apply Hα0Θ0; eapply binds_In; eauto. }
        assert (HXv : α0 `notin` ftvar_in_pskl
                        (subst_pskl_in_pskl (ptyp_to_pskl τ) β
                           (pskl_var_f α))).
        { rewrite subst_pskl_var_ptyp. rewrite ftvar_ptyp_to_pskl.
          pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                        (ptyp_var_f α) τ β) as Hup.
          simpl in Hup. clear - Hup Hα0τ Hα0α. fsetdec. }
        clear - HXsub HXv. fsetdec. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ inversion Heq; subst; exact Hτ0 | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ | exact IH2 ].
        intros _. apply inter_empty_pointwise.
        intros α0 Hα0Δ HXin.
        assert (Hβ' : α0 `notin` add β (dom Θ0))
          by (clear - Hhd Hα0Δ; fsetdec).
        assert (HΘ1 : α0 `notin` dom Θ1).
        { intro HXd. specialize (IH3 α0 Hα0Δ HXd).
          rewrite dom_app in IH3.
          assert (Hα0Ξ : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
          clear - IH3 Hα0Ξ Hβ'. fsetdec. }
        clear - HXin Hβ' HΘ1. fsetdec.
      + intros α0 Hα0Δ HXd. simpl in HXd.
        assert (Hnex : α0 <> β)
          by (intro; subst; clear - Hhd Hα0Δ; fsetdec).
        assert (HXd1 : α0 `in` dom Θ1) by (clear - HXd Hnex; fsetdec).
        specialize (IH3 α0 Hα0Δ HXd1).
        rewrite dom_app in IH3. simpl. clear - IH3. fsetdec. }
    (* 5. the augmented solution: eliminate the join [P3] *)
    (* (a) the join is a monotype painting, ≡ᵗ-equal to the subject *)
    rewrite subst_pskl_var_ptyp in HconsQ.
    rewrite ptyp_to_uskl_syn_eq in HconsQ.
    destruct (consis_mono_join HconsQ Hwf1
                (A := subst_ptyp_in_ptyp τ β (ptyp_var_f α))
                eq_refl Hmsub)
      as [C [HmC [HeqC HeqmC]]].
    (* (b) the refinement side: ⌊P[τ/β̂]⌋ ∼ P3  (subsidiary induction #1) *)
    assert (Hc0 : empty ⨟ Θ1 ⊢ₛᵃ
                    (pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P))
                    ∼ Qt).
    { eapply refine_inh_mono_consis;
        [ eapply ad_refine_syn_f_forget; exact Hrs
        | exact Hwf1
        | rewrite HeqC; apply mono_ptyp_to_bskl_syn; exact HmC
        | reflexivity
        | intros α0 Hα0; exfalso; clear - Hα0; fsetdec ]. }
    (* (c) fold the definition on the SUBJECT side *)
    assert (Hc1 : empty ⨟ ((β ~ abind_flex_mono_def τ) ++ Θ1) ⊢ₛᵃ
                    (pskl_to_uskl P) ∼ Qt).
    { eapply ad_pat_consis_fold_def with
        (β := β) (τ := τ)
        (R' := pskl_to_uskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P));
        [ apply ad_pat_consis_weaken_cons; exact Hc0
        | exact Hbβ1
        | exact Hτm
        | apply pskl_to_uskl_subst ]. }
    (* (d) fold the definition on the JOIN side (subsidiary induction #2) *)
    assert (Hbα1 : a_binds_tvar α ((β ~ abind_flex_mono_def τ) ++ Θ1)).
    { eapply a_isub_binds_tvarish; [ exact HleF | ].
      destruct Hfl as [Hb | [τ' Hb]];
        [ right; left | right; right; exists τ' ]; exact Hb. }
    assert (Heqα : ((β ~ abind_flex_mono_def τ) ++ Θ1) ⊢
                     (ptyp_var_f α) ≡ᵗ C).
    { eapply a_tyequiv__trans.
      - eapply a_tyequiv_subst_def;
          [ exact Hbβ1 | apply mono_ptyp__var | exact Hlcτ ].
      - apply a_tyequiv_weaken_cons. exact HeqmC. }
    destruct (tyequiv_mono_consis_transport_q Heqα Hwf1'
                (mono_ptyp__var α)
                ltac:(intros α0 Hα0; simpl in Hα0;
                      assert (α0 = α) by (clear - Hα0; solve_notin_auto); subst;
                      exact Hbα1))
      as [Hq _].
    replace (bskl_var_f α) with (ptyp_to_bskl_syn (ptyp_var_f α))
      by reflexivity.
    apply Hq. rewrite <- HeqC. exact Hc1.

  - (* Assign-Depend : the pending suffix grows at the TAIL, so the IH's
       context is LITERALLY the conclusion's, re-associated. *)
    intros Θ0 Θ1 Ξ α β P Hne Hβin Ha IHa Hdecl Hwf HwfP.
    assert (Hdecl' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app;
          [ exact Hdecl | apply (a_decls__cons β); apply a_decls__nil ]).
    destruct (IHa Hdecl'
                ltac:(simpl_env; exact Hwf)
                ltac:(simpl_env; exact HwfP))
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    simpl_env in Hle.
    split; [ exact Hle | ].
    split; [ exact Hwf1 | ].
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add β (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { simpl_env. exact Hnd. }
      { eapply faf_tail; eauto. }
      { repeat rewrite dom_app; simpl.
        apply inter_empty_pointwise. intros α0 Hα0Δ HXin.
        assert (Hα0Ξ : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
        assert (Hα0β : α0 `notin` add β (dom Θ0))
          by (clear - Hhd Hα0Δ; fsetdec).
        clear - HXin Hα0Ξ Hα0β. fsetdec. }
      { intros α0 Hα0. assert (HXc := Hcov α0 Hα0).
        repeat rewrite dom_app in *; simpl in *. clear - HXc. fsetdec. }
      { intros α0 Hα0Δ HXd. apply HP;
          [ exact Hα0Δ | simpl; clear - Hhd Hα0Δ HXd; fsetdec ]. }
      split; [ exact IH1 | split; [ exact IH2 | ] ].
      intros α0 Hα0Δ HXd.
      specialize (IH3 α0 Hα0Δ HXd).
      repeat rewrite dom_app in *; simpl in *. clear - IH3. fsetdec. }
    exact Hcons.

  - (* Assign-Skip *)
    intros Θ0 Θ1 Ξ α β P Hne Hβn Hbar Ha IHa Hdecl Hwf HwfP.
    assert (Huniq : uniq (Ξ ++ (β ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IHa Hdecl HwfΞΘ HwfP')
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    (* the walked head misses the output: the rule says so *)
    assert (Hβ1 : β `notin` dom Θ1) by exact Hbar.
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_flex.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__flex; auto | ].
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add β (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
                 (β ~ abind_flex_mono) Θ0). exact Hb. }
      { eapply faf_tail; eauto. }
      { exact HΔΞ. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd. apply HP; auto. simpl.
        assert (α0 `notin` add β (dom Θ0)) by (clear - Hhd Hα0Δ; fsetdec).
        auto. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ | exact IH2 ].
        intros _. apply inter_empty_pointwise.
        intros α0 Hα0Δ HXin.
        assert (Hβ' : α0 `notin` add β (dom Θ0))
          by (clear - Hhd Hα0Δ; fsetdec).
        assert (HΘ1 : α0 `notin` dom Θ1).
        { intro HXd. specialize (IH3 α0 Hα0Δ HXd).
          assert (Hα0Ξ : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
          clear - IH3 Hα0Ξ Hβ'. fsetdec. }
        clear - HXin Hβ' HΘ1. fsetdec.
      + intros α0 Hα0Δ HXd. simpl in HXd.
        assert (Hnex : α0 <> β)
          by (intro; subst; clear - Hhd Hα0Δ; fsetdec).
        assert (HXd1 : α0 `in` dom Θ1) by (clear - HXd Hnex; fsetdec).
        specialize (IH3 α0 Hα0Δ HXd1). simpl.
        clear - IH3. fsetdec. }
    apply ad_pat_consis_weaken_cons. exact Hcons.

  - (* Assign-SkipRigid *)
    intros Θ0 Θ1 Ξ α β P Hβn Hbar Ha IHa Hdecl Hwf HwfP.
    assert (Huniq : uniq (Ξ ++ (β ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IHa Hdecl HwfΞΘ HwfP')
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    (* the walked head misses the output: the rule says so *)
    assert (Hβ1 : β `notin` dom Θ1) by exact Hbar.
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_tvar.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__tvar; auto | ].
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
                 (β ~ abind_tvar) Θ0). exact Hb. }
      { eapply faf_tail; eauto. }
      { exact HΔΞ. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd.
        destruct (eq_var α0 β) as [->|Hnex]; [ exact Hβn | ].
        apply HP; auto; simpl; auto. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ intros Hne; congruence | exact IH2 ].
      + intros α0 Hα0Δ HXd. simpl in HXd. simpl.
        destruct (eq_var α0 β) as [->|Hnex]; [ clear; fsetdec | ].
        assert (HXd1 : α0 `in` dom Θ1) by (clear - HXd Hnex; fsetdec).
        specialize (IH3 α0 Hα0Δ HXd1). clear - IH3. fsetdec. }
    apply ad_pat_consis_weaken_cons. exact Hcons.

  - (* Assign-SkipTmVar (typ) *)
    intros Θ0 Θ1 Ξ α x P3 P Hbar Ha IHa Hdecl Hwf HwfP.
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_typ P3) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hxwf : a_wf_aenv ((x ~ abind_var_typ P3) ++ Θ0))
      by (eapply a_wf_aenv_strip_prefix; eauto).
    apply a_wf_aenv_var_typ_inv in Hxwf.
    destruct Hxwf as [_ [HQwf _]].
    (* a TERM variable cannot occur in a well-formed SKELETON *)
    assert (Hxn : x `notin` ftvar_in_pskl P).
    { intro Hin.
      destruct (a_wf_pskl_ftv_tvarish HwfP Hin) as [HΔ | Ht];
        [ clear - HΔ; fsetdec | ].
      assert (Hbx : binds x (abind_var_typ P3)
                      (Ξ ++ (x ~ abind_var_typ P3) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      destruct Ht as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hb Hbx Huniq) as He;
        discriminate He. }
    assert (HwfP' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IHa Hdecl HwfΞΘ HwfP')
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    assert (Hx1 : x `notin` dom Θ1).
    exact Hbar.
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strengthen_decls_src; eauto).
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_var_typ; [ exact Hle0 | eapply a_wf_ptyp_lc; exact HQwf ]. }
    split.
    { apply a_wf_aenv__var_typ; auto.
      eapply a_wf_ptyp_isub; eauto. }
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add x (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
                 (x ~ abind_var_typ P3) Θ0). exact Hb. }
      { eapply faf_tail; eauto. }
      { exact HΔΞ. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd. apply HP; auto. simpl.
        assert (α0 `notin` add x (dom Θ0)) by (clear - Hhd Hα0Δ; fsetdec).
        auto. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ | exact IH2 ].
        intros _. apply inter_empty_pointwise.
        intros α0 Hα0Δ HXin.
        assert (Hx' : α0 `notin` add x (dom Θ0))
          by (clear - Hhd Hα0Δ; fsetdec).
        assert (HΘ1 : α0 `notin` dom Θ1).
        { intro HXd. specialize (IH3 α0 Hα0Δ HXd).
          assert (Hα0Ξ : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
          clear - IH3 Hα0Ξ Hx'. fsetdec. }
        clear - HXin Hx' HΘ1. fsetdec.
      + intros α0 Hα0Δ HXd. simpl in HXd.
        assert (Hnex : α0 <> x)
          by (intro; subst; clear - Hhd Hα0Δ; fsetdec).
        assert (HXd1 : α0 `in` dom Θ1) by (clear - HXd Hnex; fsetdec).
        specialize (IH3 α0 Hα0Δ HXd1). simpl.
        clear - IH3. fsetdec. }
    apply ad_pat_consis_weaken_cons. exact Hcons.

  - (* Assign-SkipTmVar (skl) *)
    intros Θ0 Θ1 Ξ α x P3 P Hbar Ha IHa Hdecl Hwf HwfP.
    assert (Huniq : uniq (Ξ ++ (x ~ abind_var_skl P3) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (repeat rewrite dom_app in *; solve_uniq).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hxwf : a_wf_aenv ((x ~ abind_var_skl P3) ++ Θ0))
      by (eapply a_wf_aenv_strip_prefix; eauto).
    apply a_wf_aenv_var_skl_inv in Hxwf.
    destruct Hxwf as [_ [HQwf _]].
    assert (Hxn : x `notin` ftvar_in_pskl P).
    { intro Hin.
      destruct (a_wf_pskl_ftv_tvarish HwfP Hin) as [HΔ | Ht];
        [ clear - HΔ; fsetdec | ].
      assert (Hbx : binds x (abind_var_skl P3)
                      (Ξ ++ (x ~ abind_var_skl P3) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      destruct Ht as [Hb | [Hb | [τ0 Hb]]];
        pose proof (binds_unique _ _ _ _ _ Hb Hbx Huniq) as He;
        discriminate He. }
    assert (HwfP' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P)
      by (eapply a_wf_pskl_strip_mid; eauto).
    destruct (IHa Hdecl HwfΞΘ HwfP')
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    assert (Hx1 : x `notin` dom Θ1).
    exact Hbar.
    assert (Hle0 : Θ0 ⊴ Θ1)
      by (eapply a_isub_strengthen_decls_src; eauto).
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_var_skl; [ exact Hle0 | eapply a_scope_pskl_lc; exact HQwf ]. }
    split.
    { apply a_wf_aenv__var; auto.
      eapply a_scope_pskl_isub; eauto. }
    split.
    { clear - Hdom. repeat rewrite dom_app in *; simpl in *. fsetdec. }
    split.
    { intros Δ Hnd Hfaf HΔΞ Hcov HP.
      assert (Hhd : Δ ∩ (add x (dom Θ0)) [=] empty)
        by (apply (faf_head Hfaf); discriminate).
      destruct (Hinv Δ) as [IH1 [IH2 IH3]].
      { intros β' τ' Hb. apply (Hnd β' τ').
        apply (@binds_insert_mid (abind_flex_mono_def τ') β' Ξ
                 (x ~ abind_var_skl P3) Θ0). exact Hb. }
      { eapply faf_tail; eauto. }
      { exact HΔΞ. }
      { (* the IH's OUTPUT-relative coverage: a Δ-name in the sub-run's
           output is in the conclusion's too, and it is not the walked head
           (the rule's own premise says the head misses that output) *)
        intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar.
        repeat rewrite dom_app in *. simpl in *. fsetdec. }
      { intros α0 Hα0Δ HXd. apply HP; auto. simpl.
        assert (α0 `notin` add x (dom Θ0)) by (clear - Hhd Hα0Δ; fsetdec).
        auto. }
      split; [ | split ].
      + intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (IH1 β' τ' Hb') ].
      + apply faf_cons; [ | exact IH2 ].
        intros _. apply inter_empty_pointwise.
        intros α0 Hα0Δ HXin.
        assert (Hx' : α0 `notin` add x (dom Θ0))
          by (clear - Hhd Hα0Δ; fsetdec).
        assert (HΘ1 : α0 `notin` dom Θ1).
        { intro HXd. specialize (IH3 α0 Hα0Δ HXd).
          assert (Hα0Ξ : α0 `notin` dom Ξ) by (clear - HΔΞ Hα0Δ; fsetdec).
          clear - IH3 Hα0Ξ Hx'. fsetdec. }
        clear - HXin Hx' HΘ1. fsetdec.
      + intros α0 Hα0Δ HXd. simpl in HXd.
        assert (Hnex : α0 <> x)
          by (intro; subst; clear - Hhd Hα0Δ; fsetdec).
        assert (HXd1 : α0 `in` dom Θ1) by (clear - HXd Hnex; fsetdec).
        specialize (IH3 α0 Hα0Δ HXd1). simpl.
        clear - IH3. fsetdec. }
    apply ad_pat_consis_weaken_cons. exact Hcons.
  - (* U-Flex-Flex-Id *)
    intros Θ0 α Hb Hwf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    apply a_tyequiv__refl. constructor.
  - (* U-Flex-Flex-L : α̂ := β̂ *)
    intros Θ0 α β Hne Hfβ Hwf.
    assert (Hαd : α `notin` dom Θ0) by (inversion Hwf; auto).
    assert (Hwf0 : a_wf_aenv Θ0) by (inversion Hwf; auto).
    assert (Hbβ : a_binds_tvar β Θ0)
      by (destruct Hfβ as [Hb | [τ Hb]];
          [ right; left | right; right; exists τ ]; exact Hb).
    assert (Hβd : β `in` dom Θ0)
      by (destruct Hfβ as [Hb | [τ Hb]]; apply binds_In in Hb; auto).
    split.
    { split.
      - destruct (a_inc_refl_gen
          (Ξ0 := (α ~ abind_flex_mono_def (ptyp_var_f β)))
          (a_wf_aenv_lc_aenv Hwf0))
          as [κ0 [Hid0 Hinc0]].
        { apply (a_suffix__cons α (b := abind_flex_mono_def (ptyp_var_f β)));
            constructor. }
        exists ((α, ptyp_var_f α) :: κ0). split.
        { constructor; auto. unfold is_id_entry; reflexivity. }
        apply a_inc__flex; auto;
          try (apply a_wf_ptyp__var; right; right;
               exists (ptyp_var_f β); unfold binds; left; reflexivity);
          try constructor.
      - intros α1 τ0 Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | ].
        simpl. unfold binds. right. auto. }
    split.
    { apply a_wf_aenv__flex_def; auto.
      - apply a_wf_ptyp__var; exact Hbβ.
      - constructor. }
    split; [ simpl; clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      assert (Hhd : Δ ∩ (add α (dom Θ0)) [=] empty)
        by (apply (faf_head Hfa); discriminate).
      split; [ | split ].
      - intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
        + inversion Heq; subst. simpl.
          apply inter_empty_pointwise. intros α0 Hα0Δ Hα0β.
          assert (α0 = β) by (clear - Hα0β; fsetdec). subst.
          clear - Hhd Hα0Δ Hβd. fsetdec.
        + apply (Hnd β' τ'). unfold binds; right; exact Hb'.
      - apply faf_cons; [ | eapply faf_tail; eauto ].
        intros _. simpl. exact Hhd.
      - intros α0 Hα0Δ HXd. simpl in *. exact HXd. }
    apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - (* U-Flex-Flex-R : β̂ := α̂ *)
    intros Θ0 α β Hne Hfα Hwf.
    assert (Hβd : β `notin` dom Θ0) by (inversion Hwf; auto).
    assert (Hwf0 : a_wf_aenv Θ0) by (inversion Hwf; auto).
    assert (Hbα : a_binds_tvar α Θ0)
      by (destruct Hfα as [Hb | [τ Hb]];
          [ right; left | right; right; exists τ ]; exact Hb).
    assert (Hαd : α `in` dom Θ0)
      by (destruct Hfα as [Hb | [τ Hb]]; apply binds_In in Hb; auto).
    split.
    { split.
      - destruct (a_inc_refl_gen
          (Ξ0 := (β ~ abind_flex_mono_def (ptyp_var_f α)))
          (a_wf_aenv_lc_aenv Hwf0))
          as [κ0 [Hid0 Hinc0]].
        { apply (a_suffix__cons β (b := abind_flex_mono_def (ptyp_var_f α)));
            constructor. }
        exists ((β, ptyp_var_f β) :: κ0). split.
        { constructor; auto. unfold is_id_entry; reflexivity. }
        apply a_inc__flex; auto;
          try (apply a_wf_ptyp__var; right; right;
               exists (ptyp_var_f α); unfold binds; left; reflexivity);
          try constructor.
      - intros α1 τ0 Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | ].
        simpl. unfold binds. right. auto. }
    split.
    { apply a_wf_aenv__flex_def; auto.
      - apply a_wf_ptyp__var; exact Hbα.
      - constructor. }
    split; [ simpl; clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      assert (Hhd : Δ ∩ (add β (dom Θ0)) [=] empty)
        by (apply (faf_head Hfa); discriminate).
      split; [ | split ].
      - intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'].
        + inversion Heq; subst. simpl.
          apply inter_empty_pointwise. intros α0 Hα0Δ Hα0α.
          assert (α0 = α) by (clear - Hα0α; fsetdec). subst.
          clear - Hhd Hα0Δ Hαd. fsetdec.
        + apply (Hnd β' τ'). unfold binds; right; exact Hb'.
      - apply faf_cons; [ | eapply faf_tail; eauto ].
        intros _. simpl. exact Hhd.
      - intros α0 Hα0Δ HXd. simpl in *. exact HXd. }
    apply a_tyequiv__sym.
    apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - (* U-Flex-Flex-Assign : the consistency premise, through the BRIDGE *)
    intros Θ0 Θ1 α1 τ α β P3 Hfα Hfβ Hbar Hcons IHcons Hwf.
    inversion Hwf as [ | | γx τx Θx Hγd Hwτ Hmτ Hwf0 | | | ]; subst.
    (* the substituted subjects are visible monotypes over Θ0 *)
    assert (Hτvis : forall α0, α0 `in` ftvar_in_ptyp τ -> a_binds_tvar α0 Θ0)
      by (intros α0 Hα0; eapply a_wf_ptyp_ftv_tvarish; eauto).
    assert (Hsubvis : forall β1,
        a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β1 ->
        forall α0, α0 `in` ftvar_in_ptyp (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β1)) ->
        a_binds_tvar α0 Θ0).
    { intros β1 Hfδ α0 Hα0.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                    (ptyp_var_f β1) τ α1) as Hup.
      assert (HX' : α0 `in` (ftvar_in_ptyp τ `union`
                            remove α1 (ftvar_in_ptyp (ptyp_var_f β1))))
        by (clear - Hα0 Hup; fsetdec).
      destruct (union_1 HX') as [Hτ | Hβ1]; [ auto | ].
      simpl in Hβ1.
      assert (Hα0δ : α0 = β1) by (clear - Hβ1; fsetdec).
      assert (Hα0γ : α0 <> α1) by (clear - Hβ1; fsetdec).
      subst α0.
      destruct Hfδ as [Hb | [τ' Hb]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx ?] | Hb'];
        try solve [ exfalso; apply Hα0γ; exact Heqx ];
        [ right; left | right; right; exists τ' ]; exact Hb'. }
    assert (HmA' : mono_ptyp (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α)))
      by (apply mono_ptyp_subst; [ constructor | exact Hmτ ]).
    assert (HmB' : mono_ptyp (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
      by (apply mono_ptyp_subst; [ constructor | exact Hmτ ]).
    destruct (IHcons Hwf0) as
        [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [HconsQ Hrs]]] _]]]]].
    { apply mono_ptyp_wf_pskl; [ exact HmB' | apply (Hsubvis β Hfβ) ]. }
    { apply mono_ptyp_wf_pskl; [ exact HmA' | apply (Hsubvis α Hfα) ]. }
    { intros α0 Hα0. exfalso. clear - Hα0. fsetdec. }
    { intros β' τ' _. clear. fsetdec. }
    { intros Θa βa ba Θb Heq Hne. clear. fsetdec. }
    assert (Hγd1 : α1 `notin` dom Θ1) by exact Hbar.
    split.
    { apply a_isub_cons_flex_def; auto. apply mono_ptyp_lc; auto. }
    split.
    { apply a_wf_aenv__flex_def; auto.
      apply mono_ptyp_wf; [ exact Hmτ | ].
      intros α0 Hα0. eapply a_isub_binds_tvarish; eauto. }
    split; [ simpl; clear - Hdom; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      assert (Hhd : Δ ∩ (add α1 (dom Θ0)) [=] empty)
        by (apply (faf_head Hfa); discriminate).
      assert (Hτfree : Δ ∩ ftvar_in_ptyp τ [=] empty)
        by (apply (Hnd α1 τ); unfold binds; left; reflexivity).
      assert (Hsubfree : forall β1,
          a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β1 ->
          forall α0, α0 `in` Δ ->
          α0 `notin` ftvar_in_pskl
              (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β1)))).
      { intros β1 Hfδ α0 Hα0Δ.
        rewrite ftvar_ptyp_to_pskl.
        pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                      (ptyp_var_f β1) τ α1) as Hup.
        intros HXin.
        assert (HX' : α0 `in` (ftvar_in_ptyp τ `union`
                              remove α1 (ftvar_in_ptyp (ptyp_var_f β1))))
          by (clear - HXin Hup; fsetdec).
        simpl in HX'.
        assert (Hδd : β1 `in` add α1 (dom Θ0)).
        { destruct Hfδ as [Hb | [τ' Hb]]; apply binds_In in Hb;
            simpl in Hb; clear - Hb; fsetdec. }
        clear - Hτfree Hα0Δ HX' Hhd Hδd. fsetdec. }
      destruct (Hinv Δ) as [Hnd1 [Hfa1 Hbk1]].
      { eapply no_flex_dep_tail; eauto. }
      { eapply faf_tail; eauto. }
      { intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar. simpl in *. fsetdec. }
      { intros α0 Hα0 _.
        pose proof (Hsubfree β Hfβ α0 Hα0).
        pose proof (Hsubfree α Hfα α0 Hα0).
        clear - H H0. fsetdec. }
      split; [ | split ].
      - intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ inversion Heq; subst; exact Hτfree
          | exact (Hnd1 β' τ' Hb') ].
      - apply faf_cons; [ | exact Hfa1 ].
        intros _.
        apply inter_empty_pointwise. intros α0 Hα0Δ HXin.
        assert (Hα0γ : α0 <> α1) by (clear - Hhd Hα0Δ; fsetdec).
        assert (HXd : α0 `in` dom Θ1) by (clear - HXin Hα0γ; fsetdec).
        pose proof (Hbk1 α0 Hα0Δ HXd) as HX0.
        clear - Hhd Hα0Δ HX0. fsetdec.
      - intros α0 Hα0Δ HXd. simpl in HXd.
        assert (Hα0γ : α0 <> α1) by (clear - Hhd Hα0Δ; fsetdec).
        assert (HXd1 : α0 `in` dom Θ1) by (clear - HXd Hα0γ; fsetdec).
        pose proof (Hbk1 α0 Hα0Δ HXd1) as HX0.
        simpl. clear - HX0. fsetdec. }
    (* the type equivalence, via the BRIDGE *)
    assert (HeqAB : Θ1 ⊢ (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))
                       ≡ᵗ (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β))).
    { eapply consis_refine_mono_tyequiv with (Qt := Qt); eauto.
      - rewrite <- ptyp_to_uskl_syn_eq. exact HconsQ.
      - apply ad_refine_syn_f_forget with (F := empty). exact Hrs. }
    assert (Hlcτ : lc_ptyp τ) by (apply mono_ptyp_lc; assumption).
    assert (Hbγ : binds α1 (abind_flex_mono_def τ)
                    ((α1 ~ abind_flex_mono_def τ) ++ Θ1))
      by (unfold binds; left; reflexivity).
    eapply a_tyequiv__trans.
    { eapply a_tyequiv_subst_def; eauto. constructor. }
    eapply a_tyequiv__trans.
    { apply a_tyequiv_weaken_cons. exact HeqAB. }
    apply a_tyequiv__sym.
    eapply a_tyequiv_subst_def; eauto. constructor.
  - (* U-Flex-Flex-Skip *)
    intros Θ0 Θ1 α1 α β Hnα Hnβ Hbar Hu IHu Hwf.
    inversion Hwf as [ | γx Θx Hγd Hwf0 | | | | ]; subst.
    destruct (IHu Hwf0) as [Hle [Hwf1 [Hdom [Hinv Heq1]]]].
    assert (Hγd1 : α1 `notin` dom Θ1) by exact Hbar.
    split; [ apply a_isub_cons_flex; auto | ].
    split; [ apply a_wf_aenv__flex; auto | ].
    split; [ simpl; clear - Hdom; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      assert (Hhd : Δ ∩ (add α1 (dom Θ0)) [=] empty)
        by (apply (faf_head Hfa); discriminate).
      destruct (Hinv Δ) as [Hnd1 [Hfa1 Hbk1]].
      { eapply no_flex_dep_tail; eauto. }
      { eapply faf_tail; eauto. }
      { intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar. simpl in *. fsetdec. }
      split; [ | split ].
      - intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
          [ discriminate | exact (Hnd1 β' τ' Hb') ].
      - apply faf_cons; [ | exact Hfa1 ].
        intros _.
        apply inter_empty_pointwise. intros α0 Hα0Δ HXin.
        assert (Hα0γ : α0 <> α1) by (clear - Hhd Hα0Δ; fsetdec).
        assert (HXd : α0 `in` dom Θ1) by (clear - HXin Hα0γ; fsetdec).
        pose proof (Hbk1 α0 Hα0Δ HXd) as HX0.
        clear - Hhd Hα0Δ HX0. fsetdec.
      - intros α0 Hα0Δ HXd. simpl in HXd.
        assert (Hα0γ : α0 <> α1) by (clear - Hhd Hα0Δ; fsetdec).
        assert (HXd1 : α0 `in` dom Θ1) by (clear - HXd Hα0γ; fsetdec).
        pose proof (Hbk1 α0 Hα0Δ HXd1) as HX0.
        simpl. clear - HX0. fsetdec. }
    apply a_tyequiv_weaken_cons. exact Heq1.
  - (* U-Flex-Flex-Skip' *)
    intros Θ0 Θ1 c b α β Hb Hbar Hu IHu Hwf.
    assert (Hwf0c : a_wf_aenv Θ0 /\ c `notin` dom Θ0).
    { destruct Hb as [-> | [[Qb ->] | [Qb ->]]].
      - apply a_wf_aenv_tvar_inv in Hwf; tauto.
      - apply a_wf_aenv_var_typ_inv in Hwf; destruct Hwf as [? [? ?]]; auto.
      - apply a_wf_aenv_var_skl_inv in Hwf; destruct Hwf as [? [? ?]]; auto. }
    destruct Hwf0c as [Hwf0 Hcd].
    destruct (IHu Hwf0) as [Hle [Hwf1 [Hdom [Hinv Heq1]]]].
    assert (Hcd1 : c `notin` dom Θ1) by exact Hbar.
    split.
    { destruct Hb as [-> | [[Qb ->] | [Qb ->]]];
        [ apply a_isub_cons_tvar; auto
        | apply a_isub_cons_var_typ; auto;
          apply a_wf_aenv_var_typ_inv in Hwf; destruct Hwf as [_ [HQwf _]];
          eapply a_wf_ptyp_lc; exact HQwf
        | apply a_isub_cons_var_skl; auto;
          apply a_wf_aenv_var_skl_inv in Hwf; destruct Hwf as [_ [HQwf _]];
          eapply a_scope_pskl_lc; exact HQwf ]. }
    split.
    { destruct Hb as [-> | [[Qb ->] | [Qb ->]]].
      - apply a_wf_aenv__tvar; auto.
      - apply a_wf_aenv__var_typ; auto.
        apply a_wf_ptyp_isub with (Θ := Θ0); auto.
        apply a_wf_aenv_var_typ_inv in Hwf; tauto.
      - apply a_wf_aenv__var; auto.
        apply a_scope_pskl_isub with (Θ := Θ0); auto.
        apply a_wf_aenv_var_skl_inv in Hwf; tauto. }
    split; [ simpl; clear - Hdom; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov.
      destruct (Hinv Δ) as [Hnd1 [Hfa1 Hbk1]].
      { eapply no_flex_dep_tail; eauto. }
      { eapply faf_tail; eauto. }
      { intros α0 Hα0.
        assert (HXc := Hcov α0 ltac:(clear - Hα0; simpl; solve_notin_auto)).
        clear - HXc Hα0 Hbar. simpl in *. fsetdec. }
      split; [ | split ].
      - intros β' τ' Hb'.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb') as [[? Heq] | Hb''];
          [ | exact (Hnd1 β' τ' Hb'') ].
        exfalso.
        destruct Hb as [Hb2 | [[Qb Hb2] | [Qb Hb2]]]; subst; congruence.
      - apply faf_cons; [ | exact Hfa1 ].
        intros Hne.
        assert (Hhd : Δ ∩ (add c (dom Θ0)) [=] empty)
          by (apply (faf_head Hfa); exact Hne).
        apply inter_empty_pointwise. intros α0 Hα0Δ HXin.
        assert (HXc : α0 <> c) by (clear - Hhd Hα0Δ; fsetdec).
        assert (HXd : α0 `in` dom Θ1) by (clear - HXin HXc; fsetdec).
        pose proof (Hbk1 α0 Hα0Δ HXd) as HX0.
        clear - Hhd Hα0Δ HX0. fsetdec.
      - intros α0 Hα0Δ HXd. simpl in HXd.
        destruct (α0 == c) as [->|HXc]; [ simpl; clear; fsetdec | ].
        assert (HXd1 : α0 `in` dom Θ1) by (clear - HXd HXc; fsetdec).
        pose proof (Hbk1 α0 Hα0Δ HXd1) as HX0.
        simpl. clear - HX0. fsetdec. }
    apply a_tyequiv_weaken_cons. exact Heq1.
  - (* C-Ghost *)
    intros Δ1 Δ2 Θ0 P0 Hint Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _ _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    split.
    + exists (pskl_to_bskl_inh P0).
      split; [ apply bskl_to_pskl_pskl_to_bskl_inh | ].
      split.
      * apply ad_pat_consis__hole; [ fsetdec | exact HwfP0 ].
      * apply ad_refine_syn_f_refl_inh.
        eapply a_wf_pskl_delta_mono; [ exact HwfP0 | fsetdec ].
    + apply ad_refine_pskl_f__hole; [ exact Hint | exact HwfP0 ].
  - (* C-Unit *)
    intros Δ1 Δ2 Θ0 Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _ _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    split.
    + exists bskl_unit. split; [ reflexivity | ].
      split; [ apply ad_pat_consis__unit; fsetdec
             | apply ad_refine_syn_f__unit ].
    + apply ad_refine_pskl_f__unit.
  - (* C-Rigid *)
    intros Δ1 Δ2 Θ0 α Hbind Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _ _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__var; [ fsetdec | left; exact Hbind ].
      * apply ad_refine_syn_f__var. right; left; exact Hbind.
    + apply ad_refine_pskl_f__var. right; left; exact Hbind.
  - (* C-Arrow *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2
           Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    inversion HwfP0 as [ | | Θa Δa P0a' P0b' HwfP0a HwfP0b | | | ]; subst.
    inversion HwfP as [ | | Θb Δb P1' P2' HwfP1 HwfP2 | | | ]; subst.
    assert (Hft12 : forall (R : atoms) α0, α0 `in` (Δ1 `union` Δ2) ->
              α0 `notin` dom Θ0 -> α0 `notin` R).
    { intros R α0 Hα0 HXd. exfalso. apply HXd.
      eapply binds_In. apply Hrig. exact Hα0. }
    assert (Hcov12 : forall (Θx : aenv), ((Δ1 `union` Δ2) ∩ dom Θx) [<=] dom Θ0).
    { intros Θx α0 Hα0.
      assert (Hα0' : α0 `in` (Δ1 `union` Δ2)) by (clear - Hα0; fsetdec).
      apply Hrig in Hα0'. apply binds_In in Hα0'. exact Hα0'. }
    destruct (IH1 Hwf HwfP0a HwfP1 Hrig Hnfd Hfaf)
      as [Hle1 [Hwf1 [Hdom1 [Hinv1 [[Qt1 [HeQt1 [Hcons1 Hrs1]]] Hrp1]]]]].
    destruct (Hinv1 (Δ1 `union` Δ2) Hnfd Hfaf (Hcov12 _) (Hft12 _))
      as [Hnfd1 [Hfaf1 _]].
    assert (Hrig1 : forall α0, α0 `in` (Δ1 `union` Δ2) ->
              binds α0 abind_tvar Θ1)
      by (intros α0 Hα0; eapply a_isub_binds_tvar; eauto).
    destruct (IH2 Hwf1) as
        [Hle2 [Hwf2 [Hdom2 [Hinv2 [[Qt2 [HeQt2 [Hcons2 Hrs2]]] Hrp2]]]]];
      auto.
    { eapply a_wf_pskl_isub; eauto. }
    { eapply a_wf_pskl_isub; eauto. }
    split; [ eapply a_isub_trans; eauto | ].
    split; [ exact Hwf2 | ].
    split; [ clear - Hdom1 Hdom2; fsetdec | ].
    split.
    { intros Δ Hnd Hfa Hcov Hft.
      destruct (Hinv1 Δ Hnd Hfa ltac:(clear - Hcov Hdom2; solve_notin_auto))
        as [Hnd1' [Hfa1' Hbk1']].
      { intros α0 Hα0 HXd HXin. apply (Hft α0 Hα0 HXd).
        simpl. clear - HXin. fsetdec. }
      destruct (Hinv2 Δ Hnd1' Hfa1') as [Hnd2' [Hfa2' Hbk2']].
      { clear - Hcov Hdom1. fsetdec. }
      { intros α0 Hα0 HXd HXin.
        apply (Hft α0 Hα0).
        - intros HXin0. apply HXd. apply Hdom1. exact HXin0.
        - simpl. clear - HXin. fsetdec. }
      split; [ exact Hnd2' | ]. split; [ exact Hfa2' | ].
      intros α0 Hα0 HXd. apply (Hbk1' α0 Hα0). apply (Hbk2' α0 Hα0). exact HXd. }
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
  - (* C-ForallInh : ∀α.P ∼ ∀α.P3 against input ∀α.P0 *)
    (* cluster 4: the opener is the RULE's now.  Two consequences — the wf
       judgments' cofinite bounds have no reason to avoid it (so instantiate
       them AT α with [a_wf_pskl_all_inv_at]), and the freshness facts the
       old [pick fresh] supplied must be REBUILT: the input-side ones from
       the rule's own side condition, [α ∉ dom Θ1] from the premise's output
       well-formedness, and [α ∉ ftv P3] for free, since the conclusion's
       output is [close α Q]. *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfrα Hprem0 IH Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfrα; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Hfrα; fsetdec).
    assert (HαΔ1 : α `notin` Δ1) by (clear - Hfrα; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Hfrα; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfrα H; fsetdec).
    remember (close_pskl_wrt_pskl α Q) as P3 eqn:HeqP3.
    assert (HαP3 : α `notin` ftvar_in_pskl P3)
      by (subst P3; rewrite ftvar_in_pskl_close_pskl_wrt_pskl;
          clear; fsetdec).
    assert (HQP3 : Q = open_pskl_wrt_pskl P3 (pskl_var_f α))
      by (subst P3; symmetry;
          apply open_pskl_wrt_pskl_close_pskl_wrt_pskl).
    rewrite HQP3 in Hprem0, IH.
    assert (Hpostα : consis_sound_post (add α Δ1) (add α Δ2)
                       ((α ~ abind_tvar) ++ Θ0)
                       (open_pskl_wrt_pskl P0 (pskl_var_f α))
                       (open_pskl_wrt_pskl P (pskl_var_f α))
                       (open_pskl_wrt_pskl P3 (pskl_var_f α))
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply IH.
      - apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ].
      - eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc (a_wf_pskl_all_inv_at HwfP0 HαP0) α)
          | clear; fsetdec ].
      - eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc (a_wf_pskl_all_inv_at HwfP HαP) α)
          | clear; fsetdec ].
      - intros α0 Hα0. destruct (α0 == α) as [->|Hne].
        + unfold binds; left; reflexivity.
        + unfold binds; right. apply Hrig. clear - Hα0 Hne. fsetdec.
      - apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
          [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ].
      - apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
          [ clear; fsetdec
          | apply faf_open_tvar; auto; clear - HαΔ1 HαΔ2; fsetdec ]. }
    destruct Hpostα
      as [Hleα [Hwfα [Hdomα [Hinvα [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
    assert (Hwf1 : a_wf_aenv Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Hα1 : α `notin` dom Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Fr : α `notin` (dom Θ0 `union` dom Θ1 `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl P3
                  `union` Δ1 `union` Δ2))
      by (clear - HαΘ0 Hα1 HαP0 HαP HαP3 HαΔ1 HαΔ2; fsetdec).
    assert (Hdefsα : forall β τ, binds β (abind_flex_mono_def τ) Θ1 ->
                     α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      pose proof (@a_wf_aenv_def_ftv_dom Θ1 β τ Hwf1 Hb) as Hsc.
      clear - Hsc Hα1. fsetdec. }
    split; [ eapply a_isub_strip_tvar; eauto | ].
    split; [ exact Hwf1 | ].
    split.
    { intros x Hx.
      assert (Hx1 : x `in` dom ((α ~ abind_tvar) ++ Θ1))
        by (apply Hdomα; simpl; clear - Hx; fsetdec).
      simpl in Hx1.
      assert (Hxα : x <> α) by (intros ->; clear - Fr Hx; fsetdec).
      clear - Hx1 Hxα. fsetdec. }
    split.
    { intros Δ HndΔ HfaΔ HcovΔ Hft.
      (* the old proof picked a SECOND fresh atom here, only so that it could
         miss [Δ]; the rule's opener cannot, but it does not have to — the
         [α0 = α] branch below is refuted by [α ∉ dom Θ1] instead *)
      destruct (Hinvα Δ) as [Hnd' [Hfa' Hbk']].
      { intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
          [ discriminate | exact (HndΔ β' τ' Hb') ]. }
      { apply faf_cons;
          [ intros Hne; exfalso; apply Hne; reflexivity | exact HfaΔ ]. }
      { simpl. clear - HcovΔ. fsetdec. }
      { intros α0 Hα0 HXd.
        simpl in HXd.
        assert (HXd0 : α0 `notin` dom Θ0) by (clear - HXd; fsetdec).
        assert (Hα0α2 : α0 <> α) by (clear - HXd; fsetdec).
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                      P0 (pskl_var_f α)) as Hup0.
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                      P (pskl_var_f α)) as Hup1.
        specialize (Hft α0 Hα0 HXd0).
        simpl in Hup0, Hup1.
        clear - Hft Hup0 Hup1 Hα0α2. fsetdec. }
      split.
      { intros β' τ' Hb'. apply (Hnd' β' τ').
        unfold binds; right; exact Hb'. }
      split.
      { eapply faf_tail. exact Hfa'. }
      { intros α0 Hα0 HXd.
        assert (HX1 : α0 `in` dom ((α ~ abind_tvar) ++ Θ1))
          by (simpl; clear - HXd; fsetdec).
        pose proof (Hbk' α0 Hα0 HX1) as HX0. simpl in HX0.
        assert (Hα0α2 : α0 <> α) by (intros ->; clear - Hα1 HXd; fsetdec).
        clear - HX0 Hα0α2. fsetdec. } }
    split.
    + exists (bskl_all_inh (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; fsetdec ]. }
      split.
      * simpl. apply ad_pat_consis__forall_inh_untagged
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P).
        intros α0 Hα0.
        rewrite (subst_bskl_in_uskl_intro α (pskl_to_uskl P) (uskl_var_f α0));
          [ | rewrite ftvar_in_uskl_pskl; clear - Fr; fsetdec ].
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ | exact Hα1 | exact Hdefsα ].
        rewrite <- pskl_to_uskl_open_var. exact Hconsα.
      * change (pskl_to_bskl_inh (pskl_all_syn P0))
          with (bskl_all_inh (pskl_to_bskl_inh P0)).
        apply ad_refine_syn_f__all
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P0).
        intros α0 Hα0.
        rewrite <- pskl_to_bskl_inh_open.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        assert (Hfr0 : α `notin` ftvar_in_pskl P0) by (clear - Fr; fsetdec).
        rewrite (subst_pskl_in_pskl_intro α P0 (pskl_var_f α0) Hfr0).
        rewrite <- subst_var_bskl_inh.
        eapply ad_refine_syn_f_fmono with (F' := add α Δ1);
          [ clear; fsetdec | ].
        eapply ad_refine_syn_f_delta_mono;
          [ | instantiate (1 := add α0 (remove α (add α Δ1)));
              clear Fr; fsetdec ].
        apply ad_refine_syn_f_rename;
          [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
        exact (ad_refine_syn_f_strip nil Θ1 Hrsα
                 ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
    + simpl. apply ad_refine_pskl_f__all
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_pskl P `union` ftvar_in_pskl P3).
      intros α0 Hα0.
      rewrite (subst_pskl_in_pskl_intro α P (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      rewrite (subst_pskl_in_pskl_intro α P3 (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      eapply ad_refine_pskl_f_fmono with (F' := add α Δ2);
        [ clear; fsetdec | ].
      eapply ad_refine_pskl_f_delta_mono;
        [ | instantiate (1 := add α0 (remove α (add α Δ2)));
            clear Fr; fsetdec ].
      apply ad_refine_pskl_f_rename;
        [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
      exact (ad_refine_pskl_f_strip nil Θ1 Hrpα
               ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
  - (* C-ForallSyn : ∀α.P ∼ ∀α.P3 against input ∀◇P0 *)
    (* cluster 4: exists-fresh opener — see C-ForallInh for the pattern *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfrα Hprem0 IH Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    inversion HwfP0 as [ | | | | | Θc Δc P0c Hg0 Hwf0c Heqc ]; subst.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfrα; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Hfrα; fsetdec).
    assert (HαΔ1 : α `notin` Δ1) by (clear - Hfrα; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Hfrα; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfrα H; fsetdec).
    remember (close_pskl_wrt_pskl α Q) as P3 eqn:HeqP3.
    assert (HαP3 : α `notin` ftvar_in_pskl P3)
      by (subst P3; rewrite ftvar_in_pskl_close_pskl_wrt_pskl;
          clear; fsetdec).
    assert (HQP3 : Q = open_pskl_wrt_pskl P3 (pskl_var_f α))
      by (subst P3; symmetry;
          apply open_pskl_wrt_pskl_close_pskl_wrt_pskl).
    rewrite HQP3 in Hprem0, IH.
    assert (Hpostα : consis_sound_post Δ1 (add α Δ2)
                       ((α ~ abind_tvar) ++ Θ0)
                       (pskl_tophole P0)
                       (open_pskl_wrt_pskl P (pskl_var_f α))
                       (open_pskl_wrt_pskl P3 (pskl_var_f α))
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply IH.
      - apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ].
      - apply a_wf_pskl__tophole; auto.
        eapply a_wf_pskl_weaken; [ | exact Hwf0c ].
        intros y b Hb. unfold binds; right; exact Hb.
      - eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc (a_wf_pskl_all_inv_at HwfP HαP) α)
          | clear; fsetdec ].
      - intros α0 Hα0. destruct (α0 == α) as [->|Hne].
        + unfold binds; left; reflexivity.
        + unfold binds; right. apply Hrig. clear - Hα0 Hne. fsetdec.
      - apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
          [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ].
      - apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
          [ clear; fsetdec
          | apply faf_open_tvar; auto; clear - HαΔ1 HαΔ2; fsetdec ]. }
    destruct Hpostα
      as [Hleα [Hwfα [Hdomα [Hinvα [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
    assert (Hwf1 : a_wf_aenv Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Hα1 : α `notin` dom Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Fr : α `notin` (dom Θ0 `union` dom Θ1 `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl P3
                  `union` Δ1 `union` Δ2))
      by (clear - HαΘ0 Hα1 HαP0 HαP HαP3 HαΔ1 HαΔ2; fsetdec).
    assert (Hdefsα : forall β τ, binds β (abind_flex_mono_def τ) Θ1 ->
                     α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      pose proof (@a_wf_aenv_def_ftv_dom Θ1 β τ Hwf1 Hb) as Hsc.
      clear - Hsc Hα1. fsetdec. }
    split; [ eapply a_isub_strip_tvar; eauto | ].
    split; [ exact Hwf1 | ].
    split.
    { intros x Hx.
      assert (Hx1 : x `in` dom ((α ~ abind_tvar) ++ Θ1))
        by (apply Hdomα; simpl; clear - Hx; fsetdec).
      simpl in Hx1.
      assert (Hxα : x <> α) by (intros ->; clear - Fr Hx; fsetdec).
      clear - Hx1 Hxα. fsetdec. }
    split.
    { intros Δ HndΔ HfaΔ HcovΔ Hft.
      (* the rule's opener replaces the old second fresh atom; the
         [α0 = α] branch is refuted by [α ∉ dom Θ1] *)
      destruct (Hinvα Δ) as [Hnd' [Hfa' Hbk']].
      { intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
          [ discriminate | exact (HndΔ β' τ' Hb') ]. }
      { apply faf_cons;
          [ intros Hne; exfalso; apply Hne; reflexivity | exact HfaΔ ]. }
      { simpl. clear - HcovΔ. fsetdec. }
      { intros α0 Hα0 HXd.
        simpl in HXd.
        assert (HXd0 : α0 `notin` dom Θ0) by (clear - HXd; fsetdec).
        assert (Hα0α2 : α0 <> α) by (clear - HXd; fsetdec).
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                      P (pskl_var_f α)) as Hup1.
        specialize (Hft α0 Hα0 HXd0).
        simpl in Hft, Hup1.
        clear - Hft Hup1 Hα0α2. fsetdec. }
      split.
      { intros β' τ' Hb'. apply (Hnd' β' τ').
        unfold binds; right; exact Hb'. }
      split.
      { eapply faf_tail. exact Hfa'. }
      { intros α0 Hα0 HXd.
        assert (HX1 : α0 `in` dom ((α ~ abind_tvar) ++ Θ1))
          by (simpl; clear - HXd; fsetdec).
        pose proof (Hbk' α0 Hα0 HX1) as HX0. simpl in HX0.
        assert (Hα0α2 : α0 <> α) by (intros ->; clear - Hα1 HXd; fsetdec).
        clear - HX0 Hα0α2. fsetdec. } }
    split.
    + exists (bskl_all_syn (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; fsetdec ]. }
      split.
      * simpl. apply ad_pat_consis__forall_syn
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P).
        intros α0 Hα0.
        rewrite (subst_bskl_in_uskl_intro α (pskl_to_uskl P) (uskl_var_f α0));
          [ | rewrite ftvar_in_uskl_pskl; clear - Fr; fsetdec ].
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ | exact Hα1 | exact Hdefsα ].
        rewrite <- pskl_to_uskl_open_var. exact Hconsα.
      * change (pskl_to_bskl_inh (pskl_tophole P0))
          with (bskl_tophole (pskl_to_bskl_inh P0)).
        apply ad_refine_syn_f__tophole_fill
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P0
                     `union` Δ1 `union` Δ2).
        intros α0 Hα0.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        replace (bskl_tophole (pskl_to_bskl_inh P0))
          with (subst_bskl_in_bskl (bskl_var_f α0) α
                  (bskl_tophole (pskl_to_bskl_inh P0)))
          by (simpl; rewrite subst_var_bskl_inh;
              rewrite subst_pskl_in_pskl_fresh_eq;
              [ reflexivity | clear - Fr; fsetdec ]).
        eapply ad_refine_syn_f_rename_ctx with (Θ1 := nil);
          [ change (nil ++ (α ~ abind_tvar) ++ Θ1)
              with ((α ~ abind_tvar) ++ Θ1); exact Hrsα
          | simpl; exact Hα1 | clear - Fr; fsetdec | clear - Hα0; fsetdec
          | exact Hdefsα ].
    + simpl. apply ad_refine_pskl_f__all
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_pskl P `union` ftvar_in_pskl P3).
      intros α0 Hα0.
      rewrite (subst_pskl_in_pskl_intro α P (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      rewrite (subst_pskl_in_pskl_intro α P3 (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      eapply ad_refine_pskl_f_fmono with (F' := add α Δ2);
        [ clear; fsetdec | ].
      eapply ad_refine_pskl_f_delta_mono;
        [ | instantiate (1 := add α0 (remove α (add α Δ2)));
            clear Fr; fsetdec ].
      apply ad_refine_pskl_f_rename;
        [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
      exact (ad_refine_pskl_f_strip nil Θ1 Hrpα
               ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
  - (* C-UnivGhost : ∀◇P ∼ ∀◇P3 against input ∀◇P0 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P3 Hc IHc Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' ]; subst.
    inversion HwfP as [ | | | | | Θb Δb P' Hg' Hwf' ]; subst.
    destruct (IHc Hwf) as
        [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ Hnd Hfa Hcov Hft.
      apply (Hinv Δ Hnd Hfa Hcov).
      intros α0 Hα0 HXd. specialize (Hft α0 Hα0 HXd).
      simpl in Hft. exact Hft. }
    split.
    + exists (bskl_tophole Qt). split.
      { simpl. rewrite HeQt. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__tophole. exact Hcons.
      * simpl. apply ad_refine_syn_f__tophole_keep; [ | exact Hrs ].
        eapply ad_refine_syn_f_guarded_r;
          [ exact Hwf1 | exact Hrs
          | apply guarded_pskl_to_bskl_inh; exact Hg0 ].
    + simpl. apply ad_refine_pskl_f__tophole_keep; [ | exact Hrp ].
      eapply ad_refine_pskl_f_guarded_r;
        [ exact Hwf1 | exact Hrp | exact Hg' ].
  - (* C-UnivGhost1 : ∀◇P ∼ ∀α.P3 against input ∀α.P0 *)
    (* cluster 4: exists-fresh opener — see C-ForallInh for the pattern *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfrα Hprem0 IH Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0, HwfP.
    inversion HwfP as [ | | | | | Θc Δc Pc Hg' Hwf' Heqc ]; subst.
    assert (HαP0 : α `notin` ftvar_in_pskl P0) by (clear - Hfrα; fsetdec).
    assert (HαP : α `notin` ftvar_in_pskl P) by (clear - Hfrα; fsetdec).
    assert (HαΔ1 : α `notin` Δ1) by (clear - Hfrα; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Hfrα; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0)
      by (pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfrα H; fsetdec).
    remember (close_pskl_wrt_pskl α Q) as P3 eqn:HeqP3.
    assert (HαP3 : α `notin` ftvar_in_pskl P3)
      by (subst P3; rewrite ftvar_in_pskl_close_pskl_wrt_pskl;
          clear; fsetdec).
    assert (HQP3 : Q = open_pskl_wrt_pskl P3 (pskl_var_f α))
      by (subst P3; symmetry;
          apply open_pskl_wrt_pskl_close_pskl_wrt_pskl).
    rewrite HQP3 in Hprem0, IH.
    assert (Hpostα : consis_sound_post (add α Δ1) Δ2
                       ((α ~ abind_tvar) ++ Θ0)
                       (open_pskl_wrt_pskl P0 (pskl_var_f α))
                       (pskl_tophole P)
                       (open_pskl_wrt_pskl P3 (pskl_var_f α))
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply IH.
      - apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf ].
      - eapply a_wf_pskl_delta_mono;
          [ apply (a_wf_pskl_reassoc (a_wf_pskl_all_inv_at HwfP0 HαP0) α)
          | clear; fsetdec ].
      - apply a_wf_pskl__tophole; auto.
        eapply a_wf_pskl_weaken; [ | exact Hwf' ].
        intros y b Hb. unfold binds; right; exact Hb.
      - intros α0 Hα0. destruct (α0 == α) as [->|Hne].
        + unfold binds; left; reflexivity.
        + unfold binds; right. apply Hrig. clear - Hα0 Hne. fsetdec.
      - apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
          [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ].
      - apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
          [ clear; fsetdec
          | apply faf_open_tvar; auto; clear - HαΔ1 HαΔ2; fsetdec ]. }
    destruct Hpostα
      as [Hleα [Hwfα [Hdomα [Hinvα [[Qtα [HeQtα [Hconsα Hrsα]]] Hrpα]]]]].
    assert (Hwf1 : a_wf_aenv Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Hα1 : α `notin` dom Θ1)
      by (apply a_wf_aenv_tvar_inv in Hwfα; tauto).
    assert (Fr : α `notin` (dom Θ0 `union` dom Θ1 `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl P3
                  `union` Δ1 `union` Δ2))
      by (clear - HαΘ0 Hα1 HαP0 HαP HαP3 HαΔ1 HαΔ2; fsetdec).
    assert (Hdefsα : forall β τ, binds β (abind_flex_mono_def τ) Θ1 ->
                     α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      pose proof (@a_wf_aenv_def_ftv_dom Θ1 β τ Hwf1 Hb) as Hsc.
      clear - Hsc Hα1. fsetdec. }
    split; [ eapply a_isub_strip_tvar; eauto | ].
    split; [ exact Hwf1 | ].
    split.
    { intros x Hx.
      assert (Hx1 : x `in` dom ((α ~ abind_tvar) ++ Θ1))
        by (apply Hdomα; simpl; clear - Hx; fsetdec).
      simpl in Hx1.
      assert (Hxα : x <> α) by (intros ->; clear - Fr Hx; fsetdec).
      clear - Hx1 Hxα. fsetdec. }
    split.
    { intros Δ HndΔ HfaΔ HcovΔ Hft.
      destruct (Hinvα Δ) as [Hnd' [Hfa' Hbk']].
      { intros β' τ' Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
          [ discriminate | exact (HndΔ β' τ' Hb') ]. }
      { apply faf_cons;
          [ intros Hne; exfalso; apply Hne; reflexivity | exact HfaΔ ]. }
      { simpl. clear - HcovΔ. fsetdec. }
      { intros α0 Hα0 HXd.
        simpl in HXd.
        assert (HXd0 : α0 `notin` dom Θ0) by (clear - HXd; fsetdec).
        assert (Hα0α2 : α0 <> α) by (clear - HXd; fsetdec).
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                      P0 (pskl_var_f α)) as Hup0.
        specialize (Hft α0 Hα0 HXd0).
        simpl in Hft, Hup0.
        clear - Hft Hup0 Hα0α2. fsetdec. }
      split.
      { intros β' τ' Hb'. apply (Hnd' β' τ').
        unfold binds; right; exact Hb'. }
      split.
      { eapply faf_tail. exact Hfa'. }
      { intros α0 Hα0 HXd.
        assert (HX1 : α0 `in` dom ((α ~ abind_tvar) ++ Θ1))
          by (simpl; clear - HXd; fsetdec).
        pose proof (Hbk' α0 Hα0 HX1) as HX0. simpl in HX0.
        assert (Hα0α2 : α0 <> α) by (intros ->; clear - Hα1 HXd; fsetdec).
        clear - HX0 Hα0α2. fsetdec. } }
    split.
    + exists (bskl_all_inh (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; fsetdec ]. }
      split.
      * simpl. apply ad_pat_consis__tophole_inh
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P).
        intros α0 Hα0.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        replace (uskl_tophole (pskl_to_uskl P))
          with (subst_bskl_in_uskl (uskl_var_f α0) α
                  (uskl_tophole (pskl_to_uskl P)))
          by (simpl; rewrite subst_bskl_in_uskl_fresh_eq;
              [ reflexivity
              | rewrite ftvar_in_uskl_pskl; clear - Fr; fsetdec ]).
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ | exact Hα1 | exact Hdefsα ].
        exact Hconsα.
      * change (pskl_to_bskl_inh (pskl_all_syn P0))
          with (bskl_all_inh (pskl_to_bskl_inh P0)).
        apply ad_refine_syn_f__all
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P0).
        intros α0 Hα0.
        rewrite <- pskl_to_bskl_inh_open.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        assert (Hfr0 : α `notin` ftvar_in_pskl P0) by (clear - Fr; fsetdec).
        rewrite (subst_pskl_in_pskl_intro α P0 (pskl_var_f α0) Hfr0).
        rewrite <- subst_var_bskl_inh.
        eapply ad_refine_syn_f_fmono with (F' := add α Δ1);
          [ clear; fsetdec | ].
        eapply ad_refine_syn_f_delta_mono;
          [ | instantiate (1 := add α0 (remove α (add α Δ1)));
              clear Fr; fsetdec ].
        apply ad_refine_syn_f_rename;
          [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
        exact (ad_refine_syn_f_strip nil Θ1 Hrsα
                 ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
    + apply ad_refine_pskl_f__tophole_fill
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_pskl P `union` ftvar_in_pskl P3
                   `union` Δ1 `union` Δ2).
      intros α0 Hα0.
      rewrite (subst_pskl_in_pskl_intro α P3 (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      replace (pskl_tophole P)
        with (subst_pskl_in_pskl (pskl_var_f α0) α (pskl_tophole P))
        by (simpl; rewrite subst_pskl_in_pskl_fresh_eq;
            [ reflexivity | clear - Fr; fsetdec ]).
      eapply ad_refine_pskl_f_rename_ctx with (Θ1 := nil);
        [ change (nil ++ (α ~ abind_tvar) ++ Θ1)
            with ((α ~ abind_tvar) ++ Θ1); exact Hrpα
        | simpl; exact Hα1 | clear - Fr; fsetdec | clear - Hα0; fsetdec
        | exact Hdefsα ].
  - (* C-UnivGhost2 *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P3 Hg Hnf Hc IHc Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP.
    inversion HwfP as [ | | | | | Θb Δb P' Hg' Hwf' ]; subst.
    destruct (IHc Hwf) as
        [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ Hnd Hfa Hcov Hft.
      apply (Hinv Δ Hnd Hfa Hcov).
      intros α0 Hα0 HXd. specialize (Hft α0 Hα0 HXd).
      simpl in Hft. exact Hft. }
    split.
    + exists Qt. split; [ exact HeQt | ].
      split;
        [ simpl; apply ad_pat_consis__tophole_drop; exact Hcons | exact Hrs ].
    + simpl. apply ad_refine_pskl_f__tophole_remove. exact Hrp.
  - (* C-Flex : the mutual case — subjects equated by unification *)
    intros Δ1 Δ2 Θ0 Θ1 α β Hu IHu Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    destruct (IHu Hwf) as [Hle [Hwf1 [Hdom [Hinv Heq1]]]].
    destruct (a_unify_subjects_flex Hwf Hu) as [Hfα Hfβ].
    assert (HαnΔ : α `notin` (Δ1 `union` Δ2)).
    { destruct Hfα as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (HβnΔ : β `notin` (Δ1 `union` Δ2)).
    { destruct Hfβ as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (Hcov12 : forall (Θx : aenv), ((Δ1 `union` Δ2) ∩ dom Θx) [<=] dom Θ0).
    { intros Θx α0 Hα0.
      assert (Hα0' : α0 `in` (Δ1 `union` Δ2)) by (clear - Hα0; fsetdec).
      apply Hrig in Hα0'. apply binds_In in Hα0'. exact Hα0'. }
    destruct (Hinv (Δ1 `union` Δ2) Hnfd Hfaf (Hcov12 _)) as [Hnfd1 [Hfaf1 _]].
    assert (Hbα1 : a_binds_tvar α Θ1).
    { eapply a_isub_binds_tvarish; eauto.
      destruct Hfα as [Hb | [τ Hb]];
        [ right; left | right; right; exists τ ]; auto. }
    assert (Hbβ1 : a_binds_tvar β Θ1).
    { eapply a_isub_binds_tvarish; eauto.
      destruct Hfβ as [Hb | [τ Hb]];
        [ right; left | right; right; exists τ ]; auto. }
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ Hnd Hfa Hcov _. apply Hinv; auto. }
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__var; [ fsetdec | exact Hbα1 ].
      * assert (Hcbα : ad_pat_consis empty Θ1
                  (ptyp_to_uskl_syn (ptyp_var_f β))
                  (ptyp_to_bskl_syn (ptyp_var_f α))).
        { apply tyequiv_mono_consis;
            [ apply a_tyequiv__sym; exact Heq1 | exact Hwf1
            | constructor | ].
          intros α0 Hα0. simpl in Hα0.
          assert (α0 = β) by (clear - Hα0; fsetdec). subst. exact Hbβ1. }
        replace (pskl_to_bskl_inh (pskl_var_f β))
          with (pskl_to_bskl_inh
                  (uskl_to_pskl (ptyp_to_uskl_syn (ptyp_var_f β))))
          by (rewrite uskl_to_pskl_ptyp; reflexivity).
        replace (bskl_var_f α) with (ptyp_to_bskl_syn (ptyp_var_f α))
          by reflexivity.
        eapply ad_pat_consis_refine_syn_f_mono;
          [ exact Hcbα | exact Hwf1
          | apply mono_ptyp_to_bskl_syn; constructor | | ].
        { rewrite ftvar_in_bskl_ptyp_syn. simpl. clear - HαnΔ. fsetdec. }
        { intros α1 τ Hb. eapply (Hnfd1 α1 τ) in Hb. clear - Hb. fsetdec. }
    + apply ad_refine_pskl_f__var. right. exact Hbα1.
  - (* C-FlexL : assign α̂ := P0 (the input skeleton).  MUTUAL case: the
       [a_assign] premise is handled by the bundle's ASSIGN motive. *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hassign IHassign Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    destruct (IHassign a_decls__nil Hwf HwfP0)
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    assert (Hfα : a_flex_tvar Θ0 α)
      by (pose proof (a_assign_subject_flex Hassign) as Hf; simpl in Hf;
          exact Hf).
    assert (HαnΔ : α `notin` (Δ1 `union` Δ2)).
    { destruct Hfα as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (HΔdom : Δ1 `union` Δ2 [<=] dom Θ0).
    { intros α0 Hα0. apply binds_In with (a := abind_tvar). apply Hrig; auto. }
    assert (Hbα1 : a_binds_tvar α Θ1).
    { eapply a_isub_binds_tvarish; [ exact Hle | ].
      destruct Hfα as [Hb | [τ Hb]];
        [ right; left | right; right; exists τ ]; exact Hb. }
    assert (Hinv12 : no_flex_dep (Δ1 `union` Δ2) Θ1 /\
                     flex_above_free (Δ1 `union` Δ2) Θ1).
    { destruct (Hinv (Δ1 `union` Δ2)) as [Hnd [Hfaf' _]].
      { exact Hnfd. }
      { exact Hfaf. }
      { simpl. clear. fsetdec. }
      { simpl. clear - HΔdom. fsetdec. }
      { intros α0 Hα0 Hnd0. exfalso. apply Hnd0. apply HΔdom. exact Hα0. }
      split; assumption. }
    destruct Hinv12 as [Hnfd1 Hfaf1].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ HndΔ HfaΔ HcovΔ Hft.
      destruct (Hinv Δ) as [Hnd' [Hfa' Hbk']].
      { exact HndΔ. }
      { exact HfaΔ. }
      { simpl. clear. fsetdec. }
      { simpl. clear - HcovΔ. fsetdec. }
      { intros α0 Hα0 HXd. pose proof (Hft α0 Hα0 HXd) as Hf0.
        clear - Hf0. fsetdec. }
      split; [ exact Hnd' | ]. split; [ exact Hfa' | ].
      intros α0 Hα0 HXd.
      pose proof (Hbk' α0 Hα0 HXd) as HX0. simpl in HX0.
      clear - HX0. fsetdec. }
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
        { intros α1 τ Hb. eapply (Hnfd1 α1 τ) in Hb. clear - Hb. fsetdec. }
    + apply ad_refine_pskl_f__var. right. exact Hbα1.
  - (* C-FlexR : assign α̂ := P (the subject skeleton), output var α̂.
       MUTUAL case: the [a_assign] premise is the bundle's ASSIGN motive. *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hassign IHassign Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    destruct (IHassign a_decls__nil Hwf HwfP)
      as [Hle [Hwf1 [Hdom [Hinv Hcons]]]].
    assert (Hfα : a_flex_tvar Θ0 α)
      by (pose proof (a_assign_subject_flex Hassign) as Hf; simpl in Hf;
          exact Hf).
    assert (HαnΔ : α `notin` (Δ1 `union` Δ2)).
    { destruct Hfα as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (HΔdom : Δ1 `union` Δ2 [<=] dom Θ0).
    { intros α0 Hα0. apply binds_In with (a := abind_tvar). apply Hrig; auto. }
    assert (Hbα1 : a_binds_tvar α Θ1).
    { eapply a_isub_binds_tvarish; [ exact Hle | ].
      destruct Hfα as [Hb | [τ Hb]];
        [ right; left | right; right; exists τ ]; exact Hb. }
    assert (Hinv12 : no_flex_dep (Δ1 `union` Δ2) Θ1 /\
                     flex_above_free (Δ1 `union` Δ2) Θ1).
    { destruct (Hinv (Δ1 `union` Δ2)) as [Hnd [Hfaf' _]].
      { exact Hnfd. }
      { exact Hfaf. }
      { simpl. clear. fsetdec. }
      { simpl. clear - HΔdom. fsetdec. }
      { intros α0 Hα0 Hnd0. exfalso. apply Hnd0. apply HΔdom. exact Hα0. }
      split; assumption. }
    destruct Hinv12 as [Hnfd1 Hfaf1].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ HndΔ HfaΔ HcovΔ Hft.
      destruct (Hinv Δ) as [Hnd' [Hfa' Hbk']].
      { exact HndΔ. }
      { exact HfaΔ. }
      { simpl. clear. fsetdec. }
      { simpl. clear - HcovΔ. fsetdec. }
      { intros α0 Hα0 HXd. pose proof (Hft α0 Hα0 HXd) as Hf0.
        clear - Hf0. fsetdec. }
      split; [ exact Hnd' | ]. split; [ exact Hfa' | ].
      intros α0 Hα0 HXd.
      pose proof (Hbk' α0 Hα0 HXd) as HX0. simpl in HX0.
      clear - HX0. fsetdec. }
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * exact Hcons.
      * replace (pskl_to_bskl_inh (pskl_var_f α)) with (bskl_var_f α)
          by reflexivity.
        apply ad_refine_syn_f__var. right. exact Hbα1.
    + replace (pskl_var_f α) with (bskl_to_pskl (bskl_var_f α))
        by reflexivity.
      replace P with (uskl_to_pskl (pskl_to_uskl P)) at 1
        by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      eapply ad_pat_consis_refine_pskl_f_mono;
        [ exact Hcons | exact Hwf1 | apply mono_bskl__var | | ].
      { simpl. clear - HαnΔ. fsetdec. }
      { intros α1 τ Hb. eapply (Hnfd1 α1 τ) in Hb. clear - Hb. fsetdec. }
  - (* C-GhostR *)
    intros Δ1 Δ2 Θ0 P Hint Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ].
    split; [ clear; fsetdec | ].
    split.
    { intros Δ Hnd Hfa _ _.
      split; [ exact Hnd | ]. split; [ exact Hfa | ].
      intros α0 _ Hα0; exact Hα0. }
    split.
    + exists (pskl_to_bskl_syn P).
      split; [ apply bskl_to_pskl_pskl_to_bskl_syn | ].
      split.
      * replace (pskl_to_bskl_syn P)
          with (pskl_to_bskl_syn (uskl_to_pskl (pskl_to_uskl P)))
          by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        apply ad_pat_consis_refl_erase.
        { apply pskl_to_uskl_lc. eapply a_wf_pskl_lc; eauto. }
        { intros α0 Hα0. rewrite ftvar_in_uskl_pskl in Hα0.
          destruct (a_wf_pskl_ftv_tvarish HwfP Hα0) as [HΔ | Htv];
            [ clear - HΔ; fsetdec | exact Htv ]. }
      * replace (pskl_to_bskl_inh pskl_hole) with bskl_hole by reflexivity.
        apply ad_refine_syn_f__hole; [ exact Hint | exact HwfP ].
    + apply ad_refine_pskl_f_refl.
      eapply a_wf_pskl_delta_mono; [ exact HwfP | fsetdec ].
  - (* C-UnivGhostR *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P3 Hg Hnf Hc IHc Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
    simpl in HwfP0.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' ]; subst.
    destruct (IHc Hwf) as
        [Hle [Hwf1 [Hdom [Hinv [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hdom | ].
    split.
    { intros Δ Hnd Hfa Hcov Hft.
      apply (Hinv Δ Hnd Hfa Hcov).
      intros α0 Hα0 HXd. specialize (Hft α0 Hα0 HXd).
      simpl in Hft. exact Hft. }
    split.
    + exists Qt. split; [ exact HeQt | ]. split; [ exact Hcons | ].
      apply ad_refine_syn_f__tophole_remove. exact Hrs.
    + exact Hrp.
Qed.

(* ===================================================================== *)
(*  The [a_assign] lemmas, RE-EXPORTED from the bundle under their         *)
(*  original names.  Each used to be a standalone induction; now that      *)
(*  Assign-Assign's premise is a CONSISTENCY derivation they are conjuncts *)
(*  of the bundle's ASSIGN motive.  The only change to their statements is *)
(*  the wf hypothesis (full [⨟ ∅ ⊢ₚₛᵃ P] instead of the old visibility     *)
(*  side condition) — every call site has it.                             *)
(* ===================================================================== *)

(** Soundness of assignment (thm:sound-consistency part 3):
    [Θ₀ | Ξ ⊲ α̂ ≔ P ⊣ Θ₁] gives [(Ξ ++ Θ₀) ⊴ Θ₁] and, declaratively, the
    assigned skeleton is consistent with the variable in [Θ₁]. *)
Lemma a_assign_sound : forall Θ0 Ξ α P Θ1,
  Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  (Ξ ++ Θ0) ⊴ Θ1 /\
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (bskl_var_f α).
Proof.
  intros * Ha Hdecl Hwf HwfP.
  destruct (proj1 a_assign_unify_consis_sound _ _ _ _ _ Ha Hdecl Hwf HwfP)
    as [Hle [_ [_ [_ Hcons]]]].
  split; assumption.
Qed.

(** [a_assign] preserves context well-formedness. *)
Lemma a_assign_preserves_wf : forall Θ0 Ξ α P Θ1,
  Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  a_wf_aenv Θ1.
Proof.
  intros * Ha Hdecl Hwf HwfP.
  destruct (proj1 a_assign_unify_consis_sound _ _ _ _ _ Ha Hdecl Hwf HwfP)
    as [_ [Hwf1 _]]. exact Hwf1.
Qed.

(** Assignment never drops an entry: the domain only grows. *)
Lemma a_assign_dom_mono : forall Θ0 Ξ α P Θ1,
  Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  dom (Ξ ++ Θ0) [<=] dom Θ1.
Proof.
  intros * Ha Hdecl Hwf HwfP.
  destruct (proj1 a_assign_unify_consis_sound _ _ _ _ _ Ha Hdecl Hwf HwfP)
    as [_ [_ [Hdom _]]]. exact Hdom.
Qed.

(* [a_assign_new_avoids_F] / [a_assign_notin] / [a_unify_notin] /
   [a_consis_notin] DELETED with the used-name set: "a name in [F] and fresh
   for the input stays fresh" is exactly what the walk's re-attaching rules
   now state as their own premise (DESIGN.md §4.3). *)

(** Preservation of the problem invariants by assignment, at any protected Δ. *)
Lemma a_assign_preserves_inv : forall Θ0 Ξ α P Θ1 Δ,
  Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  no_flex_dep Δ (Ξ ++ Θ0) ->
  flex_above_free Δ Θ0 ->
  Δ ∩ dom Ξ [=] empty ->
  Δ ∩ dom Θ1 [<=] dom (Ξ ++ Θ0) ->
  (forall α0, α0 `in` Δ -> α0 `notin` dom Θ0 -> α0 `notin` ftvar_in_pskl P) ->
  no_flex_dep Δ Θ1 /\
  flex_above_free Δ Θ1 /\
  (forall α0, α0 `in` Δ -> α0 `in` dom Θ1 -> α0 `in` (dom Ξ `union` dom Θ0)).
Proof.
  intros * Ha Hdecl Hwf HwfP.
  destruct (proj1 a_assign_unify_consis_sound _ _ _ _ _ Ha Hdecl Hwf HwfP)
    as [_ [_ [_ [Hinv _]]]]. apply (Hinv Δ).
Qed.

(** The subject of an assignment is bound (as a flexible or defined variable)
    in the output context.  NO induction: the increase conjunct transports the
    input flexibility of the subject ([a_assign_subject_flex]) forward. *)
Lemma a_assign_subject_binds : forall Θ0 Ξ α P Θ1,
  Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 ->
  a_decls Ξ ->
  a_wf_aenv (Ξ ++ Θ0) ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
  a_binds_tvar α Θ1.
Proof.
  intros * Ha Hdecl Hwf HwfP.
  destruct (a_assign_sound Ha Hdecl Hwf HwfP) as [Hle _].
  eapply a_isub_binds_tvarish; [ exact Hle | ].
  destruct (a_assign_subject_flex Ha) as [Hb | [τ Hb]];
    [ right; left | right; right; exists τ ]; exact Hb.
Qed.


(** Part 2, packaged (thm:sound-consistency part 2, paper reading). *)
Corollary a_unify_sound : forall Θ0 α β Θ1,
  Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\ (Θ1 ⊢ (ptyp_var_f α) ≡ᵗ (ptyp_var_f β)).
Proof.
  intros * Hu Hwf.
  destruct (proj1 (proj2 a_assign_unify_consis_sound) _ _ _ _ Hu Hwf)
    as [Hle [Hwf1 [_ [_ Heq]]]]; auto.
Qed.

(** Preservation of the part-1 problem invariants by unification, at any
    protected Δ (the shape [a_consistag_sound_aux]'s Flex case needs). *)
Corollary a_unify_preserves_inv : forall Θ0 α β Θ1 Δ,
  Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  no_flex_dep Δ Θ0 ->
  flex_above_free Δ Θ0 ->
  Δ ∩ dom Θ1 [<=] dom Θ0 ->
  no_flex_dep Δ Θ1 /\ flex_above_free Δ Θ1.
Proof.
  intros * Hu Hwf Hnd Hfa Hcov.
  destruct (proj1 (proj2 a_assign_unify_consis_sound) _ _ _ _ Hu Hwf)
    as [_ [_ [_ [Hinv _]]]].
  destruct (Hinv Δ Hnd Hfa Hcov) as [Hnd1 [Hfa1 _]]; auto.
Qed.


(* ===================================================================== *)
(*  Soundness of DECORATED consistency (lemma:sound-decorated-consistency) *)
(*  The parallel of [a_consis_sound_aux] over the tagged/decorated        *)
(*  algorithmic consistency judgment [a_consistag], threading the tag     *)
(*  context Ψ into the declarative consistency component.                 *)
(* ===================================================================== *)

(** Erasure preserves free variables. *)
Lemma ftvar_in_pskl_uskl_to_pskl : forall R,
  ftvar_in_pskl (uskl_to_pskl R) [=] ftvar_in_uskl R.
Proof. induction R; simpl; fsetdec. Qed.

(** Erasure commutes with variable-opening. *)
Lemma uskl_to_pskl_open : forall R α,
  uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α))
  = open_pskl_wrt_pskl (uskl_to_pskl R) (pskl_var_f α).
Proof.
  intros. unfold open_uskl_wrt_uskl, open_pskl_wrt_pskl.
  rewrite uskl_to_pskl_open_rec. reflexivity.
Qed.

(** [ad_pat_consis] is congruent in the tag context. *)
Lemma ad_pat_consis_psi_cong : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  forall Ψ', Ψ [=] Ψ' ->
  Ψ' ⨟ Θ ⊢ₛᵃ R ∼ Q.
Proof.
  intros Ψ Θ R Q H; induction H; intros Ψ' Heq;
    econstructor; eauto; fsetdec.
Qed.

Lemma a_consistag_sound_aux : forall Δ1 Δ2 P0 Ψ Θ0 R P' Θ1,
  Θ0 ⊢ᵗ[ Δ1 | Δ2 | P0 | Ψ ] R ∼˙ P' ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  lc_uskl R ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ (uskl_to_pskl R) ->
  (forall α0, α0 `in` (Δ1 `union` Δ2) -> binds α0 abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 -> flex_above_free (Δ1 `union` Δ2) Θ0 ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  no_flex_dep (Δ1 `union` Δ2) Θ1 /\ flex_above_free (Δ1 `union` Δ2) Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     Ψ ⨟ Θ1 ⊢ₛᵃ R ∼ Qt /\
     ad_refine_syn_f Δ1 Θ1 Δ1 (pskl_to_bskl_inh P0) Qt) /\
  ad_refine_pskl_f Δ2 Θ1 Δ2 (uskl_to_pskl R) P'.
Proof.
  intros * Hc; induction Hc;
    intros Hwf HlcS HwfP0 HwfS Hrig Hnfd Hfaf.
  - (* Ghost *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists (pskl_to_bskl_inh P0).
      split; [ apply bskl_to_pskl_pskl_to_bskl_inh | ].
      split.
      * apply ad_pat_consis__hole; [ fsetdec | exact HwfP0 ].
      * apply ad_refine_syn_f_refl_inh.
        eapply a_wf_pskl_delta_mono; [ exact HwfP0 | fsetdec ].
    + apply ad_refine_pskl_f__hole; [ exact H | exact HwfP0 ].
  - (* Unit *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists bskl_unit. split; [ reflexivity | ].
      split; [ apply ad_pat_consis__unit; fsetdec | apply ad_refine_syn_f__unit ].
    + apply ad_refine_pskl_f__unit.
  - (* Rigid *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__var; [ fsetdec | left; exact H ].
      * apply ad_refine_syn_f__var. right; left; exact H.
    + apply ad_refine_pskl_f__var. right; left; exact H.
  - (* Flex : decorated — through the mutual soundness bundle *)
    destruct (a_unify_sound H Hwf) as [Hle [Hwf1 Heq1]].
    destruct (a_unify_subjects_flex Hwf H) as [Hfα Hfβ].
    assert (HαnΔ : α `notin` (Δ1 `union` Δ2)).
    { destruct Hfα as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (HβnΔ : β `notin` (Δ1 `union` Δ2)).
    { destruct Hfβ as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (Hinv : no_flex_dep (Δ1 `union` Δ2) Θ1 /\
                   flex_above_free (Δ1 `union` Δ2) Θ1).
    { eapply a_unify_preserves_inv; eauto.
      intros α0 Hα0.
      assert (Hα0' : α0 `in` (Δ1 `union` Δ2)) by (clear - Hα0; fsetdec).
      apply Hrig in Hα0'. apply binds_In in Hα0'. exact Hα0'. }
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
        { apply tyequiv_mono_consis;
            [ apply a_tyequiv__sym; exact Heq1 | exact Hwf1
            | constructor | ].
          intros α0 Hα0. simpl in Hα0.
          assert (α0 = β) by (clear - Hα0; fsetdec). subst. exact Hbβ1. }
        replace (pskl_to_bskl_inh (pskl_var_f β))
          with (pskl_to_bskl_inh (uskl_to_pskl (ptyp_to_uskl_syn (ptyp_var_f β))))
          by (rewrite uskl_to_pskl_ptyp; reflexivity).
        replace (bskl_var_f α) with (ptyp_to_bskl_syn (ptyp_var_f α))
          by reflexivity.
        eapply ad_pat_consis_refine_syn_f_mono;
          [ exact Hcbα | exact Hwf1
          | apply mono_ptyp_to_bskl_syn; constructor | | ].
        { rewrite ftvar_in_bskl_ptyp_syn. simpl. clear - HαnΔ. fsetdec. }
        { intros α1 τ Hb. eapply (Hnfd1 α1 τ) in Hb.
          clear - Hb. fsetdec. }
    + apply ad_refine_pskl_f__var. right. exact Hbα1.
  - (* FlexL : decorated *)
    assert (Hvis : forall α0, α0 `in` ftvar_in_pskl P0 -> a_binds_tvar α0 Θ0).
    { intros α0 Hα0. destruct (a_wf_pskl_ftv_tvarish HwfP0 Hα0) as [HΔ | Ht];
        [ clear - HΔ; fsetdec | exact Ht ]. }
    destruct (a_assign_sound H0 a_decls__nil Hwf HwfP0) as [Hle Hcons].
    simpl in Hle.
    assert (Hwf1 : a_wf_aenv Θ1)
      by (eapply a_assign_preserves_wf;
          [ exact H0 | apply a_decls__nil | exact Hwf | exact HwfP0 ]).
    assert (Hfα : a_flex_tvar Θ0 α)
      by (pose proof (a_assign_subject_flex H0) as Hf; simpl in Hf; exact Hf).
    assert (HαnΔ : α `notin` (Δ1 `union` Δ2)).
    { destruct Hfα as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (HΔdom : Δ1 `union` Δ2 [<=] dom Θ0).
    { intros α0 Hα0. apply binds_In with (a := abind_tvar). apply Hrig; auto. }
    assert (Hinv : no_flex_dep (Δ1 `union` Δ2) Θ1 /\
                   flex_above_free (Δ1 `union` Δ2) Θ1).
    { destruct (a_assign_preserves_inv (Δ := Δ1 `union` Δ2) H0
                  a_decls__nil Hwf HwfP0
                  ltac:(simpl; exact Hnfd) Hfaf
                  ltac:(simpl; solve_notin_auto)
                  ltac:(simpl; rewrite <- HΔdom; solve_notin_auto)
                  ltac:(intros α0 Hα0 Hnd0; exfalso; apply Hnd0;
                        apply HΔdom; exact Hα0))
        as [Hnd [Hfaf' _]].
      split; assumption. }
    destruct Hinv as [Hnfd1 Hfaf1].
    assert (Hbα1 : a_binds_tvar α Θ1)
      by (eapply a_assign_subject_binds;
          [ exact H0 | apply a_decls__nil | exact Hwf | exact HwfP0 ]).
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
        { intros α1 τ Hb. eapply (Hnfd1 α1 τ) in Hb. clear - Hb. fsetdec. }
    + apply ad_refine_pskl_f__var. right. exact Hbα1.
  - (* FlexR : decorated (subject [pskl_to_uskl P], mirrors ordinary FlexR) *)
    rewrite uskl_to_pskl_pskl_to_uskl in HwfS.
    assert (Hvis : forall α0, α0 `in` ftvar_in_pskl P -> a_binds_tvar α0 Θ0).
    { intros α0 Hα0. destruct (a_wf_pskl_ftv_tvarish HwfS Hα0) as [HΔ | Ht];
        [ clear - HΔ; fsetdec | exact Ht ]. }
    destruct (a_assign_sound H0 a_decls__nil Hwf HwfS) as [Hle Hcons].
    simpl in Hle.
    assert (Hwf1 : a_wf_aenv Θ1)
      by (eapply a_assign_preserves_wf;
          [ exact H0 | apply a_decls__nil | exact Hwf | exact HwfS ]).
    assert (Hfα : a_flex_tvar Θ0 α)
      by (pose proof (a_assign_subject_flex H0) as Hf; simpl in Hf; exact Hf).
    assert (HαnΔ : α `notin` (Δ1 `union` Δ2)).
    { destruct Hfα as [Hb | [τ Hb]];
        eapply faf_flex_notin; try exact Hfaf; try exact Hb; discriminate. }
    assert (HΔdom : Δ1 `union` Δ2 [<=] dom Θ0).
    { intros α0 Hα0. apply binds_In with (a := abind_tvar). apply Hrig; auto. }
    assert (Hinv : no_flex_dep (Δ1 `union` Δ2) Θ1 /\
                   flex_above_free (Δ1 `union` Δ2) Θ1).
    { destruct (a_assign_preserves_inv (Δ := Δ1 `union` Δ2) H0
                  a_decls__nil Hwf HwfS
                  ltac:(simpl; exact Hnfd) Hfaf
                  ltac:(simpl; solve_notin_auto)
                  ltac:(simpl; rewrite <- HΔdom; solve_notin_auto)
                  ltac:(intros α0 Hα0 Hnd0; exfalso; apply Hnd0;
                        apply HΔdom; exact Hα0))
        as [Hnd [Hfaf' _]].
      split; assumption. }
    destruct Hinv as [Hnfd1 Hfaf1].
    assert (Hbα1 : a_binds_tvar α Θ1)
      by (eapply a_assign_subject_binds;
          [ exact H0 | apply a_decls__nil | exact Hwf | exact HwfS ]).
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists (bskl_var_f α). split; [ reflexivity | ].
      split.
      * eapply ad_pat_consis_psi_cong; [ exact Hcons | symmetry; exact H1 ].
      * replace (pskl_to_bskl_inh (pskl_var_f α)) with (bskl_var_f α)
          by reflexivity.
        apply ad_refine_syn_f__var. right. exact Hbα1.
    + replace (pskl_var_f α) with (bskl_to_pskl (bskl_var_f α)) by reflexivity.
      eapply ad_pat_consis_refine_pskl_f_mono;
        [ exact Hcons | exact Hwf1 | apply mono_bskl__var | | ].
      { simpl. clear - HαnΔ. fsetdec. }
      { intros α1 τ Hb. eapply (Hnfd1 α1 τ) in Hb. clear - Hb. fsetdec. }
  - (* GhostG *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists bskl_hole. split; [ reflexivity | ].
      split.
      * apply ad_pat_consis__ghostg. fsetdec.
      * replace (@bskl_hole) with (pskl_to_bskl_syn pskl_hole) by reflexivity.
        apply ad_refine_syn_f__hole; [ simpl; fsetdec | apply a_wf_pskl__hole ].
    + apply ad_refine_pskl_f__hole; [ simpl; fsetdec | apply a_wf_pskl__hole ].
  - (* Arrow *)
    simpl in HwfP0, HwfS. inversion HlcS; subst.
    inversion HwfP0 as [ | | Θa Δa P0a' P0b' HwfP0a HwfP0b | | | ]; subst.
    inversion HwfS as [ | | Θb Δb S1p S2p HwfS1 HwfS2 | | | ]; subst.
    destruct IHHc1
      as [Hle1 [Hwf1 [Hnfd1 [Hfaf1 [[Qt1 [HeQt1 [Hcons1 Hrs1]]] Hrp1]]]]]; auto.
    destruct IHHc2
      as [Hle2 [Hwf2 [Hnfd2 [Hfaf2 [[Qt2 [HeQt2 [Hcons2 Hrs2]]] Hrp2]]]]]; auto.
    { eapply a_wf_pskl_isub; eauto. }
    { eapply a_wf_pskl_isub; eauto. }
    { intros α0 Hα0. eapply a_isub_binds_tvar; eauto. }
    split; [ eapply a_isub_trans; eauto | ].
    split; [ exact Hwf2 | ]. split; [ exact Hnfd2 | ]. split; [ exact Hfaf2 | ].
    split.
    + exists (bskl_arrow Qt1 Qt2). split.
      { simpl. rewrite HeQt1, HeQt2. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
          [ eapply ad_pat_consis_isub; eauto | exact Hcons2 | exact H ].
      * simpl. apply ad_refine_syn_f__arrow;
          [ eapply ad_refine_syn_f_isub; eauto | exact Hrs2 ].
    + simpl. apply ad_refine_pskl_f__arrow;
        [ eapply ad_refine_pskl_f_isub; eauto | exact Hrp2 ].
  - (* ForallInh tagged : decorated *)
    simpl in HwfP0, HwfS.
    inversion HwfP0 as [ | | | L0 Θa Δa P0a Hbody0 Heqa | | ]; subst.
    inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
    inversion HlcS; subst.
    match goal with Hb : forall _, lc_uskl _ |- _ => rename Hb into HlcSbody end.
    pick fresh α for
      (L `union` L0 `union` LS `union` dom Θ0 `union` dom Θ1
       `union` ftvar_in_pskl P0 `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
       `union` Δ1 `union` Δ2).
    assert (HαL : α `notin` L) by auto.
    assert (HwfΘα : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; auto).
    assert (HlcSα : lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α)))
      by (apply HlcSbody).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                       ⊢ₚₛᵃ (open_pskl_wrt_pskl P0 (pskl_var_f α))).
    { eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc (Hbody0 α ltac:(auto)) α)
        | clear; fsetdec ]. }
    assert (HwfSα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                   ⊢ₚₛᵃ (uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α)))).
    { rewrite uskl_to_pskl_open.
      eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc (HbodyS α ltac:(auto)) α)
        | clear; fsetdec ]. }
    assert (Hrigα : forall α0, α0 `in` (add α Δ1 `union` add α Δ2) ->
                    binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α0 Hα0. destruct (α0 == α) as [->|Hne].
      - unfold binds; left; reflexivity.
      - unfold binds; right. apply Hrig. clear - Hα0 Hne. fsetdec. }
    assert (Hnfdα : no_flex_dep (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ]. }
    assert (Hfafα : flex_above_free (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply faf_open_tvar; auto ]. }
    destruct (H0 α HαL HwfΘα HlcSα HwfP0α HwfSα Hrigα Hnfdα Hfafα)
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
      * simpl. apply ad_pat_consis__forall_inh_tagged
          with (Ψ0 := Ψ0) (ε := ε)
               (L := dom Θ1 `union` singleton α `union` ftvar_in_uskl R);
          [ | exact H1 ].
        intros α0 Hα0.
        rewrite (subst_bskl_in_uskl_intro α R (uskl_var_f α0));
          [ | clear - Fr; fsetdec ].
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ exact Hconsα | exact Hα1 | exact Hdefsα ].
      * change (pskl_to_bskl_inh (pskl_all_syn P0))
          with (bskl_all_inh (pskl_to_bskl_inh P0)).
        apply ad_refine_syn_f__all
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P0).
        intros α0 Hα0.
        rewrite <- pskl_to_bskl_inh_open.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        assert (Hfr0 : α `notin` ftvar_in_pskl P0) by (clear - Fr; fsetdec).
        rewrite (subst_pskl_in_pskl_intro α P0 (pskl_var_f α0) Hfr0).
        rewrite <- subst_var_bskl_inh.
        eapply ad_refine_syn_f_fmono with (F' := add α Δ1);
          [ clear; fsetdec | ].
        eapply ad_refine_syn_f_delta_mono;
          [ | instantiate (1 := add α0 (remove α (add α Δ1)));
              clear Fr; fsetdec ].
        apply ad_refine_syn_f_rename;
          [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
        exact (ad_refine_syn_f_strip nil Θ1 Hrsα
                 ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
    + simpl. apply ad_refine_pskl_f__all
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_uskl R `union` ftvar_in_pskl Q).
      intros α0 Hα0.
      assert (Hrpα' : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ1)
                        (add α Δ2) (open_pskl_wrt_pskl (uskl_to_pskl R)
                          (pskl_var_f α)) (open_pskl_wrt_pskl Q (pskl_var_f α))).
      { rewrite <- uskl_to_pskl_open. exact Hrpα. }
      rewrite (subst_pskl_in_pskl_intro α (uskl_to_pskl R) (pskl_var_f α0));
        [ | rewrite ftvar_in_pskl_uskl_to_pskl; clear - Fr; fsetdec ].
      rewrite (subst_pskl_in_pskl_intro α Q (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      eapply ad_refine_pskl_f_fmono with (F' := add α Δ2);
        [ clear; fsetdec | ].
      eapply ad_refine_pskl_f_delta_mono;
        [ | instantiate (1 := add α0 (remove α (add α Δ2)));
            clear Fr; fsetdec ].
      apply ad_refine_pskl_f_rename;
        [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
      exact (ad_refine_pskl_f_strip nil Θ1 Hrpα'
               ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
  - (* ForallInh untagged : decorated *)
    simpl in HwfP0, HwfS.
    inversion HwfP0 as [ | | | L0 Θa Δa P0a Hbody0 Heqa | | ]; subst.
    inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
    inversion HlcS; subst.
    match goal with Hb : forall _, lc_uskl _ |- _ => rename Hb into HlcSbody end.
    pick fresh α for
      (L `union` L0 `union` LS `union` dom Θ0 `union` dom Θ1
       `union` ftvar_in_pskl P0 `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
       `union` Δ1 `union` Δ2).
    assert (HαL : α `notin` L) by auto.
    assert (HwfΘα : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; auto).
    assert (HlcSα : lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α)))
      by (apply HlcSbody).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                       ⊢ₚₛᵃ (open_pskl_wrt_pskl P0 (pskl_var_f α))).
    { eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc (Hbody0 α ltac:(auto)) α)
        | clear; fsetdec ]. }
    assert (HwfSα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                   ⊢ₚₛᵃ (uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α)))).
    { rewrite uskl_to_pskl_open.
      eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc (HbodyS α ltac:(auto)) α)
        | clear; fsetdec ]. }
    assert (Hrigα : forall α0, α0 `in` (add α Δ1 `union` add α Δ2) ->
                    binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α0 Hα0. destruct (α0 == α) as [->|Hne].
      - unfold binds; left; reflexivity.
      - unfold binds; right. apply Hrig. clear - Hα0 Hne. fsetdec. }
    assert (Hnfdα : no_flex_dep (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ]. }
    assert (Hfafα : flex_above_free (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply faf_open_tvar; auto ]. }
    destruct (H0 α HαL HwfΘα HlcSα HwfP0α HwfSα Hrigα Hnfdα Hfafα)
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
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_uskl R).
        intros α0 Hα0.
        rewrite (subst_bskl_in_uskl_intro α R (uskl_var_f α0));
          [ | clear - Fr; fsetdec ].
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ exact Hconsα | exact Hα1 | exact Hdefsα ].
      * change (pskl_to_bskl_inh (pskl_all_syn P0))
          with (bskl_all_inh (pskl_to_bskl_inh P0)).
        apply ad_refine_syn_f__all
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P0).
        intros α0 Hα0.
        rewrite <- pskl_to_bskl_inh_open.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        assert (Hfr0 : α `notin` ftvar_in_pskl P0) by (clear - Fr; fsetdec).
        rewrite (subst_pskl_in_pskl_intro α P0 (pskl_var_f α0) Hfr0).
        rewrite <- subst_var_bskl_inh.
        eapply ad_refine_syn_f_fmono with (F' := add α Δ1);
          [ clear; fsetdec | ].
        eapply ad_refine_syn_f_delta_mono;
          [ | instantiate (1 := add α0 (remove α (add α Δ1)));
              clear Fr; fsetdec ].
        apply ad_refine_syn_f_rename;
          [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
        exact (ad_refine_syn_f_strip nil Θ1 Hrsα
                 ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
    + simpl. apply ad_refine_pskl_f__all
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_uskl R `union` ftvar_in_pskl Q).
      intros α0 Hα0.
      assert (Hrpα' : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ1)
                        (add α Δ2) (open_pskl_wrt_pskl (uskl_to_pskl R)
                          (pskl_var_f α)) (open_pskl_wrt_pskl Q (pskl_var_f α))).
      { rewrite <- uskl_to_pskl_open. exact Hrpα. }
      rewrite (subst_pskl_in_pskl_intro α (uskl_to_pskl R) (pskl_var_f α0));
        [ | rewrite ftvar_in_pskl_uskl_to_pskl; clear - Fr; fsetdec ].
      rewrite (subst_pskl_in_pskl_intro α Q (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      eapply ad_refine_pskl_f_fmono with (F' := add α Δ2);
        [ clear; fsetdec | ].
      eapply ad_refine_pskl_f_delta_mono;
        [ | instantiate (1 := add α0 (remove α (add α Δ2)));
            clear Fr; fsetdec ].
      apply ad_refine_pskl_f_rename;
        [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
      exact (ad_refine_pskl_f_strip nil Θ1 Hrpα'
               ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
  - (* ForallSyn tagged : decorated *)
    simpl in HwfP0, HwfS.
    inversion HwfP0 as [ | | | | | Θc Δc P0c Hg0 Hwf0c Heqc ]; subst.
    inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
    inversion HlcS; subst.
    match goal with Hb : forall _, lc_uskl _ |- _ => rename Hb into HlcSbody end.
    pick fresh α for
      (L `union` LS `union` dom Θ0 `union` dom Θ1
       `union` ftvar_in_pskl P0 `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
       `union` Δ1 `union` Δ2).
    assert (HαL : α `notin` L) by auto.
    assert (HwfΘα : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; auto).
    assert (HlcSα : lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α)))
      by (apply HlcSbody).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                       ⊢ₚₛᵃ (pskl_tophole P0)).
    { apply a_wf_pskl__tophole; auto.
      eapply a_wf_pskl_weaken; [ | exact Hwf0c ].
      intros y b Hb. unfold binds; right; exact Hb. }
    assert (HwfSα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                   ⊢ₚₛᵃ (uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α)))).
    { rewrite uskl_to_pskl_open.
      eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc (HbodyS α ltac:(auto)) α)
        | clear; fsetdec ]. }
    assert (Hrigα : forall α0, α0 `in` (Δ1 `union` add α Δ2) ->
                    binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α0 Hα0. destruct (α0 == α) as [->|Hne].
      - unfold binds; left; reflexivity.
      - unfold binds; right. apply Hrig. clear - Hα0 Hne. fsetdec. }
    assert (Hnfdα : no_flex_dep (Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ]. }
    assert (Hfafα : flex_above_free (Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply faf_open_tvar; auto ]. }
    destruct (H0 α HαL HwfΘα HlcSα HwfP0α HwfSα Hrigα Hnfdα Hfafα)
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
      apply no_flex_dep_cong with (Δ := Δ1 `union` add α Δ2);
        [ clear; fsetdec | exact Hnfdα1 ]. }
    split.
    { apply faf_strip with (α := α).
      apply faf_cong with (Δ := Δ1 `union` add α Δ2);
        [ clear; fsetdec | exact Hfafα1 ]. }
    split.
    + exists (bskl_all_syn (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; fsetdec ]. }
      split.
      * simpl. apply ad_pat_consis__forall_syn_tagged
          with (ε := ε) (L := dom Θ1 `union` singleton α `union` ftvar_in_uskl R).
        intros α0 Hα0.
        rewrite (subst_bskl_in_uskl_intro α R (uskl_var_f α0));
          [ | clear - Fr; fsetdec ].
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ exact Hconsα | exact Hα1 | exact Hdefsα ].
      * change (pskl_to_bskl_inh (pskl_tophole P0))
          with (bskl_tophole (pskl_to_bskl_inh P0)).
        apply ad_refine_syn_f__tophole_fill
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P0
                     `union` Δ1 `union` Δ2).
        intros α0 Hα0.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        replace (bskl_tophole (pskl_to_bskl_inh P0))
          with (subst_bskl_in_bskl (bskl_var_f α0) α
                  (bskl_tophole (pskl_to_bskl_inh P0)))
          by (simpl; rewrite subst_var_bskl_inh;
              rewrite subst_pskl_in_pskl_fresh_eq;
              [ reflexivity | clear - Fr; fsetdec ]).
        eapply ad_refine_syn_f_rename_ctx with (Θ1 := nil);
          [ change (nil ++ (α ~ abind_tvar) ++ Θ1)
              with ((α ~ abind_tvar) ++ Θ1); exact Hrsα
          | simpl; exact Hα1 | clear - Fr; fsetdec | clear - Hα0; fsetdec
          | exact Hdefsα ].
    + simpl. apply ad_refine_pskl_f__all
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_uskl R `union` ftvar_in_pskl Q).
      intros α0 Hα0.
      assert (Hrpα' : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ1)
                        (add α Δ2) (open_pskl_wrt_pskl (uskl_to_pskl R)
                          (pskl_var_f α)) (open_pskl_wrt_pskl Q (pskl_var_f α))).
      { rewrite <- uskl_to_pskl_open. exact Hrpα. }
      rewrite (subst_pskl_in_pskl_intro α (uskl_to_pskl R) (pskl_var_f α0));
        [ | rewrite ftvar_in_pskl_uskl_to_pskl; clear - Fr; fsetdec ].
      rewrite (subst_pskl_in_pskl_intro α Q (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      eapply ad_refine_pskl_f_fmono with (F' := add α Δ2);
        [ clear; fsetdec | ].
      eapply ad_refine_pskl_f_delta_mono;
        [ | instantiate (1 := add α0 (remove α (add α Δ2)));
            clear Fr; fsetdec ].
      apply ad_refine_pskl_f_rename;
        [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
      exact (ad_refine_pskl_f_strip nil Θ1 Hrpα'
               ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
  - (* ForallSyn untagged : decorated *)
    simpl in HwfP0, HwfS.
    inversion HwfP0 as [ | | | | | Θc Δc P0c Hg0 Hwf0c Heqc ]; subst.
    inversion HwfS as [ | | | LS ΘbS ΔbS SbS HbodyS HeqS | | ]; subst.
    inversion HlcS; subst.
    match goal with Hb : forall _, lc_uskl _ |- _ => rename Hb into HlcSbody end.
    pick fresh α for
      (L `union` LS `union` dom Θ0 `union` dom Θ1
       `union` ftvar_in_pskl P0 `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
       `union` Δ1 `union` Δ2).
    assert (HαL : α `notin` L) by auto.
    assert (HwfΘα : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; auto).
    assert (HlcSα : lc_uskl (open_uskl_wrt_uskl R (uskl_var_f α)))
      by (apply HlcSbody).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                       ⊢ₚₛᵃ (pskl_tophole P0)).
    { apply a_wf_pskl__tophole; auto.
      eapply a_wf_pskl_weaken; [ | exact Hwf0c ].
      intros y b Hb. unfold binds; right; exact Hb. }
    assert (HwfSα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                   ⊢ₚₛᵃ (uskl_to_pskl (open_uskl_wrt_uskl R (uskl_var_f α)))).
    { rewrite uskl_to_pskl_open.
      eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc (HbodyS α ltac:(auto)) α)
        | clear; fsetdec ]. }
    assert (Hrigα : forall α0, α0 `in` (Δ1 `union` add α Δ2) ->
                    binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α0 Hα0. destruct (α0 == α) as [->|Hne].
      - unfold binds; left; reflexivity.
      - unfold binds; right. apply Hrig. clear - Hα0 Hne. fsetdec. }
    assert (Hnfdα : no_flex_dep (Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ]. }
    assert (Hfafα : flex_above_free (Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply faf_open_tvar; auto ]. }
    destruct (H0 α HαL HwfΘα HlcSα HwfP0α HwfSα Hrigα Hnfdα Hfafα)
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
      apply no_flex_dep_cong with (Δ := Δ1 `union` add α Δ2);
        [ clear; fsetdec | exact Hnfdα1 ]. }
    split.
    { apply faf_strip with (α := α).
      apply faf_cong with (Δ := Δ1 `union` add α Δ2);
        [ clear; fsetdec | exact Hfafα1 ]. }
    split.
    + exists (bskl_all_syn (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; fsetdec ]. }
      split.
      * simpl. apply ad_pat_consis__forall_syn
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_uskl R).
        intros α0 Hα0.
        rewrite (subst_bskl_in_uskl_intro α R (uskl_var_f α0));
          [ | clear - Fr; fsetdec ].
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ exact Hconsα | exact Hα1 | exact Hdefsα ].
      * change (pskl_to_bskl_inh (pskl_tophole P0))
          with (bskl_tophole (pskl_to_bskl_inh P0)).
        apply ad_refine_syn_f__tophole_fill
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P0
                     `union` Δ1 `union` Δ2).
        intros α0 Hα0.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        replace (bskl_tophole (pskl_to_bskl_inh P0))
          with (subst_bskl_in_bskl (bskl_var_f α0) α
                  (bskl_tophole (pskl_to_bskl_inh P0)))
          by (simpl; rewrite subst_var_bskl_inh;
              rewrite subst_pskl_in_pskl_fresh_eq;
              [ reflexivity | clear - Fr; fsetdec ]).
        eapply ad_refine_syn_f_rename_ctx with (Θ1 := nil);
          [ change (nil ++ (α ~ abind_tvar) ++ Θ1)
              with ((α ~ abind_tvar) ++ Θ1); exact Hrsα
          | simpl; exact Hα1 | clear - Fr; fsetdec | clear - Hα0; fsetdec
          | exact Hdefsα ].
    + simpl. apply ad_refine_pskl_f__all
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_uskl R `union` ftvar_in_pskl Q).
      intros α0 Hα0.
      assert (Hrpα' : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ1)
                        (add α Δ2) (open_pskl_wrt_pskl (uskl_to_pskl R)
                          (pskl_var_f α)) (open_pskl_wrt_pskl Q (pskl_var_f α))).
      { rewrite <- uskl_to_pskl_open. exact Hrpα. }
      rewrite (subst_pskl_in_pskl_intro α (uskl_to_pskl R) (pskl_var_f α0));
        [ | rewrite ftvar_in_pskl_uskl_to_pskl; clear - Fr; fsetdec ].
      rewrite (subst_pskl_in_pskl_intro α Q (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      eapply ad_refine_pskl_f_fmono with (F' := add α Δ2);
        [ clear; fsetdec | ].
      eapply ad_refine_pskl_f_delta_mono;
        [ | instantiate (1 := add α0 (remove α (add α Δ2)));
            clear Fr; fsetdec ].
      apply ad_refine_pskl_f_rename;
        [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
      exact (ad_refine_pskl_f_strip nil Θ1 Hrpα'
               ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
  - (* UnivGhost *)
    simpl in HwfP0, HwfS.
    inversion HlcS; subst.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' Heqa ]; subst.
    inversion HwfS as [ | | | | | Θb Δb Rp Hgs Hwfs Heqb ]; subst.
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
      eapply ad_refine_pskl_f_guarded_r; [ exact Hwf1 | exact Hrp | exact Hgs ].
  - (* UnivGhostG *)
    simpl in HwfP0, HwfS.
    inversion HlcS; subst.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' Heqa ]; subst.
    inversion HwfS as [ | | | | | Θb Δb Rp Hgs Hwfs Heqb ]; subst.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists (bskl_tophole Qt). split.
      { simpl. rewrite HeQt. reflexivity. }
      split.
      * simpl. apply ad_pat_consis__topholeg. exact Hcons.
      * simpl. apply ad_refine_syn_f__tophole_keep; [ | exact Hrs ].
        eapply ad_refine_syn_f_guarded_r;
          [ exact Hwf1 | exact Hrs | apply guarded_pskl_to_bskl_inh; exact Hg0 ].
    + simpl. apply ad_refine_pskl_f__tophole_keep; [ | exact Hrp ].
      eapply ad_refine_pskl_f_guarded_r; [ exact Hwf1 | exact Hrp | exact Hgs ].
  - (* UnivGhost1 : decorated *)
    simpl in HwfP0, HwfS.
    inversion HwfP0 as [ | | | L0 Θa Δa P0a Hbody0 Heqa | | ]; subst.
    inversion HwfS as [ | | | | | ΘbS ΔbS SbS HgS HwfSbody HeqS ]; subst.
    pick fresh α for
      (L `union` L0 `union` dom Θ0 `union` dom Θ1
       `union` ftvar_in_pskl P0 `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
       `union` Δ1 `union` Δ2).
    assert (HαL : α `notin` L) by auto.
    assert (HwfΘα : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; auto).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                       ⊢ₚₛᵃ (open_pskl_wrt_pskl P0 (pskl_var_f α))).
    { eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc (Hbody0 α ltac:(auto)) α)
        | clear; fsetdec ]. }
    assert (HwfSα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty
                   ⊢ₚₛᵃ (uskl_to_pskl (uskl_tophole R))).
    { simpl. apply a_wf_pskl__tophole; [ exact HgS | ].
      eapply a_wf_pskl_weaken; [ | exact HwfSbody ].
      intros y b Hb. unfold binds; right; exact Hb. }
    assert (Hrigα : forall α0, α0 `in` (add α Δ1 `union` Δ2) ->
                    binds α0 abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros α0 Hα0. destruct (α0 == α) as [->|Hne].
      - unfold binds; left; reflexivity.
      - unfold binds; right. apply Hrig. clear - Hα0 Hne. fsetdec. }
    assert (Hnfdα : no_flex_dep (add α Δ1 `union` Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply no_flex_dep_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply no_flex_dep_open_tvar; auto ]. }
    assert (Hfafα : flex_above_free (add α Δ1 `union` Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { apply faf_cong with (Δ := add α (Δ1 `union` Δ2));
        [ clear; fsetdec | apply faf_open_tvar; auto ]. }
    destruct (H0 α HαL HwfΘα HlcS HwfP0α HwfSα Hrigα Hnfdα Hfafα)
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
      apply no_flex_dep_cong with (Δ := add α Δ1 `union` Δ2);
        [ clear; fsetdec | exact Hnfdα1 ]. }
    split.
    { apply faf_strip with (α := α).
      apply faf_cong with (Δ := add α Δ1 `union` Δ2);
        [ clear; fsetdec | exact Hfafα1 ]. }
    split.
    + exists (bskl_all_inh (close_bskl_wrt_bskl α Qtα)). split.
      { simpl. rewrite bskl_to_pskl_close. rewrite HeQtα.
        rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          [ reflexivity | clear - Fr; fsetdec ]. }
      split.
      * simpl. apply ad_pat_consis__tophole_inh
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_uskl R).
        intros α0 Hα0.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        replace (uskl_tophole R)
          with (subst_bskl_in_uskl (uskl_var_f α0) α (uskl_tophole R))
          by (simpl; rewrite subst_bskl_in_uskl_fresh_eq;
              [ reflexivity | clear - Fr; fsetdec ]).
        change ((α0 ~ abind_tvar) ++ Θ1)
          with (nil ++ (α0 ~ abind_tvar) ++ Θ1).
        eapply ad_pat_consis_rename_tvar;
          [ exact Hconsα | exact Hα1 | exact Hdefsα ].
      * change (pskl_to_bskl_inh (pskl_all_syn P0))
          with (bskl_all_inh (pskl_to_bskl_inh P0)).
        apply ad_refine_syn_f__all
          with (L := dom Θ1 `union` singleton α `union` ftvar_in_pskl P0).
        intros α0 Hα0.
        rewrite <- pskl_to_bskl_inh_open.
        rewrite (subst_bskl_in_bskl_intro α (close_bskl_wrt_bskl α Qtα)
                   (bskl_var_f α0));
          [ | rewrite ftvar_in_bskl_close_bskl_wrt_bskl; clear; fsetdec ].
        rewrite open_bskl_wrt_bskl_close_bskl_wrt_bskl.
        assert (Hfr0 : α `notin` ftvar_in_pskl P0) by (clear - Fr; fsetdec).
        rewrite (subst_pskl_in_pskl_intro α P0 (pskl_var_f α0) Hfr0).
        rewrite <- subst_var_bskl_inh.
        eapply ad_refine_syn_f_fmono with (F' := add α Δ1);
          [ clear; fsetdec | ].
        eapply ad_refine_syn_f_delta_mono;
          [ | instantiate (1 := add α0 (remove α (add α Δ1)));
              clear Fr; fsetdec ].
        apply ad_refine_syn_f_rename;
          [ | clear; fsetdec | exact Hα1 | exact Hdefsα ].
        exact (ad_refine_syn_f_strip nil Θ1 Hrsα
                 ltac:(clear; solve_notin_auto) ltac:(clear; solve_notin_auto)).
    + simpl.
      assert (Hrpα' : ad_refine_pskl_f Δ2 ((α ~ abind_tvar) ++ Θ1) Δ2
                        (pskl_tophole (uskl_to_pskl R))
                        (open_pskl_wrt_pskl Q (pskl_var_f α)))
        by exact Hrpα.
      apply ad_refine_pskl_f__tophole_fill
        with (L := dom Θ1 `union` singleton α
                   `union` ftvar_in_uskl R `union` ftvar_in_pskl Q
                   `union` Δ1 `union` Δ2).
      intros α0 Hα0.
      rewrite (subst_pskl_in_pskl_intro α Q (pskl_var_f α0));
        [ | clear - Fr; fsetdec ].
      replace (pskl_tophole (uskl_to_pskl R))
        with (subst_pskl_in_pskl (pskl_var_f α0) α
                (pskl_tophole (uskl_to_pskl R)))
        by (simpl; rewrite subst_pskl_in_pskl_fresh_eq;
            [ reflexivity
            | rewrite ftvar_in_pskl_uskl_to_pskl; clear - Fr; fsetdec ]).
      eapply ad_refine_pskl_f_rename_ctx with (Θ1 := nil);
        [ change (nil ++ (α ~ abind_tvar) ++ Θ1)
            with ((α ~ abind_tvar) ++ Θ1); exact Hrpα'
        | simpl; exact Hα1 | clear - Fr; fsetdec | clear - Hα0; fsetdec
        | exact Hdefsα ].
  - (* UnivGhost2 *)
    simpl in HwfS. inversion HlcS; subst.
    inversion HwfS as [ | | | | | Θb Δb Rp Hgs Hwfs Heqb ]; subst.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists Qt. split; [ exact HeQt | ].
      split; [ simpl; apply ad_pat_consis__tophole_drop; exact Hcons | exact Hrs ].
    + simpl. apply ad_refine_pskl_f__tophole_remove. exact Hrp.
  - (* GhostR *)
    split; [ apply a_isub_refl; try assumption; auto | ].
    split; [ exact Hwf | ]. split; [ exact Hnfd | ]. split; [ exact Hfaf | ].
    split.
    + exists (pskl_to_bskl_syn (uskl_to_pskl R)).
      split; [ apply bskl_to_pskl_pskl_to_bskl_syn | ].
      split.
      * apply ad_pat_consis_psi_cong with (Ψ := empty); [ | symmetry; exact H0 ].
        apply ad_pat_consis_refl_erase; [ exact HlcS | ].
        intros α0 Hα0.
        assert (HX' : α0 `in` ftvar_in_pskl (uskl_to_pskl R))
          by (rewrite ftvar_in_pskl_uskl_to_pskl; exact Hα0).
        destruct (a_wf_pskl_ftv_tvarish HwfS HX') as [HΔ | Ht];
          [ clear - HΔ; fsetdec | exact Ht ].
      * replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
        apply ad_refine_syn_f__hole; [ exact H | exact HwfS ].
    + apply ad_refine_pskl_f_refl.
      eapply a_wf_pskl_delta_mono; [ exact HwfS | fsetdec ].
  - (* UnivGhostR *)
    simpl in HwfP0.
    inversion HwfP0 as [ | | | | | Θa Δa P0' Hg0 Hwf0' Heqa ]; subst.
    destruct IHHc
      as [Hle [Hwf1 [Hnfd1 [Hfaf1 [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]]; auto.
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
    split.
    + exists Qt. split; [ exact HeQt | ].
      split; [ exact Hcons | ].
      apply ad_refine_syn_f__tophole_remove. exact Hrs.
    + exact Hrp.
Qed.


(* ===================================================================== *)
(*  Soundness of consistency, part 1 (thm:sound-consistency)              *)
(*                                                                        *)
(*  Now a COROLLARY of the decorated soundness above.  An ordinary        *)
(*  consistency run decorates to a run with the EMPTY tag context         *)
(*  (lemma:decorating-algorithmic-consistency, [a_consis_decorate]),      *)
(*  whose subject is the plain skeleton read as an untagged unresolved    *)
(*  skeleton.  The decorated conclusion then reads back verbatim, because *)
(*  erasure is a retraction on plain skeletons                            *)
(*  ([uskl_to_pskl_pskl_to_uskl] : ⌊pskl_to_uskl P⌋ˢ = P).                *)
(* ===================================================================== *)

Corollary a_consis_sound_aux : forall Δ1 Δ2 Θ0 P0 P P' Θ1,
  Θ0 ⊢ₐ[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (forall α, α `in` (Δ1 `union` Δ2) -> binds α abind_tvar Θ0) ->
  no_flex_dep (Δ1 `union` Δ2) Θ0 ->
  flex_above_free (Δ1 `union` Δ2) Θ0 ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  no_flex_dep (Δ1 `union` Δ2) Θ1 /\ flex_above_free (Δ1 `union` Δ2) Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     empty ⨟ Θ1 ⊢ₛᵃ (pskl_to_uskl P) ∼ Qt /\
     ad_refine_syn_f Δ1 Θ1 Δ1 (pskl_to_bskl_inh P0) Qt) /\
  ad_refine_pskl_f Δ2 Θ1 Δ2 P P'.
Proof.
  intros * Hc Hwf HwfP0 HwfP Hrig Hnfd Hfaf.
  assert (HlcS : lc_uskl (pskl_to_uskl P))
    by (apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; eauto).
  assert (HwfS : Θ0 ⨟ empty ⊢ₚₛᵃ (uskl_to_pskl (pskl_to_uskl P)))
    by (rewrite uskl_to_pskl_pskl_to_uskl; exact HwfP).
  destruct (a_consistag_sound_aux
              (a_consis_decorate Hc (a_wf_aenv_uniq_local Hwf)) Hwf HlcS
              HwfP0 HwfS Hrig Hnfd Hfaf)
    as [Hle [Hwf1 [Hnfd1 [Hfaf1 [Hex Hrp]]]]].
  rewrite uskl_to_pskl_pskl_to_uskl in Hrp.
  split; [ exact Hle | ]. split; [ exact Hwf1 | ].
  split; [ exact Hnfd1 | ]. split; [ exact Hfaf1 | ].
  split; [ exact Hex | exact Hrp ].
Qed.


(** Paper-shaped statement (thm:sound-consistency, part 1): with the
    auxiliary Δ-contexts empty, a consistency run is an identity
    increase whose output is a coloured skeleton consistent with the
    synthesised painting of the input and a valid refinement of both
    inputs.  (The fill-hygiene set is discharged by [*_f_forget].) *)
Corollary a_consis_sound : forall Θ0 P0 P P' Θ1,
  Θ0 ⊢ₐ[ P0 ] P ∼ P' ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  Θ0 ⊴ Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     empty ⨟ Θ1 ⊢ₛᵃ (pskl_to_uskl P) ∼ Qt /\
     Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0) ⊳ Qt) /\
  Θ1 ⨟ empty ⊢ᵣₚᵃ P ⊳ P'.
Proof.
  intros * Hc Hwf HwfP0 HwfP.
  destruct (a_consis_sound_aux Hc Hwf HwfP0 HwfP
              ltac:(intros α Hα; clear - Hα; solve_notin_auto)
              ltac:(intros β τ Hb; apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; solve_notin_auto)
              ltac:(intros Θa β b Θb Heq Hne;
                    apply inter_empty_pointwise;
                    intros α Hα; clear - Hα; solve_notin_auto))
    as [Hle [Hwf1 [Hnfd [Hfaf [[Qt [HeQt [Hcons Hrs]]] Hrp]]]]].
  split; [ exact Hle | ].
  split.
  - exists Qt. split; [ exact HeQt | ]. split; [ exact Hcons | ].
    eapply ad_refine_syn_f_forget; exact Hrs.
  - eapply ad_refine_pskl_f_forget; exact Hrp.
Qed.
