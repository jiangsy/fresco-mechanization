(** Frost — completeness of check-mode subtyping [⩽] against the reference
    shallow polymorphic subtyping [d_shallow_sub_mono] ([≤ₘ⟨n⟩]).

    Headline (Bruno's margin note, declarative.tex): the FN-depth-indexed
    reference relation is a lower bound on [⩽]'s expressive power, i.e.

      Γ ⊢ A ≤ₘ⟨n⟩ B  →  ∅ ⨟ Γ ⊢[mode_fn^n mode_tc] syn{A} ⩽ inh{B}.

    See [decl/def_extra.v] for the design of [d_shallow_sub_mono]. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

(** ** Paint helper lemmas. *)

(* A monotype's syn-painting is a tag-free [is_ttyp]. *)
Lemma mono_paint_is_ttyp : forall A,
    mono_ptyp A -> is_ttyp (ptyp_to_utyp_syn A).
Proof.
  intros A Hmono. induction Hmono; simpl; eauto using is_ttyp.
Qed.

Lemma mono_paint_d_tags : forall A,
    mono_ptyp A -> d_tags empty (ptyp_to_utyp_syn A).
Proof.
  intros A Hmono. induction Hmono; simpl.
  - apply d_tags__unit. fsetdec.
  - apply d_tags__var. fsetdec.
  - eapply d_tags__arrow; eauto; fsetdec.
Qed.

(* Painting preserves well-scopedness. *)
Lemma ptyp_wf_utyp_wf : forall Γ A,
    Γ ⊢ₚ A -> Γ ⊢ᵤ (ptyp_to_utyp_syn A).
Proof.
  intros Γ A Hwf. induction Hwf; simpl; eauto using d_wf_utyp.
  - eapply d_wf_utyp__all_syn with (L := L). intros α Hα.
    replace (utyp_var_f α) with (ptyp_to_utyp_syn (ptyp_var_f α)) by reflexivity.
    rewrite <- ptyp_to_utyp_syn_open. eauto.
Qed.

Lemma inh_paint_is_ityp : forall Γ A,
    Γ ⊢ₚ A -> is_ityp (ptyp_to_btyp_inh A).
Proof.
  intros Γ A Hwf. induction Hwf; simpl; eauto using is_ityp.
  - eapply is_ityp__all with (L := L). intros α Hα.
    replace (btyp_var_f α) with (ptyp_to_btyp_inh (ptyp_var_f α)) by reflexivity.
    rewrite <- ptyp_to_btyp_inh_open. eauto.
Qed.

(** ** Reflexivity of [⩽] across the syn/inh painting (the [refl] case). *)

(* Consistency is reflexive across the paint: [syn{A} ∼ inh{A}] for any [A]. *)
Lemma d_consis_refl_paint : forall Γ A,
    Γ ⊢ₚ A -> empty ⨟ Γ ⊢ (ptyp_to_utyp_syn A) ∼ (ptyp_to_btyp_inh A).
Proof.
  intros Γ A Hwf. induction Hwf; simpl.
  - apply d_consis__unit. fsetdec.
  - apply d_consis__var; [ assumption | fsetdec ].
  - eapply d_consis__arrow; [ eassumption | eassumption | fsetdec ].
  - eapply d_consis__forall_inh_untagged with (L := L). intros α Hα.
    replace (utyp_var_f α) with (ptyp_to_utyp_syn (ptyp_var_f α)) by reflexivity.
    replace (btyp_var_f α) with (ptyp_to_btyp_inh (ptyp_var_f α)) by reflexivity.
    rewrite <- ptyp_to_utyp_syn_open. rewrite <- ptyp_to_btyp_inh_open. eauto.
Qed.

(* Subtyping is reflexive across the paint at [mode_tc]: [syn{A} ⩽[tc] inh{A}].
   Guarded leaves close by [SubCheck] + consistency-refl; a top-level [∀]
   peels by [SubForallR] then [SubForallL] (instantiated by the bound var). *)
Lemma d_sub_refl_paint : forall Γ A,
    Γ ⊢ₚ A -> empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn A) ⩽ (ptyp_to_btyp_inh A).
Proof.
  intros Γ A Hwf.
  induction Hwf as [ Γ | Γ α Hbnd | Γ A1 A2 Hwf1 IH1 Hwf2 IH2 | L Γ A0 Hwf0 IH0 ];
    simpl.
  - (* unit *)
    apply d_sub__check;
      [ apply guarded_utyp__unit | apply guarded_btyp__unit
      | apply d_consis__unit; fsetdec | apply is_ityp__unit ].
  - (* var *)
    apply d_sub__check;
      [ apply guarded_utyp__var | apply guarded_btyp__var
      | apply d_consis__var; [ assumption | fsetdec ] | apply is_ityp__var ].
  - (* arrow: guarded both sides, consistency-refl, is_ityp from inh paint *)
    apply d_sub__check.
    + apply guarded_utyp__arrow; apply lc_ptyp_to_utyp_syn; eapply d_wf_ptyp_lc_loc; eassumption.
    + apply guarded_btyp__arrow; apply lc_ptyp_to_btyp_inh; eapply d_wf_ptyp_lc_loc; eassumption.
    + eapply d_consis__arrow;
        [ apply d_consis_refl_paint; eassumption
        | apply d_consis_refl_paint; eassumption | fsetdec ].
    + apply is_ityp__arrow; eapply inh_paint_is_ityp; eassumption.
  - (* ∀: SubForallR (intro α) then SubForallL (instantiate by α) *)
    apply d_sub__forall_r with (L := L `union` dom Γ).
    + apply is_ityp__all with (L := L). intros α Hα.
      replace (btyp_var_f α) with (ptyp_to_btyp_inh (ptyp_var_f α)) by reflexivity.
      rewrite <- ptyp_to_btyp_inh_open.
      eapply inh_paint_is_ityp. apply Hwf0. exact Hα.
    + intros α Hα.
      replace (btyp_var_f α) with (ptyp_to_btyp_inh (ptyp_var_f α)) by reflexivity.
      rewrite <- ptyp_to_btyp_inh_open.
      apply d_sub__forall_l_untagged with (Ψ' := (@empty : atoms)) (ph := utyp_var_f α).
      * intro Hco; discriminate.
      * fsetdec.
      * apply d_tags__var; reflexivity.
      * apply d_wf_utyp__var; simpl; auto.
      * apply is_ttyp__var.
      * replace (utyp_var_f α) with (ptyp_to_utyp_syn (ptyp_var_f α)) by reflexivity.
        rewrite <- ptyp_to_utyp_syn_open.
        apply d_sub_equiv with (Δ := (@empty : atoms)); [ fsetdec | ].
        apply IH0. clear - Hα. fsetdec.
Qed.

(* At [mode_tc] the RHS of [⩽] is always inherited (is_ityp). *)
Lemma d_sub_tc_is_ityp : forall Ψ Γ C B,
    Ψ ⨟ Γ ⊢[ mode_tc ] C ⩽ B -> is_ityp B.
Proof.
  intros Ψ Γ C B H. dependent induction H; eauto.
Qed.

(** ** Completeness of [⩽] against the paper's shallow subtyping.

      Γ ⊢ A ≤ B  →  ∅ ⨟ Γ ⊢[mode_tc] syn{A} ⩽ inh{B}.

    Each reference rule maps to the matching [⩽] rule: [refl] ↦
    [d_sub_refl_paint]; [forall_r] ↦ [SubForallR] ([is_ityp] from the IH via
    [d_sub_tc_is_ityp]); [forall_l] ↦ [SubForallL] (the monotype paint is a
    tag-free [is_ttyp]). *)
Theorem d_shallow_sub_complete : forall Γ A A',
    Γ ⊢ A ≤ A' ->
    empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn A) ⩽ (ptyp_to_btyp_inh A').
Proof.
  intros Γ A A' Hsub. induction Hsub; simpl in *.
  - (* refl *)
    apply d_sub_refl_paint. assumption.
  - (* forall_r *)
    apply d_sub__forall_r with (L := L `union` dom Γ).
    + apply is_ityp__all with (L := L). intros α Hα.
      replace (btyp_var_f α) with (ptyp_to_btyp_inh (ptyp_var_f α)) by reflexivity.
      rewrite <- ptyp_to_btyp_inh_open.
      eapply d_sub_tc_is_ityp. apply H0. fsetdec.
    + intros α Hα.
      replace (btyp_var_f α) with (ptyp_to_btyp_inh (ptyp_var_f α)) by reflexivity.
      rewrite <- ptyp_to_btyp_inh_open.
      apply H0. fsetdec.
  - (* forall_l: instantiate by the monotype paint *)
    apply d_sub__forall_l_untagged
      with (Ψ' := (@empty : atoms)) (ph := ptyp_to_utyp_syn I).
    + intro Hco; discriminate.
    + fsetdec.
    + apply mono_paint_d_tags. assumption.
    + apply ptyp_wf_utyp_wf. assumption.
    + apply mono_paint_is_ttyp. assumption.
    + rewrite <- ptyp_to_utyp_syn_open.
      apply d_sub_equiv with (Δ := (@empty : atoms)); [ fsetdec | ].
      assumption.
Qed.

(** ** Only polytypes need to be annotated (annotation-level property).

    NB. This is a DIFFERENT property from "no guessing of polytypes": that one
    is about instantiations inside SUBTYPING derivations (the [⩽] [forall_l]
    guesses), whereas this one is about the USER-WRITTEN annotations on terms.
    They are not equivalent.

    Statement (one direction, on lambda binders): a MONOTYPE annotation on a
    lambda is redundant — it may be dropped, and the monotype argument is
    recovered by inference ([d_typing__abs] guesses / inherits it).
    Contrapositive: a lambda annotation that is actually load-bearing must sit
    at a POLYMORPHIC argument type. *)

(* A monotype has a unique [btyp] pre-image under erasure: its own painting
   (and for a monotype the syn and inh paintings coincide). *)
Lemma mono_btyp_to_ptyp_inv : forall A B,
    mono_ptyp A -> btyp_to_ptyp B = A -> B = ptyp_to_btyp_inh A.
Proof.
  intros A B Hmono. revert B.
  induction Hmono; intros B Heq; destruct B; simpl in *;
    try discriminate; try reflexivity.
  - (* var *) inversion Heq; subst. reflexivity.
  - (* arrow *) simpl in Heq. injection Heq as Heq1 Heq2.
    apply IHHmono1 in Heq1. apply IHHmono2 in Heq2. subst. reflexivity.
Qed.

(* GENERALISED over the result type: with the base-term restriction removed,
   [__sub] can retype an annotated lambda (through its [ti] synthesis) and
   [__forall] can generalise it, so the proof is an induction, not a single
   inversion.  The mono domain is still FORCED: any [btyp] erasing to a
   monotype [A] is [inh A] ([mono_btyp_to_ptyp_inv]), whatever the mode. *)
Lemma mono_lambda_anno_redundant_gen : forall m Γ ea B,
    Γ ⊢[ m ] ea ⦂ B ->
    forall A e, ea = exp_abs_anno A e ->
    mono_ptyp A ->
    Γ ⊢[ m ] (exp_abs e) ⦂ B.
Proof.
  intros m Γ ea B Hty. induction Hty; intros A0 e0 Heq Hmono;
    try discriminate Heq.
  - (* __sub: drop the annotation in the [ti] synthesis, re-subsume. *)
    subst e.
    eapply d_typing__sub;
      [ eapply IHHty; [ reflexivity | exact Hmono ] | eassumption ].
  - (* __forall: the annotated lambda is a value; so is the bare one. *)
    subst e.
    apply d_typing__forall with (L := L); [ apply is_value__abs | ].
    intros α Hα. eapply H1; [ exact Hα | reflexivity | exact Hmono ].
  - (* __abs_anno: the domain [B1] erases to the mono [A0], hence is [inh A0];
       the body premise is exactly [d_typing__abs]'s. *)
    injection Heq; intros; subst.
    (* [subst] consumed the erasure equation: the annotation is now
       [btyp_to_ptyp B1] everywhere.  The mono inverse pins [B1] to the
       inherited painting of its own erasure. *)
    assert (HB1 : B1 = ptyp_to_btyp_inh (btyp_to_ptyp B1))
      by (apply mono_btyp_to_ptyp_inv; [ exact Hmono | reflexivity ]).
    match goal with Hmc : mod_comp_ty (btyp_arrow B1 _) _ |- _ =>
      rewrite HB1 in Hmc end.
    rewrite HB1.
    eapply d_typing__abs; eassumption.
Qed.

(* For a monotype annotation [A], the lambda's domain is forced to [inh A]
   (= [mono_btyp_to_ptyp_inv]); stating it that way avoids the erasure equation. *)
Theorem mono_lambda_anno_redundant : forall m Γ A e B2,
    mono_ptyp A ->
    Γ ⊢[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B2) ->
    Γ ⊢[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B2).
Proof.
  intros m Γ A e B2 Hmono Hty.
  eapply mono_lambda_anno_redundant_gen;
    [ exact Hty | reflexivity | exact Hmono ].
Qed.
