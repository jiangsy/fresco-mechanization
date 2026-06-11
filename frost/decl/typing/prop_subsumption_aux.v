(** Auxiliary facts for declarative general subsumption, stated over the
    current split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
From Hammer Require Export Tactics.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.typing.prop_weakening.
Require Import src.frost.decl.typing.def_gen.

Set Implicit Arguments.

Ltac nbauto := try sauto limit:30.

Lemma d_consis_gen_weakening : forall Γ1 Γ2 Γ3 Δ D1 D2,
    Δ ⨟ (Γ1 ++ Γ3) ⊨ᵍ D1 ≈ D2 ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊨ᵍ D1 ≈ D2.
Proof.
  intros Γ1 Γ2 Γ3 Δ D1 D2 H.
  dependent induction H; nbauto.
  - apply d_consis_gen__var.
    eapply binds_weaken; eauto.
  - apply d_consis_gen__arrow; nbauto.
  - apply d_consis_gen__forall_tag_inh with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); nbauto.
    + intros X HX.
      rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
      eapply H0; eauto.
  - apply d_consis_gen__forall_syn_inh  with 
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); nbauto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_tag_syn with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_syn with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_tag_syn_erasure with
      (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
  - apply d_consis_gen__forall_inh with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)).
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
Qed.

Lemma d_consis_gen_weakening_head : forall Γ Γ' Δ B1 B2,
    Δ ⨟ Γ ⊨ᵍ B1 ≈ B2 ->
    Δ ⨟ (Γ' ++ Γ) ⊨ᵍ B1 ≈ B2.
Proof.
  intros Γ Γ' Δ B1 B2 H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_consis_gen_weakening. simpl. exact H.
Qed.

Lemma d_sub_gen_weakening : forall Γ1 Γ2 Γ3 m Δ B1 B2,
    Δ ⨟ (Γ1 ++ Γ3) ⊢ᵍ[ m ] B1 ⊑ B2 ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ᵍ[ m ] B1 ⊑ B2.
Proof.
  intros Γ1 Γ2 Γ3 m Δ B1 B2 H.
  dependent induction H; try sauto limit:30 use:d_consis_weakening, d_consis_gen_weakening.
  - apply d_sub_gen__infer_gen; nbauto.
    + apply d_consis_weakening; nbauto.
  - apply d_sub_gen__check_gen; nbauto.
    + apply d_consis_weakening; nbauto.
  - apply d_sub_gen__forall_r with (L := L `union` dom (Γ1 ++ Γ2 ++ Γ3)); nbauto.
    intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3); nbauto.
    eapply H1; eauto.
  - apply d_sub_gen__arg.
    + apply d_consis_gen_weakening. exact H.
    + eapply IHd_sub_gen; eauto.
  - apply d_sub_gen__forall_l_tagged with (Δ' := Δ') (ph := ph); nbauto.
    + apply d_wf_utyp_weakening. eassumption.
  - apply d_sub_gen__forall_l_untagged with (Δ' := Δ') (ph := ph); nbauto.
    + apply d_wf_utyp_weakening. eassumption.
Qed.

Lemma d_sub_gen_weakening_head : forall Γ Γ' m Δ D1 D2,
    Δ ⨟ Γ ⊢ᵍ[ m ] D1 ⊑ D2 ->
    Δ ⨟ (Γ' ++ Γ) ⊢ᵍ[ m ] D1 ⊑ D2.
Proof.
  intros Γ Γ' m Δ D1 D2 H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_gen_weakening. simpl. exact H.
Qed.

Lemma list_swap_middle_gen : forall {A : Type} (l1 l2 l3 l4 : list A),
    Permutation ((l1 ++ l2) ++ (l3 ++ l4)) ((l1 ++ l3) ++ (l2 ++ l4)).
Proof.
  intros A l1 l2 l3 l4.
  replace ((l1 ++ l2) ++ (l3 ++ l4)) with (l1 ++ l2 ++ l3 ++ l4).
  - replace ((l1 ++ l3) ++ (l2 ++ l4)) with (l1 ++ l3 ++ l2 ++ l4).
    + apply Permutation_app_head. apply Permutation_app_swap_app.
    + rewrite app_assoc. reflexivity.
  - rewrite app_assoc. reflexivity.
Qed.

Lemma d_consis_gen_trans : forall Δa Δb Γ D1 D2 B,
    Δa ⨟ Γ ⊨ᵍ D1 ≈ D2 ->
    Δb ⨟ Γ ⊨ᵍ D2 ≈ btyp_to_gutyp B ->
    list_disjoint Δa Δb ->
    exists Δc, Permutation Δc (Δa ++ Δb) /\
           Δc ⨟ Γ ⊨ᵍ D1 ≈ btyp_to_gutyp B.
Proof.
Admitted.
Lemma d_consis_gen_refl_btyp : forall Γ B,
    Γ ⊢ᵦ B ->
    nil ⨟ Γ ⊨ᵍ (btyp_to_gutyp B) ≈ (btyp_to_gutyp B).
Proof.
  intros Γ B Hwf.
  dependent induction Hwf.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var. exact H.
  - simpl. replace (@nil atom) with (@nil atom ++ @nil atom) by reflexivity.
    apply d_consis_gen__arrow.
    + exact IHHwf1.
    + exact IHHwf2.
  - simpl. apply d_consis_gen__forall_syn with (L := L).
    intros X HX.
    change (gutyp_var_f X) with (btyp_to_gutyp (btyp_var_f X)).
    repeat rewrite <- btyp_to_gutyp_open.
    apply H0. exact HX.
  - simpl. apply d_consis_gen__forall_inh with (L := L).
    intros X HX.
    change (gutyp_var_f X) with (btyp_to_gutyp (btyp_var_f X)).
    repeat rewrite <- btyp_to_gutyp_open.
    apply H0. exact HX.
Qed.

Lemma d_consis_refl_styp_as_utyp : forall Γ B,
    Γ ⊢ᵦ B ->
    is_styp B ->
    nil ⨟ Γ ⊨ (btyp_to_utyp_syn B) ≈ B.
Proof.
  intros Γ B Hwf Hst.
  generalize dependent Hst.
  dependent induction Hwf; intros Hst; inversion Hst; subst; simpl.
  - apply d_consis__unit.
  - apply d_consis__var. exact H.
  - replace (@nil atom) with (@nil atom ++ @nil atom) by reflexivity.
    apply d_consis__arrow.
    + apply IHHwf1. exact H1.
    + apply IHHwf2. exact H2.
  - apply d_consis__forall_syn with (L := L `union` L0).
    intros X HX.
    change (utyp_var_f X) with (btyp_to_utyp_syn (btyp_var_f X)).
    rewrite <- btyp_to_utyp_syn_open.
    apply H0; auto.
Qed.

Lemma d_consis_gen_refl_styp_as_utyp : forall Γ B,
    Γ ⊢ᵦ B ->
    is_styp B ->
    nil ⨟ Γ ⊨ᵍ (utyp_to_gutyp (btyp_to_utyp_syn B)) ≈ (btyp_to_gutyp B).
Proof.
  intros Γ B Hwf Hst.
  generalize dependent Hst.
  dependent induction Hwf; intros Hst; inversion Hst; subst; simpl.
  - apply d_consis_gen__unit.
  - apply d_consis_gen__var. exact H.
  - replace (@nil atom) with (@nil atom ++ @nil atom) by reflexivity.
    apply d_consis_gen__arrow.
    + apply IHHwf1. exact H1.
    + apply IHHwf2. exact H2.
  - apply d_consis_gen__forall_syn with (L := L `union` L0).
    intros X HX.
    change (gutyp_var_f X) with (utyp_to_gutyp (utyp_var_f X)).
    rewrite <- utyp_to_gutyp_open.
    change (utyp_var_f X) with (btyp_to_utyp_syn (btyp_var_f X)).
    rewrite <- btyp_to_utyp_syn_open.
    replace (open_gutyp_wrt_gutyp (btyp_to_gutyp B)
               (utyp_to_gutyp (btyp_to_utyp_syn (btyp_var_f X))))
      with (btyp_to_gutyp (open_btyp_wrt_btyp B (btyp_var_f X))).
    apply H0; auto.
    change (gutyp_var_f X) with (btyp_to_gutyp (btyp_var_f X)).
    simpl.
    apply btyp_to_gutyp_open.
Qed.

(** [compose_tags C B] is the tag context produced by composing the two
    consistency derivations through a synthesised middle type.  Making it an
    explicit *function of (C,B)* (rather than an existential witness) is the
    crux of B.2: the witness is then manifestly independent of the variable
    used to open a quantifier body, so the cofinite case has a uniform Δc.

    The only rule that *grows* the context is the tagged→inh composition
    (paper [ForallInh] with δ=ε): a tagged-∀ that was dropped on the
    synthesised side ([ForallSyn], no tag) must be re-recorded when it meets
    an inherited ∀.  Hence the result is a strict superset of [Δa ∪ Δb]. *)
Fixpoint compose_tags (C : utyp) (B : btyp) {struct C} : list atom :=
  match C with
  | utyp_arrow C1 C2 =>
      match B with
      | btyp_arrow B1 B2 => compose_tags C1 B1 ++ compose_tags C2 B2
      | _ => nil
      end
  | utyp_all_etag ε C0 =>
      match B with
      | btyp_all_inh B0 => ε :: compose_tags C0 B0
      | btyp_all_syn B0 => compose_tags C0 B0
      | _ => nil
      end
  | utyp_all_syn C0 =>
      match B with
      | btyp_all_inh B0 => compose_tags C0 B0
      | btyp_all_syn B0 => compose_tags C0 B0
      | _ => nil
      end
  | _ => nil
  end.

(** [compose_tags] inspects only the head constructors and etag names, never
    type variables, so it is invariant under opening with a variable. *)
Lemma compose_tags_open_rec : forall C B X Y k,
    compose_tags (open_utyp_wrt_utyp_rec k (utyp_var_f X) C)
                 (open_btyp_wrt_btyp_rec k (btyp_var_f Y) B) = compose_tags C B.
Proof.
  induction C; intros B X Y k; destruct B; simpl;
    repeat match goal with
           | [ |- context[lt_eq_lt_dec ?a ?b] ] =>
               destruct (lt_eq_lt_dec a b) as [[|]|]
           end; simpl; try reflexivity;
    repeat match goal with
           | [ IH : forall _ _ _ _, compose_tags _ _ = compose_tags _ _ |- _ ] =>
               rewrite IH
           end; reflexivity.
Qed.

Lemma compose_tags_open : forall C B X Y,
    compose_tags (open_utyp_wrt_utyp C (utyp_var_f X))
                 (open_btyp_wrt_btyp B (btyp_var_f Y)) = compose_tags C B.
Proof.
  intros C B X Y. unfold open_utyp_wrt_utyp, open_btyp_wrt_btyp.
  apply compose_tags_open_rec.
Qed.

(** A synthesised target carries no inh quantifier, so composing against it
    introduces no tag: [compose_tags C B = nil].  This is what lets the
    [mode_ti]/[__infer_gen] base of B.4 keep its nil output. *)
Lemma compose_tags_is_syn_nil : forall B C,
    is_syn B -> compose_tags C B = nil.
Proof.
  intros B C Hsyn. generalize dependent C.
  induction Hsyn; intros C0.
  - destruct C0; reflexivity.
  - destruct C0; reflexivity.
  - destruct C0; simpl; try reflexivity. rewrite IHHsyn1, IHHsyn2. reflexivity.
  - destruct C0; simpl; try reflexivity;
      (pick fresh X for L;
       rewrite <- (compose_tags_open _ B X X);
       apply (H0 X); fsetdec).
Qed.

Lemma incl_app4 : forall {A : Type} (l1 l2 m1 m2 n1 n2 : list A),
    incl (l1 ++ m1) n1 -> incl (l2 ++ m2) n2 ->
    incl ((l1 ++ l2) ++ (m1 ++ m2)) (n1 ++ n2).
Proof.
  intros A0 l1 l2 m1 m2 n1 n2 H1 H2 x Hin.
  apply in_app_or in Hin. apply in_or_app.
  destruct Hin as [Hin|Hin]; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  - left. apply H1. apply in_or_app. left. exact Hin.
  - right. apply H2. apply in_or_app. left. exact Hin.
  - left. apply H1. apply in_or_app. right. exact Hin.
  - right. apply H2. apply in_or_app. right. exact Hin.
Qed.

(** Instantiate both opened sub-derivations at a variable [X], reshape their
    middle types back through the coercions, fire the size-induction IH, and
    fold [compose_tags] over the opening (it is invariant under [X]).  Leaves
    [Hincl] and [Hcons] for the body. *)
Ltac binder_ih IHn HszA HH HH0 AA X :=
  let HcX := fresh "HcX" in
  let HdX := fresh "HdX" in
  pose proof (HH X ltac:(fsetdec)) as HcX;
  pose proof (HH0 X ltac:(fsetdec)) as HdX;
  change (btyp_var_f X) with (ptyp_to_btyp_syn (ptyp_var_f X)) in HcX;
  rewrite <- ptyp_to_btyp_syn_open in HcX;
  change (utyp_var_f X) with (ptyp_to_utyp_syn (ptyp_var_f X)) in HdX;
  rewrite <- ptyp_to_utyp_syn_open in HdX;
  edestruct (IHn (open_ptyp_wrt_ptyp AA (ptyp_var_f X))
                 ltac:(rewrite size_ptyp_open_ptyp_wrt_ptyp_var; exact HszA)
                 _ _ _ _ _ HcX HdX) as [Hincl Hcons];
  rewrite compose_tags_open in Hincl;
  rewrite compose_tags_open in Hcons.

(** Paper B.2, native split form for a synthesized middle type.  Strengthened
    with the explicit witness [compose_tags C B] and proved by induction on the
    size of the middle type [A]. *)
Lemma d_consis_compose_strong : forall n A,
    size_ptyp A < n ->
    forall Δa Δb Γ C B,
    Δa ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    Δb ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B ->
    incl (Δa ++ Δb) (compose_tags C B) /\ (compose_tags C B) ⨟ Γ ⊨ C ≈ B.
Proof.
  induction n; intros A Hsz Δa Δb Γ C B H1 H2.
  - lia.
  - destruct A; simpl in H1, H2.
    + (* ptyp_unit *)
      dependent destruction H1. dependent destruction H2. simpl.
      split; [ apply incl_nil_l | apply d_consis__unit ].
    + (* ptyp_var_b — no consistency rule has a [btyp_var_b] RHS *)
      inversion H1.
    + (* ptyp_var_f *)
      dependent destruction H1. dependent destruction H2. simpl.
      split; [ apply incl_nil_l | apply d_consis__var; assumption ].
    + (* ptyp_arrow A1 A2 *)
      dependent destruction H1. dependent destruction H2. simpl.
      simpl in Hsz. pose proof (size_ptyp_min A1). pose proof (size_ptyp_min A2).
      assert (HszA1 : size_ptyp A1 < n) by lia.
      assert (HszA2 : size_ptyp A2 < n) by lia.
      edestruct (IHn A1 HszA1 _ _ _ _ _ H1_ H2_) as [Hincl1 Hcons1].
      edestruct (IHn A2 HszA2 _ _ _ _ _ H1_0 H2_0) as [Hincl2 Hcons2].
      split; [ apply incl_app4; assumption | apply d_consis__arrow; assumption ].
    + (* ptyp_all A — A is the (body of the) middle type *)
      assert (HszA : size_ptyp A < n) by (simpl in Hsz; lia).
      dependent destruction H1; dependent destruction H2.
      { (* tagged → syn → inh : the only context-growing composition *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [X0 HX0].
          binder_ih IHn HszA H H0 A X0. simpl. apply incl_tl. exact Hincl. }
        { simpl. apply d_consis__forall_inh_tagged with (L := L `union` L0).
          intros X HX. binder_ih IHn HszA H H0 A X. exact Hcons. } }
      { (* tagged → syn → syn *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [X0 HX0].
          binder_ih IHn HszA H H0 A X0. simpl. exact Hincl. }
        { simpl. apply d_consis__forall_syn_tagged with (L := L `union` L0).
          intros X HX. binder_ih IHn HszA H H0 A X. exact Hcons. } }
      { (* syn → syn → inh *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [X0 HX0].
          binder_ih IHn HszA H H0 A X0. simpl. exact Hincl. }
        { simpl. apply d_consis__forall_inh_untagged with (L := L `union` L0).
          intros X HX. binder_ih IHn HszA H H0 A X. exact Hcons. } }
      { (* syn → syn → syn *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [X0 HX0].
          binder_ih IHn HszA H H0 A X0. simpl. exact Hincl. }
        { simpl. apply d_consis__forall_syn with (L := L `union` L0).
          intros X HX. binder_ih IHn HszA H H0 A X. exact Hcons. } }
Qed.

Lemma d_consis_compose : forall Δa Δb Γ C A B,
    Δa ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    Δb ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B ->
    exists Δc, incl (Δa ++ Δb) Δc /\ Δc ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Δa Δb Γ C A B H1 H2.
  exists (compose_tags C B).
  exact (@d_consis_compose_strong (S (size_ptyp A)) A ltac:(lia) Δa Δb Γ C B H1 H2).
Qed.

Lemma d_sub_gen_refl_styp_ti : forall Γ B,
    Γ ⊢ᵦ B ->
    is_styp B ->
    nil ⨟ Γ ⊢ᵍ[ mode_ti ] (utyp_to_gutyp (btyp_to_utyp_syn B)) ⊑ B.
Proof.
  intros Γ B Hwf Hst.
  apply d_sub_gen__infer_gen.
  - apply is_styp_is_syn. exact Hst.
  - apply d_consis_refl_styp_as_utyp; auto.
Qed.

(** Coercions never introduce free type variables. *)
Lemma ftvar_btyp_to_gutyp : forall B,
    ftvar_in_gutyp (btyp_to_gutyp B) [<=] ftvar_in_btyp B.
Proof. induction B; simpl; fsetdec. Qed.

Lemma ftvar_btyp_to_utyp_syn : forall B,
    ftvar_in_utyp (btyp_to_utyp_syn B) [<=] ftvar_in_btyp B.
Proof. induction B; simpl; fsetdec. Qed.

Lemma ftvar_utyp_to_gutyp : forall C,
    ftvar_in_gutyp (utyp_to_gutyp C) [<=] ftvar_in_utyp C.
Proof. induction C; simpl; fsetdec. Qed.

(** Keystone for B.4: on a synthesised [btyp], the [gutyp] embedding equals
    the [utyp]-route embedding.  This collapses [d_sub_gen_trans]'s middle
    [btyp_to_gutyp B2] into the [utyp] image, where the (non-gen) B.2
    [d_consis_compose] applies. *)
Lemma btyp_to_gutyp_syn_eq : forall B,
    is_syn B ->
    btyp_to_gutyp B = utyp_to_gutyp (btyp_to_utyp_syn B).
Proof.
  intros B Hsyn. induction Hsyn; simpl; try reflexivity.
  - rewrite IHHsyn1, IHHsyn2. reflexivity.
  - f_equal.
    pick fresh X for (L `union` ftvar_in_btyp B).
    apply open_gutyp_wrt_gutyp_inj with (Xgt1 := X).
    + pose proof (ftvar_btyp_to_gutyp B). fsetdec.
    + pose proof (ftvar_utyp_to_gutyp (btyp_to_utyp_syn B)).
      pose proof (ftvar_btyp_to_utyp_syn B). fsetdec.
    + specialize (H0 X ltac:(fsetdec)).
      rewrite btyp_to_gutyp_open in H0.
      rewrite btyp_to_utyp_syn_open in H0.
      rewrite utyp_to_gutyp_open in H0.
      exact H0.
Qed.

(** A synthesised [btyp] is the syn-painting of its own forgetful image, so
    [d_consis_compose]'s [ptyp_to_btyp_syn A] middle can be fed an arbitrary
    [is_syn] btyp via [A := btyp_to_ptyp B]. *)
Lemma btyp_to_ptyp_open_rec : forall B1 B2 k,
    btyp_to_ptyp (open_btyp_wrt_btyp_rec k B2 B1) =
    open_ptyp_wrt_ptyp_rec k (btyp_to_ptyp B2) (btyp_to_ptyp B1).
Proof.
  induction B1; intros B2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHB1_1, IHB1_2; reflexivity.
  - rewrite IHB1; reflexivity.
  - rewrite IHB1; reflexivity.
Qed.

Lemma btyp_to_ptyp_open : forall B1 B2,
    btyp_to_ptyp (open_btyp_wrt_btyp B1 B2) =
    open_ptyp_wrt_ptyp (btyp_to_ptyp B1) (btyp_to_ptyp B2).
Proof.
  intros. unfold open_btyp_wrt_btyp, open_ptyp_wrt_ptyp.
  apply btyp_to_ptyp_open_rec.
Qed.

Lemma ftvar_ptyp_to_btyp_syn : forall A,
    ftvar_in_btyp (ptyp_to_btyp_syn A) [<=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

Lemma ftvar_btyp_to_ptyp : forall B,
    ftvar_in_ptyp (btyp_to_ptyp B) [<=] ftvar_in_btyp B.
Proof. induction B; simpl; fsetdec. Qed.

Lemma ptyp_to_utyp_syn_btyp_to_ptyp : forall B,
    ptyp_to_utyp_syn (btyp_to_ptyp B) = btyp_to_utyp_syn B.
Proof.
  induction B; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); rewrite IHB; reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_btyp_to_ptyp : forall B,
    is_syn B ->
    ptyp_to_btyp_syn (btyp_to_ptyp B) = B.
Proof.
  intros B Hsyn. induction Hsyn; simpl; try reflexivity.
  - rewrite IHHsyn1, IHHsyn2; reflexivity.
  - f_equal.
    pick fresh X for (L `union` ftvar_in_btyp B).
    apply open_btyp_wrt_btyp_inj with (Xbt1 := X).
    + pose proof (ftvar_ptyp_to_btyp_syn (btyp_to_ptyp B)).
      pose proof (ftvar_btyp_to_ptyp B). fsetdec.
    + fsetdec.
    + specialize (H0 X ltac:(fsetdec)).
      rewrite btyp_to_ptyp_open in H0.
      rewrite ptyp_to_btyp_syn_open in H0.
      exact H0.
Qed.

(** B.2 with an arbitrary synthesised middle [B2] (not just a ptyp painting):
    immediate corollary of [d_consis_compose] via the round-trip above. *)
Lemma d_consis_compose_syn : forall Δa Δb Γ C B2 B,
    is_syn B2 ->
    Δa ⨟ Γ ⊨ C ≈ B2 ->
    Δb ⨟ Γ ⊨ (btyp_to_utyp_syn B2) ≈ B ->
    exists Δc, incl (Δa ++ Δb) Δc /\ Δc ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Δa Δb Γ C B2 B Hsyn Hc Hd.
  apply (@d_consis_compose Δa Δb Γ C (btyp_to_ptyp B2) B).
  - rewrite ptyp_to_btyp_syn_btyp_to_ptyp by exact Hsyn. exact Hc.
  - rewrite ptyp_to_utyp_syn_btyp_to_ptyp. exact Hd.
Qed.

(** Nil-output composition: when both the synthesised middle [B2] and the
    target [B] carry no inh quantifier, the composed context is nil (no etag
    is recorded), so the result holds at the empty tag context — needed for
    the [mode_ti]/[__infer_gen] base, which demands nil. *)
Lemma d_consis_compose_syn_nil : forall Γ C B2 B,
    is_syn B2 -> is_syn B ->
    nil ⨟ Γ ⊨ C ≈ B2 ->
    nil ⨟ Γ ⊨ (btyp_to_utyp_syn B2) ≈ B ->
    nil ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Γ C B2 B Hsyn2 HsynB Hc Hd.
  rewrite <- (ptyp_to_btyp_syn_btyp_to_ptyp Hsyn2) in Hc.
  rewrite <- (ptyp_to_utyp_syn_btyp_to_ptyp B2) in Hd.
  pose proof (@d_consis_compose_strong (S (size_ptyp (btyp_to_ptyp B2)))
                (btyp_to_ptyp B2) ltac:(lia) nil nil Γ C B Hc Hd) as [_ Hcons].
  rewrite (@compose_tags_is_syn_nil B C HsynB) in Hcons.
  exact Hcons.
Qed.
(** [utyp_to_gutyp] is injective: [gutyp] has constructors outside its image
    ([gutyp_all_inh]) and is structural on the shared ones, so equal images
    come from equal sources.  Lets us invert the rule premise
    [utyp_to_gutyp C0 = utyp_to_gutyp (btyp_to_utyp_syn B2)] into [C0 = ...]. *)
Lemma utyp_to_gutyp_inj : forall C1 C2,
    utyp_to_gutyp C1 = utyp_to_gutyp C2 -> C1 = C2.
Proof.
  induction C1; intros C2 Heq; destruct C2; simpl in Heq;
    try discriminate; inversion Heq; subst; f_equal; auto.
Qed.


(** ===== Infrastructure for B.4 (generalized utyp-middle composition) =====

    The B.4 base composes a [mode_ti] first sub ([utyp_to_gutyp C ⊑ B2], i.e.
    [C ≈ B2] with [B2] synthesised) with a second sub whose LHS is a [utyp]
    image [utyp_to_gutyp Cmid].  The clean inductive invariant relates the
    source [Csrc] to the middle by a consistency against the *btyp erasure*
    [Csrc ≈ utyp_to_btyp Cmid] — this survives the [forall_l] instantiation
    (where a tagged [ph] would break a "[btyp_to_utyp_syn] image" invariant). *)

(** [utyp_to_btyp] commutes with opening. *)
Lemma utyp_to_btyp_open_rec : forall C1 C2 k,
    utyp_to_btyp (open_utyp_wrt_utyp_rec k C2 C1) =
    open_btyp_wrt_btyp_rec k (utyp_to_btyp C2) (utyp_to_btyp C1).
Proof.
  induction C1; intros C2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHC1_1, IHC1_2; reflexivity.
  - rewrite IHC1; reflexivity.
  - rewrite IHC1; reflexivity.
Qed.

Lemma utyp_to_btyp_open : forall C1 C2,
    utyp_to_btyp (open_utyp_wrt_utyp C1 C2) =
    open_btyp_wrt_btyp (utyp_to_btyp C1) (utyp_to_btyp C2).
Proof.
  intros. unfold open_utyp_wrt_utyp, open_btyp_wrt_btyp.
  apply utyp_to_btyp_open_rec.
Qed.

(** A [utyp]'s [btyp] erasure has only synthesised foralls, so it is [is_syn]
    once locally closed (lc rules out a dangling [var_b]). *)
Lemma is_syn_utyp_to_btyp : forall C,
    lc_utyp C -> is_syn (utyp_to_btyp C).
Proof.
  intros C Hlc. induction Hlc; simpl.
  - apply is_syn__unit.
  - apply is_syn__var.
  - apply is_syn__arrow; assumption.
  - apply is_syn__all with (L := empty). intros X HX.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f X))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f X)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0.
  - apply is_syn__all with (L := empty). intros X HX.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f X))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f X)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0.
Qed.

(** [btyp_to_utyp_syn ∘ utyp_to_btyp] (forcing every forall to syn) commutes
    with variable opening. *)
Lemma synerase_open : forall C X,
    btyp_to_utyp_syn (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f X))) =
    open_utyp_wrt_utyp (btyp_to_utyp_syn (utyp_to_btyp C)) (utyp_var_f X).
Proof.
  intros C X. rewrite utyp_to_btyp_open. simpl.
  rewrite btyp_to_utyp_syn_open. reflexivity.
Qed.

(** The [btyp] erasure of a consistent [utyp] is [is_syn] (all foralls become
    synthesised); read straight off the consistency derivation. *)
Lemma d_consis_is_syn_erase : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B -> is_syn (utyp_to_btyp C).
Proof.
  intros Δ Γ C B H. induction H; simpl.
  - apply is_syn__unit.
  - apply is_syn__var.
  - apply is_syn__arrow; assumption.
  - apply is_syn__all with (L := L). intros X HX.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f X))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f X)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0; assumption.
  - apply is_syn__all with (L := L). intros X HX.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f X))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f X)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0; assumption.
  - apply is_syn__all with (L := L). intros X HX.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f X))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f X)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0; assumption.
  - apply is_syn__all with (L := L). intros X HX.
    replace (open_btyp_wrt_btyp (utyp_to_btyp C) (btyp_var_f X))
      with (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f X)))
      by (rewrite utyp_to_btyp_open; reflexivity).
    apply H0; assumption.
Qed.

(** Forcing the [utyp] side's foralls to syn ([btyp_to_utyp_syn ∘ utyp_to_btyp])
    preserves consistency and lands at the empty tag context — an etag-free LHS
    triggers no [forall_inh_tagged], so nothing is recorded. *)
Lemma d_consis_synerase_lhs : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    nil ⨟ Γ ⊨ (btyp_to_utyp_syn (utyp_to_btyp C)) ≈ B.
Proof.
  intros Δ Γ C B H. induction H; simpl.
  - apply d_consis__unit.
  - apply d_consis__var; assumption.
  - replace (@nil atom) with (@nil atom ++ @nil atom) by reflexivity.
    apply d_consis__arrow; assumption.
  - apply d_consis__forall_inh_untagged with (L := L). intros X HX.
    rewrite <- synerase_open. apply H0; assumption.
  - apply d_consis__forall_inh_untagged with (L := L). intros X HX.
    rewrite <- synerase_open. apply H0; assumption.
  - apply d_consis__forall_syn with (L := L). intros X HX.
    rewrite <- synerase_open. apply H0; assumption.
  - apply d_consis__forall_syn with (L := L). intros X HX.
    rewrite <- synerase_open. apply H0; assumption.
Qed.

(** Generalized nil composition: arbitrary input tag contexts, syn middle and
    target ⟹ nil output (the [mode_ti]/[__infer_gen] base demands nil). *)
Lemma d_consis_compose_syn_nil_l : forall Δa Δb Γ C B2 B,
    is_syn B2 -> is_syn B ->
    Δa ⨟ Γ ⊨ C ≈ B2 ->
    Δb ⨟ Γ ⊨ (btyp_to_utyp_syn B2) ≈ B ->
    nil ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Δa Δb Γ C B2 B Hsyn2 HsynB Hc Hd.
  rewrite <- (ptyp_to_btyp_syn_btyp_to_ptyp Hsyn2) in Hc.
  rewrite <- (ptyp_to_utyp_syn_btyp_to_ptyp B2) in Hd.
  pose proof (@d_consis_compose_strong (S (size_ptyp (btyp_to_ptyp B2)))
                (btyp_to_ptyp B2) ltac:(lia) Δa Δb Γ C B Hc Hd) as [_ Hcons].
  rewrite (@compose_tags_is_syn_nil B C HsynB) in Hcons.
  exact Hcons.
Qed.

(** A consistency derivation's [utyp] side is locally closed. *)
Lemma d_consis_lc_utyp : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B -> lc_utyp C.
Proof.
  intros Δ Γ C B H. induction H.
  - apply lc_utyp_unit.
  - apply lc_utyp_var_f.
  - apply lc_utyp_arrow; assumption.
  - pick fresh X. apply lc_utyp_all_etag_exists with (Xut1 := X). apply H0. fsetdec.
  - pick fresh X. apply lc_utyp_all_syn_exists with (Xut1 := X). apply H0. fsetdec.
  - pick fresh X. apply lc_utyp_all_etag_exists with (Xut1 := X). apply H0. fsetdec.
  - pick fresh X. apply lc_utyp_all_syn_exists with (Xut1 := X). apply H0. fsetdec.
Qed.

(** A consistency derivation's [btyp] side is locally closed. *)
Lemma d_consis_lc_btyp : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B -> lc_btyp B.
Proof.
  intros Δ Γ C B H. induction H.
  - apply lc_btyp_unit.
  - apply lc_btyp_var_f.
  - apply lc_btyp_arrow; assumption.
  - pick fresh X. apply lc_btyp_all_inh_exists with (Xbt1 := X). apply H0. fsetdec.
  - pick fresh X. apply lc_btyp_all_inh_exists with (Xbt1 := X). apply H0. fsetdec.
  - pick fresh X. apply lc_btyp_all_syn_exists with (Xbt1 := X). apply H0. fsetdec.
  - pick fresh X. apply lc_btyp_all_syn_exists with (Xbt1 := X). apply H0. fsetdec.
Qed.

(** A guarded middle forces a guarded source: consistency against a guarded
    ([unit]/[var]/[arrow]) erasure leaves no room for a forall on the LHS. *)
Lemma d_consis_guarded_lhs : forall Δ Γ Csrc C,
    guarded_utyp C ->
    Δ ⨟ Γ ⊨ Csrc ≈ (utyp_to_btyp C) ->
    guarded_utyp Csrc.
Proof.
  intros Δ Γ Csrc C Hg Hc.
  inversion Hg; subst; simpl in Hc.
  - inversion Hc; subst. apply guarded_utyp__unit.
  - inversion Hc; subst. apply guarded_utyp__var.
  - inversion Hc; subst. apply guarded_utyp__arrow.
    + eapply d_consis_lc_utyp; eauto.
    + eapply d_consis_lc_utyp; eauto.
Qed.

(** ===== tvar renaming infrastructure (closes B.4's [forall_r]) =====

    Renaming a free type variable [X ↦ Y] in a [d_sub_gen] derivation.  The tag
    context [Δ] is etag-only, so it is untouched; [dbind] payloads are inert for
    these judgments, so the context renaming is just the binder [X~tvar ↦
    Y~tvar].  Built bottom-up: coercion/subst commutes, predicate renamings,
    then [d_consis] / [d_wf_utyp] / [d_sub_gen]. *)

(** Coercions commute with type-variable substitution. *)
Lemma subst_utyp_to_gutyp : forall C X Y,
    subst_gutyp_in_gutyp (gutyp_var_f Y) X (utyp_to_gutyp C) =
    utyp_to_gutyp (subst_utyp_in_utyp (utyp_var_f Y) X C).
Proof.
  induction C; intros X Y; simpl; try reflexivity.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; reflexivity.
  - rewrite IHC1, IHC2; reflexivity.
  - rewrite IHC; reflexivity.
  - rewrite IHC; reflexivity.
Qed.

Lemma subst_utyp_to_btyp : forall C X Y,
    subst_btyp_in_btyp (btyp_var_f Y) X (utyp_to_btyp C) =
    utyp_to_btyp (subst_utyp_in_utyp (utyp_var_f Y) X C).
Proof.
  induction C; intros X Y; simpl; try reflexivity.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; reflexivity.
  - rewrite IHC1, IHC2; reflexivity.
  - rewrite IHC; reflexivity.
  - rewrite IHC; reflexivity.
Qed.

Lemma subst_btyp_to_gutyp : forall B X Y,
    subst_gutyp_in_gutyp (gutyp_var_f Y) X (btyp_to_gutyp B) =
    btyp_to_gutyp (subst_btyp_in_btyp (btyp_var_f Y) X B).
Proof.
  induction B; intros X Y; simpl; try reflexivity.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; reflexivity.
  - rewrite IHB1, IHB2; reflexivity.
  - rewrite IHB; reflexivity.
  - rewrite IHB; reflexivity.
Qed.

(** Shape predicates are preserved by tvar renaming. *)
Lemma is_syn_rename : forall B Z W,
    is_syn B -> is_syn (subst_btyp_in_btyp (btyp_var_f W) Z B).
Proof.
  intros B Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_syn__all with (L := L `union` singleton Z `union` singleton W).
    intros X HX.
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_btyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma is_inh_rename : forall B Z W,
    is_inh B -> is_inh (subst_btyp_in_btyp (btyp_var_f W) Z B).
Proof.
  intros B Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_inh__all with (L := L `union` singleton Z `union` singleton W).
    intros X HX.
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_btyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma is_ityp_rename : forall B Z W,
    is_ityp B -> is_ityp (subst_btyp_in_btyp (btyp_var_f W) Z B).
Proof.
  intros B Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_ityp__all with (L := L `union` singleton Z `union` singleton W).
    intros X HX.
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
      by (solve [ fsetdec | apply lc_btyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma is_ttyp_rename : forall C Z W,
    is_ttyp C -> is_ttyp (subst_utyp_in_utyp (utyp_var_f W) Z C).
Proof.
  intros C Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; assumption.
  - apply is_ttyp__all_etag with (L := L `union` singleton Z `union` singleton W).
    intros X HX.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
      by (solve [ fsetdec | apply lc_utyp_var_f ]).
    apply H0; fsetdec.
Qed.

Lemma guarded_utyp_rename : forall C Z W,
    guarded_utyp C -> guarded_utyp (subst_utyp_in_utyp (utyp_var_f W) Z C).
Proof.
  intros C Z W H. induction H; simpl.
  - constructor.
  - match goal with |- context [ ?a == ?b ] => destruct (a == b) end; constructor.
  - constructor; apply subst_utyp_in_utyp_lc_utyp; auto; apply lc_utyp_var_f.
Qed.

(** [d_consis] is closed under tvar renaming (Δ is etag-only, untouched). *)
Lemma d_consis_rename : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    forall Γ1 Γ2 X0 Y,
      Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
      Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
      Δ ⨟ (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊨
         (subst_utyp_in_utyp (utyp_var_f Y) X0 C)
         ≈ (subst_btyp_in_btyp (btyp_var_f Y) X0 B).
Proof.
  intros Δ Γ C B H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst; simpl.
  - apply d_consis__unit.
  - match goal with |- context [ if ?d then _ else _ ] => destruct d end.
    + apply d_consis__var. auto.
    + apply d_consis__var. analyze_binds H; auto.
  - apply d_consis__arrow.
    + eapply IHd_consis1; [ reflexivity | exact Hfr ].
    + eapply IHd_consis2; [ reflexivity | exact Hfr ].
  - apply d_consis__forall_inh_tagged with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_consis__forall_inh_untagged with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_consis__forall_syn_tagged with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_consis__forall_syn with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
Qed.

(** [d_wf_utyp] is closed under tvar renaming (pure well-scopedness). *)
Lemma d_wf_utyp_rename : forall Γ C,
    Γ ⊢ᵤ C ->
    forall Γ1 Γ2 X0 Y,
      Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
      Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
      (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊢ᵤ (subst_utyp_in_utyp (utyp_var_f Y) X0 C).
Proof.
  intros Γ C H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst; simpl.
  - apply d_wf_utyp__unit.
  - match goal with |- context [ if ?d then _ else _ ] => destruct d end.
    + apply d_wf_utyp__var. auto.
    + apply d_wf_utyp__var. analyze_binds H; auto.
  - apply d_wf_utyp__arrow.
    + eapply IHd_wf_utyp1; [ reflexivity | exact Hfr ].
    + eapply IHd_wf_utyp2; [ reflexivity | exact Hfr ].
  - apply d_wf_utyp__all_syn with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - apply d_wf_utyp__all_etag with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    intros Z HZ.
    erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
Qed.

(** [d_sub_gen] is closed under tvar renaming.  [Δ] (etags) is untouched. *)
Lemma d_sub_gen_rename : forall m Δ Γ G B,
    Δ ⨟ Γ ⊢ᵍ[ m ] G ⊑ B ->
    forall Γ1 Γ2 X0 Y,
      Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
      Y `notin` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) ->
      Δ ⨟ (Γ1 ++ (Y ~ dbind_tvar) ++ Γ2) ⊢ᵍ[ m ]
         (subst_gutyp_in_gutyp (gutyp_var_f Y) X0 G)
         ⊑ (subst_btyp_in_btyp (btyp_var_f Y) X0 B).
Proof.
  intros m Δ Γ G B H. induction H; intros Γ1 Γ2 X0 Y Heq Hfr; subst.
  - (* infer_gen *)
    rewrite subst_utyp_to_gutyp.
    apply d_sub_gen__infer_gen.
    + apply is_syn_rename; assumption.
    + eapply d_consis_rename; [ eassumption | reflexivity | exact Hfr ].
  - (* check_gen *)
    rewrite subst_utyp_to_gutyp.
    apply d_sub_gen__check_gen.
    + apply guarded_utyp_rename; assumption.
    + apply is_inh_rename; assumption.
    + eapply d_consis_rename; [ eassumption | reflexivity | exact Hfr ].
    + apply is_ityp_rename; assumption.
  - (* forall_r *)
    rewrite subst_utyp_to_gutyp. simpl.
    apply d_sub_gen__forall_r with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    + exact (@is_inh_rename (btyp_all_inh B) X0 Y H).
    + intros Z HZ.
      erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
      rewrite <- subst_utyp_to_gutyp.
      erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
      rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
      eapply (H1 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
  - (* arg : after the [d_sub_gen__arg] redesign the LHS argument is a raw
       [gutyp Darg] related by [d_consis_gen]; this case now needs
       [d_consis_gen_rename] (the gen analog of [d_consis_rename], not yet
       proved).  Stubbed while validating the redesign. *)
    admit.
  - (* forall_l_tagged *)
    simpl.
    apply d_sub_gen__forall_l_tagged with
      (Δ' := Δ') (ph := subst_utyp_in_utyp (utyp_var_f Y) X0 ph).
    + assumption.
    + eapply d_tags_subst_tvar; eassumption.
    + eapply d_wf_utyp_rename; [ eassumption | reflexivity | exact Hfr ].
    + apply is_ttyp_rename; assumption.
    + rewrite <- subst_utyp_to_gutyp.
      rewrite <- subst_gutyp_in_gutyp_open_gutyp_wrt_gutyp; [ | apply lc_gutyp_var_f ].
      eapply IHd_sub_gen; [ reflexivity | exact Hfr ].
  - (* forall_l_untagged *)
    simpl.
    apply d_sub_gen__forall_l_untagged with
      (Δ' := Δ') (ph := subst_utyp_in_utyp (utyp_var_f Y) X0 ph).
    + assumption.
    + eapply d_tags_subst_tvar; eassumption.
    + eapply d_wf_utyp_rename; [ eassumption | reflexivity | exact Hfr ].
    + apply is_ttyp_rename; assumption.
    + rewrite <- subst_utyp_to_gutyp.
      rewrite <- subst_gutyp_in_gutyp_open_gutyp_wrt_gutyp; [ | apply lc_gutyp_var_f ].
      eapply IHd_sub_gen; [ reflexivity | exact Hfr ].
(* d_sub_gen_rename: [arg] case stubbed pending [d_consis_gen_rename]
   (gen analog needed after the d_sub_gen__arg redesign). *)
Admitted.

(** B.4 base, AUX.  [Cmid] is the second sub's LHS [utyp]; the source [Csrc] is
    tied to it by consistency against its [btyp] erasure [utyp_to_btyp Cmid].
    Inducting on the second sub with [Csrc]/[Cmid]/[Δa] quantified after lets
    the IH re-pick them in the arrow/forall recursions; the erasure invariant
    survives [forall_l] instantiation by a tagged [ph]. *)
Lemma d_sub_gen_trans_ti_lhs_aux : forall m2 Δ2 Γ G B3,
    Δ2 ⨟ Γ ⊢ᵍ[ m2 ] G ⊑ B3 ->
    forall Csrc Cmid Δa,
      G = utyp_to_gutyp Cmid ->
      Δa ⨟ Γ ⊨ Csrc ≈ (utyp_to_btyp Cmid) ->
      exists Δc, Δc ⨟ Γ ⊢ᵍ[ m2 ] (utyp_to_gutyp Csrc) ⊑ B3.
Proof.
  intros m2 Δ2 Γ G B3 H.
  dependent induction H; intros Csrc Cmid Da Heq Hcons.
  - (* infer_gen *)
    apply utyp_to_gutyp_inj in Heq. subst Cmid.
    exists (@nil atom).
    apply d_sub_gen__infer_gen; [ exact H | ].
    eapply d_consis_compose_syn_nil_l with (B2 := utyp_to_btyp C);
      [ apply (d_consis_is_syn_erase H0) | exact H | exact Hcons
      | apply (d_consis_synerase_lhs H0) ].
  - (* check_gen *)
    apply utyp_to_gutyp_inj in Heq. subst Cmid.
    pose proof (d_consis_compose_syn (d_consis_is_syn_erase H1) Hcons
                  (d_consis_synerase_lhs H1)) as [Δc [Hincl Hc2]].
    exists Δc.
    apply d_sub_gen__check_gen.
    + exact (d_consis_guarded_lhs H Hcons).
    + exact H0.
    + exact Hc2.
    + exact H2.
  - (* forall_r.  Obtain the witness [Δc] at one fresh [X0] via the IH, then
       rename [X0 ↦ X] (d_sub_gen_rename) for the uniform cofinite premise. *)
    apply utyp_to_gutyp_inj in Heq. subst Cmid.
    pose proof (d_consis_lc_utyp Hcons) as HlcS.
    pose proof (d_consis_lc_btyp Hcons) as HlcM.
    pick fresh X0 for (L `union` dom Γ `union` ftvar_in_utyp Csrc
                       `union` ftvar_in_btyp B `union` ftvar_in_utyp C).
    assert (Hcons0 : Da ⨟ ((X0 ~ dbind_tvar) ++ Γ) ⊨
              (open_utyp_wrt_utyp Csrc (utyp_var_f X0))
              ≈ (open_utyp_wrt_utyp C (utyp_var_f X0))).
    { rewrite (open_utyp_wrt_utyp_lc_utyp Csrc (utyp_var_f X0) HlcS).
      rewrite utyp_to_btyp_open.
      rewrite (open_btyp_wrt_btyp_lc_btyp (utyp_to_btyp C) (utyp_to_btyp (utyp_var_f X0)) HlcM).
      apply d_consis_weakening_head. exact Hcons. }
    edestruct (H1 X0 ltac:(fsetdec)
                 (open_utyp_wrt_utyp Csrc (utyp_var_f X0))
                 (open_utyp_wrt_utyp C (utyp_var_f X0)) Da
                 eq_refl Hcons0) as [Δc0 HD0].
    rewrite (open_utyp_wrt_utyp_lc_utyp Csrc (utyp_var_f X0) HlcS) in HD0.
    exists Δc0.
    apply d_sub_gen__forall_r with
      (L := L `union` dom Γ `union` ftvar_in_utyp Csrc `union` ftvar_in_btyp B
            `union` singleton X0).
    + exact H.
    + intros X HX.
      rewrite (open_utyp_wrt_utyp_lc_utyp Csrc (utyp_var_f X) HlcS).
      pose proof (@d_sub_gen_rename _ _ _ _ _ HD0 nil Γ X0 X ltac:(reflexivity)
                    ltac:(simpl; fsetdec)) as Hren.
      simpl in Hren.
      rewrite subst_utyp_to_gutyp in Hren.
      rewrite subst_utyp_in_utyp_fresh_eq in Hren by fsetdec.
      rewrite <- (subst_btyp_in_btyp_intro X0 B (btyp_var_f X)) in Hren by fsetdec.
      exact Hren.
  - (* arg : after the [d_sub_gen__arg] redesign the argument is a [gutyp]
       related by [d_consis_gen], so the composition here needs a *gen*
       consistency-compose (not the [d_consis_compose_syn] used here).
       Stubbed pending that gen analog. *)
    admit.
  - (* forall_l_tagged.  Instantiate [Csrc]'s ∀ with the same [ph]; recurse via
       the IH on the opened body.  Needs (a) a [d_consis] substitution lemma to
       push the body consistency under [X ↦ (ph, utyp_to_btyp ph)] (the var
       case uses the reflexive [nil ⊨ ph ≈ utyp_to_btyp ph], so no new tags),
       and (b) presenting the IH's output context as the rigid [Δ'' ++ Δ']
       append the rule demands — the list-vs-set bookkeeping the deferred
       multiset Δ refactor would dissolve.  TODO. *)
    admit.
  - (* forall_l_untagged: as forall_l_tagged. *)
    admit.
Admitted.

(** B.3 base / B.4: the output tag context is a SUPERSET of the inputs, NOT
    nil.  For a general (etag-bearing) [B1], an etag-∀ in [B1] that is
    syn-matched against the synthesised middle [B2] (no tag) but reaches an
    inh part of the target [B3] forces [forall_inh_tagged] to record a tag —
    so the composed subtyping's context is genuinely non-nil (the same
    tagged→syn→inh phenomenon as B.2).  Hence [exists Δc, incl ...]. *)
Lemma d_sub_gen_trans_ti_lhs : forall Γ B1 B2 B3 m2,
    Γ ⊢ᵦ B2 ->
    nil ⨟ Γ ⊢ᵍ[ mode_ti ] B1 ⊑ B2 ->
    nil ⨟ Γ ⊢ᵍ[ m2 ] (btyp_to_gutyp B2) ⊑ B3 ->
    exists Δc, Δc ⨟ Γ ⊢ᵍ[ m2 ] B1 ⊑ B3.
Proof.
Admitted.

Lemma d_sub_gen_trans : forall m1 Γ B1 B2 B3 m2,
    nil ⨟ Γ ⊢ᵍ[ m1 ] B1 ⊑ B2 ->
    nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] (btyp_to_gutyp B2) ⊑ B3 ->
    exists Δc, Δc ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] B1 ⊑ B3.
Proof.
  (** Native generalized consistency/subtyping composition over [gutyp],
      through [Arg] and [ForallL].  Uses [d_consis_compose_syn] at the
      [mode_ti] base ([d_sub_gen_trans_ti_lhs]). *)
Admitted.

(** Specialisation D12 actually needs: when the LHS is an etag-free
    [btyp_to_gutyp] image (a typing result), there is no syn→inh etag flip,
    so the composed context collapses to nil — letting [d_typing_gen__sub]
    (which demands a nil context) consume it. *)
Lemma d_sub_gen_trans_btyp_nil : forall m1 Γ B0 B2 B3 m2,
    nil ⨟ Γ ⊢ᵍ[ m1 ] (btyp_to_gutyp B0) ⊑ B2 ->
    nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] (btyp_to_gutyp B2) ⊑ B3 ->
    nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ] (btyp_to_gutyp B0) ⊑ B3.
Proof.
Admitted.

(** * D1/D12 route — step 1: function-side subsumption.

    The [__embed] half of D12, extracted as an induction on the *plain*
    typing derivation so the FN-spine recursion is structural (n
    decrements with the arrow spine).  Driving this case-by-case is what
    tells us whether D12 holds as currently stated, and which (if any)
    rule side-conditions must move after the bidirectional-A refactor. *)
Lemma d_typing_gen_lift : forall m_orig Γ e B1,
    d_typing m_orig Γ e B1 ->
    is_fn_n_ti m_orig ->
    d_wf_denv Γ ->
    forall m_new B2,
      nil ⨟ Γ ⊢ᵍ[ mode_fn_n_subst m_orig m_new ] (btyp_to_gutyp B1) ⊑ B2 ->
      Γ ⊢ᵍ[ mode_fn_n_subst m_orig m_new ] e ⦂ B2.
Proof.
  intros m_orig Γ e B1 H.
  induction H; intros Hfn Hwf m_new B_tgt Hsub.
  - (* __unit : ti-synthesis, wrap via gen sub *)
    eapply d_typing_gen__sub;
      [ apply d_typing_gen__embed; apply d_typing__unit | exact Hsub ].
  - (* __var *)
    eapply d_typing_gen__sub;
      [ apply d_typing_gen__embed; apply d_typing__var; exact H | exact Hsub ].
  - (* __anno *)
    eapply d_typing_gen__sub;
      [ apply d_typing_gen__embed; apply d_typing__anno; exact H | exact Hsub ].
  - (* __sub : compose the two subtypings.  Needs (a) lifting the non-gen
       [d_sub m nil Γ (ptyp_to_utyp_syn B1) B2] to [d_sub_gen], and (b)
       [d_sub_gen_trans_btyp_nil] to compose with [Hsub]; then the [ti] IH
       closes.  Tower-dependent. *)
    admit.
  - (* __freeze : mode_tc is not is_fn_n_ti *)
    inversion Hfn.
  - (* __forall : mode_tc is not is_fn_n_ti *)
    inversion Hfn.
  - (* __abs : FUNCTION-SIDE HARD CORE.  [Hsub] subtypes
       [arrow (inh A) B] at [fn^n m_new]; via [d_sub_gen__arg] the new arg
       [B1'] need only satisfy [D2 ~ B1'], but [__abs] forces the rebuilt
       arrow's arg to be exactly [ptyp_to_btyp_inh A] (the body binds
       [x : A]).  So rebuilding needs arg-PRESERVATION that the consistency
       does not give directly — the genuine obstruction. *)
    admit.
  - (* __abs_anno : as __abs, compounded by the S2 bidirectional [Barg]
       ([H0 : btyp_to_ptyp Barg = A]) — the arg painting is now existential,
       so the companion must thread the erasure invariant. *)
    admit.
  - (* __app : function-side via [e1]'s arrow type [arrow Barg B]; the
       result [B] is subtyped, the arg [Barg] reconciled through the same
       consistency mechanism as __abs. *)
    admit.
Admitted.
