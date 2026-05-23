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
    + apply d_consis_weakening. exact H.
    + eapply IHd_sub_gen; eauto.
    + exact H1.
  - apply d_sub_gen__forall_l_tagged with (Δ' := Δ') (ph := ph); nbauto.
    + apply d_wf_utyp_weakening. exact H1.
  - apply d_sub_gen__forall_l_untagged with (Δ' := Δ') (ph := ph); nbauto.
    + apply d_wf_utyp_weakening. exact H1.
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
    + apply list_disjoint_nil_l.
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
    + apply list_disjoint_nil_l.
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
