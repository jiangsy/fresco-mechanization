(** Auxiliary facts for declarative general subsumption (the [utyp]/[btyp]
    split syntax): the [compose_tags] witness and consistency composition
    (paper B.2), coercion / opening / free-variable lemmas relating the three
    type layers, and consistency basics ([lc], [guarded]).  Tvar-renaming
    closure lives in [prop_renaming]. *)

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

Set Implicit Arguments.

Ltac nbauto := try sauto limit:30.


(** [compose_tags C B] is the tag context produced by composing the two
    consistency derivations through a synthesised middle type.  Making it an
    explicit *function of (C,B)* (rather than an existential witness) is the
    crux of B.2: the witness is then manifestly independent of the variable
    used to open a quantifier body, so the cofinite case has a uniform Δc.

    The only rule that *grows* the context is the tagged→inh composition
    (paper [ForallInh] with δ=ε): a tagged-∀ that was dropped on the
    synthesised side ([ForallSyn], no tag) must be re-recorded when it meets
    an inherited ∀.  Hence the result is a strict superset of [Δa ∪ Δb]. *)
Fixpoint compose_tags (C : utyp) (B : btyp) {struct C} : atoms :=
  match C with
  | utyp_arrow C1 C2 =>
      match B with
      | btyp_arrow B1 B2 => compose_tags C1 B1 `union` compose_tags C2 B2
      | _ => empty
      end
  | utyp_all_etag ε C0 =>
      match B with
      | btyp_all_inh B0 => add ε (compose_tags C0 B0)
      | btyp_all_syn B0 => compose_tags C0 B0
      | _ => empty
      end
  | utyp_all_syn C0 =>
      match B with
      | btyp_all_inh B0 => compose_tags C0 B0
      | btyp_all_syn B0 => compose_tags C0 B0
      | _ => empty
      end
  | _ => empty
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
    [mode_ti] infer base keeps its empty-tag output. *)
Lemma compose_tags_is_syn_nil : forall B C,
    is_syn B -> compose_tags C B [=] empty.
Proof.
  intros B C Hsyn. generalize dependent C.
  induction Hsyn; intros C0.
  - destruct C0; simpl; reflexivity.
  - destruct C0; simpl; reflexivity.
  - destruct C0; simpl; try reflexivity. rewrite IHHsyn1, IHHsyn2. fsetdec.
  - destruct C0; simpl; try reflexivity;
      (pick fresh X for L;
       rewrite <- (compose_tags_open _ B X X);
       apply (H0 X); fsetdec).
Qed.

(* [incl_app4] (list inclusion) is no longer needed: the set-subset analogue
   is discharged inline by [fsetdec]. *)

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
    (Δa `union` Δb) [<=] (compose_tags C B) /\ (compose_tags C B) ⨟ Γ ⊨ C ≈ B.
Proof.
  induction n; intros A Hsz Δa Δb Γ C B H1 H2.
  - lia.
  - destruct A; simpl in H1, H2.
    + (* ptyp_unit *)
      dependent destruction H1. dependent destruction H2. simpl.
      split; [ fsetdec | apply d_consis__unit; reflexivity ].
    + (* ptyp_var_b — no consistency rule has a [btyp_var_b] RHS *)
      inversion H1.
    + (* ptyp_var_f *)
      dependent destruction H1. dependent destruction H2. simpl.
      split; [ fsetdec | apply d_consis__var; [ assumption | reflexivity ] ].
    + (* ptyp_arrow A1 A2 *)
      dependent destruction H1. dependent destruction H2. simpl.
      simpl in Hsz. pose proof (size_ptyp_min A1). pose proof (size_ptyp_min A2).
      assert (HszA1 : size_ptyp A1 < n) by lia.
      assert (HszA2 : size_ptyp A2 < n) by lia.
      edestruct (IHn A1 HszA1 _ _ _ _ _ H1_ H2_) as [Hincl1 Hcons1].
      edestruct (IHn A2 HszA2 _ _ _ _ _ H1_0 H2_0) as [Hincl2 Hcons2].
      split;
        [ fsetdec
        | eapply d_consis__arrow; [ exact Hcons1 | exact Hcons2 | reflexivity ] ].
    + (* ptyp_all A — A is the (body of the) middle type *)
      assert (HszA : size_ptyp A < n) by (simpl in Hsz; lia).
      dependent destruction H1; dependent destruction H2.
      { (* tagged → syn → inh : the only context-growing composition *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [X0 HX0].
          binder_ih IHn HszA H H0 A X0. simpl. fsetdec. }
        { simpl. eapply d_consis__forall_inh_tagged with (L := L `union` L0);
            [ | reflexivity ].
          intros X HX. binder_ih IHn HszA H H0 A X. exact Hcons. } }
      { (* tagged → syn → syn *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [X0 HX0].
          binder_ih IHn HszA H H0 A X0. simpl. fsetdec. }
        { simpl. apply d_consis__forall_syn_tagged with (L := L `union` L0).
          intros X HX. binder_ih IHn HszA H H0 A X. exact Hcons. } }
      { (* syn → syn → inh *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [X0 HX0].
          binder_ih IHn HszA H H0 A X0. simpl. fsetdec. }
        { simpl. apply d_consis__forall_inh_untagged with (L := L `union` L0).
          intros X HX. binder_ih IHn HszA H H0 A X. exact Hcons. } }
      { (* syn → syn → syn *)
        split.
        { destruct (atom_fresh (L `union` L0)) as [X0 HX0].
          binder_ih IHn HszA H H0 A X0. simpl. fsetdec. }
        { simpl. apply d_consis__forall_syn with (L := L `union` L0).
          intros X HX. binder_ih IHn HszA H H0 A X. exact Hcons. } }
Qed.

Lemma d_consis_compose : forall Δa Δb Γ C A B,
    Δa ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A ->
    Δb ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B ->
    exists Δc, (Δa `union` Δb) [<=] Δc /\ Δc ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Δa Δb Γ C A B H1 H2.
  exists (compose_tags C B).
  exact (@d_consis_compose_strong (S (size_ptyp A)) A ltac:(lia) Δa Δb Γ C B H1 H2).
Qed.


(** Coercions never introduce free type variables. *)
Lemma ftvar_btyp_to_utyp_syn : forall B,
    ftvar_in_utyp (btyp_to_utyp_syn B) [<=] ftvar_in_btyp B.
Proof. induction B; simpl; fsetdec. Qed.

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


(** ===== [utyp_to_btyp] opening / erasure lemmas ===== *)

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


(** Empty-context composition: arbitrary input tag contexts, syn middle and
    target ⟹ empty output (the [mode_ti] infer base demands the empty set). *)
Lemma d_consis_compose_syn_nil_l : forall Δa Δb Γ C B2 B,
    is_syn B2 -> is_syn B ->
    Δa ⨟ Γ ⊨ C ≈ B2 ->
    Δb ⨟ Γ ⊨ (btyp_to_utyp_syn B2) ≈ B ->
    empty ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Δa Δb Γ C B2 B Hsyn2 HsynB Hc Hd.
  rewrite <- (ptyp_to_btyp_syn_btyp_to_ptyp Hsyn2) in Hc.
  rewrite <- (ptyp_to_utyp_syn_btyp_to_ptyp B2) in Hd.
  pose proof (@d_consis_compose_strong (S (size_ptyp (btyp_to_ptyp B2)))
                (btyp_to_ptyp B2) ltac:(lia) Δa Δb Γ C B Hc Hd) as [_ Hcons].
  exact (d_consis_equiv (@compose_tags_is_syn_nil B C HsynB) Hcons).
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
