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

Set Implicit Arguments.

Ltac nbauto := try sauto limit:30.







Lemma d_consis_refl_styp_as_utyp : forall Γ B,
    Γ ⊢ᵦ B ->
    is_styp B ->
    empty ⨟ Γ ⊨ (btyp_to_utyp_syn B) ≈ B.
Proof.
  intros Γ B Hwf Hst.
  generalize dependent Hst.
  dependent induction Hwf; intros Hst; inversion Hst; subst; simpl.
  - apply d_consis__unit. reflexivity.
  - apply d_consis__var; [ exact H | reflexivity ].
  - eapply d_consis__arrow.
    + apply IHHwf1. exact H1.
    + apply IHHwf2. exact H2.
    + fsetdec.
  - apply d_consis__forall_syn with (L := L `union` L0).
    intros X HX.
    change (utyp_var_f X) with (btyp_to_utyp_syn (btyp_var_f X)).
    rewrite <- btyp_to_utyp_syn_open.
    apply H0; auto.
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
    [mode_ti]/[__infer_gen] base of B.4 keep its nil output. *)
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

(** Keystone for B.4: on a synthesised [btyp], the [gutyp] embedding equals
    the [utyp]-route embedding.  This collapses [d_sub_gen_trans]'s middle
    [btyp_to_gutyp B2] into the [utyp] image, where the (non-gen) B.2
    [d_consis_compose] applies. *)

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
    exists Δc, (Δa `union` Δb) [<=] Δc /\ Δc ⨟ Γ ⊨ C ≈ B.
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
    empty ⨟ Γ ⊨ C ≈ B2 ->
    empty ⨟ Γ ⊨ (btyp_to_utyp_syn B2) ≈ B ->
    empty ⨟ Γ ⊨ C ≈ B.
Proof.
  intros Γ C B2 B Hsyn2 HsynB Hc Hd.
  rewrite <- (ptyp_to_btyp_syn_btyp_to_ptyp Hsyn2) in Hc.
  rewrite <- (ptyp_to_utyp_syn_btyp_to_ptyp B2) in Hd.
  pose proof (@d_consis_compose_strong (S (size_ptyp (btyp_to_ptyp B2)))
                (btyp_to_ptyp B2) ltac:(lia) empty empty Γ C B Hc Hd) as [_ Hcons].
  exact (d_consis_equiv (@compose_tags_is_syn_nil B C HsynB) Hcons).
Qed.
(** [utyp_to_gutyp] is injective: [gutyp] has constructors outside its image
    ([gutyp_all_inh]) and is structural on the shared ones, so equal images
    come from equal sources.  Lets us invert the rule premise
    [utyp_to_gutyp C0 = utyp_to_gutyp (btyp_to_utyp_syn B2)] into [C0 = ...]. *)


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
    empty ⨟ Γ ⊨ (btyp_to_utyp_syn (utyp_to_btyp C)) ≈ B.
Proof.
  intros Δ Γ C B H. induction H; simpl.
  - apply d_consis__unit. reflexivity.
  - apply d_consis__var; [ assumption | reflexivity ].
  - eapply d_consis__arrow; [ eassumption | eassumption | fsetdec ].
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
  - apply d_consis__unit. assumption.
  - match goal with |- context [ if ?d then _ else _ ] => destruct d end.
    + apply d_consis__var; [ auto | assumption ].
    + apply d_consis__var; [ analyze_binds H; auto | assumption ].
  - eapply d_consis__arrow.
    + eapply IHd_consis1; [ reflexivity | exact Hfr ].
    + eapply IHd_consis2; [ reflexivity | exact Hfr ].
    + assumption.
  - eapply d_consis__forall_inh_tagged with
      (L := L `union` dom (Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2) `union` singleton X0 `union` singleton Y).
    + intros Z HZ.
      erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (solve [ fsetdec | apply lc_utyp_var_f ]).
      erewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (solve [ fsetdec | apply lc_btyp_var_f ]).
      rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ (Y ~ dbind_tvar) ++ Γ2).
      eapply (H0 Z); [ fsetdec | simpl; reflexivity | simpl; fsetdec ].
    + assumption.
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

(** B.4 base, AUX.  [Cmid] is the second sub's LHS [utyp]; the source [Csrc] is
    tied to it by consistency against its [btyp] erasure [utyp_to_btyp Cmid].
    Inducting on the second sub with [Csrc]/[Cmid]/[Δa] quantified after lets
    the IH re-pick them in the arrow/forall recursions; the erasure invariant
    survives [forall_l] instantiation by a tagged [ph]. *)

(** B.3 base / B.4: the output tag context is a SUPERSET of the inputs, NOT
    nil.  For a general (etag-bearing) [B1], an etag-∀ in [B1] that is
    syn-matched against the synthesised middle [B2] (no tag) but reaches an
    inh part of the target [B3] forces [forall_inh_tagged] to record a tag —
    so the composed subtyping's context is genuinely non-nil (the same
    tagged→syn→inh phenomenon as B.2).  Hence [exists Δc, incl ...]. *)


(** Specialisation D12 actually needs: when the LHS is an etag-free
    [btyp_to_gutyp] image (a typing result), there is no syn→inh etag flip,
    so the composed context collapses to nil — letting [d_typing_gen__sub]
    (which demands a nil context) consume it. *)

(** * D1/D12 route — step 1: function-side subsumption.

    The [__embed] half of D12, extracted as an induction on the *plain*
    typing derivation so the FN-spine recursion is structural (n
    decrements with the arrow spine).  Driving this case-by-case is what
    tells us whether D12 holds as currently stated, and which (if any)
    rule side-conditions must move after the bidirectional-A refactor. *)
