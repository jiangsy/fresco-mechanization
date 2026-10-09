(** Fresco declarative typing weakening, native split-syntax form. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.

Set Implicit Arguments.

(** ** Context weakening for consistency and subtyping (formerly
    [subtyping/prop_basics.v]). *)

Lemma d_consis_weakening : forall Γ1 Γ2 Γ3 Δ C B,
    {{ Δ ⨟ (Γ1 ++ Γ3) ⊢ C ∼ B }}d ->
    {{ Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ C ∼ B }}d.
Proof.
  intros Γ1 Γ2 Γ3 Δ C B H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst.
  - apply d_consis__unit. assumption.
  - apply d_consis__var; [ | assumption ].
    match goal with Hb : binds _ _ _ |- _ => analyze_binds Hb end.
  - eapply d_consis__arrow.
    + eapply IHd_consis1; reflexivity.
    + eapply IHd_consis2; reflexivity.
    + assumption.
  - eapply d_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ3)); [ | eassumption ].
    intros α2 Hα2.
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_consis__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros α2 Hα2.
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros α2 Hα2.
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_consis__forall_syn with (L := L `union` dom (Γ1 ++ Γ3)).
    intros α2 Hα2.
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
Qed.

Lemma d_consis_weakening_head : forall Γ Γ' Δ C B,
    {{ Δ ⨟ Γ ⊢ C ∼ B }}d ->
    {{ Δ ⨟ (Γ' ++ Γ) ⊢ C ∼ B }}d.
Proof.
  intros Γ Γ' Δ C B H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_consis_weakening. simpl. exact H.
Qed.

Lemma d_sub_weakening : forall Γ1 Γ2 Γ3 m Δ C B,
    {{ Δ ⨟ (Γ1 ++ Γ3) ⊢[ m ] C ⩽ B }}d ->
    {{ Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢[ m ] C ⩽ B }}d.
Proof.
  intros Γ1 Γ2 Γ3 m Δ C B H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst.
  - apply d_sub__infer; [ apply d_consis_weakening; assumption | assumption | assumption ].
  - apply d_sub__check;
      [ assumption | assumption | apply d_consis_weakening; assumption | assumption ].
  - apply d_sub__forall_r with (L := L `union` dom (Γ1 ++ Γ3)); [ assumption | ].
    intros α2 Hα2.
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H1 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - eapply d_sub__arg.
    + apply d_consis_weakening; eassumption.
    + match goal with IH : forall _ _, _ -> d_sub _ _ _ _ _ |- _ => apply (IH Γ1 Γ3 eq_refl) end.
    + eassumption.
  - eapply d_sub__forall_l_tagged.
    + assumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + apply d_wf_utyp_weakening; eassumption.
    + assumption.
    + match goal with IH : forall _ _, _ -> d_sub _ _ _ _ _ |- _ => apply (IH Γ1 Γ3 eq_refl) end.
  - eapply d_sub__forall_l_untagged.
    + assumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + apply d_wf_utyp_weakening; eassumption.
    + assumption.
    + match goal with IH : forall _ _, _ -> d_sub _ _ _ _ _ |- _ => apply (IH Γ1 Γ3 eq_refl) end.
Qed.

Lemma d_sub_weakening_head : forall Γ Γ' m Δ C B,
    {{ Δ ⨟ Γ ⊢[ m ] C ⩽ B }}d ->
    {{ Δ ⨟ (Γ' ++ Γ) ⊢[ m ] C ⩽ B }}d.
Proof.
  intros Γ Γ' m Δ C B H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_weakening. simpl. exact H.
Qed.

Lemma d_refine_syn_weakening : forall Γ1 Γ2 Γ3 Δ Q Q',
    {{ (Γ1 ++ Γ3) ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d ->
    {{ (Γ1 ++ Γ2 ++ Γ3) ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d.
Proof.
  intros Γ1 Γ2 Γ3 Δ Q Q' H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var.
  - apply d_refine_syn__arrow; auto.
  - apply d_refine_syn__all with (L := L `union` dom (Γ1 ++ Γ3)); [ assumption | ].
    intros α Hα.
    eapply (H1 α ltac:(solve_notin_auto) ((α ~ dbind_tvar) ++ Γ1) Γ3). simpl_env. reflexivity.
  - apply d_refine_syn__hole. assumption.
  - apply d_refine_syn__tophole_remove; auto.
  - (* [tophole_fill] now PREPENDS the bound var to [Γ]; weaken at [α::Γ1]. *)
    apply d_refine_syn__tophole_fill with (L := L `union` dom (Γ1 ++ Γ3)); [ assumption | ].
    intros α Hα.
    eapply (H1 α ltac:(solve_notin_auto) ((α ~ dbind_tvar) ++ Γ1) Γ3). simpl_env. reflexivity.
  - apply d_refine_syn__tophole_keep; auto.
Qed.

(** ⭐ The UNCOLOURED twin.  Same eight rows, same proof — the colours the
    coloured judgement tracks are exactly what this one drops, and no row's
    scoping depends on them.  Needed because the paper's presupposition on
    skeleton consistency (declarative.tex:2074) is stated at this sort. *)
Lemma d_refine_pskl_weakening : forall Γ1 Γ2 Γ3 Δ P Q,
    {{ (Γ1 ++ Γ3) ⨟ Δ ⊢ᵣₚ P ⊳ Q }}d ->
    {{ (Γ1 ++ Γ2 ++ Γ3) ⨟ Δ ⊢ᵣₚ P ⊳ Q }}d.
Proof.
  intros Γ1 Γ2 Γ3 Δ P Q H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_refine_pskl__unit.
  - apply d_refine_pskl__var.
  - apply d_refine_pskl__arrow; auto.
  - apply d_refine_pskl__all with (L := L `union` dom (Γ1 ++ Γ3)). intros α Hα.
    eapply (H0 α ltac:(solve_notin_auto) ((α ~ dbind_tvar) ++ Γ1) Γ3). simpl_env. reflexivity.
  - apply d_refine_pskl__hole. assumption.
  - apply d_refine_pskl__tophole_remove; auto.
  - apply d_refine_pskl__tophole_fill with (L := L `union` dom (Γ1 ++ Γ3)).
    intros α Hα.
    eapply (H0 α ltac:(solve_notin_auto) ((α ~ dbind_tvar) ++ Γ1) Γ3).
    simpl_env. reflexivity.
  - apply d_refine_pskl__tophole_keep. auto.
Qed.

Lemma d_pat_consis_weakening : forall Γ1 Γ2 Γ3 Δ R Q,
    {{ Δ ⨟ (Γ1 ++ Γ3) ⊢ˢ R ∼ Q }}d ->
    {{ Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ˢ R ∼ Q }}d.
Proof.
  intros Γ1 Γ2 Γ3 Δ R Q H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_pat_consis__unit. assumption.
  - apply d_pat_consis__var; [ assumption | analyze_binds H ].
  - eapply d_pat_consis__arrow;
      [ eapply IHd_pat_consis1; reflexivity
      | eapply IHd_pat_consis2; reflexivity
      | eassumption ].
  - apply d_pat_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ3)) (Ψ0 := Ψ0);
      [ intros α2 Hα2; rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3);
        eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3); simpl; reflexivity
      | eassumption ].
  - apply d_pat_consis__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros α2 Hα2. rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros α2 Hα2. rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__forall_syn with (L := L `union` dom (Γ1 ++ Γ3)).
    intros α2 Hα2. rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__ghostg. assumption.
  - apply d_pat_consis__topholeg. eapply IHd_pat_consis; reflexivity.
  - apply d_pat_consis__hole; [ assumption | apply d_wf_pskl_weakening; assumption ].
  - apply d_pat_consis__tophole. eapply IHd_pat_consis; reflexivity.
  - apply d_pat_consis__tophole_inh with (L := L `union` dom (Γ1 ++ Γ3)).
    intros α2 Hα2. rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__tophole_drop. eapply IHd_pat_consis; reflexivity.
Qed.

(** The JOIN weakens because both of its halves do. *)
Lemma d_consis_join_weakening : forall Γ1 Γ2 Γ3 Δ R Q,
    {{ Δ ⨟ (Γ1 ++ Γ3) ⊢ˢ R ∼ᵣ Q }}d ->
    {{ Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ˢ R ∼ᵣ Q }}d.
Proof.
  intros * [Hc Hr]. split.
  - apply d_pat_consis_weakening; assumption.
  - apply d_refine_pskl_weakening; assumption.
Qed.

Lemma d_pat_sub_weakening : forall Γ1 Γ2 Γ3 m Δ R Q,
    {{ Δ ⨟ (Γ1 ++ Γ3) ⊢ˢ[ m ] R ⩽ Q }}d ->
    {{ Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢ˢ[ m ] R ⩽ Q }}d.
Proof.
  intros Γ1 Γ2 Γ3 m Δ R Q H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_pat_sub__infer;
      [ assumption | apply d_consis_join_weakening; assumption | assumption ].
  - apply d_pat_sub__univ_ghost_r; try assumption;
      apply d_consis_join_weakening; assumption.
  - eapply d_pat_sub__arg;
      [ apply d_consis_join_weakening; eassumption
      | eapply IHd_pat_sub; reflexivity
      | eassumption ].
  - eapply d_pat_sub__forall_l_tagged.
    + assumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + apply d_wf_uskl_weakening; eassumption.
    + assumption.
    + eapply IHd_pat_sub; reflexivity.
  - eapply d_pat_sub__forall_l_untagged.
    + assumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + apply d_wf_uskl_weakening; eassumption.
    + assumption.
    + eapply IHd_pat_sub; reflexivity.
  - apply d_pat_sub__ghost; [ assumption | apply d_wf_pskl_weakening; assumption | assumption ].
  - apply d_pat_sub__univ_ghost_l; [ assumption | eapply IHd_pat_sub; reflexivity ].
  - apply d_pat_sub__ghostg; assumption.
  - apply d_pat_sub__univ_ghost_lg; [ assumption | eapply IHd_pat_sub; reflexivity ].
Qed.

(** Apply a cofinite-body IH (found by shape) after the env has been reshaped to
    [(bind ++ Γ1) ++ Γ2 ++ Γ3]; [eapply] unifies the split, leaving freshness +
    the trivial context equation. *)
Ltac wk_cof :=
  match goal with
  | IH : forall _ : atom, _ -> forall _ _ : list (atom * dbind), _ = _ -> _ |- _ =>
      eapply IH; [ fsetdec | simpl; reflexivity ]
  end.
(** Apply the direct IH for subterm [ex]. *)
Ltac wk_dir ex :=
  match goal with
  | IH : forall _ _ : list (atom * dbind), _ = _ -> {{ _ ⊢ˢ[ _ ] ex ⦂ _ }}d |- _ => apply IH; reflexivity
  | IH : forall _ _ : list (atom * dbind), _ = _ -> {{ _ ⊢[ _ ] ex ⦂ _ }}d |- _ => apply IH; reflexivity
  end.

(** [d_pat] is self-contained, so its weakening is a standalone induction. *)
Lemma d_pat_weakening_mid : forall Γ2 m Γ e Q,
    {{ Γ ⊢ˢ[ m ] e ⦂ Q }}d ->
    forall Γ1 Γ3, Γ = Γ1 ++ Γ3 -> {{ (Γ1 ++ Γ2 ++ Γ3) ⊢ˢ[ m ] e ⦂ Q }}d.
Proof.
  intros Γ2 m Γ e Q H. induction H; intros Γ1 Γ3 Heq; subst.
  (* Paper P-Unit/P-Var/P-Anno now embed the skeleton-subtyping premise. *)
  - apply d_pat__unit;
      [ apply d_wf_pskl_weakening; assumption
      | apply d_pat_sub_weakening; assumption ].
  - apply d_pat__var with (d := d) (P := P);
      [ analyze_binds H | exact H0 | apply d_wf_pskl_weakening; exact H1
      | apply d_pat_sub_weakening; exact H2 ].
  - apply d_pat__anno;
      [ apply d_wf_ptyp_weakening; assumption
      | apply d_wf_pskl_weakening; assumption
      | apply d_pat_sub_weakening; assumption ].
  - apply d_pat__freeze. apply IHd_pat; reflexivity.
  - apply d_pat__abs with (L := L `union` dom (Γ1 ++ Γ3)) (P := P);
      [ exact H | apply d_wf_pskl_weakening; assumption | assumption | ].
    intros x Hx. rewrite_env (((x ~ dbind_skl P) ++ Γ1) ++ Γ2 ++ Γ3). wk_cof.
  - apply d_pat__abs_anno with (L := L `union` dom (Γ1 ++ Γ3)) (B := B);
      [ exact H | apply d_wf_ptyp_weakening; assumption | reflexivity | assumption | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ (btyp_to_ptyp B)) ++ Γ1) ++ Γ2 ++ Γ3). wk_cof.
  - eapply d_pat__app;
      [ wk_dir e2 | apply d_refine_syn_weakening; eassumption | wk_dir e1 ].
  - apply d_pat__abs_check with (L := L `union` dom (Γ1 ++ Γ3)).
    intros x Hx. rewrite_env (((x ~ dbind_skl pskl_hole) ++ Γ1) ++ Γ2 ++ Γ3).
    wk_cof.
  - apply d_pat__abs_anno_check with (L := L `union` dom (Γ1 ++ Γ3)) (A := A);
      [ apply d_wf_ptyp_weakening; assumption | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3). wk_cof.
Qed.

Lemma d_pat_weakening : forall Γ1 Γ2 Γ3 m e Q,
    {{ (Γ1 ++ Γ3) ⊢ˢ[ m ] e ⦂ Q }}d ->
    {{ (Γ1 ++ Γ2 ++ Γ3) ⊢ˢ[ m ] e ⦂ Q }}d.
Proof.
  intros Γ1 Γ2 Γ3 m e Q H. eapply d_pat_weakening_mid; [ exact H | reflexivity ].
Qed.

(** General (order-preserving) context weakening: [Γ'] is [Γ] with extra
    bindings inserted at arbitrary positions.  Encoded as a chain of the
    middle-insertions that [d_typing_weakening] already supports, so the
    judgement closures below are one-liners. *)
Inductive ctx_weaken : list (atom * dbind) -> list (atom * dbind) -> Prop :=
| ctx_weaken_refl : forall Γ, ctx_weaken Γ Γ
| ctx_weaken_insert : forall Γ1 Γ2 Γ3 Γ',
    ctx_weaken (Γ1 ++ Γ2 ++ Γ3) Γ' ->
    ctx_weaken (Γ1 ++ Γ3) Γ'.

Lemma d_pat_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall m e Q, {{ Γ ⊢ˢ[ m ] e ⦂ Q }}d -> {{ Γ' ⊢ˢ[ m ] e ⦂ Q }}d.
Proof.
  induction 1; intros m e Q Hp; [ assumption | ].
  apply IHctx_weaken. apply d_pat_weakening. exact Hp.
Qed.

Lemma d_refine_syn_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall Δ Q Q', {{ Γ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d -> {{ Γ' ⨟ Δ ⊢ᵣ Q ⊳ Q' }}d.
Proof.
  induction 1; intros Δ Q Q' Hr; [ assumption | ].
  apply IHctx_weaken. apply d_refine_syn_weakening. exact Hr.
Qed.

Lemma binds_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall x b, binds x b Γ -> binds x b Γ'.
Proof.
  induction 1; intros x b Hb; [ assumption | ].
  apply IHctx_weaken. analyze_binds Hb.
Qed.

Lemma ctx_weaken_cons : forall Γ Γ' a,
    ctx_weaken Γ Γ' -> ctx_weaken (a ++ Γ) (a ++ Γ').
Proof.
  intros Γ Γ' a H. revert a. induction H; intros a.
  - apply ctx_weaken_refl.
  - rewrite_env ((a ++ Γ1) ++ Γ3).
    apply ctx_weaken_insert with (Γ2 := Γ2).
    rewrite_env (a ++ (Γ1 ++ Γ2 ++ Γ3)). apply IHctx_weaken.
Qed.

Lemma ctx_weaken_trans : forall Γ1 Γ2 Γ3,
    ctx_weaken Γ1 Γ2 -> ctx_weaken Γ2 Γ3 -> ctx_weaken Γ1 Γ3.
Proof.
  (* [induction H] reintroduces [ctx_weaken_insert]'s own [Γ1 Γ2 Γ3], so the
     reverted target is named [Γ0] to avoid colliding with the constructor's
     [Γ3] (the statement's [Γ1]/[Γ2] are fine — they are consumed by the
     induction). *)
  intros Γ1 Γ2 Γ3 H. revert Γ3. induction H; intros Γ0 Hbc; [ assumption | ].
  apply ctx_weaken_insert with (Γ2 := Γ2). apply IHctx_weaken. exact Hbc.
Qed.

(** Inserting a single block at the front. *)
Lemma ctx_weaken_app_front : forall Γ2 Γ,
    ctx_weaken Γ (Γ2 ++ Γ).
Proof.
  intros Γ2 Γ. rewrite_env (nil ++ Γ).
  apply ctx_weaken_insert with (Γ2 := Γ2). simpl. apply ctx_weaken_refl.
Qed.

Lemma d_wf_ptyp_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall A, d_wf_ptyp Γ A -> d_wf_ptyp Γ' A.
Proof.
  induction 1; intros A Hwf; [ assumption | ].
  apply IHctx_weaken. apply d_wf_ptyp_weakening. exact Hwf.
Qed.

Lemma d_sub_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall m Δ C B, d_sub m Δ Γ C B -> d_sub m Δ Γ' C B.
Proof.
  induction 1; intros m Δ C B Hs; [ assumption | ].
  apply IHctx_weaken. apply d_sub_weakening. exact Hs.
Qed.

(** [d_sd_typing] weakening — mirrors [d_typing_weakening_mid].  The embedded
    subtyping premises of [__unit]/[__var]/[__anno] weaken by
    [d_sub_weakening]; everything else is the same cofinite replay. *)
Lemma d_sd_typing_weakening_mid : forall Γ2 m Γ e B,
    {{ Γ ⊢ˢᵈ[ m ] e ⦂ B }}d ->
    forall Γ1 Γ3, Γ = Γ1 ++ Γ3 -> {{ (Γ1 ++ Γ2 ++ Γ3) ⊢ˢᵈ[ m ] e ⦂ B }}d.
Proof.
  intros Γ2 m Γ e B H. induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_sd_typing__unit. apply d_sub_weakening; assumption.
  - apply d_sd_typing__var with (A := A);
      [ analyze_binds H | apply d_sub_weakening; assumption ].
  - eapply d_sd_typing__anno;
      [ apply IHd_sd_typing; reflexivity | apply d_sub_weakening; assumption ].
  - apply d_sd_typing__freeze. apply IHd_sd_typing; reflexivity.
  - apply d_sd_typing__abs_check_step with (L := L `union` dom (Γ1 ++ Γ3));
      [ assumption | ].
    intros α Hα. rewrite_env (((α ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3). wk_cof.
  - apply d_sd_typing__abs_check_base with (L := L `union` dom (Γ1 ++ Γ3));
      [ apply d_wf_ptyp_weakening; assumption | assumption | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3). wk_cof.
  - apply d_sd_typing__abs_anno_check_step with (L := L `union` dom (Γ1 ++ Γ3));
      [ assumption | ].
    intros α Hα. rewrite_env (((α ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3). wk_cof.
  - apply d_sd_typing__abs_anno_check_base with (L := L `union` dom (Γ1 ++ Γ3));
      [ apply d_wf_ptyp_weakening; assumption | assumption | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3). wk_cof.
  - apply d_sd_typing__abs with (L := L `union` dom (Γ1 ++ Γ3)) (A := A);
      [ assumption | apply d_wf_ptyp_weakening; assumption | assumption | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3). wk_cof.
  - apply d_sd_typing__abs_anno with (L := L `union` dom (Γ1 ++ Γ3)) (A := A) (B1 := B1);
      [ assumption | apply d_wf_ptyp_weakening; assumption | assumption | assumption | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3). wk_cof.
  - eapply d_sd_typing__app;
      [ eapply d_pat_weakening_mid; [ eassumption | reflexivity ]
      | apply d_refine_syn_weakening; eassumption
      | apply IHd_sd_typing1; reflexivity
      | apply IHd_sd_typing2; reflexivity ].
Qed.

Lemma d_sd_typing_weakening : forall Γ1 Γ2 Γ3 m e B,
    {{ (Γ1 ++ Γ3) ⊢ˢᵈ[ m ] e ⦂ B }}d ->
    {{ (Γ1 ++ Γ2 ++ Γ3) ⊢ˢᵈ[ m ] e ⦂ B }}d.
Proof.
  intros. eapply d_sd_typing_weakening_mid; [ eassumption | reflexivity ].
Qed.

Lemma d_sd_typing_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall m e B, {{ Γ ⊢ˢᵈ[ m ] e ⦂ B }}d -> {{ Γ' ⊢ˢᵈ[ m ] e ⦂ B }}d.
Proof.
  induction 1; intros m e B Hty; [ assumption | ].
  apply IHctx_weaken. apply d_sd_typing_weakening. exact Hty.
Qed.
