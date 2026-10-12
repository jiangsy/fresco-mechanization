Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.

Set Implicit Arguments.

Lemma a_sk_mode_compat_arrow_inv : forall m P Q,
  a_sk_mode_compat m (pskl_arrow P Q) ->
  exists m', m = mode_fn m' /\ a_sk_mode_compat m' Q.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma a_sk_mode_compat_ghost_inv : forall m,
  a_sk_mode_compat m pskl_ghost -> m = mode_ti \/ m = mode_tc.
Proof. intros * H; inversion H; auto. Qed.

Lemma mod_comp_sk_ti_inv : forall Q, mod_comp_sk Q mode_ti -> is_sskl Q.
Proof. intros Q H; inversion H; subst; assumption. Qed.

Lemma mod_comp_sk_tc_inv : forall Q, mod_comp_sk Q mode_tc -> is_sskl Q.
Proof. intros Q H; inversion H; subst; assumption. Qed.

Lemma mod_comp_sk_fn_inv : forall Q1 Q2 m,
  mod_comp_sk (bskl_arrow Q1 Q2) (mode_fn m) -> mod_comp_sk Q2 m.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma a_sk_mode_compat_subst_mono : forall M P τ β,
  a_sk_mode_compat M P -> mono_ptyp τ ->
  a_sk_mode_compat M (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros M P τ β H Hm; induction H; simpl;
    [ apply a_sk_mode_compat__ti | apply a_sk_mode_compat__tc
    | apply a_sk_mode_compat__fn; assumption ].
Qed.

Lemma a_sk_mode_compat_mod_comp_sk : forall M P0,
  a_sk_mode_compat M P0 -> mod_comp_sk (pskl_to_bskl_inh P0) M.
Proof.
  intros M P0 H; induction H; simpl.
  - apply mod_comp_sk__ti; apply is_sskl__ghost.
  - apply mod_comp_sk__tc; apply is_sskl__ghost.
  - apply mod_comp_sk__fn; assumption.
Qed.

Lemma a_ty_mode_compat_ghost_inv : forall m,
  a_ty_mode_compat m pskl_ghost -> m = mode_ti.
Proof.
  intros m H. remember pskl_ghost as Ps eqn:HPs.
  destruct H.
  - reflexivity.
  - destruct A; simpl in HPs; discriminate.
  - discriminate.
Qed.

Lemma a_ty_mode_compat_arrow_inv : forall m P Q,
  a_ty_mode_compat m (pskl_arrow P Q) ->
  m <> mode_tc ->
  exists m', m = mode_fn m' /\ a_ty_mode_compat m' Q.
Proof.
  intros m P Q H Hne. remember (pskl_arrow P Q) as Ps eqn:HPs.
  destruct H.
  - discriminate.
  - exfalso; apply Hne; reflexivity.
  - inversion HPs; subst. exists M; split; [ reflexivity | assumption ].
Qed.

Lemma mod_comp_ty_fn_inv : forall B1 B2 m,
  mod_comp_ty (btyp_arrow B1 B2) (mode_fn m) -> mod_comp_ty B2 m.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma mod_comp_ty_ti_inv : forall B, mod_comp_ty B mode_ti -> is_styp B.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma a_ty_mode_compat_subst_mono : forall M P τ β,
  a_ty_mode_compat M P -> mono_ptyp τ ->
  a_ty_mode_compat M (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros M P τ β H Hm; induction H; simpl.
  - apply a_ty_mode_compat__ti.
  - rewrite <- ptyp_to_pskl_subst; apply a_ty_mode_compat__tc.
  - apply a_ty_mode_compat__fn; assumption.
Qed.

Lemma a_ty_mode_compat_tc_ghost_free : forall P,
  a_ty_mode_compat mode_tc P -> pskl_ghost_free P.
Proof. intros P H; inversion H; subst; apply ptyp_to_pskl_ghost_free. Qed.

Lemma pskl_ghost_free_ty_mode_compat_tc : forall P,
  pskl_ghost_free P -> a_ty_mode_compat mode_tc P.
Proof.
  intros P H; destruct (pskl_ghost_free_to_ptyp _ H) as [A ->]; apply a_ty_mode_compat__tc.
Qed.
