(** MODE COMPATIBILITY — the inversions of [skmod{SK}] / [skmod{TY}] and of
    the mode-compatibility relations they are stated over.

    Two relations at two sorts, and every consumer wants the same four
    questions answered of each: what does compatibility at a HOLE force on the
    mode, what does it force at an ARROW, and what do [mod_comp_sk] /
    [mod_comp_ty] give back at [TI] / [TC] / [FN].  They used to be split
    between [pat/prop_soundness_pat.v] (the SK half) and
    [typing/prop_soundness_typing.v] (the TY half), so half the answers came
    with a soundness theorem attached.

    ⚙ [a_sk_mode_compat] / [a_ty_mode_compat] are ALGORITHMIC ([algo/def_rules.v]);
    [mod_comp_sk] / [mod_comp_ty] are cross-system ([frost/def_shapes.v]) and
    their [TC] inversion [mod_comp_ty_tc_inv] stays with the other cross-system
    shape facts in [frost/prop_basic.v].  The substitution lemmas
    ([mod_comp_ty_subst_mono], [a_ty_mode_compat_subst_mono], …) stay with the
    substitution machinery that states them. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.

(* ⚠️ The two source files these lemmas came from both had it on, so their
   arguments were implicit at every call site. *)
Set Implicit Arguments.

(* ===================================================================== *)
(*  The SKELETON sort                                                     *)
(* ===================================================================== *)

Lemma a_sk_mode_compat_arrow_inv : forall m P Q,
  a_sk_mode_compat m (pskl_arrow P Q) ->
  exists m', m = mode_fn m' /\ a_sk_mode_compat m' Q.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma a_sk_mode_compat_hole_inv : forall m,
  a_sk_mode_compat m pskl_hole -> m = mode_ti \/ m = mode_tc.
Proof. intros * H; inversion H; auto. Qed.

Lemma mod_comp_sk_ti_inv : forall Q, mod_comp_sk Q mode_ti -> is_sskl Q.
Proof. intros Q H; inversion H; subst; assumption. Qed.

Lemma mod_comp_sk_tc_inv : forall Q, mod_comp_sk Q mode_tc -> is_sskl Q.
Proof. intros Q H; inversion H; subst; assumption. Qed.

Lemma mod_comp_sk_fn_inv : forall Q1 Q2 m,
  mod_comp_sk (bskl_arrow Q1 Q2) (mode_fn m) -> mod_comp_sk Q2 m.
Proof. intros * H; inversion H; subst; assumption. Qed.

(* ===================================================================== *)
(*  The TYPE sort                                                         *)
(* ===================================================================== *)

(** The TY-sorted twins of the three above.  ⚙ They live beside them (and
    not with type-inference soundness) because each pair is ONE fact at two
    sorts; [algo/typing/prop_scope.v] needs the TY ones without needing the
    theorem they used to travel with. *)
Lemma a_ty_mode_compat_hole_inv : forall m,
  a_ty_mode_compat m pskl_hole -> m = mode_ti.
Proof.
  intros m H. remember pskl_hole as Ps eqn:HPs.
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
