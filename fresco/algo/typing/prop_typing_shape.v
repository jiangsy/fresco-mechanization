Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.prop_stability.

Set Implicit Arguments.

Inductive fn_arrow_shape_pskl : mode -> pskl -> Prop :=
| fn_arrow_shape_pskl__ti : forall P,
    fn_arrow_shape_pskl mode_ti P
| fn_arrow_shape_pskl__tc : forall P,
    fn_arrow_shape_pskl mode_tc P
| fn_arrow_shape_pskl__fn : forall M P Q,
    fn_arrow_shape_pskl M Q ->
    fn_arrow_shape_pskl (mode_fn M) (pskl_arrow P Q).

Inductive fn_arrow_shape : mode -> ptyp -> Prop :=
| fn_arrow_shape__ti : forall A,
    fn_arrow_shape mode_ti A
| fn_arrow_shape__tc : forall A,
    fn_arrow_shape mode_tc A
| fn_arrow_shape__fn : forall M A B,
    fn_arrow_shape M B ->
    fn_arrow_shape (mode_fn M) (ptyp_arrow A B).

Lemma fn_arrow_shape_of_pskl : forall M A,
  fn_arrow_shape_pskl M (ptyp_to_pskl A) ->
  fn_arrow_shape M A.
Proof.
  intros M A H.
  remember (ptyp_to_pskl A) as P eqn:HP.
  revert A HP; induction H; intros A0 HP; subst.
  - apply fn_arrow_shape__ti.
  - apply fn_arrow_shape__tc.
  - destruct A0; simpl in HP; try discriminate.
    inversion HP; subst.
    apply fn_arrow_shape__fn. apply IHfn_arrow_shape_pskl. reflexivity.
Qed.

Lemma a_sub_sub_flex_fn_arrow_shape :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 ->
     NM = a_sub_mode_ty ->
     fn_arrow_shape_pskl M Q) /\
  (forall NM M P0 Θ0 Ξ α Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     NM = a_sub_mode_ty ->
     fn_arrow_shape_pskl (mode_fn M) Q).
Proof.
  apply a_sub_sub_flex_tm_mutind;
    intros;
    try match goal with
        | H : a_sub_mode_sk = a_sub_mode_ty |- _ => discriminate H
        end;
    try (apply fn_arrow_shape_pskl__ti);
    try (apply fn_arrow_shape_pskl__tc);
    try match goal with
        | IH : _ = a_sub_mode_ty -> fn_arrow_shape_pskl _ _ |- _ =>
            apply IH; assumption
        end.
  -
    apply fn_arrow_shape_pskl__fn.
    match goal with
    | IH : _ = a_sub_mode_ty -> fn_arrow_shape_pskl _ _ |- _ =>
        apply IH; assumption
    end.
Qed.

Lemma a_typing_fn_arrow_shape : forall M Θ0 P0 e C Θ1,
  {{ Θ0 ⊢[ M ; P0 ] e ⦂ C ⊣ Θ1 }}a ->
  fn_arrow_shape M C.
Proof.
  intros M Θ0 P0 e C Θ1 H; induction H;
    try (apply fn_arrow_shape__tc);
    try (apply fn_arrow_shape_of_pskl;
         eapply (proj1 a_sub_sub_flex_fn_arrow_shape);
         [ eassumption | reflexivity ]).
  1,2:
    destruct m as [ | | M' ];
      [ apply fn_arrow_shape__ti
      | exfalso; apply H; reflexivity
      | ];
    apply fn_arrow_shape__fn;
    cbn [decr_mode] in *;
    exact IHa_typing.
  -
    inversion IHa_typing1; subst; assumption.
Qed.
