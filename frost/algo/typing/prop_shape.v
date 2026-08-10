(** THE FN-MODE OUTPUT SHAPE — every run at mode [FN^n M] returns a syntactic
    arrow chain of depth at least [n].

    [AT-App]'s function premise demands a SYNTACTIC arrow
    ([a_typing__app]: the function runs at [FN m] and its result is matched
    against [ptyp_arrow A B]), so completeness must know that a fn-mode output
    always IS one.  The relation is indexed by the mode so the App row's own
    recursion closes: peeling one [FN] off the mode peels one arrow off the
    output.

    ⚙ A pure structural shape fact — nothing to do with [a_rigid_only]
    preservation or the TC-core discipline; like every other file in this
    directory its only consumer is [prop_typing.v].

    ⚠️ [fn_arrow_shape_pskl] and [fn_arrow_shape] are the SAME relation modulo
    [ptyp_to_pskl] — the [ptyp] one is the [pskl] one restricted to paintings,
    and both have [True] base rows, which makes them the common ERASURE of
    [a_ty_mode_compat] / [a_sk_mode_compat] (algo/def_extra.v).  Collapsing all
    four onto one arrow-spine relation is cleanup audit §4(c); until then
    [fn_arrow_shape_of_pskl] is the one bridge that is actually used. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_stability.       (* a_sub_sub_flex_tm_mutind *)

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

(** Every TY-sorted subtyping output has the fn-arrow shape of its mode. *)
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
  apply (a_sub_sub_flex_tm_mutind
           (fun NM M P0 Θ0 P Q Θ1 _ =>
              NM = a_sub_mode_ty -> fn_arrow_shape_pskl M Q)
           (fun NM M P0 Θ0 Ξ α Q Θ1 _ =>
              NM = a_sub_mode_ty -> fn_arrow_shape_pskl (mode_fn M) Q));
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
  - (* Arrow *)
    apply fn_arrow_shape_pskl__fn.
    match goal with
    | IH : _ = a_sub_mode_ty -> fn_arrow_shape_pskl _ _ |- _ =>
        apply IH; assumption
    end.
Qed.

Definition a_sub_ty_fn_arrow_shape := proj1 a_sub_sub_flex_fn_arrow_shape.

(** …hence every fn-mode [a_typing] output is a SYNTACTIC arrow chain. *)
Lemma a_typing_fn_arrow_shape : forall M Θ0 P0 e C Θ1,
  Θ0 ⊢ᵃ[ M ; P0 ] e ⦂ C ⊣ Θ1 ->
  fn_arrow_shape M C.
Proof.
  intros M Θ0 P0 e C Θ1 H; induction H;
    try (apply fn_arrow_shape__tc);
    try (apply fn_arrow_shape_of_pskl;
         eapply a_sub_ty_fn_arrow_shape; [ eassumption | reflexivity ]).
  - (* abs *)
    destruct m as [ | | M' ];
      [ apply fn_arrow_shape__ti
      | exfalso; apply H; reflexivity
      | ].
    apply fn_arrow_shape__fn.
    cbn [decr_mode] in *.
    exact IHa_typing.
  - (* abs_anno *)
    destruct m as [ | | M' ];
      [ apply fn_arrow_shape__ti
      | exfalso; apply H; reflexivity
      | ].
    apply fn_arrow_shape__fn.
    cbn [decr_mode] in *.
    exact IHa_typing.
  - (* app : the function's shape at (fn m) peels to the output's at m *)
    inversion IHa_typing1; subst; assumption.
Qed.
