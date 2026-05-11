(** Frost — declarative subtyping metatheory (Phase 2.C). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

(** * Reflexivity (on monotypes).

    The paper's [d_consis] is asymmetric: the LHS is an unresolved type
    ([is_utyp]) and the RHS is a coloured ("bidirectional") type
    ([is_typ]). Reflexivity in the strict sense [d_consis nil Γ A A] only
    makes sense when LHS-form = RHS-form — i.e. on monomorphic types,
    where both forms coincide. *)

Lemma d_consis_refl_mono : forall Γ A,
    mono_typ A ->
    d_consis nil Γ A A.
Proof.
  intros Γ A H. induction H.
  - apply d_consis__unit.
  - apply d_consis__var.
  - rewrite_env (@nil atom ++ (@nil atom)).
    apply d_consis__arrow; auto.
Qed.

(** Every monotype is in [is_syn_typ] (no quantifiers at all). *)
Lemma mono_typ_is_syn_typ : forall A,
    mono_typ A -> is_syn_typ A.
Proof.
  intros A H. induction H; constructor; auto.
Qed.

(** Every monotype is in [is_inh_typ]. *)
Lemma mono_typ_is_inh_typ : forall A,
    mono_typ A -> is_inh_typ A.
Proof.
  intros A H. induction H; constructor; auto.
Qed.

Lemma d_sub_refl_mono : forall Γ A,
    mono_typ A ->
    d_sub mode_ti nil Γ A A.
Proof.
  intros Γ A H.
  apply d_sub__infer.
  - apply mono_typ_is_syn_typ; auto.
  - apply d_consis_refl_mono; auto.
Qed.
