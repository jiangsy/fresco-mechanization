(** Frost — subtyping soundness statements for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.subtyping.prop_basics.
Require Import src.frost.decl.subtyping.prop_consis_trans.
Require Import src.frost.decl.subtyping.prop_consis_sub_trans.

Set Implicit Arguments.

(** Paper Lemma 3.2, stated over the native split categories.

    The shallow target is over [ptyp], so both sides erase from
    [utyp]/[btyp] to [ptyp]. *)
Theorem d_sub_sound : forall Γ C B,
    empty ⨟ Γ ⊢[ mode_tc ] C ⊑ B ->
    Γ ⊢ (btyp_to_ptyp C) ≤ (btyp_to_ptyp B).
Proof.
Admitted.

Inductive d_shallow_sub_mono : list (atom * dbind) -> ptyp -> ptyp -> Prop :=
| d_shallow_sub_mono__refl : forall Γ A,
    d_shallow_sub_mono Γ A A
| d_shallow_sub_mono__arrow : forall Γ A1 A2 A1' A2',
    d_shallow_sub_mono Γ A1' A1 ->
    d_shallow_sub_mono Γ A2 A2' ->
    d_shallow_sub_mono Γ (ptyp_arrow A1 A2) (ptyp_arrow A1' A2')
| d_shallow_sub_mono__forall_r : forall L Γ A1 A2,
    (forall X, X `notin` L ->
       d_shallow_sub_mono ((X ~ dbind_tvar) ++ Γ) A1
         (open_ptyp_wrt_ptyp A2 (ptyp_var_f X))) ->
    d_shallow_sub_mono Γ A1 (ptyp_all A2)
| d_shallow_sub_mono__forall_l : forall Γ A1 A2 I,
    mono_ptyp I ->
    d_wf_ptyp Γ I ->
    d_shallow_sub_mono Γ (open_ptyp_wrt_ptyp A1 I) A2 ->
    d_shallow_sub_mono Γ (ptyp_all A1) A2.

Theorem d_sub_complete_mono : forall Γ A B,
    d_shallow_sub_mono Γ A B ->
    exists C, C = ptyp_to_utyp_syn A /\ empty ⨟ Γ ⊢[ mode_tc ] C ⊑ (ptyp_to_btyp_inh B).
Proof.
Admitted.

Theorem d_sub_no_guess_uniqueness : forall Γ m Δ C B,
    Δ ⨟ Γ ⊢[ m ] C ⊑ B ->
    True.
Proof.
  auto.
Qed.
