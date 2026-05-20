(** Frost algorithmic-system definitions for the current split syntax.

    This file intentionally uses the latest generated categories
    directly: [ptyp], [btyp], [utyp], [pskl], [bskl], and [uskl]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.

Set Implicit Arguments.

Inductive abind : Set :=
| abind_tvar : abind
| abind_var_typ : ptyp -> abind
| abind_flex_mono : abind
| abind_flex_mono_def : ptyp -> abind
| abind_flex_poly_def : pskl -> abind
| abind_marker : abind.

Definition aenv : Set := list (atom * abind).

Inductive a_suffix_binding : abind -> Prop :=
| a_suffix_binding__flex_mono :
    a_suffix_binding abind_flex_mono
| a_suffix_binding__flex_mono_def : forall A,
    a_suffix_binding (abind_flex_mono_def A)
| a_suffix_binding__flex_poly_def : forall P,
    a_suffix_binding (abind_flex_poly_def P).

Inductive a_suffix : aenv -> Prop :=
| a_suffix__nil : a_suffix nil
| a_suffix__cons : forall a b Ξ,
    a_suffix Ξ ->
    a_suffix_binding b ->
    a_suffix ((a ~ b) ++ Ξ).

Inductive a_mono_aenv : aenv -> Prop :=
| a_mono_aenv__nil : a_mono_aenv nil
| a_mono_aenv__cons : forall a b Θ,
    b <> abind_marker ->
    a_mono_aenv Θ ->
    a_mono_aenv ((a ~ b) ++ Θ)
| a_mono_aenv__marker : forall a Θ,
    a_mono_aenv Θ ->
    a_mono_aenv ((a ~ abind_marker) ++ Θ).

Inductive aenv_extends : aenv -> aenv -> Prop :=
| aenv_extends__refl : forall Θ, aenv_extends Θ Θ
| aenv_extends__suffix : forall Θ Ξ,
    a_suffix Ξ ->
    aenv_extends Θ (Ξ ++ Θ).

Inductive a_wf_aenv : aenv -> Prop :=
| a_wf_aenv__nil : a_wf_aenv nil
| a_wf_aenv__cons : forall a b Θ,
    a_wf_aenv Θ ->
    a `notin` dom Θ ->
    a_wf_aenv ((a ~ b) ++ Θ).

Inductive a_wf_ptyp : aenv -> ptyp -> Prop :=
| a_wf_ptyp__decl : forall Θ A,
    lc_ptyp A ->
    a_wf_ptyp Θ A.

Inductive a_wf_btyp : aenv -> btyp -> Prop :=
| a_wf_btyp__decl : forall Θ B,
    lc_btyp B ->
    a_wf_btyp Θ B.

Inductive a_wf_pskl : aenv -> pskl -> Prop :=
| a_wf_pskl__decl : forall Θ P,
    lc_pskl P ->
    a_wf_pskl Θ P.

Inductive a_guarded : aenv -> ptyp -> Prop :=
| a_guarded__ptyp : forall Θ A, a_wf_ptyp Θ A -> a_guarded Θ A.

Inductive a_ty_mode_compat : mode -> btyp -> Prop :=
| a_ty_mode_compat__any : forall m B, a_ty_mode_compat m B.

Inductive a_sk_mode_compat : mode -> bskl -> Prop :=
| a_sk_mode_compat__any : forall m Q, a_sk_mode_compat m Q.

Inductive a_sub_mode : Set :=
| a_sub_mode_ty : a_sub_mode
| a_sub_mode_sk : a_sub_mode.

Inductive a_non_flex_poly : aenv -> ptyp -> Prop :=
| a_non_flex_poly__ptyp : forall Θ A, a_wf_ptyp Θ A -> a_non_flex_poly Θ A.

Inductive a_non_flex : aenv -> ptyp -> Prop :=
| a_non_flex__ptyp : forall Θ A, a_wf_ptyp Θ A -> a_non_flex Θ A.

Inductive a_guess_mono : aenv -> pskl -> aenv -> ptyp -> Prop :=
| a_guess_mono__plain : forall Θ A,
    a_guess_mono Θ (ptyp_to_pskl A) nil A.

Inductive a_pre_sub : aenv -> mode -> btyp -> btyp -> btyp -> Prop :=
| a_pre_sub__refl : forall Θ m B,
    a_pre_sub Θ m B B B.

Inductive a_pre_join : aenv -> bskl -> bskl -> bskl -> Prop :=
| a_pre_join__left : forall Θ Q,
    a_pre_join Θ Q Q Q.

Inductive a_unify : aenv -> btyp -> btyp -> btyp -> aenv -> Prop :=
| a_unify__refl : forall Θ B,
    a_unify Θ B B B Θ.

Inductive a_assign : aenv -> aenv -> ptyp -> ptyp -> aenv -> Prop :=
| a_assign__refl : forall Θ A,
    a_assign Θ nil A A Θ.

Inductive a_consis : aenv -> utyp -> btyp -> aenv -> Prop :=
| a_consis__decl : forall Θ C B,
    a_consis Θ C B Θ.

Inductive a_ajoin : aenv -> bskl -> bskl -> bskl -> aenv -> Prop :=
| a_ajoin__refl : forall Θ Q,
    a_ajoin Θ Q Q Q Θ.

Inductive a_meta_subst : aenv -> ptyp -> ptyp -> Prop :=
| a_meta_subst__nil : forall A, a_meta_subst nil A A.

Inductive a_broom : a_sub_mode -> mode -> pskl -> aenv -> btyp -> btyp -> aenv -> Prop :=
| a_broom__sub : forall NM m P0 Θ B,
    a_broom NM m P0 Θ B B Θ.

Inductive a_sub : a_sub_mode -> mode -> pskl -> aenv -> btyp -> btyp -> aenv -> Prop :=
| a_sub__refl : forall NM m P0 Θ B,
    a_sub NM m P0 Θ B B Θ.

Inductive a_split : aenv -> btyp -> btyp -> btyp -> aenv -> Prop :=
| a_split__arrow : forall Θ B1 B2,
    a_split Θ (btyp_arrow B1 B2) B1 B2 Θ.

Inductive a_typing : mode -> aenv -> pskl -> exp -> btyp -> aenv -> Prop :=
| a_typing__decl : forall m Θ P0 e B,
    a_typing m Θ P0 e B Θ
with a_pat : mode -> aenv -> pskl -> exp -> bskl -> aenv -> Prop :=
| a_pat__decl : forall m Θ P0 e Q,
    a_pat m Θ P0 e Q Θ.
