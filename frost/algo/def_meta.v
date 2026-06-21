(** Metasubstitutions (information increase) and the projection from
    algorithmic to declarative contexts.

    This file provides the meta-level infrastructure the paper's
    algorithmic metatheory is phrased over (paper [algorithmic.tex],
    [fig:information-increase], following Gundry et al. 2013):

    - a [metasubst] θ — a finite map from flexible variables to monotypes;
    - application of θ to the type / skeleton sorts;
    - the information-increase relation [a_inc Θ θ Θ'] (written
      [Θ ≤[θ] Θ'] in the paper);
    - its identity specialisation [a_isub Θ Θ'] ([Θ ≤ Θ'] in the paper)
      and equivalence of metasubstitutions;
    - the projection [aenv_to_denv : aenv -> denv] that interprets a
      (solved) algorithmic context as a declarative context, so the
      declarative judgments can be applied to algorithmic contexts as the
      paper does when it writes [Θ ⊢ J].

    The projection replaces the old, far-too-loose [a_transfers] relation
    (which related *any* [Θ] to *any* [Γ]); per [PROGRESS.md] it is a
    deterministic projection, NOT a worklist-style transfer search. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.notations.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Metasubstitutions θ : finite maps from flexible variables to          *)
(*  monotypes.                                                            *)
(* ===================================================================== *)

Definition metasubst : Set := list (atom * ptyp).

(* Application of θ to each sort.  Flexible variables share the (locally
   nameless) type-variable namespace, so we substitute the monotype —
   coerced to the target sort — for each flex variable in turn. *)
Fixpoint msubst_ptyp (θ : metasubst) (A : ptyp) : ptyp :=
  match θ with
  | nil => A
  | (α, τ) :: θ' => msubst_ptyp θ' (subst_ptyp_in_ptyp τ α A)
  end.

Fixpoint msubst_pskl (θ : metasubst) (P : pskl) : pskl :=
  match θ with
  | nil => P
  | (α, τ) :: θ' => msubst_pskl θ' (subst_pskl_in_pskl (ptyp_to_pskl τ) α P)
  end.

Fixpoint msubst_btyp (θ : metasubst) (B : btyp) : btyp :=
  match θ with
  | nil => B
  | (α, τ) :: θ' => msubst_btyp θ' (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B)
  end.

Fixpoint msubst_bskl (θ : metasubst) (Q : bskl) : bskl :=
  match θ with
  | nil => Q
  | (α, τ) :: θ' =>
      msubst_bskl θ' (subst_bskl_in_bskl (pskl_to_bskl_syn (ptyp_to_pskl τ)) α Q)
  end.

(* An identity entry maps a flexible variable to itself; the identity
   metasubstitution ι has only identity entries (paper [ι], §"information
   increase").  Still-unsolved flexible variables are *not* guessed. *)
Definition is_id_entry (e : atom * ptyp) : Prop :=
  snd e = ptyp_var_f (fst e).

Definition is_id_msubst (θ : metasubst) : Prop :=
  Forall is_id_entry θ.

(* Type equivalence under an algorithmic context, [Θ ⊢ τ ≡ τ'] in the
   paper.  Reflexive — definitional equality up to solved flexible
   variables; the algorithms always produce identity metasubstitutions, so
   plain syntactic equality coincides on the cases needed.  FINDING F8: the
   paper uses [\tyequiv] only in premises and never defines it formally
   (treated as α-equivalence + solved-flex equality).  Kept reflexive as our
   documented reading pending a paper definition. *)
Reserved Notation "Θ ⊢ A ≡ᵗ B"
  (at level 75, A at level 74, B at level 74, no associativity).
Inductive a_tyequiv : aenv -> ptyp -> ptyp -> Prop :=
| a_tyequiv__refl : forall Θ A, Θ ⊢ A ≡ᵗ A
where "Θ ⊢ A ≡ᵗ B" := (a_tyequiv Θ A B) : type_scope.

(* ===================================================================== *)
(*  Information increase  [Θ ≤[θ] Θ']  (paper fig:information-increase).   *)
(* ===================================================================== *)

Reserved Notation "Θ ≤[ θ ] Θ'"
  (at level 75, θ at level 0, Θ' at level 74, no associativity).
Inductive a_inc : aenv -> metasubst -> aenv -> Prop :=
(* [· ≤[ι] Ξ] : the empty source increases to any context. *)
| a_inc__empty : forall Ξ,
    nil ≤[ nil ] Ξ
(* [Θ,α̂ ≤[θ,τ/α̂] Θ'] : solve a declared flexible variable with a fresh
   monotype τ well-formed in the target. *)
| a_inc__flex : forall Θ θ Θ' α τ,
    Θ ≤[ θ ] Θ' ->
    a_wf_ptyp Θ' τ ->
    mono_ptyp τ ->
    ((α ~ abind_flex_mono) ++ Θ) ≤[ (α, τ) :: θ ] Θ'
(* [Θ,α̂:=τ ≤[θ,τ'/α̂] Θ'] : a defined flexible variable, with τ' ≡ θτ. *)
| a_inc__flex_def : forall Θ θ Θ' α τ τ',
    Θ ≤[ θ ] Θ' ->
    Θ' ⊢ τ' ≡ᵗ (msubst_ptyp θ τ) ->
    ((α ~ abind_flex_mono_def τ) ++ Θ) ≤[ (α, τ') :: θ ] Θ'
(* [Θ,x:P ≤[θ] Θ',x:θP,Ξ] : a term variable is carried over (its type
   metasubstituted), possibly followed by a fresh suffix Ξ. *)
| a_inc__var : forall Θ θ Θ' Ξ x A,
    Θ ≤[ θ ] Θ' ->
    a_suffix Ξ ->
    ((x ~ abind_var_typ A) ++ Θ) ≤[ θ ]
      (Ξ ++ (x ~ abind_var_typ (msubst_ptyp θ A)) ++ Θ')
(* [Θ,α ≤[θ] Θ',α,Ξ] : a rigid type variable is carried over. *)
| a_inc__tvar : forall Θ θ Θ' Ξ α,
    Θ ≤[ θ ] Θ' ->
    a_suffix Ξ ->
    ((α ~ abind_tvar) ++ Θ) ≤[ θ ] (Ξ ++ (α ~ abind_tvar) ++ Θ')
where "Θ ≤[ θ ] Θ'" := (a_inc Θ θ Θ') : type_scope.

(* [Θ ≤ Θ'] (paper [\inc{Θ}{Θ'}]): information increase via *some*
   metasubstitution.  Conclusions of the algorithms are always identity
   metasubstitutions; we keep the witness existential here and recover
   identity through [is_id_msubst] where needed. *)
Definition a_isub (Θ Θ' : aenv) : Prop :=
  exists θ, Θ ≤[ θ ] Θ'.

(* [Θ ⊴ Θ'] : information increase via some metasubstitution
   (paper's identity-metasubstitution shorthand [\inc{Θ}{Θ'}]). *)
Notation "Θ ⊴ Θ'" := (a_isub Θ Θ')
  (at level 75, no associativity) : type_scope.

(* Equivalence of metasubstitutions [Θ ⊢ θ₁ ≡ θ₂ : Θ → Θ']
   (paper fig:information-increase, second box). *)
Inductive a_inc_equiv : aenv -> metasubst -> metasubst -> aenv -> Prop :=
| a_inc_equiv__empty : forall Ξ,
    a_inc_equiv nil nil nil Ξ
| a_inc_equiv__flex : forall Θ θ1 θ2 Θ' α τ1 τ2,
    a_inc_equiv Θ θ1 θ2 Θ' ->
    Θ' ⊢ τ1 ≡ᵗ τ2 ->
    a_inc_equiv ((α ~ abind_flex_mono) ++ Θ) ((α, τ1) :: θ1) ((α, τ2) :: θ2) Θ'
| a_inc_equiv__flex_def : forall Θ θ1 θ2 Θ' α τ τ1 τ2,
    a_inc_equiv Θ θ1 θ2 Θ' ->
    Θ' ⊢ τ1 ≡ᵗ τ2 ->
    Θ' ⊢ τ1 ≡ᵗ (msubst_ptyp θ1 τ) ->
    a_inc_equiv ((α ~ abind_flex_mono_def τ) ++ Θ) ((α, τ1) :: θ1) ((α, τ2) :: θ2) Θ'
| a_inc_equiv__var : forall Θ θ1 θ2 Θ' Ξ x A,
    a_inc_equiv Θ θ1 θ2 Θ' ->
    a_suffix Ξ ->
    a_inc_equiv ((x ~ abind_var_typ A) ++ Θ) θ1 θ2
                (Ξ ++ (x ~ abind_var_typ (msubst_ptyp θ1 A)) ++ Θ')
| a_inc_equiv__tvar : forall Θ θ1 θ2 Θ' Ξ α,
    a_inc_equiv Θ θ1 θ2 Θ' ->
    a_suffix Ξ ->
    a_inc_equiv ((α ~ abind_tvar) ++ Θ) θ1 θ2
                (Ξ ++ (α ~ abind_tvar) ++ Θ').

(* ===================================================================== *)
(*  Projection of an algorithmic context to a declarative one.            *)
(*                                                                       *)
(*  Deterministic structural projection (replaces the old [a_transfers]   *)
(*  relation).  Term variables [x:A] project to [dbind_typ A]; rigid and  *)
(*  flexible type variables project to [dbind_tvar]; poly-defined flex    *)
(*  variables project to their skeleton; markers are dropped.            *)
(*                                                                       *)
(*  NB (scaffolding): skeleton inference reads term variables as          *)
(*  [dbind_skl] (see [d_pat__var]); a faithful treatment would need a     *)
(*  second, skeleton-flavoured projection.  Deferred — flagged here. *)
(* ===================================================================== *)

Fixpoint aenv_to_denv (Θ : aenv) : list (atom * dbind) :=
  match Θ with
  | nil => nil
  | (x, abind_var_typ A) :: Θ' => (x ~ dbind_typ A) ++ aenv_to_denv Θ'
  | (x, abind_var_skl P) :: Θ' => (x ~ dbind_skl P) ++ aenv_to_denv Θ'
  | (α, abind_tvar) :: Θ' => (α ~ dbind_tvar) ++ aenv_to_denv Θ'
  | (α, abind_flex_mono) :: Θ' => (α ~ dbind_tvar) ++ aenv_to_denv Θ'
  | (α, abind_flex_mono_def _) :: Θ' => (α ~ dbind_tvar) ++ aenv_to_denv Θ'
  | (α, abind_flex_poly_def P) :: Θ' => (α ~ dbind_skl P) ++ aenv_to_denv Θ'
  | (_, abind_marker) :: Θ' => aenv_to_denv Θ'
  end.

(* [⌊ Θ ⌋] : the declarative context a solution is checked against. *)
Definition denv_of (Θ : aenv) : list (atom * dbind) := aenv_to_denv Θ.

Notation "⌊ Θ ⌋" := (denv_of Θ)
  (at level 0, Θ at level 99) : type_scope.
