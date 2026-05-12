(** Frost — algorithmic system definitions (Phase 3.A).

    Companion of [paper/sections/algorithmic.tex] and
    [paper/sections/full-alg-spec.tex].

    The algorithmic system introduces two new sorts of type variables:
    flex-mono [α̂] and flex-poly [α̌]. These appear as constructors
    [typ_var_flex_mono] and [typ_var_flex_poly] in the unified [typ]
    inductive (see [language.ott]).

    Algorithmic contexts [Θ : aenv] are ordered lists of [abind]
    entries: rigid type variables, term bindings, flex-mono
    declarations, flex-mono definitions, flex-poly definitions, and
    markers ⊳ (used by subtyping to scope local flex-poly variables). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.

Set Implicit Arguments.


(* ===================================================================== *)
(*  Algorithmic context bindings.                                         *)
(* ===================================================================== *)

(** From paper algorithmic.tex (page 8 of frost.pdf):

      Entries     e ::= α | x : P | α̂ | α̂ ≜ τ | α̌ ≜ P | ⊳

    - [abind_tvar]          : rigid type variable α
    - [abind_var_typ A]     : term binding x : A
    - [abind_flex_mono]     : flex-mono declaration α̂ (no definition)
    - [abind_flex_mono_def] : flex-mono definition α̂ ≜ τ
    - [abind_flex_poly_def] : flex-poly definition α̌ ≜ P (always defined)
    - [abind_marker]        : marker ⊳ used by subtyping *)

Inductive abind : Set :=
| abind_tvar          : abind
| abind_var_typ       : typ -> abind
| abind_flex_mono     : abind
| abind_flex_mono_def : typ -> abind
| abind_flex_poly_def : typ -> abind
| abind_marker        : abind.


(** Algorithmic context Θ : list (atom * abind). *)
Definition aenv : Set := list (atom * abind).


(* ===================================================================== *)
(*  Suffixes.                                                             *)
(* ===================================================================== *)

(** Paper page 8:

      Suffixes  Ξ ::= · | Ξ, α̂ | Ξ, α̂ ≜ τ | Ξ, α̌ ≜ P

    A suffix is a fragment of an algorithmic context whose entries are
    only flex-mono declarations, flex-mono definitions, or flex-poly
    definitions. Suffixes appear in the information-increase rules and
    in the [a_sub] / [a_pat] / [a_typing] judgements. *)

Inductive a_suffix_binding : abind -> Prop :=
| a_suffix_binding__flex_mono : a_suffix_binding abind_flex_mono
| a_suffix_binding__flex_mono_def : forall τ,
    a_suffix_binding (abind_flex_mono_def τ)
| a_suffix_binding__flex_poly_def : forall P,
    a_suffix_binding (abind_flex_poly_def P).

Inductive a_suffix : aenv -> Prop :=
| a_suffix__nil  : a_suffix nil
| a_suffix__cons : forall a b Ξ,
    a_suffix Ξ ->
    a_suffix_binding b ->
    a_suffix ((a ~ b) ++ Ξ).


(* ===================================================================== *)
(*  Monomorphic contexts.                                                 *)
(* ===================================================================== *)

(** Paper page 9: [mono Θ] iff [Θ] contains no flex-poly entries. *)
Inductive a_mono_aenv : aenv -> Prop :=
| a_mono_aenv__nil : a_mono_aenv nil
| a_mono_aenv__tvar : forall a Θ,
    a_mono_aenv Θ -> a_mono_aenv ((a ~ abind_tvar) ++ Θ)
| a_mono_aenv__var_typ : forall a A Θ,
    a_mono_aenv Θ -> a_mono_aenv ((a ~ abind_var_typ A) ++ Θ)
| a_mono_aenv__flex_mono : forall a Θ,
    a_mono_aenv Θ -> a_mono_aenv ((a ~ abind_flex_mono) ++ Θ)
| a_mono_aenv__flex_mono_def : forall a τ Θ,
    a_mono_aenv Θ -> a_mono_aenv ((a ~ abind_flex_mono_def τ) ++ Θ)
| a_mono_aenv__marker : forall a Θ,
    a_mono_aenv Θ -> a_mono_aenv ((a ~ abind_marker) ++ Θ).
