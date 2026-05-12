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

(* ===================================================================== *)
(*  Information-increase relation Θ₀ ⊑ Θ₁.                                *)
(* ===================================================================== *)

(** Paper Fig. 4 ("Information increase").  We mechanise the
    *identity* metasubstitution variant, which is what the algorithm
    always produces (see paper page 9: "We sometimes directly write
    [Θ ⊑ Θ′] for an identity metasubstitution.").

    Under this variant every flex-mono variable in [Θ₀] is preserved
    in [Θ₁], but its sort may strengthen (declaration ⇒ definition,
    definition unchanged), and new flex-mono / flex-poly suffix entries
    may be inserted before each rigid / term / marker entry.

    Each constructor matches one rule of Fig. 4 (id-metasubst column).
    Note that the [⊑]-judgement uses [a_wf_typ] / [d_refine] etc. for
    its premises but does not require them to be cyclic: they are
    well-formedness side conditions on the target context. *)

Inductive aenv_extends : aenv -> aenv -> Prop :=

(** Empty source: any suffix is a valid extension. *)
| aenv_extends__empty : forall Ξ,
    a_suffix Ξ ->
    aenv_extends nil Ξ

(** Flex-mono declaration: target may keep it declared (no new info)
    OR may strengthen to a definition.  Both cases handled by a single
    rule whose target entry [b'] is either [abind_flex_mono] or
    [abind_flex_mono_def τ] for some τ. *)
| aenv_extends__flex_mono_keep : forall a Θ Θ',
    aenv_extends Θ Θ' ->
    aenv_extends ((a ~ abind_flex_mono) ++ Θ)
                 ((a ~ abind_flex_mono) ++ Θ')
| aenv_extends__flex_mono_solve : forall a τ Θ Θ',
    aenv_extends Θ Θ' ->
    aenv_extends ((a ~ abind_flex_mono) ++ Θ)
                 ((a ~ abind_flex_mono_def τ) ++ Θ')

(** Flex-mono definition: preserved unchanged. *)
| aenv_extends__flex_mono_def : forall a τ Θ Θ',
    aenv_extends Θ Θ' ->
    aenv_extends ((a ~ abind_flex_mono_def τ) ++ Θ)
                 ((a ~ abind_flex_mono_def τ) ++ Θ')

(** Flex-poly definition: the assigned skeleton P may be refined to Q;
    additionally a fresh suffix Ξ may be inserted after this entry. *)
| aenv_extends__flex_poly_def : forall a P Q Ξ Θ Θ',
    aenv_extends Θ Θ' ->
    a_suffix Ξ ->
    aenv_extends ((a ~ abind_flex_poly_def P) ++ Θ)
                 (Ξ ++ (a ~ abind_flex_poly_def Q) ++ Θ')

(** Term binding x : P preserved; suffix Ξ may be inserted after it. *)
| aenv_extends__var_typ : forall a P Ξ Θ Θ',
    aenv_extends Θ Θ' ->
    a_suffix Ξ ->
    aenv_extends ((a ~ abind_var_typ P) ++ Θ)
                 (Ξ ++ (a ~ abind_var_typ P) ++ Θ')

(** Rigid type variable preserved; suffix Ξ may be inserted. *)
| aenv_extends__tvar : forall a Ξ Θ Θ',
    aenv_extends Θ Θ' ->
    a_suffix Ξ ->
    aenv_extends ((a ~ abind_tvar) ++ Θ)
                 (Ξ ++ (a ~ abind_tvar) ++ Θ')

(** Marker preserved; suffix Ξ may be inserted. *)
| aenv_extends__marker : forall a Ξ Θ Θ',
    aenv_extends Θ Θ' ->
    a_suffix Ξ ->
    aenv_extends ((a ~ abind_marker) ++ Θ)
                 (Ξ ++ (a ~ abind_marker) ++ Θ').


(* ===================================================================== *)
(*  Algorithmic well-formedness for types in aenv.                        *)
(* ===================================================================== *)

(** [a_wf_typ Θ A] — analogue of [d_wf_typ] under an algorithmic
    context.  Extends [d_wf_typ] with cases for the new flex-mono
    and flex-poly constructors, looking up their entry in [Θ]. *)
Inductive a_wf_typ : aenv -> typ -> Prop :=
| a_wf_typ__unit : forall Θ,
    a_wf_typ Θ typ_unit
| a_wf_typ__var : forall Θ X,
    binds X abind_tvar Θ ->
    a_wf_typ Θ (typ_var_f X)
| a_wf_typ__arrow : forall Θ A B,
    a_wf_typ Θ A ->
    a_wf_typ Θ B ->
    a_wf_typ Θ (typ_arrow A B)
| a_wf_typ__all_col : forall L Θ c A,
    (forall X, X `notin` L ->
       a_wf_typ ((X ~ abind_tvar) ++ Θ) (open_typ_wrt_typ A (typ_var_f X))) ->
    a_wf_typ Θ (typ_all_col c A)
| a_wf_typ__all_etag : forall L Θ ε A,
    (forall X, X `notin` L ->
       a_wf_typ ((X ~ abind_tvar) ++ Θ) (open_typ_wrt_typ A (typ_var_f X))) ->
    a_wf_typ Θ (typ_all_etag ε A)
| a_wf_typ__all_plain : forall L Θ A,
    (forall X, X `notin` L ->
       a_wf_typ ((X ~ abind_tvar) ++ Θ) (open_typ_wrt_typ A (typ_var_f X))) ->
    a_wf_typ Θ (typ_all_plain A)
| a_wf_typ__hole : forall Θ,
    a_wf_typ Θ typ_hole
| a_wf_typ__tophole : forall Θ A,
    a_wf_typ Θ A ->
    a_wf_typ Θ (typ_tophole A)
| a_wf_typ__flex_mono_decl : forall Θ X,
    binds X abind_flex_mono Θ ->
    a_wf_typ Θ (typ_var_flex_mono X)
| a_wf_typ__flex_mono_def : forall Θ X τ,
    binds X (abind_flex_mono_def τ) Θ ->
    a_wf_typ Θ (typ_var_flex_mono X)
| a_wf_typ__flex_poly : forall Θ X P,
    binds X (abind_flex_poly_def P) Θ ->
    a_wf_typ Θ (typ_var_flex_poly X).

(** [a_wf_aenv Θ] — algorithmic context well-formedness.  Paper §4.2,
    "Θ ⊢ ctx".  Each entry's well-formedness is checked against the
    *prefix* (entries on its right in the list, which represent the
    earlier part of Θ in paper order; we adopt the metalib convention
    of prepending new entries to the head). *)
Inductive a_wf_aenv : aenv -> Prop :=
| a_wf_aenv__nil : a_wf_aenv nil
| a_wf_aenv__tvar : forall a Θ,
    a_wf_aenv Θ ->
    a `notin` dom Θ ->
    a_wf_aenv ((a ~ abind_tvar) ++ Θ)
| a_wf_aenv__var_typ : forall a P Θ,
    a_wf_aenv Θ ->
    a_wf_typ Θ P ->
    a `notin` dom Θ ->
    a_wf_aenv ((a ~ abind_var_typ P) ++ Θ)
| a_wf_aenv__flex_mono : forall a Θ,
    a_wf_aenv Θ ->
    a `notin` dom Θ ->
    a_wf_aenv ((a ~ abind_flex_mono) ++ Θ)
| a_wf_aenv__flex_mono_def : forall a τ Θ,
    a_wf_aenv Θ ->
    a_wf_typ Θ τ ->
    a `notin` dom Θ ->
    a_wf_aenv ((a ~ abind_flex_mono_def τ) ++ Θ)
| a_wf_aenv__flex_poly_def : forall a P Θ,
    a_wf_aenv Θ ->
    a_wf_typ Θ P ->
    a `notin` dom Θ ->
    a_wf_aenv ((a ~ abind_flex_poly_def P) ++ Θ)
| a_wf_aenv__marker : forall a Θ,
    a_wf_aenv Θ ->
    a `notin` dom Θ ->
    a_wf_aenv ((a ~ abind_marker) ++ Θ).

(** [a_guarded Θ A] — extended "guarded" predicate of paper Fig.
    "statements-in-context".  Adds two cases for flex-mono variables:
    α̂ is guarded when its entry is [α̂ : ⬒] (undefined; vacuously
    guarded) or when its definition τ is itself guarded. *)
Inductive a_guarded : aenv -> typ -> Prop :=
| a_guarded__unit : forall Θ,
    a_guarded Θ typ_unit
| a_guarded__var : forall Θ X,
    a_guarded Θ (typ_var_f X)
| a_guarded__arrow : forall Θ A B,
    a_guarded Θ (typ_arrow A B)
| a_guarded__flex_mono_decl : forall Θ X,
    binds X abind_flex_mono Θ ->
    a_guarded Θ (typ_var_flex_mono X)
| a_guarded__flex_mono_def : forall Θ X τ,
    binds X (abind_flex_mono_def τ) Θ ->
    a_guarded Θ τ ->
    a_guarded Θ (typ_var_flex_mono X)
| a_guarded__flex_poly_def : forall Θ X P,
    binds X (abind_flex_poly_def P) Θ ->
    a_guarded Θ P ->
    a_guarded Θ (typ_var_flex_poly X).

(** Modes vs. type/skeleton inputs (paper page 17 and 20).  Extends
    [mode_typ_compat] / [mode_skel_compat] to algorithmic syntax.  In
    [SK]-mode, [Hole] is required at both [TI] and [TC] (paper page
    20). *)
Inductive a_ty_mode_compat : mode -> typ -> Prop :=
| a_ty_mode_compat__ti : a_ty_mode_compat mode_ti typ_hole
| a_ty_mode_compat__tc : forall A, a_ty_mode_compat mode_tc A
| a_ty_mode_compat__fn : forall m P Q,
    a_ty_mode_compat m Q ->
    a_ty_mode_compat (mode_fn m) (typ_arrow P Q).

Inductive a_sk_mode_compat : mode -> typ -> Prop :=
| a_sk_mode_compat__ti : a_sk_mode_compat mode_ti typ_hole
| a_sk_mode_compat__tc : a_sk_mode_compat mode_tc typ_hole
| a_sk_mode_compat__fn : forall m P Q,
    a_sk_mode_compat m Q ->
    a_sk_mode_compat (mode_fn m) (typ_arrow P Q).

(** A mode-annotation distinguishing typing ([TY]) from skeleton
    inference ([SK]) judgement contexts.  Used by [a_sub] to choose
    between [fillMono] (subst suffix with flex-monos) and identity
    suffix substitution.  See paper page 24 Fig. 6. *)
Inductive a_sub_mode : Set :=
| a_sub_mode_ty : a_sub_mode
| a_sub_mode_sk : a_sub_mode.

(** "Non-flex-poly" side condition. *)
Inductive a_non_flex_poly : typ -> Prop :=
| a_non_flex_poly__unit  : a_non_flex_poly typ_unit
| a_non_flex_poly__var   : forall X, a_non_flex_poly (typ_var_f X)
| a_non_flex_poly__arrow : forall A B, a_non_flex_poly (typ_arrow A B)
| a_non_flex_poly__all_col : forall c A, a_non_flex_poly (typ_all_col c A)
| a_non_flex_poly__all_etag : forall ε A, a_non_flex_poly (typ_all_etag ε A)
| a_non_flex_poly__all_plain : forall A, a_non_flex_poly (typ_all_plain A)
| a_non_flex_poly__hole : a_non_flex_poly typ_hole
| a_non_flex_poly__tophole : forall A, a_non_flex_poly (typ_tophole A)
| a_non_flex_poly__flex_mono : forall X, a_non_flex_poly (typ_var_flex_mono X).

(** "Non-flex" side condition (paper ulab{FlexL}/{FlexR}). *)
Inductive a_non_flex : typ -> Prop :=
| a_non_flex__unit  : a_non_flex typ_unit
| a_non_flex__var   : forall X, a_non_flex (typ_var_f X)
| a_non_flex__arrow : forall A B, a_non_flex (typ_arrow A B)
| a_non_flex__all_col : forall c A, a_non_flex (typ_all_col c A)
| a_non_flex__all_etag : forall ε A, a_non_flex (typ_all_etag ε A)
| a_non_flex__all_plain : forall A, a_non_flex (typ_all_plain A)
| a_non_flex__hole : a_non_flex typ_hole
| a_non_flex__tophole : forall A, a_non_flex (typ_tophole A).
