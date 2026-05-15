(** Frost — algorithmic system definitions (Phase 3.A).

    Companion of [paper/sections/algorithmic.tex] and
    [paper/sections/full-alg-spec.tex].

    The algorithmic system has two new sorts of type variables:
    flex-mono [α̂] and flex-poly [α̌]. These are NOT distinct [typ]
    constructors — a flex variable is an ordinary [typ_var_f X], and
    whether [X] is rigid / flex-mono / flex-poly is read off its
    binding in the algorithmic context [Θ] (see [language.ott]).
    Consequently every rule that distinguishes flex-from-rigid carries
    an explicit [binds X abind_* Θ] premise, and the purely-syntactic
    side judgements ([a_non_flex], [a_non_flex_poly], [a_guess_mono],
    [a_pre_sub], [a_pre_join]) now thread [Θ] so they can do the
    lookup.

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
    a_wf_typ Θ (typ_var_f X)
| a_wf_typ__flex_mono_def : forall Θ X τ,
    binds X (abind_flex_mono_def τ) Θ ->
    a_wf_typ Θ (typ_var_f X)
| a_wf_typ__flex_poly : forall Θ X P,
    binds X (abind_flex_poly_def P) Θ ->
    a_wf_typ Θ (typ_var_f X).

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
    binds X abind_tvar Θ ->
    a_guarded Θ (typ_var_f X)
| a_guarded__arrow : forall Θ A B,
    a_guarded Θ (typ_arrow A B)
| a_guarded__flex_mono_decl : forall Θ X,
    binds X abind_flex_mono Θ ->
    a_guarded Θ (typ_var_f X)
| a_guarded__flex_mono_def : forall Θ X τ,
    binds X (abind_flex_mono_def τ) Θ ->
    a_guarded Θ τ ->
    a_guarded Θ (typ_var_f X)
| a_guarded__flex_poly_def : forall Θ X P,
    binds X (abind_flex_poly_def P) Θ ->
    a_guarded Θ P ->
    a_guarded Θ (typ_var_f X).

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

(** "Non-flex-poly" side condition. [Θ]-threaded: a [typ_var_f X] is
    non-flex-poly iff [X] is rigid or flex-mono (declared or defined)
    in [Θ] — i.e. not bound as [abind_flex_poly_def]. *)
Inductive a_non_flex_poly : aenv -> typ -> Prop :=
| a_non_flex_poly__unit  : forall Θ, a_non_flex_poly Θ typ_unit
| a_non_flex_poly__var_rigid : forall Θ X,
    binds X abind_tvar Θ -> a_non_flex_poly Θ (typ_var_f X)
| a_non_flex_poly__flex_mono : forall Θ X,
    binds X abind_flex_mono Θ -> a_non_flex_poly Θ (typ_var_f X)
| a_non_flex_poly__flex_mono_def : forall Θ X τ,
    binds X (abind_flex_mono_def τ) Θ -> a_non_flex_poly Θ (typ_var_f X)
| a_non_flex_poly__arrow : forall Θ A B, a_non_flex_poly Θ (typ_arrow A B)
| a_non_flex_poly__all_col : forall Θ c A, a_non_flex_poly Θ (typ_all_col c A)
| a_non_flex_poly__all_etag : forall Θ ε A, a_non_flex_poly Θ (typ_all_etag ε A)
| a_non_flex_poly__all_plain : forall Θ A, a_non_flex_poly Θ (typ_all_plain A)
| a_non_flex_poly__hole : forall Θ, a_non_flex_poly Θ typ_hole
| a_non_flex_poly__tophole : forall Θ A, a_non_flex_poly Θ (typ_tophole A).

(** "Non-flex" side condition (paper ulab{FlexL}/{FlexR}).
    [Θ]-threaded: a [typ_var_f X] is non-flex iff [X] is rigid. *)
Inductive a_non_flex : aenv -> typ -> Prop :=
| a_non_flex__unit  : forall Θ, a_non_flex Θ typ_unit
| a_non_flex__var   : forall Θ X,
    binds X abind_tvar Θ -> a_non_flex Θ (typ_var_f X)
| a_non_flex__arrow : forall Θ A B, a_non_flex Θ (typ_arrow A B)
| a_non_flex__all_col : forall Θ c A, a_non_flex Θ (typ_all_col c A)
| a_non_flex__all_etag : forall Θ ε A, a_non_flex Θ (typ_all_etag ε A)
| a_non_flex__all_plain : forall Θ A, a_non_flex Θ (typ_all_plain A)
| a_non_flex__hole : forall Θ, a_non_flex Θ typ_hole
| a_non_flex__tophole : forall Θ A, a_non_flex Θ (typ_tophole A).


(* ===================================================================== *)
(*  Auxiliary meta-functions: guessMono and meta_subst.                   *)
(* ===================================================================== *)

(** [a_guess_mono P Ξ A] — paper's [guessMono(P) = (ᾱ̂; A)] (page 21).
    Encoded as a 3-ary inductive: input skeleton P, output suffix Ξ
    (the freshly-introduced flex-mono declarations), and output type A.
    The suffix consists only of [abind_flex_mono] entries. *)
Inductive a_guess_mono : aenv -> typ -> aenv -> typ -> Prop :=
| a_guess_mono__hole : forall Θ α,
    a_guess_mono Θ typ_hole
      ((α ~ abind_flex_mono) ++ nil)
      (typ_var_f α)
| a_guess_mono__tophole : forall Θ P Ξ A,
    a_guess_mono Θ P Ξ A ->
    a_guess_mono Θ (typ_tophole P) Ξ A
(** [__var] covers rigid AND flex-mono variables — [guessMono] is the
    identity on both — guarded by [a_non_flex_poly] so flex-poly
    variables are (correctly) excluded. *)
| a_guess_mono__var : forall Θ X,
    a_non_flex_poly Θ (typ_var_f X) ->
    a_guess_mono Θ (typ_var_f X) nil (typ_var_f X)
| a_guess_mono__unit : forall Θ,
    a_guess_mono Θ typ_unit nil typ_unit
| a_guess_mono__all_col : forall Θ c P Ξ A,
    a_guess_mono Θ P Ξ A ->
    a_guess_mono Θ (typ_all_col c P) Ξ (typ_all_col c A)
| a_guess_mono__all_plain : forall Θ P Ξ A,
    a_guess_mono Θ P Ξ A ->
    a_guess_mono Θ (typ_all_plain P) Ξ (typ_all_plain A)
| a_guess_mono__arrow : forall Θ P Q Ξ1 Ξ2 A B,
    a_guess_mono Θ P Ξ1 A ->
    a_guess_mono Θ Q Ξ2 B ->
    a_guess_mono Θ (typ_arrow P Q) (Ξ1 ++ Ξ2) (typ_arrow A B).

(** [a_guess_mono_suffix Ξ Ξ_decl Ξ'] — extension to suffixes (paper
    page 21).  Takes an input suffix Ξ, produces the new declarations
    Ξ_decl and the rewritten suffix Ξ'. *)
Inductive a_guess_mono_suffix : aenv -> aenv -> aenv -> aenv -> Prop :=
| a_guess_mono_suffix__nil : forall Θ,
    a_guess_mono_suffix Θ nil nil nil
| a_guess_mono_suffix__flex_mono : forall Θ a Ξ Ξ' Ξ_decl,
    a_guess_mono_suffix Θ Ξ Ξ_decl Ξ' ->
    a_guess_mono_suffix Θ ((a ~ abind_flex_mono) ++ Ξ)
                        (Ξ_decl ++ (a ~ abind_flex_mono) ++ nil)
                        (Ξ' ++ (a ~ abind_flex_mono) ++ nil)
| a_guess_mono_suffix__flex_mono_def : forall Θ a τ Ξ Ξ' Ξ_decl,
    a_guess_mono_suffix Θ Ξ Ξ_decl Ξ' ->
    a_guess_mono_suffix Θ ((a ~ abind_flex_mono_def τ) ++ Ξ)
                        Ξ_decl
                        (Ξ' ++ (a ~ abind_flex_mono_def τ) ++ nil)
| a_guess_mono_suffix__flex_poly_def : forall Θ a P P' Ξ Ξ' Ξ_decl Ξ_decl',
    a_guess_mono_suffix Θ Ξ Ξ_decl Ξ' ->
    a_guess_mono (Ξ ++ Θ) P Ξ_decl' P' ->
    a_guess_mono_suffix Θ ((a ~ abind_flex_poly_def P) ++ Ξ)
                        (Ξ_decl ++ Ξ_decl')
                        (Ξ' ++ (a ~ abind_flex_poly_def P') ++ nil).


(* ===================================================================== *)
(*  Pre-subtyping and pre-join (paper Fig. "Pre-join").                   *)
(* ===================================================================== *)

(** Pre-subtyping ⊢_M P ≤̇ Q ↣ P' (paper page 26).  The output P' is
    obtained by aligning P and Q's quantifier / ghost structure. *)
Inductive a_pre_sub : aenv -> mode -> typ -> typ -> typ -> Prop :=
| a_pre_sub__unit : forall Θ m Q,
    a_pre_sub Θ m typ_unit Q typ_unit
| a_pre_sub__var : forall Θ m X Q,
    binds X abind_tvar Θ ->
    a_pre_sub Θ m (typ_var_f X) Q (typ_var_f X)
| a_pre_sub__hole_l : forall Θ m Q,
    guarded_typ Q \/ (exists c B, Q = typ_all_col c B)
                  \/ (exists ε B, Q = typ_all_etag ε B)
                  \/ (exists B, Q = typ_all_plain B)
                  \/ (exists B, Q = typ_tophole B) ->
    a_pre_sub Θ m typ_hole Q Q
| a_pre_sub__hole_r : forall Θ m P,
    guarded_typ P ->
    a_pre_sub Θ m P typ_hole P
| a_pre_sub__guarded : forall Θ m P Q P',
    guarded_typ P ->
    guarded_typ Q ->
    (m = mode_ti \/ m = mode_tc) ->
    a_pre_join Θ P Q P' ->
    a_pre_sub Θ m P Q P'
(** [__flex_mono_fn]: an unsolved flex-mono LHS in function mode is
    kept as-is. (Declared case; a solved flex-mono is unfolded by
    other rules.) *)
| a_pre_sub__flex_mono_fn : forall Θ m α Q,
    binds α abind_flex_mono Θ ->
    guarded_typ Q ->
    a_pre_sub Θ (mode_fn m) (typ_var_f α) Q (typ_var_f α)
| a_pre_sub__all_l : forall L Θ m P Q P',
    (forall X, X `notin` L ->
      a_pre_sub Θ m (open_typ_wrt_typ P (typ_var_f X)) Q P') ->
    a_pre_sub Θ m (typ_all_plain P) Q (typ_all_plain P')
| a_pre_sub__all_r : forall L Θ m P Q P',
    (forall X, X `notin` L ->
      a_pre_sub Θ m P (open_typ_wrt_typ Q (typ_var_f X)) P') ->
    a_pre_sub Θ m P (typ_all_plain Q) P'
| a_pre_sub__tophole_l : forall Θ m P Q P',
    a_pre_sub Θ m P Q P' ->
    a_pre_sub Θ m (typ_tophole P) Q P'
| a_pre_sub__tophole_r : forall Θ m P Q P',
    a_pre_sub Θ m P Q P' ->
    a_pre_sub Θ m P (typ_tophole Q) P'
| a_pre_sub__arrow : forall Θ m P1 P2 Q1 Q2 P1' P2',
    a_pre_join Θ P1 Q1 P1' ->
    a_pre_sub Θ m P2 Q2 P2' ->
    a_pre_sub Θ (mode_fn m) (typ_arrow P1 P2) (typ_arrow Q1 Q2) (typ_arrow P1' P2')

(** Pre-join ⋖̇ (paper page 26). *)
with a_pre_join : aenv -> typ -> typ -> typ -> Prop :=
| a_pre_join__unit : forall Θ Q,
    a_pre_join Θ typ_unit Q typ_unit
| a_pre_join__var : forall Θ X Q,
    binds X abind_tvar Θ ->
    a_pre_join Θ (typ_var_f X) Q (typ_var_f X)
| a_pre_join__flex_mono_l : forall Θ α Q,
    binds α abind_flex_mono Θ ->
    a_pre_join Θ (typ_var_f α) Q (typ_var_f α)
| a_pre_join__flex_mono_r : forall Θ α P,
    binds α abind_flex_mono Θ ->
    a_pre_join Θ P (typ_var_f α) P
| a_pre_join__all_both : forall L Θ P Q P',
    (forall X, X `notin` L ->
      a_pre_join Θ (open_typ_wrt_typ P (typ_var_f X))
                 (open_typ_wrt_typ Q (typ_var_f X)) P') ->
    a_pre_join Θ (typ_all_plain P) (typ_all_plain Q) (typ_all_plain P')
| a_pre_join__tophole_both : forall Θ P Q P',
    a_pre_join Θ P Q P' ->
    a_pre_join Θ (typ_tophole P) (typ_tophole Q) (typ_tophole P')
| a_pre_join__tophole_l_all : forall L Θ P Q P',
    (forall X, X `notin` L ->
      a_pre_join Θ (typ_tophole P) (open_typ_wrt_typ Q (typ_var_f X)) P') ->
    a_pre_join Θ (typ_tophole P) (typ_all_plain Q) (typ_all_plain P')
| a_pre_join__tophole_l_guarded : forall Θ P Q P',
    guarded_typ Q ->
    a_pre_join Θ P Q P' ->
    a_pre_join Θ (typ_tophole P) Q P'
| a_pre_join__all_l_tophole : forall L Θ P Q P',
    (forall X, X `notin` L ->
      a_pre_join Θ (open_typ_wrt_typ P (typ_var_f X)) (typ_tophole Q) P') ->
    a_pre_join Θ (typ_all_plain P) (typ_tophole Q) (typ_all_plain P')
| a_pre_join__guarded_r_tophole : forall Θ P Q P',
    guarded_typ P ->
    a_pre_join Θ P Q P' ->
    a_pre_join Θ P (typ_tophole Q) P'
| a_pre_join__arrow : forall Θ P1 P2 Q1 Q2 P1' P2',
    a_pre_join Θ P1 Q1 P1' ->
    a_pre_join Θ P2 Q2 P2' ->
    a_pre_join Θ (typ_arrow P1 P2) (typ_arrow Q1 Q2) (typ_arrow P1' P2').


(* ===================================================================== *)
(*  Unification (paper Fig. "Join", Fig. "Assignment").                   *)
(* ===================================================================== *)

(** [a_unify Θ S S' S'' Θ'] — paper [Θ ⊢ S ⊻ S' ↣ S''] (page 28).
    Inputs: Θ, S, S'; outputs: S'', Θ'.  Many rules pivot to
    [a_unify_var] when an operand is a flex-mono. *)
Inductive a_unify : aenv -> typ -> typ -> typ -> aenv -> Prop :=
| a_unify__unit : forall Θ,
    a_unify Θ typ_unit typ_unit typ_unit Θ
| a_unify__var : forall Θ X,
    binds X abind_tvar Θ ->
    a_unify Θ (typ_var_f X) (typ_var_f X) (typ_var_f X) Θ
| a_unify__hole_l : forall Θ P,
    a_unify Θ typ_hole P P Θ
| a_unify__hole_r : forall Θ S,
    a_unify Θ S typ_hole S Θ
| a_unify__flex_flex : forall Θ Θ' α β,
    a_unify_var Θ (typ_var_f α) β Θ' ->
    a_unify Θ (typ_var_f α) (typ_var_f β) (typ_var_f α) Θ'
| a_unify__flex_l : forall Θ Θ' α P,
    a_non_flex Θ P ->
    a_assign Θ nil (typ_var_f α) P Θ' ->
    a_unify Θ (typ_var_f α) P (typ_var_f α) Θ'
| a_unify__flex_r : forall Θ Θ' S α,
    a_non_flex Θ S ->
    a_assign Θ nil (typ_var_f α) S Θ' ->
    a_unify Θ S (typ_var_f α) (typ_var_f α) Θ'
| a_unify__arrow : forall Θ Θ1 Θ2 S1 S2 P1 P2 S1' S2',
    a_unify Θ S1 P1 S1' Θ1 ->
    a_unify Θ1 S2 P2 S2' Θ2 ->
    a_unify Θ (typ_arrow S1 S2) (typ_arrow P1 P2)
              (typ_arrow S1' S2') Θ2
| a_unify__all_plain : forall L Θ Θ' S P S',
    (forall X, X `notin` L ->
      a_unify ((X ~ abind_tvar) ++ Θ)
              (open_typ_wrt_typ S (typ_var_f X))
              (open_typ_wrt_typ P (typ_var_f X))
              (open_typ_wrt_typ S' (typ_var_f X))
              ((X ~ abind_tvar) ++ Θ')) ->
    a_unify Θ (typ_all_plain S) (typ_all_plain P) (typ_all_plain S') Θ'
| a_unify__tophole_both : forall Θ Θ' S P S',
    a_unify Θ S P S' Θ' ->
    a_unify Θ (typ_tophole S) (typ_tophole P) (typ_tophole S') Θ'
| a_unify__all_l_tophole : forall L Θ Θ' S P S',
    (forall X, X `notin` L ->
      a_unify ((X ~ abind_tvar) ++ Θ)
              (open_typ_wrt_typ S (typ_var_f X))
              (typ_tophole P)
              (open_typ_wrt_typ S' (typ_var_f X))
              ((X ~ abind_tvar) ++ Θ')) ->
    a_unify Θ (typ_all_plain S) (typ_tophole P) (typ_all_plain S') Θ'
| a_unify__guarded_l_tophole : forall Θ Θ' S P S',
    a_guarded Θ S ->
    a_non_flex Θ S ->
    a_unify Θ S P S' Θ' ->
    a_unify Θ S (typ_tophole P) S' Θ'
| a_unify__tophole_l_all : forall L Θ Θ' S P S',
    (forall X, X `notin` L ->
      a_unify ((X ~ abind_tvar) ++ Θ)
              (typ_tophole S)
              (open_typ_wrt_typ P (typ_var_f X))
              (open_typ_wrt_typ S' (typ_var_f X))
              ((X ~ abind_tvar) ++ Θ')) ->
    a_unify Θ (typ_tophole S) (typ_all_plain P) (typ_all_plain S') Θ'
| a_unify__tophole_l_guarded : forall Θ Θ' S P S',
    a_guarded Θ P ->
    a_non_flex Θ P ->
    a_unify Θ S P S' Θ' ->
    a_unify Θ (typ_tophole S) P S' Θ'

(** [a_unify_var Θ αx β̂ Θ'] — paper [Θ ⊢ αx ≐ β̂ ↣ Θ'] (page 29). *)
with a_unify_var : aenv -> typ -> atom -> aenv -> Prop :=
| a_unify_var__id : forall Θ α,
    binds α abind_flex_mono Θ ->
    a_unify_var Θ (typ_var_f α) α Θ
| a_unify_var__flex_flex_l : forall Θ α β,
    α <> β ->
    a_unify_var ((α ~ abind_flex_mono) ++ Θ)
                (typ_var_f α) β
                ((α ~ abind_flex_mono_def (typ_var_f β)) ++ Θ)
| a_unify_var__flex_flex_r : forall Θ α β,
    α <> β ->
    a_unify_var ((β ~ abind_flex_mono) ++ Θ)
                (typ_var_f α) β
                ((β ~ abind_flex_mono_def (typ_var_f α)) ++ Θ)
| a_unify_var__assign_mono : forall Θ Θ' γ τ αx β,
    a_unify Θ
            (open_typ_wrt_typ (close_typ_wrt_typ γ αx) τ)
            (open_typ_wrt_typ (close_typ_wrt_typ γ (typ_var_f β)) τ)
            (open_typ_wrt_typ (close_typ_wrt_typ γ αx) τ)  (* unused output *)
            Θ' ->
    a_unify_var ((γ ~ abind_flex_mono_def τ) ++ Θ) αx β
                ((γ ~ abind_flex_mono_def τ) ++ Θ')
| a_unify_var__assign_poly : forall Θ Θ' α P β Q,
    a_unify Θ P (typ_var_f β) Q Θ' ->
    a_unify_var ((α ~ abind_flex_poly_def P) ++ Θ)
                (typ_var_f α) β
                ((α ~ abind_flex_poly_def Q) ++ Θ')
| a_unify_var__skip_poly : forall Θ Θ' α P αx β,
    αx <> typ_var_f α ->
    a_unify_var Θ αx β Θ' ->
    a_unify_var ((α ~ abind_flex_poly_def P) ++ Θ) αx β
                ((α ~ abind_flex_poly_def P) ++ Θ')
| a_unify_var__skip_mono : forall Θ Θ' γ αx β,
    αx <> typ_var_f γ ->
    β <> γ ->
    a_unify_var Θ αx β Θ' ->
    a_unify_var ((γ ~ abind_flex_mono) ++ Θ) αx β
                ((γ ~ abind_flex_mono) ++ Θ')
| a_unify_var__skip_other_tvar : forall Θ Θ' a αx β,
    a_unify_var Θ αx β Θ' ->
    a_unify_var ((a ~ abind_tvar) ++ Θ) αx β
                ((a ~ abind_tvar) ++ Θ')
| a_unify_var__skip_other_var_typ : forall Θ Θ' a A αx β,
    a_unify_var Θ αx β Θ' ->
    a_unify_var ((a ~ abind_var_typ A) ++ Θ) αx β
                ((a ~ abind_var_typ A) ++ Θ')
| a_unify_var__skip_other_marker : forall Θ Θ' a αx β,
    a_unify_var Θ αx β Θ' ->
    a_unify_var ((a ~ abind_marker) ++ Θ) αx β
                ((a ~ abind_marker) ++ Θ')

(** [a_assign Θ Ξ αx S Θ'] — paper [Θ | Ξ ⊢ αx ≔ S ↣ Θ']
    (page 30).  The "split-context" Θ | Ξ is encoded as two aenvs.
    The first ([Θ]) is the prefix; the second ([Ξ]) is the suffix of
    additional declarations introduced during the search. *)
with a_assign : aenv -> aenv -> typ -> typ -> aenv -> Prop :=
| a_assign__solve_mono : forall Θ Ξ α S Ξ_decl τ,
    α `notin` (ftvar_in_typ S) ->
    a_guess_mono (Ξ ++ Θ) S Ξ_decl τ ->
    a_assign ((α ~ abind_flex_mono) ++ Θ) Ξ
             (typ_var_f α) S
             (Θ ++ Ξ ++ Ξ_decl ++
              (α ~ abind_flex_mono_def τ) ++ nil)
| a_assign__solve_poly : forall Θ Ξ Θ' α P Q P',
    a_unify (Θ ++ Ξ) P Q P' Θ' ->
    a_assign ((α ~ abind_flex_poly_def P) ++ Θ) Ξ
             (typ_var_f α) Q
             ((α ~ abind_flex_poly_def P') ++ Θ')
| a_assign__assign_mono : forall Θ Ξ Θ' β τ α S αx Sout,
    αx = typ_var_f α ->
    a_unify (Θ ++ Ξ)
            (open_typ_wrt_typ (close_typ_wrt_typ β S) τ)
            (open_typ_wrt_typ (close_typ_wrt_typ β αx) τ)
            Sout Θ' ->
    a_assign ((β ~ abind_flex_mono_def τ) ++ Θ) Ξ
             αx S
             ((β ~ abind_flex_mono_def τ) ++ Θ')
| a_assign__assign_mono_poly : forall Θ Ξ Θ' β τ α P Pout,
    a_unify (Θ ++ Ξ) (typ_var_f α)
            (open_typ_wrt_typ (close_typ_wrt_typ β P) τ)
            Pout Θ' ->
    a_assign ((β ~ abind_flex_mono_def τ) ++ Θ) Ξ
             (typ_var_f α) P
             ((β ~ abind_flex_mono_def τ) ++ Θ')
| a_assign__assign_poly : forall Θ Ξ Θ' β P γ_decl τ αx S Sout,
    a_non_flex (Θ ++ Ξ) S ->  (* β ∈ ftv(S) is the paper's condition *)
    a_guess_mono (Ξ ++ Θ) P γ_decl τ ->
    a_assign Θ (γ_decl ++ Ξ) αx
             (open_typ_wrt_typ (close_typ_wrt_typ β S) τ)
             Θ' ->
    Sout = open_typ_wrt_typ (close_typ_wrt_typ β S) τ ->
    a_assign ((β ~ abind_flex_poly_def P) ++ Θ) Ξ αx S
             ((β ~ abind_flex_poly_def τ) ++ Θ')
| a_assign__skip_poly : forall Θ Ξ Θ' β P αx S,
    αx <> typ_var_f β ->
    β `notin` (ftvar_in_typ S) ->
    a_assign Θ Ξ αx S Θ' ->
    a_assign ((β ~ abind_flex_poly_def P) ++ Θ) Ξ αx S
             ((β ~ abind_flex_poly_def P) ++ Θ')
| a_assign__depend_mono : forall Θ Ξ Θ' β αx S,
    αx <> typ_var_f β ->
    β `in` (ftvar_in_typ S) ->
    a_assign Θ ((β ~ abind_flex_mono) ++ Ξ) αx S Θ' ->
    a_assign ((β ~ abind_flex_mono) ++ Θ) Ξ αx S Θ'
| a_assign__skip_mono : forall Θ Ξ Θ' β αx S,
    αx <> typ_var_f β ->
    β `notin` (ftvar_in_typ S) ->
    a_assign Θ Ξ αx S Θ' ->
    a_assign ((β ~ abind_flex_mono) ++ Θ) Ξ αx S
             ((β ~ abind_flex_mono) ++ Θ')
| a_assign__skip_rigid : forall Θ Ξ Θ' β αx S,
    β `notin` (ftvar_in_typ S) ->
    a_assign Θ Ξ αx S Θ' ->
    a_assign ((β ~ abind_tvar) ++ Θ) Ξ αx S
             ((β ~ abind_tvar) ++ Θ')
| a_assign__skip_var_typ : forall Θ Ξ Θ' x P αx S,
    a_assign Θ Ξ αx S Θ' ->
    a_assign ((x ~ abind_var_typ P) ++ Θ) Ξ αx S
             ((x ~ abind_var_typ P) ++ Θ')
| a_assign__skip_marker : forall Θ Ξ Θ' a αx S,
    a_assign Θ Ξ αx S Θ' ->
    a_assign ((a ~ abind_marker) ++ Θ) Ξ αx S
             ((a ~ abind_marker) ++ Θ').


(* ===================================================================== *)
(*  Algorithmic consistency Θ₀ ⊢ T ~ A ⊣ Θ₁.                              *)
(* ===================================================================== *)

(** Algorithmic analogue of [d_consis].  Each rule of [d_consis]
    becomes an [a_consis] rule with input/output Θ; new rules cover
    flex-mono and flex-poly lookups, plus delegation to unification. *)
Inductive a_consis : aenv -> typ -> typ -> aenv -> Prop :=
| a_consis__unit : forall Θ,
    a_consis Θ typ_unit typ_unit Θ
| a_consis__var : forall Θ X,
    binds X abind_tvar Θ ->
    a_consis Θ (typ_var_f X) (typ_var_f X) Θ
| a_consis__forall_inh_tagged : forall L Θ Θ' ε T A,
    (forall X, X `notin` L ->
       a_consis ((X ~ abind_tvar) ++ Θ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))
         ((X ~ abind_tvar) ++ Θ')) ->
    a_consis Θ (typ_all_etag ε T) (typ_all_col colour_inh A) Θ'
| a_consis__forall_inh_untagged : forall L Θ Θ' T A,
    (forall X, X `notin` L ->
       a_consis ((X ~ abind_tvar) ++ Θ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))
         ((X ~ abind_tvar) ++ Θ')) ->
    a_consis Θ (typ_all_plain T) (typ_all_col colour_inh A) Θ'
| a_consis__forall_syn_tagged : forall L Θ Θ' ε T A,
    (forall X, X `notin` L ->
       a_consis ((X ~ abind_tvar) ++ Θ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))
         ((X ~ abind_tvar) ++ Θ')) ->
    a_consis Θ (typ_all_etag ε T) (typ_all_col colour_syn A) Θ'
| a_consis__forall_syn_untagged : forall L Θ Θ' T A,
    (forall X, X `notin` L ->
       a_consis ((X ~ abind_tvar) ++ Θ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))
         ((X ~ abind_tvar) ++ Θ')) ->
    a_consis Θ (typ_all_plain T) (typ_all_col colour_syn A) Θ'
| a_consis__arrow : forall Θ Θ1 Θ2 T1 T2 A1 A2,
    a_consis Θ T1 A1 Θ1 ->
    a_consis Θ1 T2 A2 Θ2 ->
    a_consis Θ (typ_arrow T1 T2) (typ_arrow A1 A2) Θ2
(** Flex-mono lookups (paper full-alg-spec Fig. "Consistency"). *)
| a_consis__flex_mono_def : forall Θ Θ' α τ A,
    binds α (abind_flex_mono_def τ) Θ ->
    a_consis Θ τ A Θ' ->
    a_consis Θ (typ_var_f α) A Θ'
| a_consis__flex_mono_decl : forall Θ Θ' α A,
    binds α abind_flex_mono Θ ->
    a_unify Θ (typ_var_f α) A (typ_var_f α) Θ' ->
    a_consis Θ (typ_var_f α) A Θ'
| a_consis__ghost : forall Θ A,
    a_consis Θ typ_hole A Θ
| a_consis__univ_ghost_both : forall Θ Θ' T A,
    a_consis Θ T A Θ' ->
    a_consis Θ (typ_tophole T) (typ_tophole A) Θ'
| a_consis__univ_ghost_inh : forall L Θ Θ' T A,
    (forall X, X `notin` L ->
       a_consis ((X ~ abind_tvar) ++ Θ)
         (typ_tophole T)
         (open_typ_wrt_typ A (typ_var_f X))
         ((X ~ abind_tvar) ++ Θ')) ->
    a_consis Θ (typ_tophole T) (typ_all_col colour_inh A) Θ'
| a_consis__univ_ghost_pass : forall Θ Θ' T A,
    a_consis Θ T A Θ' ->
    a_consis Θ (typ_tophole T) A Θ'.


(* ===================================================================== *)
(*  a_ajoin: Θ ⊢ S ⊕ P ↣ S' ⊣ Θ' (paper Fig. "Join", page 28).            *)
(* ===================================================================== *)

(** Paper Fig. "Join", main `\ajoin` judgement on page 28. *)
Inductive a_ajoin : aenv -> typ -> typ -> typ -> aenv -> Prop :=
| a_ajoin__ghost_l : forall Θ P,
    a_ajoin Θ typ_hole P P Θ
| a_ajoin__ghost_r : forall Θ S,
    a_ajoin Θ S typ_hole S Θ
| a_ajoin__unit : forall Θ,
    a_ajoin Θ typ_unit typ_unit typ_unit Θ
| a_ajoin__rigid : forall Θ α,
    binds α abind_tvar Θ ->
    a_ajoin Θ (typ_var_f α) (typ_var_f α) (typ_var_f α) Θ
| a_ajoin__flex : forall Θ Θ' αx β,
    a_unify_var Θ αx β Θ' ->
    a_ajoin Θ αx (typ_var_f β) αx Θ'
| a_ajoin__flex_l : forall Θ Θ' αx P,
    a_non_flex Θ P ->
    a_assign Θ nil αx P Θ' ->
    a_ajoin Θ αx P αx Θ'
| a_ajoin__flex_r : forall Θ Θ' α S,
    a_non_flex Θ S ->
    a_assign Θ nil (typ_var_f α) S Θ' ->
    a_ajoin Θ S (typ_var_f α) (typ_var_f α) Θ'.


(* ===================================================================== *)
(*  Meta-subst (substituting a suffix into a type).                       *)
(* ===================================================================== *)

(** [a_meta_subst Ξ A A'] — applies the substitution induced by a
    suffix Ξ to A.  Used by the outer [a_sub] to "apply" the suffix
    produced by [a_broom] to its output. *)
Inductive a_meta_subst : aenv -> typ -> typ -> Prop :=
| a_meta_subst__nil : forall A, a_meta_subst nil A A
| a_meta_subst__flex_mono_def : forall a τ Ξ A A',
    a_meta_subst Ξ (subst_typ_in_typ τ a A) A' ->
    a_meta_subst ((a ~ abind_flex_mono_def τ) ++ Ξ) A A'
| a_meta_subst__flex_poly_def : forall a P Ξ A A',
    a_meta_subst Ξ (subst_typ_in_typ P a A) A' ->
    a_meta_subst ((a ~ abind_flex_poly_def P) ++ Ξ) A A'
| a_meta_subst__flex_mono : forall a Ξ A A',
    a_meta_subst Ξ A A' ->
    a_meta_subst ((a ~ abind_flex_mono) ++ Ξ) A A'.


(* ===================================================================== *)
(*  Algorithmic subtyping (paper Fig. "alg-subtyping", page 24).          *)
(* ===================================================================== *)

(** Three judgements, mutually recursive:

    - [a_broom NM m P0 Θ_0 S S' Θ_1] : the inner judgement
        Θ_0 ⊢_M^{P_0} S ◁ S' ⊣ Θ_1
      (paper [\abroom]).  NM is the sub_mode (TY or SK).

    - [a_sub_flex_poly NM m P0 Θ_0 Ξ α S Θ_1] : the flex-poly side
      judgement Θ_0 | Ξ ⊢_M^{P_0} α̌ ↣ S ⊣ Θ_1 (paper bottom-right of
      Fig.  "alg-subtyping"). *)

Inductive a_broom : a_sub_mode -> mode -> typ -> aenv -> typ -> typ -> aenv -> Prop :=
| a_broom__infer : forall NM Θ S,
    a_broom NM mode_ti typ_hole Θ S S Θ
| a_broom__check : forall Θ Θ' T A,
    a_guarded Θ T ->
    a_guarded Θ A ->
    a_consis Θ T A Θ' ->
    a_broom a_sub_mode_ty mode_tc A Θ T A Θ'
| a_broom__univ_ghost_r : forall Θ S,
    a_guarded Θ S ->
    a_non_flex_poly Θ S ->
    a_broom a_sub_mode_sk mode_tc typ_hole Θ S (typ_tophole S) Θ
| a_broom__forall_r : forall L Θ Θ' T A,
    a_non_flex_poly Θ T ->
    (forall X, X `notin` L ->
      a_broom a_sub_mode_ty mode_tc A
              ((X ~ abind_tvar) ++ Θ) T
              (open_typ_wrt_typ A (typ_var_f X))
              ((X ~ abind_tvar) ++ Θ')) ->
    a_broom a_sub_mode_ty mode_tc (typ_all_col colour_inh A) Θ T
            (typ_all_col colour_inh A) Θ'
| a_broom__arg : forall NM m Θ Θ1 Θ2 S1 S2 P1 P2 S1' S2',
    a_unify Θ S1 P1 S1' Θ1 ->
    a_broom NM m P2 Θ1 S2 S2' Θ2 ->
    a_broom NM (mode_fn m) (typ_arrow P1 P2) Θ
            (typ_arrow S1 S2) (typ_arrow S1' S2') Θ2
| a_broom__forall_l : forall L NM m Θ Θ' P S S',
    m <> mode_ti ->
    (forall X, X `notin` L ->
      a_broom NM m P
              ((X ~ abind_flex_poly_def typ_hole) ++ Θ)
              (open_typ_wrt_typ S (typ_var_f X))
              S'
              Θ') ->
    a_broom NM m P Θ (typ_all_plain S) S' Θ'
| a_broom__univ_ghost_l : forall m Θ Θ' P S S',
    m <> mode_ti ->
    a_broom a_sub_mode_sk m P Θ S S' Θ' ->
    a_broom a_sub_mode_sk m P Θ (typ_tophole S) S' Θ'
| a_broom__ghost : forall m Θ P,
    m <> mode_ti ->
    a_broom a_sub_mode_sk m P Θ typ_hole P Θ
| a_broom__flex_mono : forall NM m Θ Θ' P α τ,
    a_ajoin Θ (typ_var_f α) P τ Θ' ->
    a_broom NM (mode_fn m) P Θ (typ_var_f α) τ Θ'
| a_broom__flex_poly : forall NM m Θ Θ' P α S,
    m <> mode_ti ->
    a_sub_flex_poly NM m P Θ nil α S Θ' ->
    a_broom NM m P Θ (typ_var_f α) S Θ'

(** Flex-poly side judgement: Θ₀ | Ξ ⊢ α̌ ↣ S ⊣ Θ₁ (paper page 25). *)
with a_sub_flex_poly :
    a_sub_mode -> mode -> typ -> aenv -> aenv -> atom -> typ -> aenv -> Prop :=
| a_sub_flex_poly__solve_ty : forall m Θ Ξ Θ' P α Q Q' Ξ_decl A T,
    a_pre_sub (Ξ ++ Θ) m Q P Q' ->
    a_guess_mono (Ξ ++ Θ) Q' Ξ_decl A ->
    a_broom a_sub_mode_ty m P (Θ ++ Ξ ++ Ξ_decl) A T Θ' ->
    a_sub_flex_poly a_sub_mode_ty m P
      ((α ~ abind_flex_poly_def Q) ++ Θ) Ξ α T
      ((α ~ abind_flex_poly_def A) ++ Θ')
| a_sub_flex_poly__solve_sk : forall m Θ Ξ Θ' P α Q Q' S,
    a_pre_sub (Ξ ++ Θ) m Q P Q' ->
    a_broom a_sub_mode_sk m P (Θ ++ Ξ) Q' S Θ' ->
    a_sub_flex_poly a_sub_mode_sk m P
      ((α ~ abind_flex_poly_def Q) ++ Θ) Ξ α S
      ((α ~ abind_flex_poly_def Q') ++ Θ')
| a_sub_flex_poly__assign_mono : forall NM m Θ Ξ Θ' P β τ α S,
    a_sub_flex_poly NM m
      (open_typ_wrt_typ (close_typ_wrt_typ β P) τ)
      Θ Ξ α S Θ' ->
    a_sub_flex_poly NM m P
      ((β ~ abind_flex_mono_def τ) ++ Θ) Ξ α S
      ((β ~ abind_flex_mono_def τ) ++ Θ')
| a_sub_flex_poly__depend_mono : forall NM m Θ Ξ Θ' P β α S,
    β `in` (ftvar_in_typ P) ->
    a_sub_flex_poly NM m P Θ ((β ~ abind_flex_mono) ++ Ξ) α S Θ' ->
    a_sub_flex_poly NM m P ((β ~ abind_flex_mono) ++ Θ) Ξ α S Θ'
| a_sub_flex_poly__skip_mono : forall NM m Θ Ξ Θ' P β α S,
    β `notin` (ftvar_in_typ P) ->
    a_sub_flex_poly NM m P Θ Ξ α S Θ' ->
    a_sub_flex_poly NM m P
      ((β ~ abind_flex_mono) ++ Θ) Ξ α S
      ((β ~ abind_flex_mono) ++ Θ')
| a_sub_flex_poly__skip_poly : forall NM m Θ Ξ Θ' P β Q α S,
    α <> β ->
    a_sub_flex_poly NM m P Θ Ξ α S Θ' ->
    a_sub_flex_poly NM m P
      ((β ~ abind_flex_poly_def Q) ++ Θ) Ξ α S
      ((β ~ abind_flex_poly_def Q) ++ Θ')
| a_sub_flex_poly__skip_rigid : forall NM m Θ Ξ Θ' P β α S,
    β `notin` (ftvar_in_typ P) ->
    a_sub_flex_poly NM m P Θ Ξ α S Θ' ->
    a_sub_flex_poly NM m P
      ((β ~ abind_tvar) ++ Θ) Ξ α S
      ((β ~ abind_tvar) ++ Θ').


(** Outer subtyping judgement (paper page 24).  The judgement wraps
    [a_broom] with marker / suffix bookkeeping: a fresh marker [a] is
    introduced before the inner call, then [a_broom]'s output context
    is split at that marker, the suffix [Ξ] is transformed (filled
    with flex-monos in TY mode, kept as-is in SK mode), and [a_meta_subst]
    is applied to the inner output. *)
Inductive a_sub : a_sub_mode -> mode -> typ -> aenv -> typ -> typ -> aenv -> Prop :=
| a_sub__ty : forall L m P0 Θ Θ' Ξ Ξ_decl Ξ' P S Q,
    (forall a, a `notin` L ->
      a_broom a_sub_mode_ty m P0
              ((a ~ abind_marker) ++ Θ) P S
              (Ξ ++ (a ~ abind_marker) ++ Θ')) ->
    a_guess_mono_suffix Θ' Ξ Ξ_decl Ξ' ->
    a_meta_subst Ξ' S Q ->
    a_sub a_sub_mode_ty m P0 Θ P Q (Ξ_decl ++ Θ')
| a_sub__sk : forall L m P0 Θ Θ' Ξ P S Q,
    (forall a, a `notin` L ->
      a_broom a_sub_mode_sk m P0
              ((a ~ abind_marker) ++ Θ) P S
              (Ξ ++ (a ~ abind_marker) ++ Θ')) ->
    a_meta_subst Ξ S Q ->
    a_sub a_sub_mode_sk m P0 Θ P Q Θ'.


(* ===================================================================== *)
(*  Skeleton splitting (paper Fig. "alg-type-inference", page 21).        *)
(* ===================================================================== *)

(** [a_split Θ_0 P_0 P Q Θ_1] — paper [\mov{Θ_0}{P_0 ▷ P→Q}{Θ_1}]
    (page 21).  Splits the input skeleton P_0 into an arrow shape
    P→Q, possibly introducing fresh flex-monos when P_0 is itself a
    flex-mono.

    The third paper rule unifies α̂ with β̂→γ̂ in an extended context
    (β̂ and γ̂ fresh).  We expose the freshness here via the L-cofinite
    encoding: the resulting P / Q are not the freshly-bound names but
    rather the *output* of unification on a context with two extra
    flex-monos.  Constructor takes both fresh names directly. *)
Inductive a_split : aenv -> typ -> typ -> typ -> aenv -> Prop :=
| a_split__arrow : forall Θ P Q,
    a_split Θ (typ_arrow P Q) P Q Θ
| a_split__hole : forall Θ,
    a_split Θ typ_hole typ_hole typ_hole Θ
| a_split__flex_mono : forall Θ Θ' α β γ,
    binds α abind_flex_mono Θ ->
    β <> γ ->
    β `notin` dom Θ ->
    γ `notin` dom Θ ->
    β <> α ->
    γ <> α ->
    a_unify
      ((β ~ abind_flex_mono) ++ (γ ~ abind_flex_mono) ++ Θ)
      (typ_var_f α)
      (typ_arrow (typ_var_f β) (typ_var_f γ))
      (typ_var_f α)
      Θ' ->
    a_split Θ (typ_var_f α)
              (typ_var_f β)
              (typ_var_f γ)
              Θ'.

(* ===================================================================== *)
(*  Algorithmic typing and skeleton inference.                            *)
(* ===================================================================== *)

(** Paper Fig. "alg-type-inference" (page 21) and Fig.
    "alg-skeleton-inference" (page 22).  Mutually recursive due to App.

    [a_typing m Θ_0 P_0 e A Θ_1] — paper [\atypp{Θ_0}{m}{P_0}{e}{A}{Θ_1}].
    [a_pat m Θ_0 P_0 e Q Θ_1]    — paper [\apatp{Θ_0}{m}{P_0}{e}{Q}{Θ_1}]. *)

Inductive a_typing : mode -> aenv -> typ -> exp -> typ -> aenv -> Prop :=
| a_typing__unit : forall m Θ Θ' P0 A,
    a_sub a_sub_mode_ty m P0 Θ typ_unit A Θ' ->
    a_typing m Θ P0 exp_unit A Θ'
| a_typing__var : forall m Θ Θ' P0 x A B,
    binds x (abind_var_typ A) Θ ->
    a_sub a_sub_mode_ty m P0 Θ A B Θ' ->
    a_typing m Θ P0 (exp_var_f x) B Θ'
| a_typing__anno : forall m Θ Θ1 Θ2 P0 e A B,
    a_typing mode_tc Θ A e A Θ1 ->
    a_sub a_sub_mode_ty m P0 Θ1 A B Θ2 ->
    a_typing m Θ P0 (exp_anno e A) B Θ2
| a_typing__freeze : forall Θ Θ1 Θ2 A B e,
    a_typing mode_ti Θ typ_hole e B Θ1 ->
    a_consis Θ1 B A Θ2 ->
    a_typing mode_tc Θ A (exp_freeze e) A Θ2
(** Paper's [\tilab{AbsCheck}] with a single ∀-prefix (n=1).  The
    paper's n-ary version unrolls via repeated application of
    [a_typing__forall_check] below. *)
| a_typing__abs_check : forall L Θ Θ' Ξ A B e,
    (forall x, x `notin` L ->
      a_typing mode_tc Θ B
        (open_exp_wrt_exp e (exp_var_f x)) B
        ((x ~ abind_var_typ A) ++ Ξ ++ Θ')) ->
    a_typing mode_tc Θ (typ_arrow A B) (exp_abs e) (typ_arrow A B) Θ'
(** [\tilab{Forall}]: under inherited ∀, generalise the result.  The
    n-ary [\tilab{AbsCheck}] is recovered by applying [a_typing__abs_check]
    followed by repeated applications of this rule. *)
| a_typing__forall_check : forall L Θ Θ' P0 A e,
    (forall X, X `notin` L ->
      a_typing mode_tc
        ((X ~ abind_tvar) ++ Θ) P0 e
        (open_typ_wrt_typ A (typ_var_f X))
        ((X ~ abind_tvar) ++ Θ')) ->
    a_typing mode_tc Θ P0 e (typ_all_col colour_inh A) Θ'
| a_typing__abs : forall L Θ Θ1 Θ2 Ξ Ξ_decl m P0 P Q A B e,
    m <> mode_tc ->
    a_split Θ P0 P Q Θ1 ->
    a_guess_mono Θ1 P Ξ_decl A ->
    (forall x, x `notin` L ->
      a_typing (decr_mode m)
               (Ξ_decl ++ Θ1) Q
               (open_exp_wrt_exp e (exp_var_f x))
               B
               ((x ~ abind_var_typ A) ++ Ξ ++ Θ2)) ->
    a_typing m Θ P0 (exp_abs e) (typ_arrow A B) (Ξ ++ Θ2)
(** [\tilab{AbsAnnoCheck}] with single ∀-prefix; n-ary follows by
    iterating [a_typing__forall_check]. *)
| a_typing__abs_anno_check : forall L Θ Θ1 Θ' Ξ A A' B e,
    a_consis Θ A' A Θ1 ->
    (forall x, x `notin` L ->
      a_typing mode_tc Θ1 B
        (open_exp_wrt_exp e (exp_var_f x))
        B
        ((x ~ abind_var_typ A) ++ Ξ ++ Θ')) ->
    a_typing mode_tc Θ (typ_arrow A' B) (exp_abs_anno A e)
             (typ_arrow A' B) Θ'
| a_typing__abs_anno : forall L Θ Θ1 Θ2 Ξ m P0 P Q A B e,
    m <> mode_tc ->
    a_split Θ P0 P Q Θ1 ->
    (forall x, x `notin` L ->
      a_typing (decr_mode m)
               Θ1 Q
               (open_exp_wrt_exp e (exp_var_f x))
               B
               ((x ~ abind_var_typ A) ++ Ξ ++ Θ2)) ->
    a_typing m Θ P0 (exp_abs_anno A e) (typ_arrow A B) (Ξ ++ Θ2)
| a_typing__app : forall m Θ Θ1 Θ2 Θ3 P0 e1 e2 A B P,
    a_pat mode_tc Θ typ_hole e2 P Θ1 ->
    a_typing (mode_fn m) Θ1 (typ_arrow P P0) e1 (typ_arrow A B) Θ2 ->
    a_typing mode_tc Θ2 A e2 A Θ3 ->
    a_typing m Θ P0 (exp_app e1 e2) B Θ3

with a_pat : mode -> aenv -> typ -> exp -> typ -> aenv -> Prop :=
| a_pat__unit : forall m Θ Θ' P0 Q,
    a_sub a_sub_mode_sk m P0 Θ typ_unit Q Θ' ->
    a_pat m Θ P0 exp_unit Q Θ'
| a_pat__var : forall m Θ Θ' P0 x Q P',
    binds x (abind_var_typ Q) Θ ->
    a_sub a_sub_mode_sk m P0 Θ Q P' Θ' ->
    a_pat m Θ P0 (exp_var_f x) P' Θ'
| a_pat__anno : forall m Θ Θ' P0 e A Q,
    a_sub a_sub_mode_sk m P0 Θ A Q Θ' ->
    a_pat m Θ P0 (exp_anno e A) Q Θ'
| a_pat__freeze : forall Θ Θ' e P,
    a_pat mode_ti Θ typ_hole e P Θ' ->
    a_pat mode_tc Θ typ_hole (exp_freeze e) P Θ'
| a_pat__abs_check : forall L Θ Θ' Ξ e Q,
    (forall x, x `notin` L ->
      a_pat mode_tc
        ((x ~ abind_var_typ typ_hole) ++ Θ) typ_hole
        (open_exp_wrt_exp e (exp_var_f x))
        Q
        ((x ~ abind_var_typ typ_hole) ++ Ξ ++ Θ')) ->
    a_pat mode_tc Θ typ_hole (exp_abs e)
      (typ_arrow (typ_tophole typ_hole) Q) (Ξ ++ Θ')
| a_pat__abs : forall L Θ Θ1 Θ2 Ξ m P0 P Q Q' e,
    m <> mode_tc ->
    a_split Θ P0 P Q Θ1 ->
    (forall x, x `notin` L ->
      a_pat (decr_mode m)
            Θ1 Q
            (open_exp_wrt_exp e (exp_var_f x))
            Q'
            ((x ~ abind_var_typ P) ++ Ξ ++ Θ2)) ->
    a_pat m Θ P0 (exp_abs e) (typ_arrow P Q') (Ξ ++ Θ2)
| a_pat__abs_anno_check : forall L Θ Θ' Ξ A e Q,
    (forall x, x `notin` L ->
      a_pat mode_tc
        ((x ~ abind_var_typ A) ++ Θ) typ_hole
        (open_exp_wrt_exp e (exp_var_f x))
        Q
        ((x ~ abind_var_typ A) ++ Ξ ++ Θ')) ->
    a_pat mode_tc Θ typ_hole (exp_abs_anno A e)
      (typ_arrow (typ_tophole A) Q) (Ξ ++ Θ')
| a_pat__abs_anno : forall L Θ Θ1 Θ2 Ξ m P0 P Q A B e,
    m <> mode_tc ->
    a_split Θ P0 P Q Θ1 ->
    (forall x, x `notin` L ->
      a_pat (decr_mode m)
            Θ1 Q
            (open_exp_wrt_exp e (exp_var_f x))
            B
            ((x ~ abind_var_typ A) ++ Ξ ++ Θ2)) ->
    a_pat m Θ P0 (exp_abs_anno A e) (typ_arrow A B) (Ξ ++ Θ2)
| a_pat__app : forall m Θ Θ1 Θ2 P0 e1 e2 P P' Q',
    a_pat mode_tc Θ typ_hole e2 P Θ1 ->
    a_pat (mode_fn m) Θ1 (typ_arrow P P0) e1 (typ_arrow P' Q') Θ2 ->
    a_pat m Θ P0 (exp_app e1 e2) Q' Θ2.
