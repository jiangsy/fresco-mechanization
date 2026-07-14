(** Metasubstitutions (information increase), paper app:metasubstitutions
    (fig:information-increase-and-equivalence), and the aenv↔denv bridges.

    A metasubstitution θ is a finite map from flexible variables to
    monotypes; [a_inc Θ θ Θ'] is the paper's [Θ ⊑[θ] Θ'].  The algorithms
    always produce identity metasubstitutions ι (every entry [α̂ ↦ α̂]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Metasubstitutions and their application                               *)
(* ===================================================================== *)

Definition metasubst : Set := list (atom * ptyp).

(** [paper-gap / MECH-BUG fixed]  The paper (algorithmic.tex:123) says a
    metasubstitution IS "a finite MAP θ from flexible variables in Θ to
    well-formed monotypes in Θ'" — i.e. a SIMULTANEOUS substitution.  These were
    previously encoded as a SEQUENTIAL fold
    ([msubst ((α,τ)::θ) A = msubst θ (A[τ/α])]), which is a different function:
    the fold lets a LATER entry rewrite inside an EARLIER entry's image.  E.g.
    for the (legal) [θ = α ↦ β̂, β̂ ↦ unit] the fold sends [α ↦ unit] where the
    map sends [α ↦ β̂].  The two coincide on IDENTITY metasubstitutions (each
    [α ↦ α] substitution is a no-op), which is all the algorithm ever produces —
    which is why nothing depended on the difference.  But composition [ζ ∘ θ] and
    hence COMPLETENESS need general θ, and there the fold is simply the wrong
    function.  So: recurse on the TYPE and look each free variable up. *)

Fixpoint msubst_lookup (θ : metasubst) (X : atom) : ptyp :=
  match θ with
  | nil => ptyp_var_f X
  | (Y, τ) :: θ' => if X == Y then τ else msubst_lookup θ' X
  end.

Fixpoint msubst_ptyp (θ : metasubst) (A : ptyp) : ptyp :=
  match A with
  | ptyp_unit => ptyp_unit
  | ptyp_var_b n => ptyp_var_b n
  | ptyp_var_f X => msubst_lookup θ X
  | ptyp_arrow A1 A2 => ptyp_arrow (msubst_ptyp θ A1) (msubst_ptyp θ A2)
  | ptyp_all A0 => ptyp_all (msubst_ptyp θ A0)
  end.

Fixpoint msubst_pskl (θ : metasubst) (P : pskl) : pskl :=
  match P with
  | pskl_unit => pskl_unit
  | pskl_var_b n => pskl_var_b n
  | pskl_var_f X => ptyp_to_pskl (msubst_lookup θ X)
  | pskl_arrow P1 P2 => pskl_arrow (msubst_pskl θ P1) (msubst_pskl θ P2)
  | pskl_all_syn P0 => pskl_all_syn (msubst_pskl θ P0)
  | pskl_hole => pskl_hole
  | pskl_tophole P0 => pskl_tophole (msubst_pskl θ P0)
  end.

Fixpoint msubst_btyp (θ : metasubst) (B : btyp) : btyp :=
  match B with
  | btyp_unit => btyp_unit
  | btyp_var_b n => btyp_var_b n
  | btyp_var_f X => ptyp_to_btyp_syn (msubst_lookup θ X)
  | btyp_arrow B1 B2 => btyp_arrow (msubst_btyp θ B1) (msubst_btyp θ B2)
  | btyp_all_syn B0 => btyp_all_syn (msubst_btyp θ B0)
  | btyp_all_inh B0 => btyp_all_inh (msubst_btyp θ B0)
  end.

Fixpoint msubst_bskl (θ : metasubst) (Q : bskl) : bskl :=
  match Q with
  | bskl_unit => bskl_unit
  | bskl_var_b n => bskl_var_b n
  | bskl_var_f X => pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup θ X))
  | bskl_arrow Q1 Q2 => bskl_arrow (msubst_bskl θ Q1) (msubst_bskl θ Q2)
  | bskl_all_syn Q0 => bskl_all_syn (msubst_bskl θ Q0)
  | bskl_all_inh Q0 => bskl_all_inh (msubst_bskl θ Q0)
  | bskl_hole => bskl_hole
  | bskl_tophole Q0 => bskl_tophole (msubst_bskl θ Q0)
  end.

(** Composition of metasubstitutions, [ζ ∘ θ].  A metasubstitution is a finite
    MAP (algorithmic.tex:123), so composition is pointwise on the domain:
    (ζ ∘ θ)(α) = ζ(θ(α)).  Its action law — and the side condition that law
    needs — is [msubst_ptyp_compose] in algo/prop_compose.v. *)
Definition msubst_compose (ζ θ : metasubst) : metasubst :=
  List.map (fun e => (fst e, msubst_ptyp ζ (snd e))) θ.

(** The identity metasubstitution ι maps each flexible variable to itself. *)
Definition is_id_entry (e : atom * ptyp) : Prop :=
  snd e = ptyp_var_f (fst e).

Definition is_id_msubst (θ : metasubst) : Prop :=
  Forall is_id_entry θ.

(* ===================================================================== *)
(*  Type equivalence in algorithmic contexts  [Θ ⊢ A ≡ B]                 *)
(*  (paper app:decl-in-algo-context: α-equivalence, made explicit          *)
(*  because flexible-variable definitions are retrieved from Θ).           *)
(* ===================================================================== *)

Reserved Notation "Θ ⊢ A ≡ᵗ B"
  (at level 75, A at level 74, B at level 74, no associativity).
Inductive a_tyequiv : aenv -> ptyp -> ptyp -> Prop :=
| a_tyequiv__refl : forall Θ A,
    lc_ptyp A ->
    Θ ⊢ A ≡ᵗ A
| a_tyequiv__sym : forall Θ A B,
    Θ ⊢ A ≡ᵗ B ->
    Θ ⊢ B ≡ᵗ A
| a_tyequiv__trans : forall Θ A B C,
    Θ ⊢ A ≡ᵗ B ->
    Θ ⊢ B ≡ᵗ C ->
    Θ ⊢ A ≡ᵗ C
(* retrieve a flexible variable's definition *)
| a_tyequiv__flex_def : forall Θ α τ,
    binds α (abind_flex_mono_def τ) Θ ->
    Θ ⊢ (ptyp_var_f α) ≡ᵗ τ
| a_tyequiv__arrow : forall Θ A1 A2 B1 B2,
    Θ ⊢ A1 ≡ᵗ B1 ->
    Θ ⊢ A2 ≡ᵗ B2 ->
    Θ ⊢ (ptyp_arrow A1 A2) ≡ᵗ (ptyp_arrow B1 B2)
| a_tyequiv__all : forall L Θ A B,
    (forall X, X `notin` L ->
       Θ ⊢ (open_ptyp_wrt_ptyp A (ptyp_var_f X)) ≡ᵗ
           (open_ptyp_wrt_ptyp B (ptyp_var_f X))) ->
    Θ ⊢ (ptyp_all A) ≡ᵗ (ptyp_all B)
where "Θ ⊢ A ≡ᵗ B" := (a_tyequiv Θ A B) : type_scope.

(* ===================================================================== *)
(*  Information increase  [Θ ⊑[θ] Θ']  (fig:information-increase)          *)
(* ===================================================================== *)

Reserved Notation "Θ ≤[ θ ] Θ'"
  (at level 75, θ at level 0, Θ' at level 74, no associativity).
Inductive a_inc : aenv -> metasubst -> aenv -> Prop :=
| a_inc__empty : forall Ξ,                       (* · ⊑[ι] Ξ *)
    a_suffix Ξ ->
    nil ≤[ nil ] Ξ
| a_inc__flex : forall Θ θ Θ' α τ,               (* Θ,α̂ ⊑[θ,τ/α̂] Θ' *)
    Θ ≤[ θ ] Θ' ->
    a_wf_ptyp Θ' τ ->
    mono_ptyp τ ->
    ((α ~ abind_flex_mono) ++ Θ) ≤[ (α, τ) :: θ ] Θ'
| a_inc__flex_def : forall Θ θ Θ' α τ τ',        (* Θ,α̂:=τ ⊑[θ,τ'/α̂] Θ', τ' ≡ θτ *)
    Θ ≤[ θ ] Θ' ->
    (* the paper's prose side-condition on θ (algorithmic.tex:123): every
       image is a well-formed monotype in the target *)
    a_wf_ptyp Θ' τ' ->
    mono_ptyp τ' ->
    Θ' ⊢ τ' ≡ᵗ (msubst_ptyp θ τ) ->
    ((α ~ abind_flex_mono_def τ) ++ Θ) ≤[ (α, τ') :: θ ] Θ'
| a_inc__var : forall Θ θ Θ' Ξ x A,              (* Θ,x:A ⊑[θ] Θ',x:θA,Ξ (type entry) *)
    Θ ≤[ θ ] Θ' ->
    a_suffix Ξ ->
    ((x ~ abind_var_typ A) ++ Θ) ≤[ θ ]
      (Ξ ++ (x ~ abind_var_typ (msubst_ptyp θ A)) ++ Θ')
| a_inc__var_skl : forall Θ θ Θ' Ξ x P,          (* Θ,x:P ⊑[θ] Θ',x:θP,Ξ (skeleton entry) *)
    Θ ≤[ θ ] Θ' ->
    a_suffix Ξ ->
    ((x ~ abind_var_skl P) ++ Θ) ≤[ θ ]
      (Ξ ++ (x ~ abind_var_skl (msubst_pskl θ P)) ++ Θ')
| a_inc__tvar : forall Θ θ Θ' Ξ α,               (* Θ,α ⊑[θ] Θ',α,Ξ *)
    Θ ≤[ θ ] Θ' ->
    a_suffix Ξ ->
    ((α ~ abind_tvar) ++ Θ) ≤[ θ ] (Ξ ++ (α ~ abind_tvar) ++ Θ')
where "Θ ≤[ θ ] Θ'" := (a_inc Θ θ Θ') : type_scope.

(** [Θ ⊴ Θ'] (paper [⊑{Θ}{Θ'}], identity-metasubstitution shorthand).

    Besides an identity witness for the figure's rules, this carries the
    paper's PROSE characterization of identity metasubstitutions
    (algorithmic.tex:135): "all entries of flexible variables in Θ are
    preserved in Θ'" — in particular a definition [α̂:=τ], once made, is
    never rewritten (the algorithm only adds definitions).  This component
    is what makes the FlexL/FlexR lookup rules stable under [⊴]. *)
Definition a_isub (Θ Θ' : aenv) : Prop :=
  (exists θ, is_id_msubst θ /\ Θ ≤[ θ ] Θ') /\
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
               binds α (abind_flex_mono_def τ) Θ').

Notation "Θ ⊴ Θ'" := (a_isub Θ Θ')
  (at level 75, no associativity) : type_scope.

(** Equivalence of metasubstitutions [θ₁ ≡ θ₂ : Θ ⇒ Θ']
    (fig:information-increase-and-equivalence, second box). *)
Inductive a_inc_equiv : aenv -> metasubst -> metasubst -> aenv -> Prop :=
| a_inc_equiv__empty : forall Ξ,
    a_suffix Ξ ->
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
| a_inc_equiv__var_skl : forall Θ θ1 θ2 Θ' Ξ x P,
    a_inc_equiv Θ θ1 θ2 Θ' ->
    a_suffix Ξ ->
    a_inc_equiv ((x ~ abind_var_skl P) ++ Θ) θ1 θ2
                (Ξ ++ (x ~ abind_var_skl (msubst_pskl θ1 P)) ++ Θ')
| a_inc_equiv__tvar : forall Θ θ1 θ2 Θ' Ξ α,
    a_inc_equiv Θ θ1 θ2 Θ' ->
    a_suffix Ξ ->
    a_inc_equiv ((α ~ abind_tvar) ++ Θ) θ1 θ2
                (Ξ ++ (α ~ abind_tvar) ++ Θ').
