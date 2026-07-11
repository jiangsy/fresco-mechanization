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
