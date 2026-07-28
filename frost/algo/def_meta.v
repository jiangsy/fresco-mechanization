(** Metasubstitutions (information increase), paper app:metasubstitutions
    (fig:information-increase-and-equivalence), and the aenv↔denv bridges.

    A metasubstitution ρ is a finite map from flexible variables to
    monotypes; [a_inc Θ ρ Θ'] is the paper's [Θ ⊑[θ] Θ'].  The algorithms
    always produce identity metasubstitutions ι (every entry [α̂ ↦ α̂]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_decl_algo.   (* [ptyp_to_uskl_syn] *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  Metasubstitutions and their application                               *)
(* ===================================================================== *)

Definition metasubst : Set := list (atom * ptyp).

(** [paper-gap / MECH-BUG fixed]  The paper (algorithmic.tex:123) says a
    metasubstitution IS "a finite MAP ρ from flexible variables in Θ to
    well-formed monotypes in Θ'" — i.e. a SIMULTANEOUS substitution.  These were
    previously encoded as a SEQUENTIAL fold
    ([msubst ((α,τ)::ρ) A = msubst ρ' (A[τ/α])]), which is a different function:
    the fold lets a LATER entry rewrite inside an EARLIER entry's image.  E.g.
    for the (legal) [θ = α ↦ β̂, β̂ ↦ unit] the fold sends [α ↦ unit] where the
    map sends [α ↦ β̂].  The two coincide on IDENTITY metasubstitutions (each
    [α ↦ α] substitution is a no-op), which is all the algorithm ever produces —
    which is why nothing depended on the difference.  But composition [ζ ∘ θ] and
    hence COMPLETENESS need general θ, and there the fold is simply the wrong
    function.  So: recurse on the TYPE and look each free variable up. *)

Fixpoint msubst_lookup (ρ : metasubst) (X : atom) : ptyp :=
  match ρ with
  | nil => ptyp_var_f X
  | (Y, τ) :: ρ' => if X == Y then τ else msubst_lookup ρ' X
  end.

Fixpoint msubst_ptyp (ρ : metasubst) (A : ptyp) : ptyp :=
  match A with
  | ptyp_unit => ptyp_unit
  | ptyp_var_b n => ptyp_var_b n
  | ptyp_var_f X => msubst_lookup ρ X
  | ptyp_arrow A1 A2 => ptyp_arrow (msubst_ptyp ρ A1) (msubst_ptyp ρ A2)
  | ptyp_all A0 => ptyp_all (msubst_ptyp ρ A0)
  end.

Fixpoint msubst_pskl (ρ : metasubst) (P : pskl) : pskl :=
  match P with
  | pskl_unit => pskl_unit
  | pskl_var_b n => pskl_var_b n
  | pskl_var_f X => ptyp_to_pskl (msubst_lookup ρ X)
  | pskl_arrow P1 P2 => pskl_arrow (msubst_pskl ρ P1) (msubst_pskl ρ P2)
  | pskl_all_syn P0 => pskl_all_syn (msubst_pskl ρ P0)
  | pskl_hole => pskl_hole
  | pskl_tophole P0 => pskl_tophole (msubst_pskl ρ P0)
  end.

(** [θ S] on UNRESOLVED skeletons — the sort the decorated consistency's
    subject lives in.  NB distinct from [prop_decorate_sub.msubst_uskl], which
    is the PAPER's ρ (a map from rigid variables to decorated SKELETONS); this
    one applies a METASUBSTITUTION (flexibles ↦ monotypes), hence the [_syn]
    suffix: an image is embedded with the synthesised painting.  A flexible variable's image is a monotype, so it is
    embedded with the synthesised painting; every other constructor (including
    the plain and dotted ghosts) is structural.  This is what lets a subject be
    written as the paper writes it, [(θS)[ψa/α]], instead of baking θ into it. *)
Fixpoint msubst_uskl_syn (ρ : metasubst) (S : uskl) : uskl :=
  match S with
  | uskl_unit => uskl_unit
  | uskl_var_b n => uskl_var_b n
  | uskl_var_f X => ptyp_to_uskl_syn (msubst_lookup ρ X)
  | uskl_arrow S1 S2 => uskl_arrow (msubst_uskl_syn ρ S1) (msubst_uskl_syn ρ S2)
  | uskl_all_syn S0 => uskl_all_syn (msubst_uskl_syn ρ S0)
  | uskl_all_etag ε S0 => uskl_all_etag ε (msubst_uskl_syn ρ S0)
  | uskl_hole => uskl_hole
  | uskl_tophole S0 => uskl_tophole (msubst_uskl_syn ρ S0)
  | uskl_holeg => uskl_holeg
  | uskl_topholeg S0 => uskl_topholeg (msubst_uskl_syn ρ S0)
  end.

Fixpoint msubst_btyp (ρ : metasubst) (B : btyp) : btyp :=
  match B with
  | btyp_unit => btyp_unit
  | btyp_var_b n => btyp_var_b n
  | btyp_var_f X => ptyp_to_btyp_syn (msubst_lookup ρ X)
  | btyp_arrow B1 B2 => btyp_arrow (msubst_btyp ρ B1) (msubst_btyp ρ B2)
  | btyp_all_syn B0 => btyp_all_syn (msubst_btyp ρ B0)
  | btyp_all_inh B0 => btyp_all_inh (msubst_btyp ρ B0)
  end.

Fixpoint msubst_bskl (ρ : metasubst) (Q : bskl) : bskl :=
  match Q with
  | bskl_unit => bskl_unit
  | bskl_var_b n => bskl_var_b n
  | bskl_var_f X => pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ X))
  | bskl_arrow Q1 Q2 => bskl_arrow (msubst_bskl ρ Q1) (msubst_bskl ρ Q2)
  | bskl_all_syn Q0 => bskl_all_syn (msubst_bskl ρ Q0)
  | bskl_all_inh Q0 => bskl_all_inh (msubst_bskl ρ Q0)
  | bskl_hole => bskl_hole
  | bskl_tophole Q0 => bskl_tophole (msubst_bskl ρ Q0)
  end.

(** Composition of metasubstitutions, [ζ ∘ θ].  A metasubstitution is a finite
    MAP (algorithmic.tex:123), so composition is pointwise on the domain:
    (ζ ∘ ρ)(α) = ζ(θ(α)).  Its action law — and the side condition that law
    needs — is [msubst_ptyp_compose] in algo/prop_compose.v. *)
Definition msubst_compose (ζ ρ : metasubst) : metasubst :=
  List.map (fun e => (fst e, msubst_ptyp ζ (snd e))) ρ.

(** The identity metasubstitution ι maps each flexible variable to itself. *)
Definition is_id_entry (e : atom * ptyp) : Prop :=
  snd e = ptyp_var_f (fst e).

Definition is_id_msubst (ρ : metasubst) : Prop :=
  Forall is_id_entry ρ.

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
(*  Skeleton equivalence  [Θ ⊢ P ≡ˢ Q]  — the [a_tyequiv] equational      *)
(*  theory lifted to skeletons: definitions of flexible variables unfold,  *)
(*  ghosts are inert (related only by congruence/reflexivity).             *)
(*                                                                        *)
(*  Introduced for the GMM-STYLE SEMANTIC ENTRIES of information increase *)
(*  (see [a_inc] below): GundryMM10 §3.1 preserve context entries UP TO    *)
(*  the equational theory (Δ ⊩ δ⟦vD⟧, i.e. δα ≡ δτ for a definition),     *)
(*  never syntactically.  The previous SYNTACTIC middles [x : θP] made     *)
(*  the optimality half of thm:complete-consistency FALSE                  *)
(*  (machine-checked: algo/cex/cex_assign_optimal_syn_middle.v).               *)
(* ===================================================================== *)

Reserved Notation "Θ ⊢ P ≡ˢ Q"
  (at level 75, P at level 74, Q at level 74, no associativity).
Inductive a_pskl_tyequiv : aenv -> pskl -> pskl -> Prop :=
| a_pskl_tyequiv__refl : forall Θ P,
    lc_pskl P ->
    Θ ⊢ P ≡ˢ P
| a_pskl_tyequiv__sym : forall Θ P Q,
    Θ ⊢ P ≡ˢ Q ->
    Θ ⊢ Q ≡ˢ P
| a_pskl_tyequiv__trans : forall Θ P Q R,
    Θ ⊢ P ≡ˢ Q ->
    Θ ⊢ Q ≡ˢ R ->
    Θ ⊢ P ≡ˢ R
(* retrieve a flexible variable's definition *)
| a_pskl_tyequiv__flex_def : forall Θ α τ,
    binds α (abind_flex_mono_def τ) Θ ->
    Θ ⊢ (pskl_var_f α) ≡ˢ (ptyp_to_pskl τ)
| a_pskl_tyequiv__arrow : forall Θ P1 P2 Q1 Q2,
    Θ ⊢ P1 ≡ˢ Q1 ->
    Θ ⊢ P2 ≡ˢ Q2 ->
    Θ ⊢ (pskl_arrow P1 P2) ≡ˢ (pskl_arrow Q1 Q2)
| a_pskl_tyequiv__all : forall L Θ P Q,
    (forall X, X `notin` L ->
       Θ ⊢ (open_pskl_wrt_pskl P (pskl_var_f X)) ≡ˢ
           (open_pskl_wrt_pskl Q (pskl_var_f X))) ->
    Θ ⊢ (pskl_all_syn P) ≡ˢ (pskl_all_syn Q)
| a_pskl_tyequiv__tophole : forall Θ P Q,
    Θ ⊢ P ≡ˢ Q ->
    Θ ⊢ (pskl_tophole P) ≡ˢ (pskl_tophole Q)
where "Θ ⊢ P ≡ˢ Q" := (a_pskl_tyequiv Θ P Q) : type_scope.

(* ===================================================================== *)
(*  Information increase  [θ ∷ Θ ⊑ Θ']  (fig:information-increase)         *)
(* ===================================================================== *)

Reserved Notation "ρ ∷ Θ ⊑ Θ'"
  (at level 75, Θ at level 74, Θ' at level 74, no associativity).
Inductive a_inc : aenv -> metasubst -> aenv -> Prop :=
| a_inc__empty : forall Ξ,                       (* ι ∷ · ⊑ Ξ *)
    a_suffix Ξ ->
    nil ∷ nil ⊑ Ξ
| a_inc__flex : forall Θ ρ Θ' α τ,               (* θ,τ/α̂ ∷ Θ,α̂ ⊑ Θ' *)
    ρ ∷ Θ ⊑ Θ' ->
    a_wf_ptyp Θ' τ ->
    mono_ptyp τ ->
    ((α, τ) :: ρ) ∷ ((α ~ abind_flex_mono) ++ Θ) ⊑ Θ'
| a_inc__flex_def : forall Θ ρ Θ' α τ τ',        (* θ,τ'/α̂ ∷ Θ,α̂:=τ ⊑ Θ', τ' ≡ θτ *)
    ρ ∷ Θ ⊑ Θ' ->
    (* the paper's prose side-condition on ρ (algorithmic.tex:123): every
       image is a well-formed monotype in the target *)
    a_wf_ptyp Θ' τ' ->
    mono_ptyp τ' ->
    Θ' ⊢ τ' ≡ᵗ (msubst_ptyp ρ τ) ->
    ((α, τ') :: ρ) ∷ ((α ~ abind_flex_mono_def τ) ++ Θ) ⊑ Θ'
(* SEMANTIC ENTRIES for the two binder cases (GundryMM10 §3.1; 2026-07-15).
   The target's binding is preserved UP TO THE EQUATIONAL THEORY, not
   syntactically: [Θ' ⊢ A' ≡ᵗ θA] instead of [A' = θA].  With syntactic
   middles the optimality half of thm:complete-consistency is FALSE — the
   assignment walk moves a flexible below a term binder (forced by wf of the
   deposited definition), and a competing solution may then use scope that
   exists only above it (machine-checked counterexample:
   algo/cex/cex_assign_optimal_syn_middle.v). *)
| a_inc__var : forall Θ ρ Θ' Ξ x A A',           (* θ ∷ Θ,x:A ⊑ Θ',x:A'≡θA,Ξ (type entry) *)
    ρ ∷ Θ ⊑ Θ' ->
    Θ' ⊢ A' ≡ᵗ (msubst_ptyp ρ A) ->
    a_suffix Ξ ->
    ρ ∷ ((x ~ abind_var_typ A) ++ Θ) ⊑
      (Ξ ++ (x ~ abind_var_typ A') ++ Θ')
| a_inc__var_skl : forall Θ ρ Θ' Ξ x P P',       (* θ ∷ Θ,x:P ⊑ Θ',x:P'≡θP,Ξ (skeleton entry) *)
    ρ ∷ Θ ⊑ Θ' ->
    Θ' ⊢ P' ≡ˢ (msubst_pskl ρ P) ->
    a_suffix Ξ ->
    ρ ∷ ((x ~ abind_var_skl P) ++ Θ) ⊑
      (Ξ ++ (x ~ abind_var_skl P') ++ Θ')
| a_inc__tvar : forall Θ ρ Θ' Ξ α,               (* θ ∷ Θ,α ⊑ Θ',α,Ξ *)
    ρ ∷ Θ ⊑ Θ' ->
    a_suffix Ξ ->
    ρ ∷ ((α ~ abind_tvar) ++ Θ) ⊑ (Ξ ++ (α ~ abind_tvar) ++ Θ')
where "ρ ∷ Θ ⊑ Θ'" := (a_inc Θ ρ Θ') : type_scope.

(** [Θ ⊴ Θ'] (paper [⊑{Θ}{Θ'}], identity-metasubstitution shorthand).

    Besides an identity witness for the figure's rules, this carries the
    paper's PROSE characterization of identity metasubstitutions
    (algorithmic.tex:135): "all entries of flexible variables in Θ are
    preserved in Θ'" — in particular a definition [α̂:=τ], once made, is
    never rewritten (the algorithm only adds definitions).  This component
    is what makes the FlexL/FlexR lookup rules stable under [⊴]. *)
Definition a_isub (Θ Θ' : aenv) : Prop :=
  (exists ρ, is_id_msubst ρ /\ ρ ∷ Θ ⊑ Θ') /\
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
| a_inc_equiv__flex : forall Θ ρ1 ρ2 Θ' α τ1 τ2,
    a_inc_equiv Θ ρ1 ρ2 Θ' ->
    Θ' ⊢ τ1 ≡ᵗ τ2 ->
    a_inc_equiv ((α ~ abind_flex_mono) ++ Θ) ((α, τ1) :: ρ1) ((α, τ2) :: ρ2) Θ'
| a_inc_equiv__flex_def : forall Θ ρ1 ρ2 Θ' α τ τ1 τ2,
    a_inc_equiv Θ ρ1 ρ2 Θ' ->
    Θ' ⊢ τ1 ≡ᵗ τ2 ->
    Θ' ⊢ τ1 ≡ᵗ (msubst_ptyp ρ1 τ) ->
    a_inc_equiv ((α ~ abind_flex_mono_def τ) ++ Θ) ((α, τ1) :: ρ1) ((α, τ2) :: ρ2) Θ'
(* semantic entries, mirroring [a_inc__var]/[a_inc__var_skl] above *)
| a_inc_equiv__var : forall Θ ρ1 ρ2 Θ' Ξ x A A',
    a_inc_equiv Θ ρ1 ρ2 Θ' ->
    Θ' ⊢ A' ≡ᵗ (msubst_ptyp ρ1 A) ->
    a_suffix Ξ ->
    a_inc_equiv ((x ~ abind_var_typ A) ++ Θ) ρ1 ρ2
                (Ξ ++ (x ~ abind_var_typ A') ++ Θ')
| a_inc_equiv__var_skl : forall Θ ρ1 ρ2 Θ' Ξ x P P',
    a_inc_equiv Θ ρ1 ρ2 Θ' ->
    Θ' ⊢ P' ≡ˢ (msubst_pskl ρ1 P) ->
    a_suffix Ξ ->
    a_inc_equiv ((x ~ abind_var_skl P) ++ Θ) ρ1 ρ2
                (Ξ ++ (x ~ abind_var_skl P') ++ Θ')
| a_inc_equiv__tvar : forall Θ ρ1 ρ2 Θ' Ξ α,
    a_inc_equiv Θ ρ1 ρ2 Θ' ->
    a_suffix Ξ ->
    a_inc_equiv ((α ~ abind_tvar) ++ Θ) ρ1 ρ2
                (Ξ ++ (α ~ abind_tvar) ++ Θ').
