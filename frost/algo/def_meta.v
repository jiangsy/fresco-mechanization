(** Metasubstitutions (information increase), paper app:metasubstitutions
    (fig:information-increase-and-equivalence), and the aenv↔denv bridges.

    A metasubstitution κ is a finite map from flexible variables to
    monotypes; [a_inc Θ κ Θ'] is the paper's [Θ ⊑[κ] Θ'].  The algorithms
    always produce identity metasubstitutions ι (every entry [α̂ ↦ α̂]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.notations.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo_decl.def_consis_refine.   (* [ptyp_to_uskl_syn] *)

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope frost_a_scope.

(* ===================================================================== *)
(*  Metasubstitutions and their application                               *)
(* ===================================================================== *)

Definition metasubst : Set := list (atom * ptyp).

(** [paper-gap / MECH-BUG fixed]  The paper (algorithmic.tex:123) says a
    metasubstitution IS "a finite MAP κ from flexible variables in Θ to
    well-formed monotypes in Θ'" — i.e. a SIMULTANEOUS substitution.  These were
    previously encoded as a SEQUENTIAL fold
    ([msubst ((α,τ)::κ) A = msubst κ' (A[τ/α])]), which is a different function:
    the fold lets a LATER entry rewrite inside an EARLIER entry's image.  E.g.
    for the (legal) [κ = α ↦ β̂, β̂ ↦ unit] the fold sends [α ↦ unit] where the
    map sends [α ↦ β̂].  The two coincide on IDENTITY metasubstitutions (each
    [α ↦ α] substitution is a no-op), which is all the algorithm ever produces —
    which is why nothing depended on the difference.  But composition [ζ ∘ κ] and
    hence COMPLETENESS need general κ, and there the fold is simply the wrong
    function.  So: recurse on the TYPE and look each free variable up. *)

Fixpoint msubst_lookup (κ : metasubst) (α : atom) : ptyp :=
  match κ with
  | nil => ptyp_var_f α
  | (β, τ) :: κ' => if α == β then τ else msubst_lookup κ' α
  end.

Fixpoint msubst_ptyp (κ : metasubst) (A : ptyp) : ptyp :=
  match A with
  | ptyp_unit => ptyp_unit
  | ptyp_var_b n => ptyp_var_b n
  | ptyp_var_f α => msubst_lookup κ α
  | ptyp_arrow A1 A2 => ptyp_arrow (msubst_ptyp κ A1) (msubst_ptyp κ A2)
  | ptyp_all A0 => ptyp_all (msubst_ptyp κ A0)
  end.

Fixpoint msubst_pskl (κ : metasubst) (P : pskl) : pskl :=
  match P with
  | pskl_unit => pskl_unit
  | pskl_var_b n => pskl_var_b n
  | pskl_var_f α => ptyp_to_pskl (msubst_lookup κ α)
  | pskl_arrow P1 P2 => pskl_arrow (msubst_pskl κ P1) (msubst_pskl κ P2)
  | pskl_all_syn P0 => pskl_all_syn (msubst_pskl κ P0)
  | pskl_hole => pskl_hole
  | pskl_tophole P0 => pskl_tophole (msubst_pskl κ P0)
  end.

(** [κ R] on UNRESOLVED skeletons — the sort the decorated consistency's
    subject lives in.  NB distinct from [prop_decorate_sub.msubst_uskl], which
    is the PAPER's κ (a map from rigid variables to decorated SKELETONS); this
    one applies a METASUBSTITUTION (flexibles ↦ monotypes), hence the [_syn]
    suffix: an image is embedded with the synthesised painting.  A flexible variable's image is a monotype, so it is
    embedded with the synthesised painting; every other constructor (including
    the plain and dotted ghosts) is structural.  This is what lets a subject be
    written as the paper writes it, [(κR)[ψa/α]], instead of baking κ into it. *)
Fixpoint msubst_uskl_syn (κ : metasubst) (R : uskl) : uskl :=
  match R with
  | uskl_unit => uskl_unit
  | uskl_var_b n => uskl_var_b n
  | uskl_var_f α => ptyp_to_uskl_syn (msubst_lookup κ α)
  | uskl_arrow R1 R2 => uskl_arrow (msubst_uskl_syn κ R1) (msubst_uskl_syn κ R2)
  | uskl_all_syn R0 => uskl_all_syn (msubst_uskl_syn κ R0)
  | uskl_all_tag ε R0 => uskl_all_tag ε (msubst_uskl_syn κ R0)
  | uskl_hole => uskl_hole
  | uskl_tophole R0 => uskl_tophole (msubst_uskl_syn κ R0)
  | uskl_holeg => uskl_holeg
  | uskl_topholeg R0 => uskl_topholeg (msubst_uskl_syn κ R0)
  end.

Fixpoint msubst_btyp (κ : metasubst) (B : btyp) : btyp :=
  match B with
  | btyp_unit => btyp_unit
  | btyp_var_b n => btyp_var_b n
  | btyp_var_f α => ptyp_to_btyp_syn (msubst_lookup κ α)
  | btyp_arrow B1 B2 => btyp_arrow (msubst_btyp κ B1) (msubst_btyp κ B2)
  | btyp_all_syn B0 => btyp_all_syn (msubst_btyp κ B0)
  | btyp_all_inh B0 => btyp_all_inh (msubst_btyp κ B0)
  end.

Fixpoint msubst_bskl (κ : metasubst) (Q : bskl) : bskl :=
  match Q with
  | bskl_unit => bskl_unit
  | bskl_var_b n => bskl_var_b n
  | bskl_var_f α => pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α))
  | bskl_arrow Q1 Q2 => bskl_arrow (msubst_bskl κ Q1) (msubst_bskl κ Q2)
  | bskl_all_syn Q0 => bskl_all_syn (msubst_bskl κ Q0)
  | bskl_all_inh Q0 => bskl_all_inh (msubst_bskl κ Q0)
  | bskl_hole => bskl_hole
  | bskl_tophole Q0 => bskl_tophole (msubst_bskl κ Q0)
  end.

(** Composition of metasubstitutions, [ζ ∘ κ].  A metasubstitution is a finite
    MAP (algorithmic.tex:123), so composition is pointwise on the domain:
    (ζ ∘ κ)(α) = ζ(κ(α)).  Its action law — and the side condition that law
    needs — is [msubst_ptyp_compose] in algo/prop_compose.v. *)
Definition msubst_compose (ζ κ : metasubst) : metasubst :=
  List.map (fun e => (fst e, msubst_ptyp ζ (snd e))) κ.

(** The identity metasubstitution ι maps each flexible variable to itself. *)
Definition is_id_entry (e : atom * ptyp) : Prop :=
  snd e = ptyp_var_f (fst e).

Definition is_id_msubst (κ : metasubst) : Prop :=
  Forall is_id_entry κ.

(* ===================================================================== *)
(*  Type equivalence in algorithmic contexts  [Θ ⊢ A ≡ B]                 *)
(*  (paper app:decl-in-algo-context: α-equivalence, made explicit          *)
(*  because flexible-variable definitions are retrieved from Θ).           *)
(* ===================================================================== *)

Reserved Notation "{{ Θ ⊢ A ≡ᵗ B }}a"
  (at level 0, A at level 74, B at level 74,
   format "'{{'  Θ  ⊢  A  ≡ᵗ  B  '}}a'").
Inductive a_tyequiv : aenv -> ptyp -> ptyp -> Prop :=
| a_tyequiv__refl : forall Θ A,
    lc_ptyp A ->
    {{ Θ ⊢ A ≡ᵗ A }}a
| a_tyequiv__sym : forall Θ A B,
    {{ Θ ⊢ A ≡ᵗ B }}a ->
    {{ Θ ⊢ B ≡ᵗ A }}a
| a_tyequiv__trans : forall Θ A B C,
    {{ Θ ⊢ A ≡ᵗ B }}a ->
    {{ Θ ⊢ B ≡ᵗ C }}a ->
    {{ Θ ⊢ A ≡ᵗ C }}a
(* retrieve a flexible variable's definition *)
| a_tyequiv__flex_def : forall Θ α τ,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⊢ (ptyp_var_f α) ≡ᵗ τ }}a
| a_tyequiv__arrow : forall Θ A1 A2 B1 B2,
    {{ Θ ⊢ A1 ≡ᵗ B1 }}a ->
    {{ Θ ⊢ A2 ≡ᵗ B2 }}a ->
    {{ Θ ⊢ (ptyp_arrow A1 A2) ≡ᵗ (ptyp_arrow B1 B2) }}a
| a_tyequiv__all : forall L Θ A B,
    (forall α, α `notin` L ->
       {{ Θ ⊢ (open_ptyp_wrt_ptyp A (ptyp_var_f α)) ≡ᵗ
           (open_ptyp_wrt_ptyp B (ptyp_var_f α)) }}a) ->
    {{ Θ ⊢ (ptyp_all A) ≡ᵗ (ptyp_all B) }}a
where "{{ Θ ⊢ A ≡ᵗ B }}a" := (a_tyequiv Θ A B) : frost_a_scope.

(* ===================================================================== *)
(*  Skeleton equivalence  [{{ Θ ⊢ P ≡ˢ Q }}a]  — the [a_tyequiv] equational *)
(*  theory lifted to skeletons: definitions of flexible variables unfold,  *)
(*  ghosts are inert (related only by congruence/reflexivity).             *)
(*                                                                        *)
(*  Introduced for the GMM-STYLE SEMANTIC ENTRIES of information increase *)
(*  (see [a_inc] below): GundryMM10 §3.1 preserve context entries UP TO    *)
(*  the equational theory (Δ ⊩ β1⟦vD⟧, i.e. β1α ≡ β1τ for a definition),     *)
(*  never syntactically.  The previous SYNTACTIC middles [x : κP] made     *)
(*  the optimality half of thm:complete-consistency FALSE                  *)
(*  (machine-checked: algo/cex/cex_assign_optimal_syn_middle.v).               *)
(* ===================================================================== *)

Reserved Notation "{{ Θ ⊢ P ≡ˢ Q }}a"
  (at level 0, P at level 74, Q at level 74,
   format "'{{'  Θ  ⊢  P  ≡ˢ  Q  '}}a'").
Inductive a_pskl_tyequiv : aenv -> pskl -> pskl -> Prop :=
| a_pskl_tyequiv__refl : forall Θ P,
    lc_pskl P ->
    {{ Θ ⊢ P ≡ˢ P }}a
| a_pskl_tyequiv__sym : forall Θ P Q,
    {{ Θ ⊢ P ≡ˢ Q }}a ->
    {{ Θ ⊢ Q ≡ˢ P }}a
| a_pskl_tyequiv__trans : forall Θ P Q R,
    {{ Θ ⊢ P ≡ˢ Q }}a ->
    {{ Θ ⊢ Q ≡ˢ R }}a ->
    {{ Θ ⊢ P ≡ˢ R }}a
(* retrieve a flexible variable's definition *)
| a_pskl_tyequiv__flex_def : forall Θ α τ,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⊢ (pskl_var_f α) ≡ˢ (ptyp_to_pskl τ) }}a
| a_pskl_tyequiv__arrow : forall Θ P1 P2 Q1 Q2,
    {{ Θ ⊢ P1 ≡ˢ Q1 }}a ->
    {{ Θ ⊢ P2 ≡ˢ Q2 }}a ->
    {{ Θ ⊢ (pskl_arrow P1 P2) ≡ˢ (pskl_arrow Q1 Q2) }}a
| a_pskl_tyequiv__all : forall L Θ P Q,
    (forall α, α `notin` L ->
       {{ Θ ⊢ (open_pskl_wrt_pskl P (pskl_var_f α)) ≡ˢ
           (open_pskl_wrt_pskl Q (pskl_var_f α)) }}a) ->
    {{ Θ ⊢ (pskl_all_syn P) ≡ˢ (pskl_all_syn Q) }}a
| a_pskl_tyequiv__tophole : forall Θ P Q,
    {{ Θ ⊢ P ≡ˢ Q }}a ->
    {{ Θ ⊢ (pskl_tophole P) ≡ˢ (pskl_tophole Q) }}a
where "{{ Θ ⊢ P ≡ˢ Q }}a" := (a_pskl_tyequiv Θ P Q) : frost_a_scope.

(* ===================================================================== *)
(*  Information increase  [κ ∷ Θ ⊑ Θ']  (fig:information-increase)         *)
(* ===================================================================== *)

Reserved Notation "κ ∷ Θ ⊑ Θ'"
  (at level 75, Θ at level 74, Θ' at level 74, no associativity).
Inductive a_inc : aenv -> metasubst -> aenv -> Prop :=
| a_inc__empty : forall Ξ,                       (* ι ∷ · ⊑ Ξ *)
    a_suffix Ξ ->
    nil ∷ nil ⊑ Ξ
| a_inc__flex : forall Θ κ Θ' α τ,               (* κ,τ/α̂ ∷ Θ,α̂ ⊑ Θ' *)
    κ ∷ Θ ⊑ Θ' ->
    a_wf_ptyp Θ' τ ->
    mono_ptyp τ ->
    ((α, τ) :: κ) ∷ ((α ~ abind_flex_mono) ++ Θ) ⊑ Θ'
| a_inc__flex_def : forall Θ κ Θ' α τ τ',        (* κ,τ'/α̂ ∷ Θ,α̂:=τ ⊑ Θ', τ' ≡ κτ *)
    κ ∷ Θ ⊑ Θ' ->
    (* the paper's prose side-condition on κ (algorithmic.tex:123): every
       image is a well-formed monotype in the target *)
    a_wf_ptyp Θ' τ' ->
    mono_ptyp τ' ->
    {{ Θ' ⊢ τ' ≡ᵗ (msubst_ptyp κ τ) }}a ->
    ((α, τ') :: κ) ∷ ((α ~ abind_flex_mono_def τ) ++ Θ) ⊑ Θ'
(* SEMANTIC ENTRIES for the two binder cases (GundryMM10 §3.1; 2026-07-15).
   The target's binding is preserved UP TO THE EQUATIONAL THEORY, not
   syntactically: [{{ Θ' ⊢ A' ≡ᵗ κA }}a] instead of [A' = κA].  With syntactic
   middles the optimality half of thm:complete-consistency is FALSE — the
   assignment walk moves a flexible below a term binder (forced by wf of the
   deposited definition), and a competing solution may then use scope that
   exists only above it (machine-checked counterexample:
   algo/cex/cex_assign_optimal_syn_middle.v). *)
| a_inc__var : forall Θ κ Θ' Ξ x A A',           (* κ ∷ Θ,x:A ⊑ Θ',x:A'≡κA,Ξ (type entry) *)
    κ ∷ Θ ⊑ Θ' ->
    {{ Θ' ⊢ A' ≡ᵗ (msubst_ptyp κ A) }}a ->
    a_suffix Ξ ->
    κ ∷ ((x ~ abind_var_typ A) ++ Θ) ⊑
      (Ξ ++ (x ~ abind_var_typ A') ++ Θ')
| a_inc__var_skl : forall Θ κ Θ' Ξ x P P',       (* κ ∷ Θ,x:P ⊑ Θ',x:P'≡κP,Ξ (skeleton entry) *)
    κ ∷ Θ ⊑ Θ' ->
    {{ Θ' ⊢ P' ≡ˢ (msubst_pskl κ P) }}a ->
    a_suffix Ξ ->
    κ ∷ ((x ~ abind_var_skl P) ++ Θ) ⊑
      (Ξ ++ (x ~ abind_var_skl P') ++ Θ')
| a_inc__tvar : forall Θ κ Θ' Ξ α,               (* κ ∷ Θ,α ⊑ Θ',α,Ξ *)
    κ ∷ Θ ⊑ Θ' ->
    a_suffix Ξ ->
    κ ∷ ((α ~ abind_tvar) ++ Θ) ⊑ (Ξ ++ (α ~ abind_tvar) ++ Θ')
where "κ ∷ Θ ⊑ Θ'" := (a_inc Θ κ Θ') : type_scope.

(** [Θ ⊴ Θ'] (paper [⊑{Θ}{Θ'}], identity-metasubstitution shorthand).

    Besides an identity witness for the figure's rules, this carries the
    paper's PROSE characterization of identity metasubstitutions
    (algorithmic.tex:135): "all entries of flexible variables in Θ are
    preserved in Θ'" — in particular a definition [α̂:=τ], once made, is
    never rewritten (the algorithm only adds definitions).  This component
    is what makes the FlexL/FlexR lookup rules stable under [⊴]. *)
Definition a_isub (Θ Θ' : aenv) : Prop :=
  (exists κ, is_id_msubst κ /\ κ ∷ Θ ⊑ Θ') /\
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
               binds α (abind_flex_mono_def τ) Θ').

Notation "Θ ⊴ Θ'" := (a_isub Θ Θ')
  (at level 75, no associativity) : type_scope.

(** Equivalence of metasubstitutions [κ₁ ≡ κ₂ : Θ ⇒ Θ']
    (fig:information-increase-and-equivalence, second box). *)
Inductive a_inc_equiv : aenv -> metasubst -> metasubst -> aenv -> Prop :=
| a_inc_equiv__empty : forall Ξ,
    a_suffix Ξ ->
    a_inc_equiv nil nil nil Ξ
| a_inc_equiv__flex : forall Θ κ1 κ2 Θ' α τ1 τ2,
    a_inc_equiv Θ κ1 κ2 Θ' ->
    {{ Θ' ⊢ τ1 ≡ᵗ τ2 }}a ->
    a_inc_equiv ((α ~ abind_flex_mono) ++ Θ) ((α, τ1) :: κ1) ((α, τ2) :: κ2) Θ'
| a_inc_equiv__flex_def : forall Θ κ1 κ2 Θ' α τ τ1 τ2,
    a_inc_equiv Θ κ1 κ2 Θ' ->
    {{ Θ' ⊢ τ1 ≡ᵗ τ2 }}a ->
    {{ Θ' ⊢ τ1 ≡ᵗ (msubst_ptyp κ1 τ) }}a ->
    a_inc_equiv ((α ~ abind_flex_mono_def τ) ++ Θ) ((α, τ1) :: κ1) ((α, τ2) :: κ2) Θ'
(* semantic entries, mirroring [a_inc__var]/[a_inc__var_skl] above *)
| a_inc_equiv__var : forall Θ κ1 κ2 Θ' Ξ x A A',
    a_inc_equiv Θ κ1 κ2 Θ' ->
    {{ Θ' ⊢ A' ≡ᵗ (msubst_ptyp κ1 A) }}a ->
    a_suffix Ξ ->
    a_inc_equiv ((x ~ abind_var_typ A) ++ Θ) κ1 κ2
                (Ξ ++ (x ~ abind_var_typ A') ++ Θ')
| a_inc_equiv__var_skl : forall Θ κ1 κ2 Θ' Ξ x P P',
    a_inc_equiv Θ κ1 κ2 Θ' ->
    {{ Θ' ⊢ P' ≡ˢ (msubst_pskl κ1 P) }}a ->
    a_suffix Ξ ->
    a_inc_equiv ((x ~ abind_var_skl P) ++ Θ) κ1 κ2
                (Ξ ++ (x ~ abind_var_skl P') ++ Θ')
| a_inc_equiv__tvar : forall Θ κ1 κ2 Θ' Ξ α,
    a_inc_equiv Θ κ1 κ2 Θ' ->
    a_suffix Ξ ->
    a_inc_equiv ((α ~ abind_tvar) ++ Θ) κ1 κ2
                (Ξ ++ (α ~ abind_tvar) ++ Θ').
