(** Questions, solutions, and optimality for the algorithmic judgments.

    These wrap the declarative judgments (applied to the projected
    declarative context [denv_of Θ]) with the paper's metasubstitution
    discipline, so the soundness / completeness / optimality theorems can
    be stated faithfully (paper [algorithmic.tex]):

      - consistency        [Definition: Questions of consistency]
      - subtyping          [Definition: Questions of subtyping]
      - skeleton inference [Definition: Questions of skeleton inference]
      - type inference     [Definition: Questions of type inference]

    A *solution* pairs an information increase [Θ₀ ≤[θ₁] Θ₁] with an
    output, witnessing the relevant declarative judgment plus the
    inherited-refinement side condition [Θ₁ ⊢ inh(θ₁ P) ▷syn bid(out)].
    A solution is *optimal* when every other solution factors through it
    via a cofactor metasubstitution [ζ]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.notations.
Require Import src.frost.algo.def_meta.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Skeleton view of a type ([bid{A}] when the output is a type [A]).     *)
(*  A type has no ghosts, so its skeleton view is the full painting of    *)
(*  its erasure.                                                          *)
(* ===================================================================== *)

Definition btyp_to_bskl_syn (B : btyp) : bskl :=
  pskl_to_bskl_syn (ptyp_to_pskl (btyp_to_ptyp B)).

Definition btyp_to_bskl_inh (B : btyp) : bskl :=
  pskl_to_bskl_inh (ptyp_to_pskl (btyp_to_ptyp B)).

(* ===================================================================== *)
(*  Placeholders for declarative notions not yet mechanised.              *)
(* ===================================================================== *)

(* Skeleton precision [Θ ⊢ P' ≼ P] (paper [\precise]).  PLACEHOLDER:
   reflexive under-approximation; replace with the real precision
   relation (and its lemma [inherited-refinement-gives-precision]). *)
Inductive a_precise : aenv -> bskl -> bskl -> Prop :=
| a_precise__refl : forall Θ Q, a_precise Θ Q Q.

(* [Θ ⊢ P ≼ Q] : P is more precise than Q (paper [\precise]). *)
Notation "Θ ⊢ P ≼ Q" := (a_precise Θ P Q)
  (at level 75, P at level 74, Q at level 74, no associativity) : type_scope.

(* Type equivalence over [btyp] (companion to [a_tyequiv] on [ptyp]).
   PLACEHOLDER: syntactic equality. *)
Inductive a_btyequiv : aenv -> btyp -> btyp -> Prop :=
| a_btyequiv__refl : forall Θ B, a_btyequiv Θ B B.

(* Composition of metasubstitutions [ζ ∘ θ₁] (cofactor on the left). *)
Definition msubst_compose (ζ θ1 : metasubst) : metasubst :=
  map (fun A => msubst_ptyp ζ A) θ1.

(* The inherited-refinement side condition [Θ ⊢ inh(θ P₀) ▷syn out],
   shared by all four solution definitions (the output [out] is already a
   [bskl]). *)
Definition a_fillsyn (Θ : aenv) (θ : metasubst) (P0 : pskl) (out : bskl) : Prop :=
  d_refine_syn nil ⌊ Θ ⌋ (pskl_to_bskl_inh (msubst_pskl θ P0)) out.

(* ===================================================================== *)
(*  Consistency  (paper: Questions of consistency).                       *)
(*    question  (Θ₀; P₀; P)                                              *)
(*    solution  (Θ₀ ≤[θ₁] Θ₁; P₁)                                        *)
(*    with  Θ₁ ⊢ syn(θ₁ P) ~ bid(P₁)  and  Θ₁ ⊢ inh(θ₁ P₀) ▷syn bid(P₁)  *)
(* ===================================================================== *)

Definition a_consis_solution
    (Θ0 : aenv) (P0 P : pskl) (θ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  d_pat_consis nil ⌊ Θ1 ⌋
    (bskl_to_uskl (pskl_to_bskl_syn (msubst_pskl θ1 P))) P1 /\
  a_fillsyn Θ1 θ1 P0 P1.

Definition a_consis_solution_ex (Θ0 : aenv) (P0 P : pskl) : Prop :=
  exists θ1 Θ1 P1, a_consis_solution Θ0 P0 P θ1 Θ1 P1.

Definition a_consis_optimal
    (Θ0 : aenv) (P0 P : pskl) (θ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  a_consis_solution Θ0 P0 P θ1 Θ1 P1 /\
  (forall θ Θ Q,
     a_consis_solution Θ0 P0 P θ Θ Q ->
     exists ζ, Θ1 ≤[ ζ ] Θ /\
               a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
               Θ ⊢ msubst_bskl ζ P1 ≼ Q).

(* ===================================================================== *)
(*  Subtyping  (paper: Questions of subtyping).                           *)
(*    question  (Θ₀; N; M; P₀; P)        [N collapsed: type-level d_sub]  *)
(*    solution  (Θ₀ ≤[θ₁] Θ₁; P₁)                                        *)
(*    with  ⊢_{N,M} Θ₁ syn(θ₁ P) ⊑ bid(P₁)  and the refinement side cond. *)
(* ===================================================================== *)

Definition a_sub_solution
    (M : mode) (Θ0 : aenv) (P0 : pskl) (B : btyp)
    (θ1 : metasubst) (Θ1 : aenv) (B1 : btyp) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  d_sub M empty ⌊ Θ1 ⌋ (btyp_to_utyp_syn (msubst_btyp θ1 B)) B1 /\
  a_fillsyn Θ1 θ1 P0 (btyp_to_bskl_inh B1).

Definition a_sub_solution_ex (M : mode) (Θ0 : aenv) (P0 : pskl) (B : btyp) : Prop :=
  exists θ1 Θ1 B1, a_sub_solution M Θ0 P0 B θ1 Θ1 B1.

Definition a_sub_optimal
    (M : mode) (Θ0 : aenv) (P0 : pskl) (B : btyp)
    (θ1 : metasubst) (Θ1 : aenv) (B1 : btyp) : Prop :=
  a_sub_solution M Θ0 P0 B θ1 Θ1 B1 /\
  (forall θ Θ Q,
     a_sub_solution M Θ0 P0 B θ Θ Q ->
     exists ζ, Θ1 ≤[ ζ ] Θ /\
               a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
               Θ ⊢ btyp_to_bskl_inh (msubst_btyp ζ B1) ≼ btyp_to_bskl_inh Q).

(* ===================================================================== *)
(*  Skeleton inference  (paper: Questions of skeleton inference).         *)
(*    question  (Θ₀; M; P₀; e)                                            *)
(*    solution  (Θ₀ ≤[θ₁] Θ₁; P₁)                                        *)
(*    with  Θ₁ ⊢ e ⇨ bid(P₁)  and  Θ₁ ⊢ inh(θ₁ P₀) ▷syn bid(P₁)          *)
(* ===================================================================== *)

Definition a_pat_solution
    (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (θ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  d_pat M ⌊ Θ1 ⌋ e P1 /\
  a_fillsyn Θ1 θ1 P0 P1.

Definition a_pat_solution_ex (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp) : Prop :=
  exists θ1 Θ1 P1, a_pat_solution M Θ0 P0 e θ1 Θ1 P1.

Definition a_pat_optimal
    (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (θ1 : metasubst) (Θ1 : aenv) (P1 : bskl) : Prop :=
  a_pat_solution M Θ0 P0 e θ1 Θ1 P1 /\
  (forall θ Θ Q,
     a_pat_solution M Θ0 P0 e θ Θ Q ->
     exists ζ, Θ1 ≤[ ζ ] Θ /\
               a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
               Θ ⊢ msubst_bskl ζ P1 ≼ Q).

(* ===================================================================== *)
(*  Type inference  (paper: Questions of type inference).                 *)
(*    question  (Θ₀; M; P; e)                                             *)
(*    solution  (Θ₀ ≤[θ₁] Θ₁; A)                                         *)
(*    with  Θ₁ ⊢ e ⦂ bid(A)  and  Θ₁ ⊢ inh(θ₁ P) ▷syn bid(A)             *)
(*    optimality uses type equivalence [ζ A ≡ B] (not precision).         *)
(* ===================================================================== *)

Definition a_typing_solution
    (M : mode) (Θ0 : aenv) (P : pskl) (e : exp)
    (θ1 : metasubst) (Θ1 : aenv) (A : btyp) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  d_typing M ⌊ Θ1 ⌋ e A /\
  a_fillsyn Θ1 θ1 P (btyp_to_bskl_inh A).

Definition a_typing_solution_ex (M : mode) (Θ0 : aenv) (P : pskl) (e : exp) : Prop :=
  exists θ1 Θ1 A, a_typing_solution M Θ0 P e θ1 Θ1 A.

Definition a_typing_optimal
    (M : mode) (Θ0 : aenv) (P : pskl) (e : exp)
    (θ1 : metasubst) (Θ1 : aenv) (A : btyp) : Prop :=
  a_typing_solution M Θ0 P e θ1 Θ1 A /\
  (forall θ Θ B,
     a_typing_solution M Θ0 P e θ Θ B ->
     exists ζ, Θ1 ≤[ ζ ] Θ /\
               a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
               a_btyequiv Θ (msubst_btyp ζ A) B).
