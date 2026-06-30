(** Questions, solutions, and optimality for the algorithmic judgments.

    The algorithmic system is uncoloured (works on [ptyp]/[pskl]); the
    solution predicates bridge to the (coloured) declarative judgments by
    *painting* the algorithmic output at the boundary — [ptyp_to_btyp_*]
    for type inference, [pskl_to_bskl_*] for skeleton inference and
    subtyping.  Each judgment is wrapped with the paper's metasubstitution
    discipline (paper [algorithmic.tex]):

      - consistency        [Definition: Questions of consistency]
      - subtyping          [Definition: Questions of subtyping]
      - skeleton inference [Definition: Questions of skeleton inference]
      - type inference     [Definition: Questions of type inference]

    A *solution* pairs an information increase [Θ₀ ≤[θ₁] Θ₁] with an
    output, witnessing the declarative judgment under [⌊Θ₁⌋] plus the
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
Require Import src.frost.algo.def_meta.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Painting an uncoloured algorithmic type / skeleton to the coloured    *)
(*  declarative sorts ([bid] = bidirectional reading at the boundary).    *)
(* ===================================================================== *)

Definition ptyp_to_bskl_syn (A : ptyp) : bskl := pskl_to_bskl_syn (ptyp_to_pskl A).
Definition ptyp_to_bskl_inh (A : ptyp) : bskl := pskl_to_bskl_inh (ptyp_to_pskl A).
Definition pskl_to_uskl_syn (P : pskl) : uskl := bskl_to_uskl (pskl_to_bskl_syn P).

(* ===================================================================== *)
(*  Placeholders for declarative notions not yet mechanised.              *)
(* ===================================================================== *)

(* Skeleton precision [Θ ⊢ P ≼ Q] (paper [\precise], algorithmic.tex:854-922):
   [P] has exactly [Q]'s quantifiers but may have more universal ghosts and
   fewer monotypes.  Over the (coloured) [bskl]; algorithmic [pskl] outputs
   are painted (syn) before comparison.  Flex vars [α̂] are [bskl_var_f]
   distinguished by their [Θ]-binding.  ([□ ≼ π] "[π] a monotype" is read as
   [guarded_bskl] — head-monotype — since there is no [bskl] monotype
   predicate; the [∀] rule uses the syn colour, matching [pskl_to_bskl_syn].) *)
Inductive a_precise : aenv -> bskl -> bskl -> Prop :=
| a_precise__unit : forall Θ,
    a_precise Θ bskl_unit bskl_unit
| a_precise__var : forall Θ X,                       (* rigid α / unsolved flex α̂ *)
    a_precise Θ (bskl_var_f X) (bskl_var_f X)
| a_precise__hole : forall Θ,
    a_precise Θ bskl_hole bskl_hole
| a_precise__hole_mono : forall Θ Q,                 (* □ ≼ π *)
    guarded_bskl Q ->
    a_precise Θ bskl_hole Q
| a_precise__arrow : forall Θ P1 P2 Q1 Q2,
    a_precise Θ P1 Q1 ->
    a_precise Θ P2 Q2 ->
    a_precise Θ (bskl_arrow P1 P2) (bskl_arrow Q1 Q2)
| a_precise__all : forall L Θ P Q,
    (forall α, α `notin` L ->
       a_precise Θ (open_bskl_wrt_bskl P (bskl_var_f α))
                   (open_bskl_wrt_bskl Q (bskl_var_f α))) ->
    a_precise Θ (bskl_all_syn P) (bskl_all_syn Q)
| a_precise__tophole_l : forall Θ P Q,               (* ⫯.P ≼ Q (more ghosts) *)
    a_precise Θ P Q ->
    a_precise Θ (bskl_tophole P) Q
| a_precise__tophole : forall Θ P Q,                 (* ⫯.P ≼ ⫯.Q *)
    a_precise Θ P Q ->
    a_precise Θ (bskl_tophole P) (bskl_tophole Q)
| a_precise__flex_l : forall Θ α τ Q,               (* Θ ∋ α̂:=τ,  τ ≼ Q *)
    binds α (abind_flex_mono_def τ) Θ ->
    a_precise Θ (pskl_to_bskl_syn (ptyp_to_pskl τ)) Q ->
    a_precise Θ (bskl_var_f α) Q
| a_precise__flex_r : forall Θ α τ P,               (* Θ ∋ α̂:=τ,  P ≼ τ *)
    binds α (abind_flex_mono_def τ) Θ ->
    a_precise Θ P (pskl_to_bskl_syn (ptyp_to_pskl τ)) ->
    a_precise Θ P (bskl_var_f α).

Notation "Θ ⊢ P ≼ Q" := (a_precise Θ P Q)
  (at level 75, P at level 74, Q at level 74, no associativity) : type_scope.

(* Composition of metasubstitutions [ζ ∘ θ₁] (cofactor on the left). *)
Definition msubst_compose (ζ θ1 : metasubst) : metasubst :=
  map (fun A => msubst_ptyp ζ A) θ1.

(* The inherited-refinement side condition [Θ ⊢ inh(θ P₀) ▷syn out]. *)
Definition a_fillsyn (Θ : aenv) (θ : metasubst) (P0 : pskl) (out : bskl) : Prop :=
  ⌊ Θ ⌋ ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl θ P0)) ⊳ out.

(* ===================================================================== *)
(*  Consistency  (paper: Questions of consistency).                       *)
(* ===================================================================== *)

Definition a_consis_solution
    (Θ0 : aenv) (P0 P : pskl) (θ1 : metasubst) (Θ1 : aenv) (P1 : pskl) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  empty ⨟ ⌊ Θ1 ⌋ ⊨ₛ (pskl_to_uskl_syn (msubst_pskl θ1 P)) ≈ (pskl_to_bskl_syn P1) /\
  a_fillsyn Θ1 θ1 P0 (pskl_to_bskl_syn P1).

Definition a_consis_solution_ex (Θ0 : aenv) (P0 P : pskl) : Prop :=
  exists θ1 Θ1 P1, a_consis_solution Θ0 P0 P θ1 Θ1 P1.

Definition a_consis_optimal
    (Θ0 : aenv) (P0 P : pskl) (θ1 : metasubst) (Θ1 : aenv) (P1 : pskl) : Prop :=
  a_consis_solution Θ0 P0 P θ1 Θ1 P1 /\
  (forall θ Θ Q,
     a_consis_solution Θ0 P0 P θ Θ Q ->
     exists ζ, Θ1 ≤[ ζ ] Θ /\
               a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
               Θ ⊢ pskl_to_bskl_syn (msubst_pskl ζ P1) ≼ pskl_to_bskl_syn Q).

(* ===================================================================== *)
(*  Subtyping  (paper: Questions of subtyping).  Related at the skeleton  *)
(*  level via [d_pat_sub] (the uncoloured [a_sub] outputs a [pskl]).      *)
(* ===================================================================== *)

Definition a_sub_solution
    (M : mode) (Θ0 : aenv) (P0 P : pskl)
    (θ1 : metasubst) (Θ1 : aenv) (Q : pskl) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  empty ⨟ ⌊ Θ1 ⌋ ⊢ₛ[ M ] (pskl_to_uskl_syn (msubst_pskl θ1 P)) ⊑ (pskl_to_bskl_syn Q) /\
  a_fillsyn Θ1 θ1 P0 (pskl_to_bskl_syn Q).

Definition a_sub_solution_ex (M : mode) (Θ0 : aenv) (P0 P : pskl) : Prop :=
  exists θ1 Θ1 Q, a_sub_solution M Θ0 P0 P θ1 Θ1 Q.

Definition a_sub_optimal
    (M : mode) (Θ0 : aenv) (P0 P : pskl)
    (θ1 : metasubst) (Θ1 : aenv) (Q : pskl) : Prop :=
  a_sub_solution M Θ0 P0 P θ1 Θ1 Q /\
  (forall θ Θ Q',
     a_sub_solution M Θ0 P0 P θ Θ Q' ->
     exists ζ, Θ1 ≤[ ζ ] Θ /\
               a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
               Θ ⊢ pskl_to_bskl_syn (msubst_pskl ζ Q) ≼ pskl_to_bskl_syn Q').

(* ===================================================================== *)
(*  Skeleton inference  (paper: Questions of skeleton inference).         *)
(* ===================================================================== *)

Definition a_pat_solution
    (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (θ1 : metasubst) (Θ1 : aenv) (P1 : pskl) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  (⌊ Θ1 ⌋ ⊢[ M ] e ⇨ (pskl_to_bskl_syn P1)) /\
  a_fillsyn Θ1 θ1 P0 (pskl_to_bskl_syn P1).

Definition a_pat_solution_ex (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp) : Prop :=
  exists θ1 Θ1 P1, a_pat_solution M Θ0 P0 e θ1 Θ1 P1.

Definition a_pat_optimal
    (M : mode) (Θ0 : aenv) (P0 : pskl) (e : exp)
    (θ1 : metasubst) (Θ1 : aenv) (P1 : pskl) : Prop :=
  a_pat_solution M Θ0 P0 e θ1 Θ1 P1 /\
  (forall θ Θ Q,
     a_pat_solution M Θ0 P0 e θ Θ Q ->
     exists ζ, Θ1 ≤[ ζ ] Θ /\
               a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
               Θ ⊢ pskl_to_bskl_syn (msubst_pskl ζ P1) ≼ pskl_to_bskl_syn Q).

(* ===================================================================== *)
(*  Type inference  (paper: Questions of type inference).  Output is a    *)
(*  [ptyp]; optimality uses type equivalence [ζ A ≡ B] (not precision).   *)
(* ===================================================================== *)

Definition a_typing_solution
    (M : mode) (Θ0 : aenv) (P : pskl) (e : exp)
    (θ1 : metasubst) (Θ1 : aenv) (A : ptyp) : Prop :=
  Θ0 ≤[ θ1 ] Θ1 /\
  (⌊ Θ1 ⌋ ⊢[ M ] e ⦂ (ptyp_to_btyp_syn A)) /\
  a_fillsyn Θ1 θ1 P (ptyp_to_bskl_inh A).

Definition a_typing_solution_ex (M : mode) (Θ0 : aenv) (P : pskl) (e : exp) : Prop :=
  exists θ1 Θ1 A, a_typing_solution M Θ0 P e θ1 Θ1 A.

Definition a_typing_optimal
    (M : mode) (Θ0 : aenv) (P : pskl) (e : exp)
    (θ1 : metasubst) (Θ1 : aenv) (A : ptyp) : Prop :=
  a_typing_solution M Θ0 P e θ1 Θ1 A /\
  (forall θ Θ B,
     a_typing_solution M Θ0 P e θ Θ B ->
     exists ζ, Θ1 ≤[ ζ ] Θ /\
               a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ /\
               Θ ⊢ msubst_ptyp ζ A ≡ᵗ B).
