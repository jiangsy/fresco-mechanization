(** Auxiliary lemmas for the algorithmic metatheory.

    Scaffolding for the lemmas in [paper/sections/proofs.tex] §"Lemmas"
    (and the two substitution lemmas just before §"Skeleton Inference").
    Every lemma is stated faithfully against the metasubstitution /
    projection infrastructure ([def_meta.v]) and the question/solution
    layer ([def_question.v]); proofs are [Admitted] and tagged with the
    paper label.

    A handful of declarative notions the paper relies on are not yet
    mechanised (skeleton precision, context precision, safe / most-
    informative skeletons, the poly-information order, skeleton
    splitting).  They are introduced here as clearly-marked PLACEHOLDER
    predicates so the lemma statements type-check; replace them with the
    real relations when mechanising the proofs. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.notations.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_question.

Set Implicit Arguments.

(* ===================================================================== *)
(*  PLACEHOLDER predicates for unmechanised paper notions.                *)
(* ===================================================================== *)

(* Context precision [Θ' ⪯ctx Θ] (paper Definition: Context precision):
   same non-term-variable entries, every term variable more precise. *)
Inductive a_ctx_precise : aenv -> aenv -> Prop :=
| a_ctx_precise__nil :
    a_ctx_precise nil nil
| a_ctx_precise__other : forall Θ' Θ x b,
    (forall A, b <> abind_var_typ A) ->
    a_ctx_precise Θ' Θ ->
    a_ctx_precise ((x ~ b) ++ Θ') ((x ~ b) ++ Θ)
| a_ctx_precise__var : forall Θ' Θ x A' A,
    a_ctx_precise Θ' Θ ->
    a_precise Θ' (pskl_to_bskl_syn (ptyp_to_pskl A'))
                 (pskl_to_bskl_syn (ptyp_to_pskl A)) ->
    a_ctx_precise ((x ~ abind_var_typ A') ++ Θ') ((x ~ abind_var_typ A) ++ Θ).

(* [P] is a safe skeleton for [e] under [Θ] and mode [M] (paper "Safe"). *)
Inductive a_safe_skel : aenv -> mode -> pskl -> Prop :=
| a_safe_skel__any : forall Θ M P, a_safe_skel Θ M P.

(* [P] is a most-informative skeleton for [e] under [Θ] and mode [M]
   (paper "most informative"). *)
Inductive a_most_informative : aenv -> mode -> pskl -> Prop :=
| a_most_informative__any : forall Θ M P, a_most_informative Θ M P.

(* [Θ ⊢ A' ⊑poly A]: [A'] carries at least as much polymorphic
   information as [A] (paper [\morepoly]). *)
Inductive a_morepoly : aenv -> btyp -> btyp -> Prop :=
| a_morepoly__refl : forall Θ A, a_morepoly Θ A A.

(* Skeleton splitting [mov Θ₀ (split P₀ P₁) Θ₁] (paper [split]). *)
Inductive a_skel_split : aenv -> pskl -> pskl -> aenv -> Prop :=
| a_skel_split__refl : forall Θ P, a_skel_split Θ P P Θ.

(* ===================================================================== *)
(*  Stability (paper Lemma: Stability) — every statement is preserved by  *)
(*  information increase [Θ₀ ≤ Θ₁].  One lemma per judgment.              *)
(* ===================================================================== *)

Lemma a_stable_d_typing : forall M Θ0 Θ1 e A,
    d_typing M ⌊ Θ0 ⌋ e A ->
    Θ0 ⊴ Θ1 ->
    d_typing M ⌊ Θ1 ⌋ e A.
Proof. Admitted.

Lemma a_stable_d_pat : forall M Θ0 Θ1 e P,
    d_pat M ⌊ Θ0 ⌋ e P ->
    Θ0 ⊴ Θ1 ->
    d_pat M ⌊ Θ1 ⌋ e P.
Proof. Admitted.

Lemma a_stable_d_sub : forall M Θ0 Θ1 C B,
    d_sub M empty ⌊ Θ0 ⌋ C B ->
    Θ0 ⊴ Θ1 ->
    d_sub M empty ⌊ Θ1 ⌋ C B.
Proof. Admitted.

Lemma a_stable_d_consis : forall Θ0 Θ1 C B,
    d_consis empty ⌊ Θ0 ⌋ C B ->
    Θ0 ⊴ Θ1 ->
    d_consis empty ⌊ Θ1 ⌋ C B.
Proof. Admitted.

Lemma a_stable_d_refine_syn : forall Θ0 Θ1 P Q,
    d_refine_syn nil ⌊ Θ0 ⌋ P Q ->
    Θ0 ⊴ Θ1 ->
    d_refine_syn nil ⌊ Θ1 ⌋ P Q.
Proof. Admitted.

(* ===================================================================== *)
(*  Structural rules (paper Lemma: Structural rules, rule SuffixMoving).  *)
(*  Contexts grow at the head in the locally-nameless encoding, so paper  *)
(*  [Θ₁,Θ₂,Ξ] is [Ξ ++ Θ₂ ++ Θ₁] and [Θ₁,Ξ,Θ₂] is [Θ₂ ++ Ξ ++ Θ₁].      *)
(* ===================================================================== *)

Lemma a_structural_suffix_moving : forall M Θ1 Θ2 Ξ e A,
    a_suffix Ξ ->
    d_typing M ⌊ Ξ ++ Θ2 ++ Θ1 ⌋ e A ->
    d_typing M ⌊ Θ2 ++ Ξ ++ Θ1 ⌋ e A.
Proof. Admitted.

(* ===================================================================== *)
(*  Suffix erasure (paper Lemma: Suffix erasure).                         *)
(* ===================================================================== *)

Lemma a_suffix_erasure : forall M Θ Ξ e A,
    a_suffix Ξ ->
    (forall x, x `in` dom Ξ -> x `notin` ftvar_in_btyp A) ->
    d_typing M ⌊ Ξ ++ Θ ⌋ e A ->
    d_typing M ⌊ Θ ⌋ e A.
Proof. Admitted.

(* ===================================================================== *)
(*  Splitting refines (paper Lemma: Splitting refines).                   *)
(* ===================================================================== *)

Lemma a_split_refine : forall Θ0 Θ1 P0 P1,
    a_skel_split Θ0 P0 P1 Θ1 ->
    d_refine_syn nil ⌊ Θ1 ⌋
      (pskl_to_bskl_inh P0) (pskl_to_bskl_inh P1).
Proof. Admitted.

(* ===================================================================== *)
(*  Consistency extends subtyping (paper Lemma: Consistency extends       *)
(*  subtyping).  If [C ~ B] and [C ⊑ Q] then [B ⊑ Q].                     *)
(* ===================================================================== *)

Lemma a_consis_extends_sub : forall M Θ C B Bq,
    d_consis empty ⌊ Θ ⌋ C B ->
    d_sub M empty ⌊ Θ ⌋ C Bq ->
    d_sub M empty ⌊ Θ ⌋ (btyp_to_utyp_syn B) Bq.
Proof. Admitted.

(* ===================================================================== *)
(*  Precision extends skeleton subtyping (paper Lemma: Precision extends   *)
(*  skeleton subtyping).                                                  *)
(* ===================================================================== *)

Lemma a_precision_extends_sub : forall M Θ P P' Q,
    a_precise Θ (pskl_to_bskl_syn P') (pskl_to_bskl_syn P) ->
    d_pat_sub M nil ⌊ Θ ⌋ (bskl_to_uskl (pskl_to_bskl_syn P)) Q ->
    d_pat_sub M nil ⌊ Θ ⌋ (bskl_to_uskl (pskl_to_bskl_syn P')) Q.
Proof. Admitted.

(* ===================================================================== *)
(*  Inherited refinement gives precision (paper Lemma: Inherited           *)
(*  refinement gives precision).                                          *)
(* ===================================================================== *)

Lemma a_inherited_refinement_precision : forall Θ P Q,
    d_refine_syn nil ⌊ Θ ⌋ (pskl_to_bskl_inh P) (pskl_to_bskl_inh Q) ->
    a_precise Θ (pskl_to_bskl_syn P) (pskl_to_bskl_syn Q).
Proof. Admitted.

(* ===================================================================== *)
(*  Context precision for skeleton inference (paper Lemma: Context         *)
(*  precision for skeleton inference).                                    *)
(* ===================================================================== *)

Lemma a_context_precision_skeleton : forall M Θ Θ' P e Q,
    a_ctx_precise Θ' Θ ->
    d_pat M ⌊ Θ ⌋ e Q ->
    d_refine_syn nil ⌊ Θ ⌋ (pskl_to_bskl_inh P) Q ->
    exists Q',
      d_pat M ⌊ Θ' ⌋ e Q' /\
      d_refine_syn nil ⌊ Θ' ⌋ (pskl_to_bskl_inh P) Q' /\
      a_precise Θ' Q' Q.
Proof. Admitted.

(* ===================================================================== *)
(*  Substitution preserves safety / informativeness (paper Lemmas).       *)
(* ===================================================================== *)

Lemma a_subst_preserves_safety : forall Θ Θ' θ M P,
    a_safe_skel Θ M P ->
    Θ ≤[ θ ] Θ' ->
    a_mono_aenv Θ ->
    a_mono_aenv Θ' ->
    a_safe_skel Θ' M (msubst_pskl θ P).
Proof. Admitted.

Lemma a_subst_preserves_informativeness : forall Θ Θ' θ M P,
    a_most_informative Θ M P ->
    Θ ≤[ θ ] Θ' ->
    a_mono_aenv Θ ->
    a_mono_aenv Θ' ->
    a_most_informative Θ' M (msubst_pskl θ P).
Proof. Admitted.

(* ===================================================================== *)
(*  More information does not harm (paper Lemma: More information does     *)
(*  not harm).                                                            *)
(* ===================================================================== *)

Lemma a_more_information_no_harm : forall M Θ e A A',
    d_typing M ⌊ Θ ⌋ e A ->
    a_morepoly Θ A' A ->
    d_typing M ⌊ Θ ⌋ e A'.
Proof. Admitted.
