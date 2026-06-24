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
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_question.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Declarative notions used in the solution / optimality statements.     *)
(*  [a_skel_split] removed — the real [a_split] (def_extra.v, now with the *)
(*  flex case) is the single splitting relation.                          *)
(* ===================================================================== *)

(* Context precision [Θ' ⪯ctx Θ]: same non-term-variable entries, every term
   variable more precise.  Now meaningful (derives from the real [a_precise]).
   FINDING F5: the paper has NO standalone context-precision relation — it
   expresses the notion via metasubstitution / information increase
   ([\inc], algorithmic.tex:133-209).  This is our reading; the
   [lemma:context-precision-skeleton] (proofs.tex:119-156, itself marked
   "TODO: check") should be cross-checked and back-ported. *)
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

(* [P] is a safe skeleton for a term under [Θ] and mode [M] (paper "Safe
   Skeleton", declarative.tex:1927-1931: P safe for M iff every type the
   term checks against is refined by [inh P]).  PLACEHOLDER (accept-all) —
   FINDING F7: the signature lacks the term [e], so the paper definition
   (which quantifies over the term's checking types) cannot be expressed
   here without a signature refactor of the bridge layer (the
   substitution-preservation lemmas below would thread [e] too).  Left as a
   flagged stub pending that refactor. *)
Inductive a_safe_skel : aenv -> mode -> pskl -> Prop :=
| a_safe_skel__any : forall Θ M P, a_safe_skel Θ M P.

(* [P] is a most-informative skeleton.  PLACEHOLDER (accept-all) — FINDING
   F7: "most-informative skeleton" is used only in paper lemma prose and is
   never formally defined; it also needs the term [e] (see [a_safe_skel]).
   Flagged stub pending a paper definition. *)
Inductive a_most_informative : aenv -> mode -> pskl -> Prop :=
| a_most_informative__any : forall Θ M P, a_most_informative Θ M P.

(* [Θ ⊢ A' ⊑poly A]: [A'] carries at least as much polymorphic information
   as [A] (paper [\morepoly]).  PLACEHOLDER (reflexive) — FINDING F6: the
   paper's [\morepoly] definition (algorithmic.tex:694-819, 10 rules) is
   currently inside an [\iffalse] block (disabled), yet "More information
   does not harm" depends on it.  Left reflexive pending the authors'
   decision to re-enable / finalise that definition. *)
Inductive a_morepoly : aenv -> btyp -> btyp -> Prop :=
| a_morepoly__refl : forall Θ A, a_morepoly Θ A A.

(* ===================================================================== *)
(*  Identity information increase.  Every algorithm produces the identity  *)
(*  metasubstitution between its input and output contexts; the reflexive  *)
(*  case [Θ ⊴ Θ] is the witness used by the soundness base cases.          *)
(* ===================================================================== *)

Lemma a_isub_refl : forall Θ, Θ ⊴ Θ.
Proof. Admitted.

(* Identity metasubstitution acts trivially on skeletons / types. *)
Lemma msubst_pskl_refl_hole : forall θ, msubst_pskl θ pskl_hole = pskl_hole.
Proof. induction θ as [|[α A] θ IH]; simpl; auto. Qed.

(* ===================================================================== *)
(*  Stability (paper Lemma: Stability) — every statement is preserved by  *)
(*  information increase [Θ₀ ≤ Θ₁].  One lemma per judgment.              *)
(* ===================================================================== *)

Lemma a_stable_d_typing : forall M Θ0 Θ1 e A,
    (⌊ Θ0 ⌋ ⊢[ M ] e ⦂ A) ->
    Θ0 ⊴ Θ1 ->
    (⌊ Θ1 ⌋ ⊢[ M ] e ⦂ A).
Proof. Admitted.

Lemma a_stable_d_pat : forall M Θ0 Θ1 e P,
    (⌊ Θ0 ⌋ ⊢[ M ] e ⇨ P) ->
    Θ0 ⊴ Θ1 ->
    (⌊ Θ1 ⌋ ⊢[ M ] e ⇨ P).
Proof. Admitted.

Lemma a_stable_d_sub : forall M Θ0 Θ1 C B,
    empty ⨟ ⌊ Θ0 ⌋ ⊢[ M ] C ⊑ B ->
    Θ0 ⊴ Θ1 ->
    empty ⨟ ⌊ Θ1 ⌋ ⊢[ M ] C ⊑ B.
Proof. Admitted.

Lemma a_stable_d_consis : forall Θ0 Θ1 C B,
    empty ⨟ ⌊ Θ0 ⌋ ⊨ C ≈ B ->
    Θ0 ⊴ Θ1 ->
    empty ⨟ ⌊ Θ1 ⌋ ⊨ C ≈ B.
Proof. Admitted.

Lemma a_stable_d_refine_syn : forall Θ0 Θ1 P Q,
    ⌊ Θ0 ⌋ ⨟ nil ⨟ nil ⊢ᵣ P ⊳ Q ->
    Θ0 ⊴ Θ1 ->
    ⌊ Θ1 ⌋ ⨟ nil ⨟ nil ⊢ᵣ P ⊳ Q.
Proof. Admitted.

(* ===================================================================== *)
(*  Structural rules (paper Lemma: Structural rules, rule SuffixMoving).  *)
(*  Contexts grow at the head in the locally-nameless encoding, so paper  *)
(*  [Θ₁,Θ₂,Ξ] is [Ξ ++ Θ₂ ++ Θ₁] and [Θ₁,Ξ,Θ₂] is [Θ₂ ++ Ξ ++ Θ₁].      *)
(* ===================================================================== *)

Lemma a_structural_suffix_moving : forall M Θ1 Θ2 Ξ e A,
    a_suffix Ξ ->
    (⌊ Ξ ++ Θ2 ++ Θ1 ⌋ ⊢[ M ] e ⦂ A) ->
    (⌊ Θ2 ++ Ξ ++ Θ1 ⌋ ⊢[ M ] e ⦂ A).
Proof. Admitted.

(* ===================================================================== *)
(*  Suffix erasure (paper Lemma: Suffix erasure).                         *)
(* ===================================================================== *)

Lemma a_suffix_erasure : forall M Θ Ξ e A,
    a_suffix Ξ ->
    (forall x, x `in` dom Ξ -> x `notin` ftvar_in_btyp A) ->
    (⌊ Ξ ++ Θ ⌋ ⊢[ M ] e ⦂ A) ->
    (⌊ Θ ⌋ ⊢[ M ] e ⦂ A).
Proof. Admitted.

(* ===================================================================== *)
(*  Splitting refines (paper Lemma: Splitting refines).                   *)
(* ===================================================================== *)

Lemma a_split_refine : forall Θ0 Θ1 P0 P Q,
    a_split Θ0 P0 P Q Θ1 ->
    ⌊ Θ1 ⌋ ⨟ nil ⨟ nil ⊢ᵣ
      (pskl_to_bskl_inh P0) ⊳ (pskl_to_bskl_inh (pskl_arrow P Q)).
Proof. Admitted.

(* ===================================================================== *)
(*  Consistency extends subtyping (paper Lemma: Consistency extends       *)
(*  subtyping).  If [C ~ B] and [C ⊑ Q] then [B ⊑ Q].                     *)
(* ===================================================================== *)

Lemma a_consis_extends_sub : forall M Θ C B Bq,
    empty ⨟ ⌊ Θ ⌋ ⊨ C ≈ B ->
    empty ⨟ ⌊ Θ ⌋ ⊢[ M ] C ⊑ Bq ->
    empty ⨟ ⌊ Θ ⌋ ⊢[ M ] (btyp_to_utyp_syn B) ⊑ Bq.
Proof. Admitted.

(* ===================================================================== *)
(*  Precision extends skeleton subtyping (paper Lemma: Precision extends   *)
(*  skeleton subtyping).                                                  *)
(* ===================================================================== *)

Lemma a_precision_extends_sub : forall M Θ P P' Q,
    Θ ⊢ (pskl_to_bskl_syn P') ≼ (pskl_to_bskl_syn P) ->
    empty ⨟ ⌊ Θ ⌋ ⊢ₛ[ M ] (bskl_to_uskl (pskl_to_bskl_syn P)) ⊑ Q ->
    empty ⨟ ⌊ Θ ⌋ ⊢ₛ[ M ] (bskl_to_uskl (pskl_to_bskl_syn P')) ⊑ Q.
Proof. Admitted.

(* ===================================================================== *)
(*  Inherited refinement gives precision (paper Lemma: Inherited           *)
(*  refinement gives precision).                                          *)
(* ===================================================================== *)

Lemma a_inherited_refinement_precision : forall Θ P Q,
    ⌊ Θ ⌋ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh Q) ->
    Θ ⊢ (pskl_to_bskl_syn P) ≼ (pskl_to_bskl_syn Q).
Proof. Admitted.

(* ===================================================================== *)
(*  Context precision for skeleton inference (paper Lemma: Context         *)
(*  precision for skeleton inference).                                    *)
(* ===================================================================== *)

Lemma a_context_precision_skeleton : forall M Θ Θ' P e Q,
    a_ctx_precise Θ' Θ ->
    (⌊ Θ ⌋ ⊢[ M ] e ⇨ Q) ->
    ⌊ Θ ⌋ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Q ->
    exists Q',
      (⌊ Θ' ⌋ ⊢[ M ] e ⇨ Q') /\
      ⌊ Θ' ⌋ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Q' /\
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
    (⌊ Θ ⌋ ⊢[ M ] e ⦂ A) ->
    a_morepoly Θ A' A ->
    (⌊ Θ ⌋ ⊢[ M ] e ⦂ A').
Proof. Admitted.
