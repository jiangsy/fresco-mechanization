(** Soundness of the algorithmic system (paper [algorithmic.tex] /
    [proofs.tex] / [subtyping-proofs.tex]).

    Each algorithmic judgment, when it succeeds, yields a *solution* to
    the corresponding question (in the sense of [def_question.v]): the
    output context is an information increase of the input, and the
    declarative judgment holds under the projected context [⌊Θ⌋] together
    with the inherited-refinement side condition.  The algorithm is
    uncoloured ([ptyp]/[pskl]); painting to the declarative sorts happens
    inside the solution predicates.  Proofs are [Admitted] scaffolding. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.notations.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_question.
Require Import src.frost.algo.prop_lemmas.

Set Implicit Arguments.

(* Soundness of consistency (paper Lemma: Soundness of consistency). *)
Theorem a_consis_sound : forall Θ0 P0 P Q Θ1,
    a_consis Θ0 P0 P Q Θ1 ->
    exists θ1, a_consis_solution Θ0 P0 P θ1 Θ1 Q.
Proof. Admitted.

(* Soundness of subtyping (paper Theorem / subtyping-proofs.tex).
   Proof scaffolding: induction on the algorithmic derivation, one
   obligation per rule.  Each case must (1) exhibit the identity
   metasubstitution [θ₁] for [Θ₀ ≤[θ₁] Θ₁], (2) build the declarative
   skeleton subtyping [d_pat_sub] under [⌊Θ₁⌋], and (3) discharge the
   inherited-refinement side condition [a_fillsyn]. *)
Theorem a_sub_sound : forall NM M P0 Θ0 P Q Θ1,
    a_sub NM M P0 Θ0 P Q Θ1 ->
    exists θ1, a_sub_solution M Θ0 P0 P θ1 Θ1 Q.
Proof.
  intros NM M P0 Θ0 P Q Θ1 Hsub.
  induction Hsub.
  - (* Infer  [⊢_{ti;□} P ⊑ P ⊣ Θ₀]: identity increase; the painted
       [d_pat_sub] is reflexive ti-mode subtyping; [a_fillsyn] refines the
       hole [□] (= [msubst_pskl θ₁ □]) to [P].  Needs [a_isub_refl],
       [msubst_pskl_refl_hole], d_pat_sub reflexivity, d_refine hole. *)
    admit.
  - (* Check  [⊢_{TY;TC;B} A ⊑ B]: from soundness of consistency
       ([a_consis_chk] ⇒ [d_pat_consis]) + the [Check] subtyping rule
       (paper subtyping-proofs.tex, Check case). *)
    admit.
  - (* ForallR: extend the context with [α], apply the IH, repackage the
       output dropping the suffix [Ξ]. *)
    admit.
  - (* UnivGhostR  [⊢_{SK;TC;□} P ⊑ ⫯.P]: identity increase; refinement
       fills the universal ghost. *)
    admit.
  - (* Arrow: compose consistency soundness on the argument with the IH on
       the result; the join outputs [Q₁→Q₂]. *)
    admit.
  - (* Ghost  [⊢_{SK;M;P₀} □ ⊑ P₀]: identity increase. *)
    admit.
  - (* UnivGhostL: strip the universal ghost on the left and apply the IH. *)
    admit.
Admitted.

(* Soundness of skeleton inference (paper Theorem). *)
Theorem a_pat_sound : forall M Θ0 P0 e P Θ1,
    a_pat M Θ0 P0 e P Θ1 ->
    exists θ1, a_pat_solution M Θ0 P0 e θ1 Θ1 P.
Proof. Admitted.

(* Soundness of type inference (paper Theorem: Soundness of type inference). *)
Theorem a_typing_sound : forall M Θ0 P e A Θ1,
    a_typing M Θ0 P e A Θ1 ->
    exists θ1, a_typing_solution M Θ0 P e θ1 Θ1 A.
Proof. Admitted.
