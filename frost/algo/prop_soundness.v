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
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_question.
Require Import src.frost.algo.prop_lemmas.

Set Implicit Arguments.

(* Algorithmic judgments are written with the [⊢ₐ[ … ]] notation
   ([algo/def_extra.v], paper algorithmic.tex with the [ₐ]-subscripted
   turnstile); the declarative readings live inside the opaque [*_solution]
   predicates ([def_question.v]). *)

(* Soundness of consistency (paper Lemma: Soundness of consistency). *)
Theorem a_consis_sound : forall Θ0 P0 P Q Θ1,
    Θ0 ⊢ₐ[ P0 ] P ~ᴬ Q ⊣ Θ1 ->
    exists θ1, a_consis_solution Θ0 P0 P θ1 Θ1 Q.
Proof. Admitted.

(* Soundness of subtyping (paper Theorem / subtyping-proofs.tex).
   Proof scaffolding: induction on the algorithmic derivation, one
   obligation per rule.  Each case must (1) exhibit the identity
   metasubstitution [θ₁] for [Θ₀ ≤[θ₁] Θ₁], (2) build the declarative
   skeleton subtyping [d_pat_sub] under [⌊Θ₁⌋], and (3) discharge the
   inherited-refinement side condition [a_fillsyn]. *)
Theorem a_sub_sound : forall NM M P0 Θ0 P Q Θ1,
    Θ0 ⊢ₐ[ NM | M | P0 ] P ⊑ᴬ Q ⊣ Θ1 ->
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

(* Soundness of SKELETON inference (paper Theorem, proofs.tex:1421-1702).
   SCAFFOLDING.  [a_pat] is SELF-CONTAINED (paper [\pilab{App}] skeleton-infers
   the function — [a_pat] only calls [a_pat], F20), so induction on [a_pat]
   alone.  Driven by subtyping / consistency soundness ([a_sub_sound] /
   [a_consis_sound], the "subtyping admit") + the structural lemmas — admitted. *)
Theorem a_pat_sound : forall M Θ0 P0 e P Θ1,
    Θ0 ⊢ₐ[ M ; P0 ] e ⇨ P ⊣ Θ1 ->
    exists θ1, a_pat_solution M Θ0 P0 e θ1 Θ1 P.
Proof.
  intros M Θ0 P0 e P Θ1 H. induction H.
  - (* Unit *) admit.
  - (* Var (type-bound) *) admit.
  - (* Var (skeleton-bound) *) admit.
  - (* Anno *) admit.
  - (* Freeze *) admit.
  - (* Abs *) admit.
  - (* AbsCheck *) admit.
  - (* AbsAnno *) admit.
  - (* AbsAnnoCheck *) admit.
  - (* App: BOTH premises are [a_pat] (skeleton-infer arg + function); compose
       their IHs (no [a_typing] — see F20). *)
    admit.
Admitted.

(* Soundness of TYPE inference (paper Theorem, proofs.tex:175-593).
   SCAFFOLDING.  Induction on [a_typing]; the App case uses [a_pat_sound] for
   the argument-skeleton premise (the only cross-judgement dependency).  Per
   WT's paper proofs, driven by subtyping / consistency soundness, stability,
   splitting-refines and identity increase — admitted. *)
Theorem a_typing_sound : forall M Θ0 P e A Θ1,
    Θ0 ⊢ₐ[ M ; P ] e ⦂ A ⊣ Θ1 ->
    exists θ1, a_typing_solution M Θ0 P e θ1 Θ1 A.
Proof.
  intros M Θ0 P e A Θ1 H. induction H.
  - (* Unit: identity increase; declarative Unit + subtyping soundness; fillsyn. *)
    admit.
  - (* Var: declarative Var + subtyping soundness on the looked-up A. *)
    admit.
  - (* Anno: IH on the annotation check (tc) + subtyping soundness. *)
    admit.
  - (* Freeze: IH (ti) + consistency soundness (the join). *)
    admit.
  - (* Abs (M≠TC): split P0, guessMono, body IH; splitting-refines for fillsyn. *)
    admit.
  - (* AbsAnno (M≠TC): split + domain consistency soundness + body IH. *)
    admit.
  - (* AbsCheck (TC): check-mode λ under the inherited skeleton; body IH. *)
    admit.
  - (* AbsAnnoCheck (TC): domain consistency soundness + body IH. *)
    admit.
  - (* App: a_pat_sound (argument skeleton) + a_typing IH (function) +
       a_typing IH (argument re-check); compose via refinement + stability. *)
    admit.
Admitted.
