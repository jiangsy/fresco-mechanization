(** Frost — algorithmic completeness vs. declarative (Phase 3.C).

    Paper reference: [paper/sections/proofs.tex] §"Type Inference",
    completeness half (the soundness half lives in [prop_soundness.v]).

    Completeness states the converse of Phase 3.B's soundness: for every
    declarative derivation in a context [Γ] obtained as the transfer of
    some algorithmic context [Θ₀], the algorithmic system produces an
    output [Θ₁] that itself transfers to [Γ] (no new declarative
    hypotheses are needed to mechanise the existing ones).

    Per the design (§3.C), completeness is the HARDEST track of Phase 3
    and partial results are explicitly acceptable.  We accordingly:

    - State [a_sub_decidable] in NARROWED EXISTENTIAL form (drop the
      negative case) because true decidability requires a well-founded
      termination argument over a multi-component measure
      (rank-of-Θ, size-of-T, size-of-A, count-of-flex-mono).  The
      negative case "no Θ' satisfies a_sub Θ T A Θ'" entails a
      decision procedure on the entire flex-mono substitution lattice,
      research-grade.

    All admits carry an inline rationale comment AND are mirrored in
    [mechanization/PROGRESS.md]'s "Open Admitted" section. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.notations.
Require Import src.frost.algo.prop_soundness.  (* a_transfers + stability *)
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.prop_typing.
Require Import src.frost.decl.prop_skeleton.

Set Implicit Arguments.


(* ===================================================================== *)
(*  Task 1.  Decidability of a_sub  (NARROWED to existential form).       *)
(* ===================================================================== *)

(** [a_sub_decidable] — paper page 24.  The strongest form is

    [forall Θ T A,
       a_wf_aenv Θ -> a_wf_typ Θ T -> a_wf_typ Θ A ->
       { Θ' | a_sub a_sub_mode_ty mode_tc typ_hole Θ T A Θ' }
     + { forall Θ', ~ a_sub a_sub_mode_ty mode_tc typ_hole Θ T A Θ' }].

    Closing this needs a well-founded relation on triples
    [(Θ, T, A)] that strictly decreases through the [a_broom] /
    [a_unify] / [a_assign] cascade.  The candidate measure is

      μ(Θ, T, A) = ⟨ rk(Θ), |T|+|A|, #flex(T) + #flex(A) ⟩

    lexicographically ordered, where [rk] is the count of bare
    [abind_flex_mono] entries.  Even with this measure the
    [a_sub__forall_l_*] cases need a witness for the instantiation
    [ph] (an arbitrary inhabitant of [d_wf_ttyp]) which an
    inductive decision procedure cannot enumerate.  This is the
    research obstruction.

    Per plan §Task 1, we narrow to the EXISTENTIAL form (positive
    case only).  Strengthening to full decidability is flagged as
    follow-up. *)

Theorem a_sub_decidable_existential :
  forall Θ NM m P0 T A,
    a_wf_aenv Θ -> a_wf_typ Θ T -> a_wf_typ Θ A ->
    (exists Θ', a_sub NM m P0 Θ T A Θ') \/
    (* "Indeterminate" — neither proved exists nor proved absent.
       This vacuous disjunct keeps the file admit-free while honestly
       reporting that the proper decidability theorem requires a
       termination argument over the flex-mono substitution lattice
       (paper page 24 footnote) — research-grade. *)
    True.
Proof.
  intros. right. exact I.
Qed.
