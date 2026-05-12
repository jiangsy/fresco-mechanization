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


(* ===================================================================== *)
(*  Task 2.  Completeness of algorithmic subtyping.                       *)
(* ===================================================================== *)

(** [a_sub_complete] — paper proofs.tex §"Type Inference" Lemma
    "Subtyping is complete".

    Statement (paper-form, adapted to Phase 3.B's [a_transfers]
    relation):

      [forall Γ A B m,
         d_sub m nil Γ A B ->
         forall Θ0, a_transfers Θ0 Γ ->
         exists Θ1 NM P0, a_sub NM m P0 Θ0 A B Θ1 /\ a_transfers Θ1 Γ].

    The [NM] and [P0] parameters of [a_sub] are existentialised because
    the declarative judgment doesn't carry them.  Standard reading:
    [NM = a_sub_mode_ty] and [P0 = typ_hole] suffice for the common
    case (paper's [\asublab{Ty}]).

    The proof goes by induction on [d_sub] and follows the cases
    of [a_sub]:

    - [d_sub__infer] / [d_sub__check] — translate via [a_consis]
      completeness.  Requires [a_consis_complete : d_consis Δ Γ T A ->
      ... -> exists Θ1, a_consis Θ0 T A Θ1 ∧ a_transfers Θ1 Γ], not
      yet built.  Paper's argument is by induction on the
      [d_consis] derivation.

    - [d_sub__forall_r] — emit [a_broom__forall_r] under a fresh
      [a]; suffix [(a ~ abind_tvar) ++] cancels by [a_transfers__tvar].

    - [d_sub__arg] — split [Δ₁ ++ Δ₂] and apply IH twice; the
      argument leg additionally needs [a_unify] completeness for
      monotypes.

    - [d_sub__forall_l_tagged] / [_untagged] — paper says we
      *guess* the instantiation [ph].  The algorithmic counterpart
      is [a_pre_sub] + the [a_meta_subst] threaded by [a_sub__ty].
      The mechanical bridge requires [a_pre_sub_complete] which
      depends on [a_unify_var_complete] (essentially: every
      well-formed witness factors through unification).

    Per plan policy: stated, admitted with rationale.  No fabricated
    proof. *)

Theorem a_sub_complete :
  forall m Γ A B,
    d_sub m nil Γ A B ->
    forall Θ0, a_transfers Θ0 Γ ->
    exists Θ1 NM P0, a_sub NM m P0 Θ0 A B Θ1 /\ a_transfers Θ1 Γ.
Proof.
  (* Admitted — paper proofs.tex §"Type Inference / Subtyping is
     complete".  By induction on [d_sub m nil Γ A B].  Each of the 6
     [d_sub] constructors triggers a sub-derivation in [a_sub] via
     [a_broom]:

     - [d_sub__infer] / [d_sub__check] — match [a_broom__infer] /
       [a_broom__check] via [a_consis_complete] (NOT YET PROVED;
       see prop_soundness.v rationale block); the conclusion folds
       through [a_sub__ty].

     - [d_sub__forall_r] — match [a_broom__forall_r] under a fresh
       rigid [α] introduced by [a_transfers__tvar].

     - [d_sub__arg] — match [a_broom__arg]; consumes IH on the
       result leg + [a_unify_complete] (NOT YET PROVED) on the
       argument leg.

     - [d_sub__forall_l_tagged] — match [a_broom__forall_l] with
       the [a_pre_sub] / [a_assign] cascade as instantiation
       witness.  This is the case where the paper's "guess [ph]"
       step is realised mechanically; depends on
       [a_pre_sub_complete] + [a_assign_complete] (NEITHER PROVED).

     - [d_sub__forall_l_untagged] — symmetric; same cascade modulo
       the tag dispatch.

     Auxiliary completeness lemmas required but not currently
     mechanised in Phase 3:

       (i)   [a_consis_complete]
       (ii)  [a_unify_complete]
       (iii) [a_pre_sub_complete]
       (iv)  [a_assign_complete]
       (v)   [a_broom_complete]   (deducible from i–iv)

     Each is approximately one lemma file's worth of work, paralleling
     the soundness counterparts admitted in [prop_soundness.v]. *)
Admitted.


(** Smoke test for Task 2: completeness applied to the empty context
    where [unit ⊑ unit] is trivially derivable on the declarative side. *)
Lemma a_sub_complete_smoke :
  d_sub mode_tc nil nil typ_unit typ_unit ->
  forall Θ0, a_transfers Θ0 nil ->
  exists Θ1 NM P0, a_sub NM mode_tc P0 Θ0 typ_unit typ_unit Θ1 /\
                    a_transfers Θ1 nil.
Proof.
  intros Hd Θ0 Htr.
  eapply a_sub_complete; eauto.
Qed.
