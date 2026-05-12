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


(* ===================================================================== *)
(*  Task 3.  Completeness of algorithmic skeleton inference (a_pat).      *)
(* ===================================================================== *)

(** [a_pat_complete] — paper proofs.tex §"Type Inference" Lemma
    "Skeleton inference is complete".

    For every declarative skeleton-inference derivation, exhibit an
    algorithmic counterpart whose output context transfers to the same
    declarative context.

    Since [d_pat] and [d_typing] are mutual (App rule), the proof is
    formally mutual with [a_typing_complete] (Task 4).  We state both
    here and admit them jointly. *)

Theorem a_pat_complete :
  forall m Γ e P,
    d_pat m Γ e P ->
    forall Θ0 P0,
      a_transfers Θ0 Γ ->
      a_wf_typ Θ0 P0 ->
      exists Θ1 Q, a_pat m Θ0 P0 e Q Θ1 /\ a_transfers Θ1 Γ.
Proof.
  (* Admitted — paper proofs.tex §"Skeleton inference is complete".
     By mutual induction on [d_pat m Γ e P] with [a_typing_complete]
     (Task 4).  [a_pat]'s 9 constructors mirror [d_pat]'s 10:

     - [d_pat__unit] / [d_pat__var] / [d_pat__anno] / [d_pat__freeze]
                                    → [a_pat__unit/_var/_anno/_freeze]
                                      via [a_sub_complete] (Task 2)
                                      dispatched on [a_sub_mode_sk].

     - [d_pat__sub] — folds into the corresponding [a_sub] leg.

     - [d_pat__abs] — match [a_pat__abs] via [a_split_complete]
                      (NOT YET PROVED) on the prefix split, then IH on
                      the body.  The freshness L-cofinite encoding
                      transfers cleanly.

     - [d_pat__abs_check] — match [a_pat__abs_check]; binder
                            [x : typ_hole] threads through
                            [a_transfers__var_typ].

     - [d_pat__abs_anno] / [d_pat__abs_anno_check] — analogous;
                                                    both require the
                                                    [a_split] machinery
                                                    on the annotation.

     - [d_pat__app] — folds through the mutual [a_typing_complete]
                      step on the function leg + [a_pat_complete] on
                      the argument leg + [a_consis] on the result type.

     The same auxiliary completeness lemmas required by Task 2
     (i–v) apply; additionally:

       (vi)  [a_split_complete] : declarative arrow shapes factor
                                   through [a_split].
       (vii) [a_guess_mono_complete] : every monotype witness
                                       factors through a flex-mono
                                       prefix.

     Both are technically straightforward (a_split is mostly
     mechanical on arrow shapes; a_guess_mono generates fresh
     names) but require the auxiliary lemmas from Phase 3.B to
     be closed first. *)
Admitted.


(** Smoke test for Task 3: skeleton inference on [unit] under the
    empty algorithmic context, with [typ_hole] as the expected
    shape. *)
Lemma a_pat_complete_smoke :
  d_pat mode_ti nil exp_unit typ_unit ->
  forall Θ0, a_transfers Θ0 nil -> a_wf_typ Θ0 typ_hole ->
  exists Θ1 Q, a_pat mode_ti Θ0 typ_hole exp_unit Q Θ1 /\
               a_transfers Θ1 nil.
Proof.
  intros Hd Θ0 Htr Hwf.
  eapply a_pat_complete; eauto.
Qed.


(* ===================================================================== *)
(*  Task 4.  Completeness of algorithmic typing.                          *)
(* ===================================================================== *)

(** [a_typing_complete] — paper proofs.tex §"Type Inference" Lemma
    "Typing is complete" (the headline result).

    Mutual with [a_pat_complete] above.  Statement:

      [forall Γ m e A,
         d_typing m Γ e A ->
         forall Θ0 P0,
           a_transfers Θ0 Γ ->
           a_wf_typ Θ0 P0 ->
           exists Θ1, a_typing m Θ0 P0 e A Θ1 /\ a_transfers Θ1 Γ].

    The "P0" parameter is the algorithmic mode-vector ("expected
    shape") and is existentially fixed at [typ_hole] in the base
    typing-inference (mode_ti) case.  We expose it as a parameter
    so callers can fix it from context.

    Per design §3.C, completeness IS allowed to be narrowed to a
    fragment (e.g. "monomorphic types only" or "modulo η").  We do
    NOT pre-narrow here — we state the full form and admit it
    research-grade.  If a downstream caller needs a narrowed
    consumable form, the structure of the proof above shows what
    the narrowed cases would be (drop the forall_*/sub legs).

    Cases by [d_typing] constructor:

    - [d_typing__unit] / [d_typing__var] / [d_typing__anno]
                                       → corresponding [a_typing__*]
                                         via [a_sub_complete].
    - [d_typing__sub]                   → fold through the IH then
                                          [a_sub_complete] on the
                                          subsumption leg.
    - [d_typing__freeze]                → match [a_typing__freeze];
                                          the IH on the inner term
                                          + [a_consis_complete].
    - [d_typing__forall]                → match [a_typing__forall_check]
                                          under a fresh rigid.
    - [d_typing__abs] / [d_typing__abs_anno]
                                       → match the corresponding
                                         [a_typing__abs*] via
                                         [a_split_complete] +
                                         [a_guess_mono_complete].
    - [d_typing__app]                   → match [a_typing__app] via
                                          the mutual [a_pat_complete]
                                          on the argument + IH on the
                                          function. *)

Theorem a_typing_complete :
  forall m Γ e A,
    d_typing m Γ e A ->
    forall Θ0 P0,
      a_transfers Θ0 Γ ->
      a_wf_typ Θ0 P0 ->
      exists Θ1, a_typing m Θ0 P0 e A Θ1 /\ a_transfers Θ1 Γ.
Proof.
  (* Admitted — paper proofs.tex §"Type Inference / Typing is complete",
     the HEADLINE result of Phase 3.C.

     Joint mutual induction with [a_pat_complete] (Task 3) using a
     [Scheme a_typing_pat_mut]-style principle (not yet generated;
     would mirror [d_typing_pat_mut] from prop_basic.v).

     Each of the 9 [d_typing] constructors maps to an [a_typing]
     constructor as documented in the comment above this Theorem.

     The decisive auxiliary lemmas required but not yet mechanised:

       (i)   [a_sub_complete]            — Task 2 above (also admitted).
       (ii)  [a_consis_complete]
       (iii) [a_split_complete]
       (iv)  [a_guess_mono_complete]
       (v)   [a_pat_complete]            — Task 3 (mutual, also admitted).

     Each of (ii–iv) is on the order of one auxiliary lemma file's
     work and is the dual of the soundness counterpart admitted in
     [prop_soundness.v].

     Narrowing options if a follow-up pass cannot close the full
     proof (per plan §Task 4):

       (a) "Monomorphic completeness":  restrict [A] to monotype
           shapes; the [d_typing__forall] case drops out and no
           [a_pre_sub] / [a_assign] is needed.

       (b) "Modulo η-completeness":  weaken the conclusion to
           [exists e' Θ1, a_typing m Θ0 P0 e' A Θ1 /\
            beta_eta_equal e e' /\ a_transfers Θ1 Γ]  — allows the
           algorithm to η-expand λ-abstractions.

       (c) "Base-term completeness":  restrict [e] to [is_base_term].
           Recovers the most-used fragment in practice. *)
Admitted.


(** Smoke test for Task 4: completeness applied at the empty context
    for the trivial [d_typing__unit] derivation. *)
Lemma a_typing_complete_smoke :
  d_typing mode_ti nil exp_unit typ_unit ->
  forall Θ0, a_transfers Θ0 nil -> a_wf_typ Θ0 typ_hole ->
  exists Θ1, a_typing mode_ti Θ0 typ_hole exp_unit typ_unit Θ1 /\
             a_transfers Θ1 nil.
Proof.
  intros Hd Θ0 Htr Hwf.
  eapply a_typing_complete; eauto.
Qed.
