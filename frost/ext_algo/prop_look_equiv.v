(** THE EXTRACT LEVEL'S FOUNDATIONS — structure facts about the look
    judgements' collections and the fold, feeding §8c.9's b-core (the
    fused look-pair/fold-transport lemma; docs/
    HANDOFF-extractable-algo-encoding.md §8c.9).

    The collection is NOT deterministic up to renaming
    (cex/cex_looksub_not_det.v), but two derivations of the same look
    node differ ONLY by fresh names, by the ∀-peel slack at the final
    sub-constraint, and by ◇-EMISSION slack ([≼m ◇] / [eq ◇] vs
    nothing) — and a ◇-target solve step is the IDENTITY, which is what
    makes the slack free to transport.  This file proves the four
    foundation facts of that inventory:

    §1  a lookeq collection is PURE-EQ (so LS-Arrow's left half never
        contributes a sub-constraint, and the fold of [𝒞1 ++ 𝒞2]
        decomposes at the seam);
    §2  an α-FREE subject collects NOTHING, through EVERY derivation
        (crossing 4 of §8c.9's inventory: LS/LE-Absent vs a structural
        derivation is no slack at all);
    §3  a ◇-TARGET solve step is the identity — nil block, pattern
        through — on both layers (crossing 3: the ◇-emission slack);
    §4  the fold's head inversions and the PURE-EQ APPEND DECOMPOSITION
        [a_solve_cstr_app_inv], the mirror of [a_solve_cstr_app]
        (algo/sub/look/prop_eq_cstr.v) that the b-core's Arrow case
        splits the given fold with.  ⚙ [a_solve_cstr_sub_inv] /
        [a_solve_cstr_eq_inv] MOVED here from prop_run_complete.v §5
        (2026-08-16, one fact one name one file — this file sits below
        the runner-completeness stack, which now imports it). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.prop_ln.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.

(* the ∀-quantified inputs are inferable from the derivation arguments, so
   applications read [lemma Hd Habs] — the §8c.6 note on implicit result
   args applies to this file's consumers *)
Set Implicit Arguments.

Open Scope frost_a_scope.

(* ===================================================================== *)
(*  §1  A lookeq collection is pure-eq                                    *)
(* ===================================================================== *)

Definition a_cstr_is_eq (c : a_cstr) : Prop := exists Q, c = a_cstr_eq Q.

Lemma a_lookeq_cstrs_pure_eq : forall Θ α P P' Ξ C,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
  Forall a_cstr_is_eq C.
Proof.
  intros * H.
  induction H; try solve [ constructor ]; auto.
  - (* LE-Var *)
    constructor; [ exists P; reflexivity | constructor ].
  - (* LE-FlexR *)
    constructor; [ eexists; reflexivity | constructor ].
  - (* LE-Arrow *)
    apply Forall_app; split; assumption.
Qed.

(* ===================================================================== *)
(*  §2  An α-free subject collects nothing                                *)
(* ===================================================================== *)

(** The only EMITTING rules — LS/LE-Var, LE-FlexR — need an α-occurrence
    in the subject, and every ∀-opener is fresh from α, so absence is an
    invariant of the whole subtree: EVERY derivation at an α-free
    subject returns [nil ⨾ nil], not just the LS/LE-Absent one. *)
Lemma a_lookeq_subject_absent : forall Θ α P P' Ξ C,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil.
Proof.
  intros * H.
  induction H; intros Habs; simpl in *; auto.
  - (* LE-Var: subject IS α *)
    exfalso. clear - Habs. fsetdec.
  - (* LE-FlexR: α ∈ ftv P by the rule's own premise *)
    exfalso.
    match goal with
    | Hin : α `in` ftvar_in_pskl _ |- _ => clear - Habs Hin; fsetdec
    end.
  - (* LE-Arrow *)
    destruct IHa_lookeq1 as [-> ->]; [ clear - Habs; fsetdec | ].
    destruct IHa_lookeq2 as [-> ->]; [ clear - Habs; fsetdec | ].
    auto.
  - (* LE-ForallInh: the opener is fresh from α *)
    apply IHa_lookeq.
    match goal with
    | |- α `notin` ftvar_in_pskl (open_pskl_wrt_pskl ?B (pskl_var_f ?b)) =>
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
          as Hup;
        match goal with
        | Hfr : b `notin` add α _ |- _ =>
            clear - Habs Hfr Hup; simpl in *; fsetdec
        end
    end.
  - (* LE-ForallSyn *)
    apply IHa_lookeq.
    match goal with
    | |- α `notin` ftvar_in_pskl (open_pskl_wrt_pskl ?B (pskl_var_f ?b)) =>
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
          as Hup;
        match goal with
        | Hfr : b `notin` add α _ |- _ =>
            clear - Habs Hfr Hup; simpl in *; fsetdec
        end
    end.
Qed.

Lemma a_looksub_subject_absent : forall Θ α m P P' Ξ C,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil.
Proof.
  intros * H.
  induction H; intros Habs; simpl in *; auto.
  - (* LS-Var: subject IS α *)
    exfalso. clear - Habs. fsetdec.
  - (* LS-Check: drops into the eq layer *)
    match goal with
    | He : a_lookeq _ _ _ _ _ _ |- _ =>
        eapply a_lookeq_subject_absent; [ exact He | exact Habs ]
    end.
  - (* LS-Arrow *)
    match goal with
    | He : a_lookeq _ _ ?A _ _ _ |- _ =>
        assert (Habs1 : α `notin` ftvar_in_pskl A)
          by (clear - Habs; fsetdec);
        destruct (a_lookeq_subject_absent He Habs1) as [-> ->]
    end.
    destruct IHa_looksub as [-> ->]; [ clear - Habs; fsetdec | ].
    auto.
  - (* LS-ForallL: the opener is fresh from α *)
    apply IHa_looksub.
    match goal with
    | |- α `notin` ftvar_in_pskl (open_pskl_wrt_pskl ?B (pskl_var_f ?b)) =>
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
          as Hup;
        match goal with
        | Hfr : b `notin` add α _ |- _ =>
            clear - Habs Hfr Hup; simpl in *; fsetdec
        end
    end.
Qed.

(* ===================================================================== *)
(*  §3  A ◇-target solve step is the identity                             *)
(* ===================================================================== *)

(** Crossing 3's engine: the slack constraints ([eq ◇] and [≼m ◇]) cost
    the fold NOTHING — the pattern passes through and no names are
    generated — so the side that emitted them and the side that did not
    fold to the SAME state.  (The BUILD direction is one constructor,
    SE-VacuousR / SS-Vacuous; these are the INVERSIONS.) *)
Lemma a_solve_eq_hole_target_inv : forall Θ P Ξ P',
  {{ Θ ⊢ₑ P ∼ pskl_hole ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = P.
Proof.
  intros * H.
  inversion H; subst; auto.
  (* SE-GhostGuarded: guarded ◇ has no constructor *)
  match goal with
  | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
  end.
Qed.

Lemma a_solve_sub_hole_target_inv : forall Θ m P Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] pskl_hole ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = P.
Proof.
  intros Θ m P Ξ P' H.
  remember pskl_hole as T eqn:HT.
  induction H; inversion HT; subst.
  - (* SS-Var *) auto.
  - (* SS-ForallL: the yield re-closes to the subject *)
    destruct IHa_solve_sub as [-> ->]; [ reflexivity | ].
    split; [ reflexivity | ].
    rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
      [ reflexivity | clear - H; fsetdec ].
  - (* SS-UnivGhostL *)
    destruct IHa_solve_sub as [-> ->]; [ reflexivity | ]. auto.
  - (* SS-Vacuous *) auto.
  - (* SS-Check: guarded ◇ has no constructor *)
    match goal with
    | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
    end.
  - (* SS-GhostL at B = ◇: ghost-free ◇ has no constructor *)
    match goal with
    | Hg : pskl_ghost_free pskl_hole |- _ => inversion Hg
    end.
Qed.

(* ===================================================================== *)
(*  §4  The fold's head inversions and the pure-eq append decomposition   *)
(* ===================================================================== *)

(** ⚙ Moved from prop_run_complete.v §5 (2026-08-16) — see the header. *)
Lemma a_solve_cstr_sub_inv : forall Θ m Q C P Ξ P',
  {{ Θ ⊩ (a_cstr_sub m Q :: C) ⨾ P ⤳ Ξ ⨾ P' }}a ->
  C = nil /\ {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a.
Proof.
  intros * Hd. inversion Hd; subst. split; [ reflexivity | assumption ].
Qed.

Lemma a_solve_cstr_eq_inv : forall Θ Q C P Ξ P',
  {{ Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ Ξ ⨾ P' }}a ->
  exists Ξ1 Ξ2 P'',
    Ξ = Ξ2 ++ Ξ1
    /\ {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}a
    /\ {{ (Ξ1 ++ Θ) ⊩ C ⨾ P'' ⤳ Ξ2 ⨾ P' }}a.
Proof.
  intros * Hd. inversion Hd; subst.
  match goal with
  | Hh : a_solve_eq _ _ _ ?X1 ?Pm, Ht : a_solve_cstr _ _ _ ?X2 _ |- _ =>
      exists X1, X2, Pm
  end.
  repeat split; assumption.
Qed.

(** The mirror of [a_solve_cstr_app] (algo/sub/look/prop_eq_cstr.v:155):
    a fold across a pure-eq prefix SPLITS at the seam.  The b-core's
    Arrow case decomposes the derivation-side fold with this, hands the
    halves to the two IHs, and recomposes the runner side with the
    original. *)
Lemma a_solve_cstr_app_inv : forall C1 Θ 𝒞2 P Ξ P',
  Forall a_cstr_is_eq C1 ->
  {{ Θ ⊩ (C1 ++ 𝒞2) ⨾ P ⤳ Ξ ⨾ P' }}a ->
  exists Ξ1 Ξ2 Pmid,
    Ξ = Ξ2 ++ Ξ1
    /\ {{ Θ ⊩ C1 ⨾ P ⤳ Ξ1 ⨾ Pmid }}a
    /\ {{ (Ξ1 ++ Θ) ⊩ 𝒞2 ⨾ Pmid ⤳ Ξ2 ⨾ P' }}a.
Proof.
  induction C1 as [ | c C1' IH ]; intros Θ 𝒞2 P Ξ P' Hall Hd.
  - exists nil, Ξ, P.
    split; [ rewrite app_nil_r; reflexivity | ].
    split; [ apply a_solve_cstr__empty | ].
    simpl. exact Hd.
  - inversion Hall as [ | ? ? [Q ->] Hall' ]; subst.
    simpl in Hd.
    apply a_solve_cstr_eq_inv in Hd
      as (Ξa & Ξb & Pmid0 & -> & Hhead & Htail).
    apply IH in Htail as (Ξ1' & Ξ2 & Pmid & -> & Hpre & Hpost);
      [ | exact Hall' ].
    exists (Ξ1' ++ Ξa), Ξ2, Pmid.
    split;
      [ solve [ apply app_assoc | symmetry; apply app_assoc ] | ].
    split.
    + eapply a_solve_cstr__eq; [ exact Hhead | exact Hpre ].
    + replace ((Ξ1' ++ Ξa) ++ Θ) with (Ξ1' ++ (Ξa ++ Θ))
        by (solve [ apply app_assoc | symmetry; apply app_assoc ]).
      exact Hpost.
Qed.
