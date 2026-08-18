(** ⚠️ REFUTATION (2026-08-18, campaign §8c.16 / level 6, STEP 2):
    **[e_extract] is STILL not deterministic up to a renaming after the
    three dispatch guards** — a FOURTH cell of the collection's dispatch is
    unguarded, and there the two rows disagree in BLOCK, in COLLECTION and
    in SUPPLY at once.

    ⭐ THE CELL, and it is [probe_bcore_ug2_flexr.v]'s, one level up.
    [guarded_pskl] includes VARIABLES (frost/def_shapes.v), so at

        ⫯Q  ∼[α]  β                (subject a ⫯, counterpart a variable)

    with [α ∈ ftv Q] BOTH [LE-FlexR] (counterpart a variable, subject not
    [α], [α] occurs) and [LE-UnivGhost2] (⫯ subject, counterpart guarded)
    fire, and their answers are of different KINDS:

        LE-FlexR      Ξ = (α̂1 ~ flex)   𝒞 = [≐ α̂1]   S ↝ add α̂1 S
        LE-UnivGhost2 Ξ = ·             𝒞 = [≐ β]     S ↝ S       (via LE-Var)

    §8c.9's fourth pass met this pair and DODGED it — the b-core was
    re-stated RUNNER-SIDED, which is sound at level 4 because that level's
    conclusion carries a rel-or-HATCH yield and no supply.  Level 6 cannot
    dodge it: [SI-ForallL] must move the DERIVATION's extract outputs onto
    the RUNNER's rails by a swap chain, and a chain relates neither the
    blocks (one is [·]) nor the supplies (they differ by one atom).

    ⭐ WHAT THE IMPLEMENTATION DOES, checked (type.ml:547-620,
    [constr_collect_eq]).  Its match tests

        LE-Var (:549)  →  LE-Absent (:553)  →  LE-Vacuous (:557)
                       →  ⭐ LE-FlexR (:561)  →  … →  LE-UnivGhost2 (:618)

    so **LE-FlexR wins**, and [e_lookeq_impl] agrees verbatim (the
    ⫯-subject / var-counterpart clause, def_look_impl.v:293-300).  The
    relation has no match order, so the exclusion must be a PREMISE on
    [LE-UnivGhost2], and it is not one.  Identical species to the three
    guards already landed (§8c.14, §8c.15).

    ⭐ THE LIFT TO [e_extract] IS ONE ARROW AND ONE [LS-Check].  Take

        NM = SK   m = TC   Θ0 = ·   subject (⫯α) → 1   counterpart β → 1

    [LS-Check] is the only collection row at an arrow subject with [α]
    occurring and a guarded ghost-free counterpart, and it hands the pair
    straight to [LE-Arrow], whose left half IS the cell.  Below the fork
    everything is free: the right halves are [α]-free ([LE-Absent]), both
    folds are a single [SE-GhostL] at the accumulator [◇], and at [NM = SK]
    the guess is the identity.  So the two extractions differ by exactly
    the cell's own disagreement.

    ⛔ AND THE BLOCK CONJUNCT ALONE REFUTES IT — no counting argument is
    needed.  [swaps_aenv ps · = ·] for EVERY chain, and one side's block is
    [(α̂1 ~ flex)]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_tag.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.prop_solve_det.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The configuration                                                 *)
(* ===================================================================== *)

(** The subject [(⫯α) → 1] and the counterpart [β → 1]. *)
Definition drift_subj (α : atom) : pskl :=
  pskl_arrow (pskl_tophole (pskl_var_f α)) pskl_unit.
Definition drift_cpt (β : atom) : pskl :=
  pskl_arrow (pskl_var_f β) pskl_unit.

(* ===================================================================== *)
(*  §2  The two derivations                                               *)
(* ===================================================================== *)

(** ROUTE A — [LE-UnivGhost2] then [LE-Var]: the RAW counterpart is
    collected, nothing is invented and nothing is spent. *)
Lemma probe_extract_ug2 : forall S0 α β,
  {{ S0 ↝ S0 ⊨ nil ⊢ (drift_subj α)
     ⊳[ a_sub_mode_sk , α , mode_tc ] (drift_cpt β)
     ⤳ nil ↪ (pskl_var_f β) }}e.
Proof.
  intros S0 α β. unfold drift_subj, drift_cpt.
  apply e_extract__solve
    with (Ξ := nil) (Ξs := nil) (Ξ' := nil)
         (C := a_cstr_eq (pskl_var_f β) :: nil)
         (Q := pskl_var_f β) (S1 := S0) (S2 := S0).
  - (* the collection: LS-Check ∘ LE-Arrow ∘ (LE-UnivGhost2 ∘ LE-Var, LE-Absent) *)
    apply e_looksub__check.
    + simpl. repeat split.
    + discriminate.
    + constructor; auto.
    + constructor; auto.
    + apply e_lookeq__arrow
        with (S1 := S0) (Ξ1 := nil) (Ξ2 := nil)
             (C1 := a_cstr_eq (pskl_var_f β) :: nil) (C2 := nil).
      * apply e_lookeq__univ_ghost2; [ constructor | ].
        apply e_lookeq__var.
      * apply e_lookeq__absent. simpl. fsetdec.
  - (* the fold: one SE-GhostL at the accumulator ◇ *)
    apply e_solve_cstr__eq
      with (P'' := pskl_var_f β) (Ξ1 := nil) (Ξ2 := nil) (S1 := S0).
    + apply e_solve_eq__hole_l.
    + apply e_solve_cstr__empty.
  - apply e_guess__sk.
Qed.

(** ROUTE B — [LE-FlexR]: a FRESH flexible replaces the counterpart, so the
    block grows, the collection names the invention and the supply is
    spent. *)
Lemma probe_extract_flexr : forall S0 α β α1,
  α1 `notin` S0 ->
  {{ S0 ↝ (add α1 S0) ⊨ nil ⊢ (drift_subj α)
     ⊳[ a_sub_mode_sk , α , mode_tc ] (drift_cpt β)
     ⤳ ((α1 ~ abind_flex_mono) ++ nil) ↪ (pskl_var_f α1) }}e.
Proof.
  intros S0 α β α1 Hα1. unfold drift_subj, drift_cpt.
  apply e_extract__solve
    with (Ξ := (α1 ~ abind_flex_mono) ++ nil) (Ξs := nil) (Ξ' := nil)
         (C := a_cstr_eq (pskl_var_f α1) :: nil)
         (Q := pskl_var_f α1) (S1 := add α1 S0) (S2 := add α1 S0).
  - apply e_looksub__check.
    + simpl. repeat split.
    + discriminate.
    + constructor; auto.
    + constructor; auto.
    + apply e_lookeq__arrow
        with (S1 := add α1 S0) (Ξ1 := (α1 ~ abind_flex_mono) ++ nil)
             (Ξ2 := nil)
             (C1 := a_cstr_eq (pskl_var_f α1) :: nil) (C2 := nil).
      * apply e_lookeq__flex_r.
        -- exact Hα1.
        -- discriminate.
        -- simpl. fsetdec.
      * apply e_lookeq__absent. simpl. fsetdec.
  - apply e_solve_cstr__eq
      with (P'' := pskl_var_f α1) (Ξ1 := nil) (Ξ2 := nil)
           (S1 := add α1 S0).
    + apply e_solve_eq__hole_l.
    + apply e_solve_cstr__empty.
  - apply e_guess__sk.
Qed.

(* ===================================================================== *)
(*  §3  ⛔ THE REFUTATION                                                  *)
(* ===================================================================== *)

Definition e_extract_det : Prop :=
  forall S0 Θ0 NM α m P P' S1 Ξ Q S1' Ξ' Q',
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
    {{ S0 ↝ S1' ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ' ↪ Q' }}e ->
    add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
    exists ps,
      (forall x y, In (x, y) ps -> x `notin` S0 /\ y `notin` S0)
      /\ swaps_atoms ps S1 [=] S1'
      /\ swaps_aenv ps Ξ = Ξ'
      /\ swaps_pskl ps Q = Q'.

(** ⛔ The BLOCK conjunct alone: a chain maps the empty block to the empty
    block, and route B's is a singleton. *)
Theorem e_extract_det_false : ~ e_extract_det.
Proof.
  intros Hdet.
  destruct (atom_fresh empty) as [α _].
  destruct (atom_fresh (singleton α)) as [β Hβ].
  destruct (atom_fresh (add β (singleton α))) as [α1 Hα1].
  destruct (Hdet (add β (singleton α)) nil a_sub_mode_sk α mode_tc
              (drift_subj α) (drift_cpt β)
              (add β (singleton α)) nil (pskl_var_f β)
              (add α1 (add β (singleton α)))
              ((α1 ~ abind_flex_mono) ++ nil) (pskl_var_f α1)
              (probe_extract_ug2 (add β (singleton α)) α β)
              (probe_extract_flexr (add β (singleton α)) α β α1 Hα1)
              ltac:(unfold drift_subj, drift_cpt; simpl; fsetdec))
    as [ps [_ [_ [HΞ _]]]].
  rewrite swaps_aenv_nil in HΞ. discriminate.
Qed.
