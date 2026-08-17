(** ⚠️ REFUTATION (2026-08-17, campaign §8c.11 / level 6): **[e_extract] is
    NOT deterministic up to a fresh renaming** — two derivations at the SAME
    inputs can spend DIFFERENT NUMBERS of fresh names, so no renaming
    (no bijection at all) relates their output supplies.

    WHY IT MATTERS.  Level 6's plan carried the hypothesis

      e_extract_det :=
        two [e_extract]s at the same inputs give [ps] with
          swaps_atoms ps S1 [=] S1'  /\  swaps_aenv ps Ξ = Ξ'
                                     /\  swaps_pskl ps Q = Q'

    as the one debt [SI-ForallL] owes (level 4 closed with the b-core's SUB
    half carrying a BARE conclusion pack).  This file says that hypothesis
    is not merely unproved but FALSE, so the debt cannot be discharged as
    stated — and, because [SI-ForallL] inherits the drift, the level-6
    motive mirrored from level 5 (derivation's outputs = runner's UP TO A
    SWAP CHAIN) is false at its SUPPLY conjunct too.

    ⭐ THE CONFIGURATION, and it is as small as it looks.  Take an
    α-FREE subject and a ∀ counterpart:

        Θ = ·        α ∈ S0       subject  1       counterpart  ∀_. 1

    Two collection rules fire at the root and neither is guarded against
    the other:

      LS-Absent    α ∉ ftv(1), so the whole call collects NOTHING and
                   spends NO supply                        (S0 ↝ S0)
      LS-ForallR   peels the counterpart's quantifier at a DRAWN opener β,
                   and the premise then collects nothing   (S0 ↝ S0 ∪ {β})

    Both emit [Ξ = ·] and [𝒞 = ·], so the fold is empty and the yield is the
    accumulator [◇] on both sides; at [NM = SK] the guess is the identity.
    The two extractions therefore agree on EVERYTHING the statement asks
    about except the output supply, where they differ by exactly one atom —
    and a swap chain that fixes [S0] cannot add an atom to it.

    ⭐⭐ THE DIAGNOSIS IS LEVEL 5's, ONE LAYER DOWN: A MISSING DISPATCH
    GUARD.  The reference implementation tests ABSENCE FIRST — [type.ml]'s
    [constr_collect_sub] (:649-701) and, in this tree, every non-Absent
    clause of [e_looksub_impl] / [e_lookeq_impl] sits behind
    [mem α (ftvar_in_pskl P)] (def_look_impl.v:360, 377, 393, 406, …).  The
    RELATION has no match order, so that exclusion has to be a PREMISE, and
    it is not one: [e_looksub__forall_r] and its neighbours carry no
    [α ∈ ftvar_in_pskl P].  That is the identical species as [U-FlexL] /
    [U-FlexR]'s missing [≠ ◇] (level 5, `0829607`) and [SI-Ghost]'s missing
    [M ≠ TI] (level 6's audit, `35a13b3`).

    ⚙ [LS-Vacuous] (counterpart [◇]) overlaps the same way and the runner
    tests it second, so the repair is a pair of guards, not one.

    ⚙ WHAT THIS FILE DOES NOT CLAIM.  It does not say the two collections
    disagree — here they are both empty.  The older
    [cex_looksub_not_det.v] is the exhibit for the COLLECTION's
    non-determinism (the ∀-peel ORDER decides which constraint is emitted);
    this one is about the SUPPLY, survives the fold, and is therefore the
    one that reaches level 6. *)

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
(*  §1  The two derivations                                               *)
(* ===================================================================== *)

(** The ABSENT route: nothing is collected and nothing is spent. *)
Lemma probe_extract_absent : forall S0 α,
  {{ S0 ↝ S0 ⊨ nil ⊢ pskl_unit
     ⊳[ a_sub_mode_sk , α , mode_tc ] (pskl_all_syn pskl_unit)
     ⤳ nil ↪ pskl_hole }}e.
Proof.
  intros S0 α.
  apply e_extract__solve with (Ξ := nil) (Ξs := nil) (Ξ' := nil)
    (C := nil) (Q := pskl_hole) (S1 := S0) (S2 := S0).
  - apply e_looksub__absent. simpl. fsetdec.
  - apply e_solve_cstr__empty.
  - apply e_guess__sk.
Qed.

(** The FORALL-R route: the counterpart's quantifier is peeled at a drawn
    opener, and the premise is then the absent call. *)
Lemma probe_extract_forall_r : forall S0 α β,
  β `notin` S0 ->
  {{ S0 ↝ (add β S0) ⊨ nil ⊢ pskl_unit
     ⊳[ a_sub_mode_sk , α , mode_tc ] (pskl_all_syn pskl_unit)
     ⤳ nil ↪ pskl_hole }}e.
Proof.
  intros S0 α β Hβ.
  apply e_extract__solve with (Ξ := nil) (Ξs := nil) (Ξ' := nil)
    (C := nil) (Q := pskl_hole) (S1 := add β S0) (S2 := add β S0).
  - apply e_looksub__forall_r with (β := β).
    + simpl. exact I.
    + exact Hβ.
    + simpl. apply e_looksub__absent. simpl. fsetdec.
  - apply e_solve_cstr__empty.
  - apply e_guess__sk.
Qed.

(* ===================================================================== *)
(*  §2  ⛔ THE REFUTATION                                                  *)
(*                                                                        *)
(*  A chain whose every pair dodges [S0] fixes [S0] pointwise             *)
(*  ([swaps_atoms_notin]), so the two output supplies would have to be    *)
(*  EQUAL — and one of them properly contains the other.                  *)
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

Theorem e_extract_det_false : ~ e_extract_det.
Proof.
  intros Hdet.
  (* one atom for the target [α], a second for the drawn opener [β] *)
  destruct (atom_fresh empty) as [α _].
  destruct (atom_fresh (singleton α)) as [β HβS].
  destruct (Hdet (singleton α) nil a_sub_mode_sk α mode_tc
              pskl_unit (pskl_all_syn pskl_unit)
              (singleton α) nil pskl_hole
              (add β (singleton α)) nil pskl_hole
              (probe_extract_absent (singleton α) α)
              (probe_extract_forall_r (singleton α) α β HβS)
              ltac:(simpl; fsetdec))
    as [ps [Hav [HS _]]].
  (* the chain dodges [S0], so it moves [S0] nowhere *)
  assert (Hfix : swaps_atoms ps (singleton α) [=] singleton α)
    by (apply swaps_atoms_notin; exact Hav).
  (* … which forces the drawn opener to have been there all along *)
  assert (Hin : β `in` singleton α)
    by (rewrite <- Hfix; rewrite HS; clear; fsetdec).
  clear - Hin HβS. fsetdec.
Qed.

(** ⭐ THE CONSEQUENCE FOR LEVEL 6 — ⚠️ ARGUED BY INSPECTION HERE, NOT
    MACHINE-CHECKED.  What §2 proves is exactly its statement: [e_extract]
    is not deterministic up to a renaming.  The further claim — that the
    drift REACHES [e_sub], so the level-6 motive's supply conjunct
    ([swaps_atoms ps Sd [=] sb_supply r]) is false as well — is the
    following configuration, checked on paper only:

        NM = TY     M = FN TC     P0 = 1 → ∀_. 1     subject = ∀β. (1 → 1)

    [SI-ForallL] applies ([P0] is an arrow, hence guarded), and its
    extraction is called at the α-free subject [1 → 1] against [1 → ∀_. 1],
    where §1's two routes reappear one arrow down: LS-Absent at the root,
    or LS-Arrow whose right half peels the codomain's ∀ at a drawn opener.
    The fold is empty either way and [guess^TY] then draws one flexible on
    both routes, so the extraction's blocks and instantiations still agree
    and only the supply drifts by one atom — which the surrounding [e_sub]
    derivation carries to its own output.  ⛔ Confirming that end-to-end is
    the next probe to write; until it exists, treat the [e_sub]-level claim
    as a diagnosis rather than a theorem. *)
