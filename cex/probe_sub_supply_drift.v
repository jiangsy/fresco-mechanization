(** ⚠️ REFUTATION (2026-08-17, campaign §8c.13 / level 6): the collection's
    supply drift **REACHES [e_sub]**, so level 6's motive is false at its
    SUPPLY conjunct — not merely level 4's.

    WHAT THIS FILE CLOSES.  [cex/probe_extract_supply_drift.v] proves
    [e_extract] is not deterministic up to a renaming, and its closing note
    then ARGUES BY INSPECTION that [SI-ForallL] carries the drift up to
    subtyping.  That was the one step of §8c.13's diagnosis with no machine
    behind it, and this file supplies it: two [e_sub] derivations at the SAME
    inputs, with the SAME output context and the SAME output skeleton,
    differing only in how much of the supply they spent — by one atom.

    ⭐ THE CONFIGURATION.  It is the inspection note's, tuned so that
    EVERYTHING AFTER THE DRIFT IS FREE — no rule below the fork draws a name,
    so the two runs differ by exactly one atom and the refutation needs no
    counting argument, only [swaps_atoms_add] down to the common base [S0].

        NM = SK      M = FN TC      P0 = 1 → ∀_. 1      subject ∀_. (◇ → ◇)

    [SI-ForallL] applies: [M ≠ TI], and [P0] is an ARROW, hence [guarded], so
    the [guarded P0 ∨ P0 = ◇] guard is satisfied.  It draws its opener [α] and
    runs [extract] at the α-FREE subject [◇ → ◇] against [1 → ∀_. 1], where
    §8c.13's two routes reappear one arrow down:

      LS-Absent    α ∉ ftv(◇ → ◇) = ∅: collects nothing, spends nothing
      LS-Arrow     LE-Absent on the domain, then LS-ForallR peels the
                   codomain's ∀ at a DRAWN opener [β], then LS-Absent

    Both emit [Ξ = ·] and [𝒞 = ·], so the fold is empty and the accumulator
    [◇] survives; at [NM = SK] the guess is the IDENTITY, so — unlike the
    [TY] reading of the inspection note — it draws nothing and the extraction's
    block is [·] on both routes, with [P1 = ◇].

    ⭐⭐ AND THE TAIL IS FREE.  [SI-ForallL]'s third premise re-runs the
    subject [◇ → ◇] against [1 → ∀_. 1] at [FN TC], where [SI-Arrow] splits it
    into two AXIOMS: [C-Ghost] at the ghost domain ([◇ ∼ 1]) and [SI-Ghost] at
    the ghost codomain ([◇ ⩽ ∀_. 1], legal since [TC ≠ TI]).  Neither draws,
    so the whole difference between the two derivations is the [β] that
    LS-ForallR spent and LS-Absent did not.

    ⭐ WHY IT KILLS THE MOTIVE.  Level 5 relates a derivation's outputs to the
    runner's UP TO A SWAP CHAIN whose pairs avoid the input supply [S0],
    supply included ([swaps_atoms ps Sd [=] sb_supply r]).  §2 shows no such
    chain exists here: peeling the one [add] with [swaps_atoms_add] and fixing
    the base with [swaps_atoms_notin] forces the drawn opener [α] and the
    drawn peeler [β] to be the same atom, which their own freshness refutes.

    ⚙ WHAT THIS FILE DOES NOT CLAIM.  It does not say the two derivations
    disagree on their ANSWER — they return the same [Θ] and the same [Q].  The
    supply is the whole of the difference, and that is precisely the conjunct
    level 5's motive carries.

    ⛔ THIS FILE IS THE JUSTIFICATION FOR THE ABSENCE-FIRST GUARD.  Once
    [e_looksub__forall_r] carries [α ∈ ftvar_in_pskl P], §1's second
    derivation stops typechecking and this file is retracted along with
    [probe_extract_supply_drift.v]; see docs/PAPER-GAPS.md. *)

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
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.def_sub.
Require Import src.frost.ext_algo.prop_solve_det.

Open Scope frost_e_scope.

(** The one counterpart, written once: [1 → ∀_. 1].  An arrow, hence
    [guarded], which is what [SI-ForallL] tests. *)
Definition drift_P0 : pskl :=
  pskl_arrow pskl_unit (pskl_all_syn pskl_unit).

(** The subject [∀_. (◇ → ◇)].  Its body is CLOSED, so opening it at the
    rule's own binder leaves an α-free subject — which is what lets LS-Absent
    fire beside LS-Arrow. *)
Definition drift_subject : pskl :=
  pskl_all_syn (pskl_arrow pskl_hole pskl_hole).

(* ===================================================================== *)
(*  §1  The two derivations                                               *)
(*                                                                        *)
(*  Same inputs, same output context, same output skeleton.  They differ  *)
(*  in ONE thing: the second spends [β].                                  *)
(* ===================================================================== *)

(** The shared tail: [SI-Arrow] over two axioms, at ANY supply, spending
    nothing.  Factored out so that §1's two derivations are literally the
    same proof below the fork. *)
Lemma drift_tail : forall S,
  {{ S ↝ S ⊨ nil ⊢[ a_sub_mode_sk | (mode_fn mode_tc) | drift_P0 ]
     (pskl_arrow pskl_hole pskl_hole) ⩽ drift_P0 ⊣ nil }}e.
Proof.
  intros S. unfold drift_P0.
  apply e_sub__arrow with (Θ1 := nil) (S1 := S).
  - (* C-Ghost: [◇ ∼ 1], an axiom *)
    apply e_consis__ghost. clear. fsetdec.
  - (* SI-Ghost: [◇ ⩽ ∀_. 1], an axiom — legal because [TC ≠ TI] *)
    apply e_sub__ghost. discriminate.
Qed.

(** THE ABSENT ROUTE.  The collection sees an α-free subject and stops: the
    only name spent by the whole derivation is [SI-ForallL]'s own opener. *)
Lemma probe_sub_absent : forall S0 α,
  α `notin` S0 ->
  {{ S0 ↝ (add α S0) ⊨ nil
     ⊢[ a_sub_mode_sk | (mode_fn mode_tc) | drift_P0 ]
     drift_subject ⩽ drift_P0 ⊣ nil }}e.
Proof.
  intros S0 α Hα. unfold drift_subject, drift_P0.
  apply e_sub__forall_l with (α := α) (Ξ := nil) (P1 := pskl_hole)
    (S1 := add α S0).
  - discriminate.
  - left. apply guarded_pskl__arrow; auto.
  - exact Hα.
  - simpl.
    apply e_extract__solve with (Ξ := nil) (Ξs := nil) (Ξ' := nil)
      (C := nil) (Q := pskl_hole) (S1 := add α S0) (S2 := add α S0).
    + apply e_looksub__absent. simpl. fsetdec.
    + apply e_solve_cstr__empty.
    + apply e_guess__sk.
  - apply a_wf_pskl__hole.
  - simpl. apply drift_tail.
Qed.

(** THE FORALL-R ROUTE.  The collection descends the arrow, meets the
    counterpart's ∀ in the codomain, and peels it at a DRAWN opener [β] —
    after which its premise collects nothing, exactly as the absent route
    did at the root.  Same block, same constraint list, one more atom. *)
Lemma probe_sub_forall_r : forall S0 α β,
  α `notin` S0 ->
  β `notin` (add α S0) ->
  {{ S0 ↝ (add β (add α S0)) ⊨ nil
     ⊢[ a_sub_mode_sk | (mode_fn mode_tc) | drift_P0 ]
     drift_subject ⩽ drift_P0 ⊣ nil }}e.
Proof.
  intros S0 α β Hα Hβ. unfold drift_subject, drift_P0.
  apply e_sub__forall_l with (α := α) (Ξ := nil) (P1 := pskl_hole)
    (S1 := add β (add α S0)).
  - discriminate.
  - left. apply guarded_pskl__arrow; auto.
  - exact Hα.
  - simpl.
    apply e_extract__solve with (Ξ := nil) (Ξs := nil) (Ξ' := nil)
      (C := nil) (Q := pskl_hole)
      (S1 := add β (add α S0)) (S2 := add β (add α S0)).
    + (* LS-Arrow — and NOTE that its two halves are the SAME two calls the
         absent route never made *)
      change (@nil (atom * abind)) with (nil ++ nil : aenv).
      change (@nil a_cstr) with (nil ++ nil : a_cstrs).
      apply e_looksub__arrow with (S1 := add α S0).
      * (* domain: [◇ ∼[α] 1] — absent *)
        apply e_lookeq__absent. simpl. fsetdec.
      * (* codomain: [◇ ≼[α,TC] ∀_. 1] — LS-ForallR DRAWS [β] *)
        apply e_looksub__forall_r with (β := β).
        -- simpl. exact I.
        -- exact Hβ.
        -- simpl. apply e_looksub__absent. simpl. fsetdec.
    + apply e_solve_cstr__empty.
    + apply e_guess__sk.
  - apply a_wf_pskl__hole.
  - simpl. apply drift_tail.
Qed.

(* ===================================================================== *)
(*  §2  ⛔ THE REFUTATION                                                  *)
(*                                                                        *)
(*  Level 5's motive, mirrored to subtyping, would relate the two output  *)
(*  supplies by a swap chain whose pairs avoid [S0].  Peel the one [add]  *)
(*  ([swaps_atoms_add]), fix the base ([swaps_atoms_notin]), and the      *)
(*  chain is forced to identify the two DISTINCT drawn atoms.            *)
(* ===================================================================== *)

(** The supply conjunct of level 5's motive, transplanted to [e_sub] — the
    statement level 6's plan carried, and the one this file refutes.  The
    context and skeleton conjuncts are included so that what is refuted is
    the FULL mirrored motive, not a strengthening of it. *)
Definition e_sub_det : Prop :=
  forall S0 NM M P0 Θ0 P Q S1 Θ1 S1' Θ1',
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1' ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1' }}e ->
    ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P
      ∪ ftvar_in_pskl Q [<=] S0 ->
    exists ps,
      (forall x y, In (x, y) ps -> x `notin` S0 /\ y `notin` S0)
      /\ swaps_atoms ps S1 [=] S1'
      /\ swaps_aenv ps Θ1 = Θ1'.

Theorem e_sub_det_false : ~ e_sub_det.
Proof.
  intros Hdet.
  (* two atoms: [SI-ForallL]'s opener and LS-ForallR's peeler *)
  destruct (atom_fresh empty) as [α _].
  destruct (atom_fresh (singleton α)) as [β Hβ].
  assert (Hα : α `notin` (empty : atoms)) by fsetdec.
  assert (Hβ' : β `notin` (add α empty)) by (clear - Hβ; fsetdec).
  destruct (Hdet empty a_sub_mode_sk (mode_fn mode_tc) drift_P0 nil
              drift_subject drift_P0
              (add α empty) nil (add β (add α empty)) nil
              (probe_sub_absent empty α Hα)
              (probe_sub_forall_r empty α β Hα Hβ')
              ltac:(simpl; fsetdec))
    as [ps [Hav [HS _]]].
  (* peel the [add], then fix the base: the chain moves [S0 = ∅] nowhere *)
  assert (Hpeel : swaps_atoms ps (add α empty)
                  [=] add (swaps_atom ps α) (swaps_atoms ps empty))
    by apply swaps_atoms_add.
  assert (Hbase : swaps_atoms ps (empty : atoms) [=] empty)
    by (apply swaps_atoms_notin; exact Hav).
  (* so the chain's image of [α] is a SINGLETON that has to contain BOTH the
     drawn opener and the drawn peeler — and they are distinct *)
  set (γ := swaps_atom ps α) in *.
  assert (Hβγ : β `in` add γ (swaps_atoms ps empty))
    by (rewrite <- Hpeel; rewrite HS; clear; fsetdec).
  assert (Hαγ : α `in` add γ (swaps_atoms ps empty))
    by (rewrite <- Hpeel; rewrite HS; clear; fsetdec).
  rewrite Hbase in Hβγ, Hαγ.
  assert (Heqβ : γ = β)
    by (apply AtomSetFacts.add_iff in Hβγ;
        destruct Hβγ as [ H | H ]; [ exact H | exfalso; clear - H; fsetdec ]).
  assert (Heqα : γ = α)
    by (apply AtomSetFacts.add_iff in Hαγ;
        destruct Hαγ as [ H | H ]; [ exact H | exfalso; clear - H; fsetdec ]).
  rewrite Heqβ in Heqα. clear - Heqα Hβ. fsetdec.
Qed.

(** ⭐ THE CONSEQUENCE, and it is now a theorem rather than a diagnosis.
    [SI-ForallL] runs [extract] at a subject the rule's own opener does not
    occur in, and the COLLECTION has two rules there — one that spends and one
    that does not.  So level 6 cannot mirror level 5's motive, and the repair
    is not a change of motive but a change of RULE: the collection owes the
    absence-first exclusion its own implementation already dispatches on
    ([type.ml]'s [constr_collect_sub], and [e_looksub_impl]'s [mem α (ftvar_in_pskl P)]
    tests).  With [e_looksub__forall_r] guarded by [α ∈ ftvar_in_pskl P],
    §1's [probe_sub_forall_r] cannot be built and the motive is restored. *)
