(** ⚠️ REFUTATION (2026-08-17, campaign §8c.14): the ABSENCE-FIRST GUARD IS
    NOT THE WHOLE REPAIR — [e_looksub] still spends a name it never needed,
    now through the OTHER dispatch test the runner performs, [LS-Vacuous].

    ⭐ WHY THIS FILE EXISTS.  §8c.13's repair landed
    [α ∈ ftvar_in_pskl <subject>] on the five leaking rows, which kills the
    ABSENT overlap.  The two source documents both said in passing that the
    repair is "a pair of guards, not one" — the runner tests VACUOUS second
    (`def_look_impl.v`: every `pskl_hole` counterpart answers `nil ⨾ nil`
    BEFORE the α-membership test is even reached) — but the guard that
    renders THAT test was not stated and is not on the rules.  This file is
    the witness that it is load-bearing rather than cosmetic.

    ⭐ THE CONFIGURATION, and it is [cex_looksub_not_det.v]'s subject against
    the OTHER counterpart:

        Θ = ·      α ∈ S0      subject  ∀_. α      counterpart  ◇

    The subject is a VACUOUS binder over the looked-for variable, so
    [α ∈ ftv(∀_. α)] and §8c.13's guard is SATISFIED — [LS-ForallL] may fire.

      LS-Vacuous   the counterpart is ◇: collects nothing, spends nothing
      LS-ForallL   peels the SUBJECT at a DRAWN opener β, and the premise
                   [α ≼[α,m] ◇] is then LS-Vacuous again

    Both emit [Ξ = ·] and [𝒞 = ·] — so this is not the constraint-shape
    divergence of [cex_looksub_not_det.v], it is the SUPPLY drift of
    §8c.13 exactly, one dispatch test over.

    ⚙ AND THE SAME PREMISE ADMITS A THIRD ANSWER.  The premise [α ≼[α,m] ◇]
    is ALSO an [LS-Var] node, which emits [𝒞 = [≼m ◇]].  §3 records that,
    because it shows the [◇] counterpart is not merely a supply question:
    [LS-Var] and [LS-Vacuous] overlap at the looked-for variable itself, and
    the runner dispatches on the SUBJECT first, so it takes Var.

    ⛔ CONSEQUENCE.  [e_extract_det] is still FALSE after §8c.13's guard, so
    level 6's motive is still not restored.  The repair the runner's dispatch
    actually calls for is the mirror exclusion [P' ≠ ◇] on the rows that can
    fire at a ghost counterpart, plus [P ≠ α] on [LS-Vacuous] itself. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.prop_solve_det.

Open Scope frost_e_scope.

(** [∀_. α] — a vacuous binder over the looked-for variable, so the
    absence-first guard is satisfied and does not block [LS-ForallL]. *)
Definition vac_subj (α : atom) : pskl := pskl_all_syn (pskl_var_f α).

(* ===================================================================== *)
(*  §1  The two derivations — same answer, different spend                *)
(* ===================================================================== *)

Lemma probe_vacuous_nospend : forall S0 Θ α m,
  {{ S0 ↝ S0 ⊨ Θ ⊢ (vac_subj α) ≼[ α , m ] pskl_hole ⤳ nil ⨾ nil }}e.
Proof.
  intros. unfold vac_subj. apply e_looksub__vacuous.
Qed.

Lemma probe_vacuous_spends : forall S0 Θ α m β,
  β `notin` S0 ->
  {{ S0 ↝ (add β S0) ⊨ Θ ⊢ (vac_subj α) ≼[ α , m ] pskl_hole ⤳ nil ⨾ nil }}e.
Proof.
  intros S0 Θ α m β Hβ. unfold vac_subj.
  apply e_looksub__forall_l with (β := β).
  - exact Hβ.
  - (* §8c.13's guard is SATISFIED — the binder is vacuous over α *)
    simpl. clear. fsetdec.
  - unfold open_pskl_wrt_pskl. simpl. apply e_looksub__vacuous.
Qed.

(* ===================================================================== *)
(*  §2  ⛔ THE REFUTATION — the collection is still not deterministic      *)
(*      up to a renaming, supply included                                 *)
(* ===================================================================== *)

Definition e_looksub_det : Prop :=
  forall S0 Θ α m P P' S1 Ξ C S1' Ξ' C',
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1' ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ' ⨾ C' }}e ->
    add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
    exists ps,
      (forall x y, In (x, y) ps -> x `notin` S0 /\ y `notin` S0)
      /\ swaps_atoms ps S1 [=] S1'
      /\ swaps_aenv ps Ξ = Ξ'.

Theorem e_looksub_det_false : ~ e_looksub_det.
Proof.
  intros Hdet.
  destruct (atom_fresh empty) as [α _].
  destruct (atom_fresh (singleton α)) as [β Hβ].
  assert (Hβ' : β `notin` (singleton α : atoms)) by (clear - Hβ; fsetdec).
  destruct (Hdet (singleton α) nil α mode_tc (vac_subj α) pskl_hole
              (singleton α) nil nil
              (add β (singleton α)) nil nil
              (probe_vacuous_nospend (singleton α) nil α mode_tc)
              (probe_vacuous_spends (singleton α) nil α mode_tc β Hβ')
              ltac:(unfold vac_subj; simpl; fsetdec))
    as [ps [Hav [HS _]]].
  (* the chain dodges [S0], so it moves [S0] nowhere *)
  assert (Hfix : swaps_atoms ps (singleton α) [=] singleton α)
    by (apply swaps_atoms_notin; exact Hav).
  assert (Hin : β `in` singleton α)
    by (rewrite <- Hfix; rewrite HS; clear; fsetdec).
  clear - Hin Hβ. fsetdec.
Qed.

(* ===================================================================== *)
(*  §3  ⚙ AND THE CONSTRAINT LIST DIVERGES TOO, at the same cell          *)
(*                                                                        *)
(*  [LS-Var] and [LS-Vacuous] both fire at (subject α, counterpart ◇) and *)
(*  they emit DIFFERENT collections.  The runner dispatches on the        *)
(*  SUBJECT first (def_look_impl.v's [pskl_var_f β] clause precedes every *)
(*  counterpart test), so it takes Var — which is the exclusion           *)
(*  [LS-Vacuous] owes.                                                    *)
(* ===================================================================== *)

Lemma probe_var_at_hole : forall S Θ α m,
  {{ S ↝ S ⊨ Θ ⊢ (pskl_var_f α) ≼[ α , m ] pskl_hole ⤳ nil
     ⨾ (a_cstr_sub m pskl_hole :: nil) }}e.
Proof. intros. apply e_looksub__var. Qed.

Lemma probe_vacuous_at_var : forall S Θ α m,
  {{ S ↝ S ⊨ Θ ⊢ (pskl_var_f α) ≼[ α , m ] pskl_hole ⤳ nil ⨾ nil }}e.
Proof. intros. apply e_looksub__vacuous. Qed.

(** The two collections are not equal — and being CLOSED, no renaming
    relates them either. *)
Lemma probe_var_vacuous_differ : forall m,
  (a_cstr_sub m pskl_hole :: nil) <> (@nil a_cstr).
Proof. intros m Hc. inversion Hc. Qed.

(* ===================================================================== *)
(*  §4  ⛔⛔ WHY THE ◇-GUARD CANNOT BE ONE-SIDED — the a-side's own        *)
(*      derivation at that cell collects something NON-EMPTY              *)
(*                                                                        *)
(*  §8c.13's guard was safe on [ext_algo/] ALONE for one reason: wherever  *)
(*  it blocks a row, the answer that replaces it is the EMPTY one, which   *)
(*  is ALSO what the a-side gives ([a_looksub_subject_absent]).  That is   *)
(*  what lets [rel_e_absent_sub] discharge [a_looksub_lookeq_rel_e]        *)
(*  (transport 5, prop_solve_rel.v §7).                                    *)
(*                                                                        *)
(*  ⛔ A ◇-GUARD HAS NO SUCH PROPERTY.  Below, the a-side peels the        *)
(*  vacuous binder and its LS-Var bottom reads the ghost counterpart into  *)
(*  the collection, giving [𝒞 = [≼m ◇]].  A [P' ≠ ◇] guard on the e-side's *)
(*  LS-ForallL leaves LS-Vacuous as the only rule at that cell, and        *)
(*  LS-Vacuous collects [·].  Transport 5 demands [rel_a_cstrs ρ V 𝒞₁ 𝒞₂], *)
(*  a [Forall2] — and the two lists have DIFFERENT LENGTHS.                *)
(* ===================================================================== *)

Open Scope frost_a_scope.

(** The a-side derivation the transport would have to answer: it peels the
    subject at [β] and its [LS-Var] bottom collects the ghost counterpart. *)
Lemma probe_a_forall_l_at_hole : forall α β m,
  β <> α ->
  {{ nil ⊢ (vac_subj α) ≼[ α , m ] pskl_hole ⤳ nil
     ⨾ (a_cstr_sub m pskl_hole :: nil) }}a.
Proof.
  intros α β m Hβ. unfold vac_subj.
  apply a_looksub__forall_l with (β := β).
  - simpl. clear - Hβ. fsetdec.
  - (* the absence-first guard is SATISFIED — vacuous binder over α *)
    simpl. clear. fsetdec.
  - unfold open_pskl_wrt_pskl. simpl. apply a_looksub__var.
Qed.

(** …and a [Forall2] cannot relate its collection to the empty one, whatever
    the pair list and whatever the relation. *)
Lemma probe_rel_cstrs_length_clash :
  forall (R : a_cstr -> a_cstr -> Prop) m,
  ~ Forall2 R (a_cstr_sub m pskl_hole :: nil) (@nil a_cstr).
Proof. intros R m Hc. inversion Hc. Qed.
