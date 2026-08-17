(** PROBE (2026-08-17): §8c.12's motive must relate the runner's output to
    the derivation's by [a_inc], NOT by the identity shorthand [⊴].
    (docs/HANDOFF-extractable-algo-encoding.md §8c.12a.)

    ⚠️ §8c.12a's first write-up of the motive said the context clause becomes
    [cs_ctx r ⊴ swaps_aenv ps Θd].  That is TOO STRONG, and the counterexample
    is one [U-Arrow] away from the divergent ghost cell — i.e. it is reached
    by the very configuration the lift exists to handle.

    ⚙ WHERE THE TWO CONTEXTS COME FROM.  At [Θ = (β̂)], pattern [β̂ → β̂],
    subject [◇ → 1], the arrow's two halves run in sequence:

      RUNNER      half 1 takes U-Ghost      (Θ untouched, answer β̂)
                  half 2 takes U-FlexR      assign β̂ ≔ 1, so SolveM
                  ⇒ output  β̂ ≔ 1

      DERIVATION  half 1 may take U-FlexR   assign β̂ ≔ ◇, and guess^TY(◇)
                                            invents a FRESH flexible γ̂,
                                            so β̂ ≔ γ̂ with γ̂ declared
                  half 2 then finds β̂ DEFINED, so Assign-Assign substitutes
                                            γ̂ for β̂ and solves γ̂ ≔ 1
                  ⇒ output  β̂ ≔ γ̂, γ̂ ≔ 1

    The two agree on everything the equational theory can see — in the
    derivation's context [β̂ ≡ᵗ γ̂ ≡ᵗ 1] — but they DISAGREE syntactically on
    what [β̂] is defined to be.  ⚙ The routing above is by INSPECTION of the
    rules and the runner's dispatch; what is machine-checked here is the
    claim about the two CONTEXTS, which is what the motive quantifies over.

    ⭐ [a_isub] has TWO conjuncts, and it is the second that fails: it
    demands definitions be preserved SYNTACTICALLY
    ([binds α (flex_def τ) Θ -> binds α (flex_def τ) Θ']), and the
    derivation's [β̂ ≔ γ̂] is an ALIAS where the runner committed to
    [β̂ ≔ 1].  The [a_inc] half survives, because [a_inc__flex_def] asks only
    for [Θ' ⊢ τ' ≡ᵗ κτ] — equivalence, not equality — and the alias chain
    supplies it.

    ⇒ §8c.12's motive must carry [a_inc] (an identity metasubstitution is
    enough — see §2 below, whose witness IS the identity), and the increase
    lemma is still usable: [⊴]'s FIRST conjunct is exactly that [a_inc]. *)

From Coq Require Import Lists.List.
From Metalib Require Import Metatheory.

From src Require Import frost.notations.
From src Require Import frost.def_shapes.
From src Require Import frost.algo.def_rules.
From src Require Import frost.algo.def_meta.

Open Scope frost_a_scope.

(** The runner committed; the derivation went through a fresh alias. *)
Definition runner_out (β : atom) : aenv :=
  (β ~ abind_flex_mono_def ptyp_unit) ++ nil.
Definition deriv_out (β γ : atom) : aenv :=
  (β ~ abind_flex_mono_def (ptyp_var_f γ))
  ++ (γ ~ abind_flex_mono_def ptyp_unit) ++ nil.

(* ===================================================================== *)
(*  §1  ⛔ [⊴] FAILS — its definition-preservation conjunct is syntactic  *)
(* ===================================================================== *)

(** ⚙ [γ̂] is the name [guess^TY(◇)] invented, so it is FRESH — without
    [β ≠ γ] the two contexts would name the same variable twice and
    [binds] (which is [In], not first-match) would find the unit
    definition after all. *)
Lemma probe_isub_fails : forall β γ, β <> γ ->
  ~ ((runner_out β) ⊴ (deriv_out β γ)).
Proof.
  intros β γ Hne [_ Hdef].
  assert (Hb : binds β (abind_flex_mono_def ptyp_unit) (runner_out β))
    by (unfold runner_out, binds; left; reflexivity).
  pose proof (Hdef _ _ Hb) as Hb'.
  unfold deriv_out in Hb'.
  destruct (binds_cons_1 _ _ _ _ _ _ Hb') as [[? Heq] | Hb2];
    [ discriminate | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb2) as [[Heq2 ?] | Hb3];
    [ apply Hne; exact Heq2 | inversion Hb3 ].
Qed.

(* ===================================================================== *)
(*  §2  ⭐ [a_inc] SURVIVES, at the IDENTITY metasubstitution              *)
(* ===================================================================== *)

Lemma probe_inc_holds : forall β γ, β <> γ ->
  ((β, ptyp_var_f β) :: nil) ∷ (runner_out β) ⊑ (deriv_out β γ).
Proof.
  intros β γ Hne. unfold runner_out, deriv_out.
  apply a_inc__flex_def.
  - apply a_inc__empty.
    apply a_suffix__cons; [ | apply a_suffix_binding__flex_mono_def ].
    apply a_suffix__cons; [ | apply a_suffix_binding__flex_mono_def ].
    apply a_suffix__nil.
  - apply a_wf_ptyp__var. right; right. exists (ptyp_var_f γ).
    unfold binds; left; reflexivity.
  - apply mono_ptyp__var.
  - (* β̂ ≡ᵗ γ̂ ≡ᵗ 1, the alias chain — and [msubst] of the identity is [1] *)
    simpl. apply a_tyequiv__trans with (B := ptyp_var_f γ).
    + apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
    + apply a_tyequiv__flex_def. unfold binds; right; left; reflexivity.
Qed.
