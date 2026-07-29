(** Machine-checked evidence for the CORRECTED P6-Ss ForallL gap entry
    (docs/PAPER-GAPS.md, "the IH instance needs θψ_b = ψ_b").

    The paper's Sub-ForallL completeness step silently needs [θψ_b = ψ_b]
    for a Θ-scoped guess ψ_b.  Two candidate premises were considered:

    1. Barendregt DISJOINTNESS  [∀ α̂ ∈ dom θ, α̂ ∉ dom Θ]  — WRONG.
       [id_inc_dom_overlap]: the identity metasubstitution — the only kind
       the algorithms produce (algorithmic.tex:140), whose flexible entries
       are all PRESERVED in the target (algorithmic.tex:135) — puts dom θ
       INSIDE dom Θ, so the disjointness premise is unsatisfiable at ι.

    2. COMPATIBILITY-ON-SURVIVORS  [∀ α̂ ∈ dom θ ∩ dom Θ, θα̂ = α̂]  — the
       repair actually proposed.  [inc_moves_survivor] shows it is NOT
       derivable from [κ ∷ Θ0 ⊑ Θ] alone: [a_inc__flex] derives
       [(α̂, ⟨⟩)] ∷ [α̂] ⊑ [α̂], a θ that "solves" α̂ to ⟨⟩ while the target
       still declares the SAME α̂ unsolved — plainly outside the paper's
       intent, but formally admitted.  Hence a lemma premise. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.

(** Fact 1: at the identity metasubstitution, dom θ ⊆ dom Θ — so
    [∀ α̂ ∈ dom θ, α̂ ∉ dom Θ] is UNSATISFIABLE whenever Θ0 has a flexible. *)
Example id_inc_dom_overlap : forall α,
  ((α, ptyp_var_f α) :: nil) ∷ ((α ~ abind_flex_mono) ++ nil)
    ⊑ ((α ~ abind_flex_mono) ++ nil)
  /\ α `in` dom ((α ~ abind_flex_mono) ++ nil).
Proof.
  intros α. split.
  - apply a_inc__flex.
    + apply a_inc__empty.
      apply a_suffix__cons;
        [ apply a_suffix__nil | apply a_suffix_binding__flex_mono ].
    + apply a_wf_ptyp__var. right; left. auto.
    + apply mono_ptyp__var.
  - simpl. fsetdec.
Qed.

(** Fact 2: [a_inc] does NOT force θ to fix a surviving flexible — the
    compatibility condition must be a premise, not a derived fact. *)
Example inc_moves_survivor : forall α,
  ((α, ptyp_unit) :: nil) ∷ ((α ~ abind_flex_mono) ++ nil)
    ⊑ ((α ~ abind_flex_mono) ++ nil).
Proof.
  intros α.
  apply a_inc__flex.
  - apply a_inc__empty.
    apply a_suffix__cons;
      [ apply a_suffix__nil | apply a_suffix_binding__flex_mono ].
  - apply a_wf_ptyp__unit.
  - apply mono_ptyp__unit.
Qed.
