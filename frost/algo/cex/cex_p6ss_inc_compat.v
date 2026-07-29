(** Machine-checked evidence for the P6-Ss ForallL gap entry
    (docs/PAPER-GAPS.md, "the IH instance needs θψ_b = ψ_b").

    The paper's Sub-ForallL completeness step silently needs [θψ_b = ψ_b]
    for a Θ-scoped guess ψ_b.  The three examples below show that NO side
    condition on θ's treatment of surviving flexibles rescues that step,
    which is why the repair is PROOF-side (a ρ-generalized induction) and
    the paper's statement stays unchanged.

    1. [id_inc_dom_overlap] — Barendregt disjointness [dom θ ∩ dom Θ = ∅]
       is UNSATISFIABLE at identity metasubstitutions: ι's flexible entries
       are all PRESERVED in the target (algorithmic.tex:135), and ι is the
       only kind the algorithms produce (algorithmic.tex:140).

    2. [inc_moves_survivor] — the figure's flex rule constrains the image
       by nothing but well-formedness, so [(α̂, ⟨⟩)] ∷ [α̂] ⊑ [α̂] is
       derivable: θ "solves" α̂ to ⟨⟩ while the target keeps the SAME α̂
       UNDEFINED.  Junk under the intended information-increase reading —
       the slack is in the paper's own definition, and the invariant that
       kills it is [α̂ ∈ dom Θ' ⟹ Θ' ⊢ θα̂ ≡ᵗ α̂] (for an undefined
       survivor, ≡ᵗ forces θα̂ = α̂).

    3. [def_subst_theta_is_legit] — that invariant is the STRONGEST
       defensible one, and it still does not give [θψ_b = ψ_b]: at
       Θ = [α̂ := ⟨⟩] the θ with θα̂ = ⟨⟩ satisfies it (substituting a
       DEFINED survivor's definition — "preserved ... but possibly with
       more monomorphic information"), is inc-EQUIVALENT to ι, and still
       moves a ψ_b that mentions α̂.  Hence no premise on θ repairs the
       paper's written step; only ι-like θ satisfy it syntactically. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.

(** 1: at the identity metasubstitution, dom θ ⊆ dom Θ. *)
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

(** 2: [a_inc] (faithfully mirroring the paper's figure) admits a θ that
    moves an UNDEFINED survivor — junk under the intended reading. *)
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

(** 3: substituting a DEFINED survivor's definition is a LEGITIMATE θ —
    inc-equivalent to the identity — and it moves ψ_b = α̂. *)
Example def_subst_theta_is_legit : forall α,
  ((α, ptyp_unit) :: nil) ∷ ((α ~ abind_flex_mono) ++ nil)
    ⊑ ((α ~ abind_flex_mono_def ptyp_unit) ++ nil)
  /\ a_inc_equiv ((α ~ abind_flex_mono) ++ nil)
       ((α, ptyp_unit) :: nil)            (* θ : substitutes the definition *)
       ((α, ptyp_var_f α) :: nil)         (* ι : the identity               *)
       ((α ~ abind_flex_mono_def ptyp_unit) ++ nil)
  /\ msubst_pskl ((α, ptyp_unit) :: nil) (pskl_var_f α) <> pskl_var_f α.
Proof.
  intros α. repeat split.
  - apply a_inc__flex.
    + apply a_inc__empty.
      apply a_suffix__cons;
        [ apply a_suffix__nil | apply a_suffix_binding__flex_mono_def ].
    + apply a_wf_ptyp__unit.
    + apply mono_ptyp__unit.
  - apply a_inc_equiv__flex.
    + apply a_inc_equiv__empty.
      apply a_suffix__cons;
        [ apply a_suffix__nil | apply a_suffix_binding__flex_mono_def ].
    + apply a_tyequiv__sym.
      apply a_tyequiv__flex_def with (τ := ptyp_unit). auto.
  - cbn. destruct (α == α); [ discriminate | contradiction ].
Qed.
