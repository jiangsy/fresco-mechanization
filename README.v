(** Frost mechanization index for the current split syntax. *)

Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_general_subsumption.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.decl.prop_stability.
Require Import src.frost.algo.prop_soundness.
Require Import src.frost.algo.prop_completeness.

(** Finished properties — each [Check] is paired with its [Print Assumptions]
    (all "Closed under the global context"). *)

(* Paper Lemma 3.1 (General subsumption):
     d_wf_denv Γ  →  Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A
       →  ∅ ⨟ Γ ⊢[ m ] ptyp_to_utyp_syn A ⊑ B  →  Γ ⊢[ m ] e ⦂ B *)
Check d_typing_general_subsumption.
Print Assumptions d_typing_general_subsumption.

(* Paper Lemma B.5 (Generalised general subsumption, FN^n spine):
     Γ ⊢[ m₁ ] e ⦂ Bfull  →  ctx_weaken Γ Γ'  →  is_fn_n n m₁
       →  btyp_spine n Bfull A B Bres  →  ∅ ⨟ Γ' ⊢[ M ] btyp_to_utyp_syn A ⊑ B
       →  Γ' ⊢[ mode_fn_n_subst m₁ M ] e ⦂ Bres *)
Check d_typing_general_subsumption_spine.
Print Assumptions d_typing_general_subsumption_spine.

(* Paper Lemma B.2 (Consistency transitivity):
     Δa ⨟ Γ ⊨ C ≈ ptyp_to_btyp_syn A  →  Δb ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B
       →  ∃ Δc, Δa ∪ Δb ⊆ Δc  ∧  Δc ⨟ Γ ⊨ C ≈ B *)
Check d_consis_compose.
Print Assumptions d_consis_compose.

(* Paper Lemma B.3 (Consistency–subtyping transitivity):
     Δb ⨟ Γ ⊢[ M ] btyp_to_utyp_syn B_A ⊑ B  →  is_syn B_A  →  Δt ⨟ Γ ⊨ T ≈ B_A
       →  ∃ Δ, Δb ⊆ Δ  ∧  Δ ⨟ Γ ⊢[ M ] T ⊑ B *)
Check d_consis_sub_trans.
Print Assumptions d_consis_sub_trans.

(* Argument-order irrelevance (no numbered paper lemma — curried polymorphic
   functions, n-ary, full permutation):
     d_wf_denv Γ  →  Permutation args args'
       →  binds x (∀ⁿ. curry_ptyp args R) Γ  →  binds y (∀ⁿ. curry_ptyp args' R) Γ
       →  Γ ⊢[ m ] curry_exp (var x) args ⦂ R'
       →  Γ ⊢[ m ] curry_exp (var y) args' ⦂ R' *)
Check d_typing_order_irrel.
Print Assumptions d_typing_order_irrel.

(** In-progress properties — stated and [Check]ed, but still depend on admits
    (so no [Print Assumptions] yet). *)

(* Paper Lemma D4 (declarative.tex:1386 — refinement preserves wf):
     Ψ ⨟ Γ ⊢ᵣ Q ⊳ P  →  d_wf_pskl Ψ Γ (bskl_to_pskl P)        [Admitted] *)
Check d_refine_preserves_wf.

(* Typing / pattern-synthesis preserve well-formedness (mutual):
     (Γ ⊢[ m ] e ⦂ B → d_wf_btyp Γ B)  ∧  (Γ ⊢[ m ] e ⇨ Q → d_wf_pskl ∅ Γ Q) *)
Check d_typing_pat_preserves_wf.

(* Paper Lemma D5 (declarative.tex:1976 — preservation of skeleton wf):
     Γ ⊢[ mode_tc ] e ⇨ Q  →  d_wf_denv Γ  →  d_wf_pskl ∅ Γ Q *)
Check d_pat_preserves_skel_wf.

(* Paper Lemma D6 (declarative.tex:1987 — validity of skeleton inference):
     Γ ⊢[ mode_ti ] e ⇨ Q  →  (∃ B, Γ ⊢[ mode_ti ] e ⦂ B)  →  d_wf_denv Γ
       →  ∃ A, Γ ⊢[ mode_tc ] e ⦂ ptyp_to_btyp_inh A
              ∧ ∅ ⨟ Γ ⊢ᵣ Q ⊳ pskl_to_bskl_inh (ptyp_to_pskl A) *)
Check d_pat_validity.

(* Paper Lemma D7 (declarative.tex:1992 — safety of skeleton inference):
     (∃ B, Γ ⊢[ mode_ti ] e ⦂ B)  →  d_wf_denv Γ
       →  ∃ Q, Γ ⊢[ mode_ti ] e ⇨ Q
              ∧ (∀ A, Γ ⊢[ mode_tc ] e ⦂ ptyp_to_btyp_inh A
                      → ∅ ⨟ Γ ⊢ᵣ Q ⊳ pskl_to_bskl_inh (ptyp_to_pskl A)) *)
Check d_pat_safety.

(* Paper Theorem 4.19 (soundness of algorithmic subtyping):
     a_sub NM m P0 Θ0 B1 B2 Θ1  →  a_transfers Θ1 Γ
       →  ∃ C, B1 = utyp_to_btyp C  ∧  ∅ ⨟ Γ ⊢[ m ] C ⊑ B2 *)
Check a_sub_sound.

(* Paper Theorem E.4 (soundness of type inference):
     a_typing m Θ0 P0 e B Θ1  →  a_transfers Θ1 Γ  →  Γ ⊢[ m ] e ⦂ B *)
Check a_typing_sound.

(* Paper Theorem 4.15 (soundness of skeleton inference):
     a_pat m Θ0 P0 e Q Θ1  →  a_transfers Θ1 Γ  →  Γ ⊢[ m ] e ⇨ Q *)
Check a_pat_sound.

(* Paper Theorem 4.19 (completeness of algorithmic subtyping):
     ∅ ⨟ Γ ⊢[ m ] C ⊑ B  →  a_transfers Θ0 Γ
       →  ∃ Θ1 NM P0, a_sub NM m P0 Θ0 (utyp_to_btyp C) B Θ1 ∧ a_transfers Θ1 Γ *)
Check a_sub_complete.

(* Paper Theorem E.5 (completeness & minimality of type inference):
     Γ ⊢[ m ] e ⦂ B  →  a_transfers Θ0 Γ
       →  ∃ Θ1 P0, a_typing m Θ0 P0 e B Θ1 ∧ a_transfers Θ1 Γ *)
Check a_typing_complete.

(* Paper Theorem 4.16 (completeness of skeleton inference):
     Γ ⊢[ m ] e ⇨ Q  →  a_transfers Θ0 Γ
       →  ∃ Θ1 P0, a_pat m Θ0 P0 e Q Θ1 ∧ a_transfers Θ1 Γ *)
Check a_pat_complete.
