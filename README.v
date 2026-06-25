(** Frost mechanization index for the current split syntax. *)

Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_general_subsumption.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.decl.prop_safety.
Require Import src.frost.decl.prop_stability.
Require Import src.frost.decl.prop_syntax_directed.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_question.
Require Import src.frost.algo.prop_lemmas.
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

(* Syntax-directed system equivalence — soundness (syntax-directed.tex):
     d_syn_typing M Γ e A  →  d_typing M Γ e A *)
Check d_syn_typing_sound.
Print Assumptions d_syn_typing_sound.

(* Syntax-directed system equivalence — completeness (syntax-directed.tex);
   the base-term ∀-admissibility [dtylab{Forall}] is discharged by the
   [X := unit] type-substitution strengthening:
     d_typing M Γ e A  →  d_syn_typing M Γ e A *)
Check d_syn_typing_complete.
Print Assumptions d_syn_typing_complete.

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

(* Paper Lemma D6 (validity of skeleton inference) was REMOVED: the paper's
   Valid-Skeleton definition is now commented out (declarative.tex), so there
   is no d_pat_validity. *)

(* Paper Lemma D7 (declarative.tex — safety of skeleton inference):
   existential (∃ a safe inference); CHECK mode.  Current "Safe Skeleton"
   def: ∀A with M ⦂ inh{A}, inh{P} ⊳ bid{A} (inferred skeleton painted
   inherited fills to some bidirectional colouring of A).
     Γ ⊢[ mode_tc ] e ⦂ B0  →  d_wf_denv Γ
       →  ∃ Q, Γ ⊢[ mode_tc ] e ⇨ Q
              ∧ (∀ A, Γ ⊢[ mode_tc ] e ⦂ ptyp_to_btyp_inh A
                      → ∃ B, bskl_to_pskl B = ptyp_to_pskl A
                             ∧ Γ ⨟ ∅ ⨟ ∅ ⊢ᵣ pskl_to_bskl_inh (bskl_to_pskl Q) ⊳ B) *)
Check d_pat_safety.

(* === Algorithmic metatheory (faithful question / solution / optimality
   layer, paper algorithmic.tex / proofs.tex / subtyping-proofs.tex).

   The old [a_transfers] placeholder (which related *any* Θ to *any* Γ) is
   replaced by:
     - the metasubstitution / information-increase relation [a_inc] /
       [a_isub] (paper fig:information-increase), in [algo/def_meta.v];
     - the deterministic projection [denv_of] from algorithmic to
       declarative contexts, in [algo/def_meta.v];
     - the [*_solution] / [*_solution_ex] / [*_optimal] predicates
       encoding the paper's questions and (optimal) solutions, in
       [algo/def_question.v].
   The ~11 auxiliary lemmas of proofs.tex §Lemmas are in
   [algo/prop_lemmas.v].  All headline theorems below are [Admitted]
   scaffolding. *)

(* Infrastructure. *)
Check a_inc.        (* Θ ≤[θ] Θ'   (metasubstitution / information increase) *)
Check a_isub.       (* Θ ≤ Θ'      (information increase, some metasubst) *)
Check denv_of.      (* aenv → denv (projection replacing a_transfers) *)

(* Paper Lemma: Soundness of consistency (part 1, type level):
     a_consis Θ0 C B Θ1  →  ∃ θ1, a_inc Θ0 θ1 Θ1 ∧ ∅ ⨟ denv_of Θ1 ⊨ C ≈ B *)
Check a_consis_sound.

(* Paper Theorem: Soundness of subtyping:
     a_sub NM M P0 Θ0 B B1 Θ1  →  ∃ θ1, a_sub_solution M Θ0 P0 B θ1 Θ1 B1 *)
Check a_sub_sound.

(* Paper Theorem: Soundness of type inference:
     a_typing M Θ0 P e A Θ1  →  ∃ θ1, a_typing_solution M Θ0 P e θ1 Θ1 A *)
Check a_typing_sound.

(* Paper Theorem: Soundness of skeleton inference:
     a_pat M Θ0 P0 e P Θ1  →  ∃ θ1, a_pat_solution M Θ0 P0 e θ1 Θ1 P *)
Check a_pat_sound.

(* Paper Lemma: Completeness of consistency (part 1, type level). *)
Check a_consis_complete.

(* Paper Theorem: Completeness & optimality of subtyping:
     a_sub_solution_ex M Θ0 P0 B
       →  ∃ θ1 Θ1 B1, a_sub NM M P0 Θ0 B B1 Θ1 ∧ a_sub_optimal … *)
Check a_sub_complete.

(* Paper Theorem: Completeness & optimality of type inference. *)
Check a_typing_complete.

(* Paper Theorem: Completeness & optimality of skeleton inference. *)
Check a_pat_complete.

(* Representative auxiliary lemmas (proofs.tex §Lemmas). *)
Check a_stable_d_typing.                 (* Lemma: Stability *)
Check a_structural_suffix_moving.        (* Lemma: Structural rules *)
Check a_suffix_erasure.                  (* Lemma: Suffix erasure *)
Check a_split_refine.                    (* Lemma: Splitting refines *)
Check a_consis_extends_sub.              (* Lemma: Consistency extends subtyping *)
Check a_precision_extends_sub.           (* Lemma: Precision extends skeleton subtyping *)
Check a_inherited_refinement_precision.  (* Lemma: Inherited refinement gives precision *)
Check a_context_precision_skeleton.      (* Lemma: Context precision for skeleton inference *)
Check a_subst_preserves_safety.          (* Lemma: Substitution preserves safety *)
Check a_subst_preserves_informativeness. (* Lemma: Substitution preserves informativeness *)
Check a_more_information_no_harm.         (* Lemma: More information does not harm *)
