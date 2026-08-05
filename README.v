(** Frost re-mechanization — compilable paper-to-Coq theorem index.

    One [Check] per mechanized paper claim, plus [Print Assumptions] for the
    flagship theorems (the build tail shows them; they must all print
    "Closed under the global context"). *)

Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_syntax_directed.
Require Import src.frost.decl.prop_general_subsumption.
Require Import src.frost.algo.decorated_algo.prop_decorate.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_soundness_consis.
Require Import src.frost.algo.prop_consis_rename.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.test_unify_regression.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_completeness_consis.
Require Import src.frost.algo.decorated_algo.prop_decorate_key.
Require Import src.frost.algo.prop_completeness_sub_precise.
Require Import src.frost.algo.completeness_look.prop_eq_var.
Require Import src.frost.algo.completeness_look.prop_eq_cstr.
Require Import src.frost.algo.completeness_look.prop_sub_var.
Require Import src.frost.algo.completeness_look.prop_sub_cstr.
Require Import src.frost.algo.completeness_look.prop_extract.
Require Import src.frost.algo.prop_completeness_sub.

(* ===================================================================== *)
(*  full-decl-proofs.tex / app:syntax-directed                            *)
(* ===================================================================== *)

(* Lemma [Soundness of Syntax-Directed Rule] (lemma:typing-syn-soundness) *)
Check d_sd_typing_sound :
  forall M Γ e A, d_sd_typing M Γ e A -> d_typing M Γ e A.

(* Lemma [Completeness of Syntax-Directed Rule] (lemma:typing-syn-completeness) *)
Check d_sd_typing_complete.

(* ===================================================================== *)
(*  consistency-proofs.tex (appendix B)                                   *)
(* ===================================================================== *)

(* Lemma [Decorating algorithmic consistency]
   (lemma:decorating-algorithmic-consistency) *)
Check a_consis_decorate.

(* Lemma [Soundness of consistency] (thm:sound-consistency): the MUTUAL
   soundness bundle over [a_assign] + [a_unify] + [a_consis].  BOTH auxiliary
   judgments drop back into consistency — the paper's two-slot [∼] is the
   OUTPUT-SUPPRESSED CONSISTENCY abbreviation (full-algo-spec.tex:1440-1442),
   so [Flex-Flex-Assign] AND [Assign-Assign] both recurse into it (the
   reference implementation agrees: both call [join_sk], type.ml:316-321,
   :358-363).  All three are therefore one SCC, and their soundness is ONE
   3-WAY mutual induction — exactly as the paper organises its own proof
   ("together with the two auxiliary judgements of variable unification and
   assignment", consistency-proofs.tex:1562).  Parts 2 & 3 packaged below. *)
Check a_assign_unify_consis_sound.
Check a_unify_sound.
Check a_assign_sound.

(* The BRIDGE both ways (algo/prop_mono_bridge.v): on monotypes,
   consistency's join + the input's refinement yield a type EQUIVALENCE,
   and conversely a type equivalence yields consistency of the paintings —
   what the corrected [Flex-Flex-Assign] produces and consumes. *)
Check consis_refine_mono_tyequiv.
Check tyequiv_mono_consis.
Check consis_mono_trans.

(* REGRESSION (algo/test_unify_regression.v): the instance the pre-fix
   [a_unify] was machine-checked to be STUCK on now succeeds. *)
Check a_unify_succeeds_on_arrow_definition.

(* Lemma [Soundness of decorated consistency]
   (lemma:sound-decorated-consistency): the main induction, over the
   tagged/decorated consistency judgment, threading the tag context Ψ. *)
Check a_consistag_sound_aux.

(* Lemma [Precision preserves refinement]
   (lemma:precision-preserves-refinement, full-algo-spec.tex:716).
   Precision is refinement between the two inherited paintings, so this is
   transitivity of refinement — which holds exactly because the paper requires
   the refinement judgment's arguments to be well-formed (declarative.tex:1427).
   Without that condition refinement is NOT transitive: see
   algo/cex_refine_not_transitive.v.  Cf. docs/WF-SIDE-CONDITIONS.md. *)
Check ad_refine_syn_trans.
Check ad_precise_preserves_refine.

(* Lemma [Soundness of consistency] (thm:sound-consistency), part 1:
   the paper-shaped corollary (Δ-contexts empty).  The ordinary
   induction is DERIVED from the decorated one via [a_consis_decorate]. *)
Check a_consis_sound.

(* Information-increase algebra (the paper's "stability" infrastructure) *)
Check a_isub_refl.
Check a_isub_weaken_suffix.
Check a_isub_trans.

(* Theorem [Completeness and optimality of consistency]
   (thm:complete-consistency, consistency-proofs.tex:2225-3167), all three
   parts: the μ-indexed bundle [complete_mu] and the paper-shaped corollary. *)
Check a_consis_complete_thm.
Check complete_mu.

(* Theorem [Soundness of subtyping] (thm:sound-subtyping): an algorithmic
   subtyping run is an information increase whose output is a declarative
   subtype of the subject and a valid fill of the input skeleton.  Assembled
   from decoration ([a_sub_decorate]) + soundness of the DECORATED system
   ([a_subtag_sound_bundle]). *)
Check a_sub_sound_thm.

(* Lemma [Stability of subtyping under more precise substitution]
   (subtyping-proofs.tex:1664) — P5, the first half of thm:complete-subtyping. *)
Check ad_pat_sub_precise_upre.

(* Lemma [Completeness of consistency constraint collection and solving]
   (consistency-proofs.tex:920) and its variable case (:1180) — P6-Cs / P6-Cv.
   P6-Cs carries one paper-external wf side condition (well-formedness of the
   consistency subject) whose NECESSITY is machine-checked in
   algo/cex/cex_p6cs_subject_wf.v; see docs/WF-SIDE-CONDITIONS.md. *)
Check a_lookeq_solve_complete.
Check a_solve_eq_complete_var.

(* Lemma [Completeness of subtyping constraint collection and solving]
   (subtyping-proofs.tex:1696) and its variable case — P6-Ss / P6-Sv.  BOTH are
   REPAIRED statements: the paper's P6-Sv is FALSE (machine-checked counter-
   example algo/cex/cex_p6sv_forall_flex.v), and P6-Ss's Sub-ForallR needs a
   mode-guarded ftv-𝒞 disjunction because the sub-side analogue of
   [ad_pat_consis_target_ftv] is FALSE (algo/cex/cex_p6ss_sub_target_ftv.v).
   See docs/PAPER-GAPS.md. *)
Check a_looksub_solve_complete.
Check a_solve_sub_complete_var.

(* Lemma [Look completeness] (subtyping-proofs.tex:2730) — P6-L, the last of
   P6's five lemmas.  Wraps P6-Ss at [Pi = □] / [Ψi = ∅], upgrades ⊑ᵖ to ⊑ via
   [ad_partial_precise_complete] (P5b-i) and supplies the guess^N step — at TY
   by building [a_guess_mono] and the metasubstitution extension at once
   ([a_guess_ty_witness]). *)
Check a_extract_complete_gen.
Check a_extract_complete.

(* ⭐⭐⭐ Theorem [Completeness of subtyping] (thm:complete-subtyping,
   algorithmic.tex:1446) — P7, and UNCONDITIONAL since 2026-08-05.  It used to
   take [forall n, main_forall n] as a hypothesis, whose one unsupplied
   premise was the mech-invented [sub_shield]; under the authors' repaired
   [SolE-FlexR] that gate is discharged outright ([sub_shield_empty]).
   [a_sub_complete_bundle_holds] is the mutual main ⇄ flex bundle;
   [a_sub_complete_thm] is its [Ψ := ∅], [R := ⌈P⌉ᵘ] instance.
   Premises beyond the paper's are the EXTERNAL wf side conditions of
   docs/WF-SIDE-CONDITIONS.md (well-formedness of the counterpart, and the
   subject's ghost-freeness at the TY sort). *)
Check a_sub_complete_bundle_holds.
Check a_sub_complete_thm.

(* ===================================================================== *)
(*  Assumption audit — all must be "Closed under the global context"      *)
(* ===================================================================== *)

Print Assumptions d_sd_typing_sound.
Print Assumptions d_sd_typing_complete.
Print Assumptions d_sd_typing_general_subsumption.
Print Assumptions d_typing_general_subsumption.
Print Assumptions d_sd_typing_general_subsumption_spine.
Print Assumptions a_consis_decorate.
Print Assumptions a_isub_trans.
Print Assumptions a_assign_unify_consis_sound.
Print Assumptions a_unify_sound.
Print Assumptions a_assign_sound.
Print Assumptions tyequiv_mono_consis.
Print Assumptions a_unify_succeeds_on_arrow_definition.
Print Assumptions a_consistag_sound_aux.
Print Assumptions ad_precise_preserves_refine.
Print Assumptions a_consis_sound.
Print Assumptions a_consis_complete_thm.
Print Assumptions complete_mu.
Print Assumptions a_sub_sound_thm.
Print Assumptions ad_pat_sub_precise_upre.
Print Assumptions a_solve_eq_complete_var.
Print Assumptions a_lookeq_solve_complete.
Print Assumptions a_solve_sub_complete_var.
Print Assumptions a_looksub_solve_complete.
Print Assumptions a_extract_complete.
Print Assumptions a_sub_complete_bundle_holds.
Print Assumptions a_sub_complete_thm.
Print Assumptions a_extract_complete_gen.
Print Assumptions a_extract_complete.
