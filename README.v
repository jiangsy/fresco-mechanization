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
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_precise.

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

(* Lemma [Soundness of consistency] (thm:sound-consistency), parts 2 & 3:
   variable unification and assignment. *)
Check a_unify_sound.
Check a_assign_sound.

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
Print Assumptions a_unify_sound.
Print Assumptions a_assign_sound.
Print Assumptions a_consistag_sound_aux.
Print Assumptions ad_precise_preserves_refine.
Print Assumptions a_consis_sound.
