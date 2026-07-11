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

(* ===================================================================== *)
(*  full-decl-proofs.tex / app:syntax-directed                            *)
(* ===================================================================== *)

(* Lemma [Soundness of Syntax-Directed Rule] (lemma:typing-syn-soundness) *)
Check d_sd_typing_sound :
  forall M Γ e A, d_sd_typing M Γ e A -> d_typing M Γ e A.

(* Lemma [Completeness of Syntax-Directed Rule] (lemma:typing-syn-completeness) *)
Check d_sd_typing_complete.

(* Lemma [General subsumption] (on the syntax-directed side + d_typing corollary) *)
Check d_sd_typing_general_subsumption.
Check d_typing_general_subsumption.
Check d_sd_typing_general_subsumption_spine.
Check d_typing_general_subsumption_spine.

(* ===================================================================== *)
(*  consistency-proofs.tex (appendix B)                                   *)
(* ===================================================================== *)

(* Lemma [Decorating algorithmic consistency]
   (lemma:decorating-algorithmic-consistency) *)
Check a_consis_decorate.

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
