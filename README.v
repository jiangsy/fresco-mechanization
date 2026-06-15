(** Frost mechanization index for the current split syntax. *)

Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_general_subsumption.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.prop_soundness.
Require Import src.frost.algo.prop_completeness.

Check d_typing_general_subsumption.
Check d_typing_general_subsumption_spine.

Check d_refine_preserves_wf.
Check d_typing_pat_preserves_wf.
Check d_pat_preserves_skel_wf.
Check d_pat_validity.
Check d_pat_safety.

Check d_consis_compose.
Check d_consis_sub_trans.

Check a_sub_sound.
Check a_typing_sound.
Check a_pat_sound.
Check a_sub_complete.
Check a_typing_complete.
Check a_pat_complete.

Print Assumptions d_typing_general_subsumption.
