(** Frost — declarative subtyping metatheory (Phase 2.C).

    Umbrella file: re-exports the split modules under [prop_subtyping/]
    and defines [d_typing_sub_compose], the only top-level lemma that
    must live here (its callers in [prop_typing.v] expect
    [Require Import src.frost.decl.prop_subtyping] to bring it into
    scope). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Require Export src.frost.decl.subtyping.prop_basics.
Require Export src.frost.decl.subtyping.prop_consis_trans.
Require Export src.frost.decl.subtyping.prop_consis_sub_trans.
Require Export src.frost.decl.subtyping.prop_sub_sound.

Set Implicit Arguments.

(** * Composing the [d_typing__sub] step with an outer subsumption.

    This is the helper that extends paper Lemma 3.1 (general subsumption,
    [d_typing_general_subsumption] in [prop_typing.v]) to its [__sub]
    case at mode_ti. Lives here (not in prop_typing.v) because it
    routes through [d_consis_sub_trans] which lives in the
    [consis_extends] split above. *)
Lemma d_typing_sub_compose : forall Γ e A1 A2 B m,
    is_base_term e ->
    Γ ⊢[ mode_ti ] e ⇒ ptyp_to_btyp_syn A1 ->
    Γ ⊢[ mode_ti ; nil ] (ptyp_to_utyp_syn A1) ⊑ ptyp_to_btyp_syn A2 ->
    Γ ⊢[ m ; nil ] (ptyp_to_utyp_syn A2) ⊑ B ->
    d_wf_denv Γ ->
    Γ ⊢[ m ] e ⇒ B.
Proof.
Admitted.
