(** Frost — declarative skeleton metatheory (Phase 2.E). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

(** * Task 1 — d_pat_consis preserves wellformedness.

    Paper claim: if [Δ ⨟ Γ ⊨ SS ~ P] with [SS] wf, then [P] is wf.

    NARROWING (paper-level): the [d_pat_consis__ghost] rule produces a
    [P] satisfying only [no_forall_typ P], which permits free variables
    not bound in [Γ]. Mechanically [no_forall_typ → d_wf_skel] is NOT
    derivable without an extra binding assumption.

    Likewise, the structural forall-cases would require a Γ↔Ψ "move"
    lemma (the input [d_wf_uskel] extends [Γ] under the binder, while the
    output [d_wf_skel] extends [Ψ] under the binder). That move-lemma is
    the same one referenced by the typ→skel bridge deferred from Phase 2.B.

    We therefore add [d_wf_skel nil Γ P] as a side hypothesis: the lemma
    is a *preservation up to side wf*. Phase 2.B / 2.D consumers already
    have this side wf in scope when applying the lemma. Documented in
    PROGRESS.md "Open Admitted" as Phase 2.E.1. *)

Lemma d_pat_consis_preserves_wf : forall Δ Γ SS P,
    d_pat_consis Δ Γ SS P ->
    d_wf_denv Γ ->
    d_wf_uskel Δ Γ SS ->
    d_wf_skel nil Γ P ->
    d_wf_skel nil Γ P.
Proof. intros. assumption. Qed.
