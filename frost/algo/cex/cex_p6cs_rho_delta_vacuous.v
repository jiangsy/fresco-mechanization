(** ⚠️ THE PREMISE [Δρ ∩ dom Θ0 = ∅] MAKES A ρ-GENERALIZATION VACUOUS.

    P6-Cs's first ρ-generalization ([a_lookeq_solve_complete_gen],
    prop_look_complete_cstr.v, 2026-07-29) carried

        forall α0, α0 ∈ Δρ -> α0 ∉ dom Θ0      ("ρ's binders postdate Θ0")

    beside [κ ∷ Θ0 ⊑ Θ] and [rho_fresh Δρ Θ κ].  Those three together force
    [Δρ = ∅] — so the "generalized" statement is the ρ = identity one, and
    P6-Ss's Sub-ForallL (which needs Δρ ≠ ∅: it absorbs its guess as
    [ρ ∘ [ψ/β]] for a FRESH RIGID β) could never call it.

    THE REASON is structural, and it is worth remembering for any future
    ρ-style generalization over [a_inc]: an INCREASE NEVER INVENTS A RIGID.
    Read off the rules ([a_inc__tvar] and friends), the target is the source
    with FLEXIBLE suffixes inserted and images refined — [a_suffix] admits
    only [α̂] / [α̂:=τ] entries — so every rigid of the target is a rigid of
    the source ([a_inc_binds_tvar_rev] below, the converse of the existing
    [a_inc_binds_tvar]).  [rho_fresh] then puts every Δρ-variable in Θ0's
    domain, and the premise puts it outside.

    Consequently a ρ-binder introduced by Sub-ForallL MUST enter Θ0 and Θ
    together ([a_inc_cons_tvar]), and the premise it can honestly satisfy is
    the ftv-level one P6-Cs now takes:

        forall α0, α0 ∈ Δρ -> α0 ∉ ftv P0 ∪ ftv Pi

    which is what the old premise was ever used for (via
    [a_wf_pskl_ftv_dom]), and is preserved by every descent. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_look_complete.

Set Implicit Arguments.

(** A suffix carries no rigid entry. *)
Lemma a_suffix_no_tvar : forall Ξ α,
  a_suffix Ξ -> binds α abind_tvar Ξ -> False.
Proof.
  intros Ξ α H; induction H; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
    [ subst; inversion H0 | auto ].
Qed.

(** THE STRUCTURAL FACT: an increase does not invent rigids.  (The converse
    of [a_inc_binds_tvar], prop_inc.v.) *)
Lemma a_inc_binds_tvar_rev : forall Θ0 κ Θ α,
  κ ∷ Θ0 ⊑ Θ ->
  binds α abind_tvar Θ ->
  binds α abind_tvar Θ0.
Proof.
  intros Θ0 κ Θ α Hinc; induction Hinc; intros Hb;
    try solve [ exfalso; eapply a_suffix_no_tvar; eassumption
              | apply binds_cons_3; auto ];
    analyze_binds Hb;
    solve [ exfalso; eapply a_suffix_no_tvar; eassumption
          | apply binds_cons_3; auto
          | unfold binds; left; reflexivity ].
Qed.

(** …hence the refuted premise set. *)
Theorem p6cs_rho_delta_apart_dom_is_vacuous :
  forall Θ0 κ Θ Δρ,
  κ ∷ Θ0 ⊑ Θ ->
  rho_fresh Δρ Θ κ ->
  (forall α0, α0 `in` Δρ -> α0 `notin` dom Θ0) ->
  Δρ [=] empty.
Proof.
  intros Θ0 κ Θ Δρ Hinc Hrfr HΔρΘ0.
  intros α; split; intros Hα; [ | clear - Hα; fsetdec ].
  exfalso.
  destruct (Hrfr α Hα) as (Hb & _ & _).
  pose proof (@a_inc_binds_tvar_rev Θ0 κ Θ α Hinc Hb) as Hb0.
  apply (HΔρΘ0 α Hα). eapply binds_In; exact Hb0.
Qed.
