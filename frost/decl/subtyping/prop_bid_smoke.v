(** Smoke test for the type-hierarchy refactor.

    Validates: the new [d_sub_bid__infer] (broadened LHS to [utyp], no
    [d_wf_typ Γ T] premise) closes paper B.3's SInfer case cleanly.

    The legacy [d_consis_sub_trans] over [typ] required a [d_wf_typ Γ T]
    premise to rule out tagged LHS at mode_ti — without it, the lemma
    was false (counter-example via [d_consis__forall_syn_tagged]). The
    new bid-typed formulation moves the LHS shape constraint into the
    type system: [d_sub_bid__infer]'s LHS is [utyp] (paper's syn{∀^δ}),
    which is the broad shape the paper actually intends. Tagged LHS is
    now permitted at mode_ti — the broadened rule fires for it via the
    [d_consis_bid__forall_syn_tagged] body.

    So B.3's SInfer case becomes a one-liner: compose the two
    consistencies via B.2 (assumed here as a placeholder), then apply
    [d_sub_bid__infer]. No wf premise, no special-casing of tagged
    shapes.

    The B.2 lemma ([d_consis_compose_bid]) is admitted in this smoke
    test — proving it is a separate effort (~similar size to the
    legacy [d_consis_compose] in [prop_consis_trans.v]). *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.

(** [d_consis_compose_bid]: B.2 over the new types. ADMITTED in this
    smoke test — full proof mirrors the legacy [d_consis_compose] over
    bid shapes. About ~150 lines. *)
Lemma d_consis_compose_bid : forall Δa Δb Γ T A B,
    d_consis_bid Δa Γ T A ->
    d_consis_bid Δb Γ A B ->
    list_disjoint Δa Δb ->
    exists Δc, Permutation Δc (Δa ++ Δb) /\ d_consis_bid Δc Γ T B.
Admitted.

(** [d_consis_sub_trans_bid__infer]: B.3's SInfer case over bid.

    The legacy version of this case required [d_wf_typ Γ T] (the
    spurious-but-load-bearing premise we identified earlier). The new
    version has NO wf premise.

    Proof structure:
    1. Invert [Hs] (d_sub_bid mode_ti) — only [d_sub_bid__infer] fires
       at mode_ti, giving us a [utyp] LHS [F] (with [A = utyp_to_bid F])
       and a body [d_consis_bid nil Γ F D].
    2. Compose [Hc] with the body via B.2: get [d_consis_bid nil Γ T D].
    3. Re-apply [d_sub_bid__infer] (T is already [utyp]).
*)
Lemma d_consis_sub_trans_bid__infer :
  forall Γ (T : utyp) (A : bid) (B : bid),
    d_consis_bid nil Γ T A ->
    d_sub_bid mode_ti nil Γ A B ->
    exists Δc, Permutation Δc nil /\ d_sub_bid mode_ti Δc Γ T B.
Proof.
  intros Γ T A B Hc Hs.
  (* Invert Hs: gives 3 cases at mode_ti — d_sub_bid__infer (productive),
     __forall_l_tagged (with m ≠ mode_ti contradiction), __forall_l_untagged
     (same). *)
  inversion Hs; subst.
  - (* __infer: the productive case. *)
    edestruct d_consis_compose_bid as [Δc [Hperm Hcomp]];
      [ exact Hc
      | eassumption
      | apply list_disjoint_nil_l
      | ].
    rewrite app_nil_r in Hperm.
    apply Permutation_sym, Permutation_nil in Hperm. subst Δc.
    exists nil. split; [reflexivity |].
    apply d_sub_bid__infer; assumption.
  - (* __forall_l_tagged at mode_ti — contradicts m ≠ mode_ti. *)
    match goal with H : mode_ti <> mode_ti |- _ => exfalso; apply H; reflexivity end.
  - (* __forall_l_untagged — same. *)
    match goal with H : mode_ti <> mode_ti |- _ => exfalso; apply H; reflexivity end.
Qed.

(** Compare with the legacy [d_consis_sub_trans] in [prop_consis_sub_trans.v],
    which for the SInfer case requires [d_wf_typ Γ T] as a premise AND
    cannot handle [T = typ_all_etag _] at mode_ti (counter-example via
    [d_consis__forall_syn_tagged]).

    The new version handles tagged T uniformly: [T : utyp] admits both
    [utyp_all_syn] and [utyp_all_etag], and the compose-and-re-infer
    pattern goes through identically for both. *)
