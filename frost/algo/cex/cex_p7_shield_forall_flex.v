(** ⚠️ THE P7 SHIELD RESIDUAL IS UNDERIVABLE AT ITS DANGER SHAPE.

    TASK 0's residual (docs/DESIGN-completeness-subtyping.md §9.0.2) is a [P0]
    carrying a ∀ BELOW its head; [prop_sub_shield_supply.v] closes every other
    shape.  This file settles the FIRST half of the question — whether the
    residual instance of [sub_shield] can hold at all.

    WHAT IS MACHINE-CHECKED HERE.  For a Θ0-FLEXIBLE [α̂] and a tag [ε ∈ Ψ'],

      flex_shield Θ0 Ψ' Δρ α̂ (∀^ε β. β→β)          is UNDERIVABLE, and hence
      sub_shield  Θ0 Ψ' ∅ ((∀γ.γ) → α̂) (∀^ε β. β→β) is UNDERIVABLE

    — the second because [ss_walk] reaches the codomain [α̂] in one
    [sss_arrow_r] step, and [sub_shield] demands the shield at EVERY
    walk-reachable [P0]-part against the WHOLE fixed guess [ψa].  The leaf is
    stuck for a structural reason with no escape: [fsh_clean] is blocked by
    the tag, [fsh_flexfree] by the flexible, and [fsh_all_r] only descends
    into [α → α] at [add α Δρ], where [fsh_clean] is blocked by α itself and
    every congruence by a shape mismatch (P0 is a variable, ψa an arrow).
    This is the [cex_p6sv_forall_flex.v] configuration, reached from a [P0]
    that has a ∀ as well as a flexible.

    WHAT THIS DOES **NOT** ESTABLISH.  That the P7b Sub-ForallL rows can
    actually be REACHED with this [(P0, ψa)] pair and [ε ∈ Ψa] — i.e. that
    the ambient join [ad_pat_sub_gv n NM M (Ψ ∪ Ψa) Θ (open Rj ψa) Q] and
    fill [Θ ⊢ᵣ inh{κP0} ⊳ Q] are jointly inhabited there.  Note the fill does
    NOT rule it out the way it rules out the ∀-free case: with a ∀ inside
    [P0], [κP0] carries a ∀, the fill may emit a [bskl_all_inh], [Q] is not
    [bskl_inh_free], and [ad_pat_sub_g_inh_free_tag_free] no longer collapses
    [Ψa] to ∅ — which is exactly why [sub_shield_supply_all_free_p0] stops
    covering this shape.

    IF the configuration is realizable, the conclusion is NOT that P6-Ss is
    false but that [sub_shield] — a MECH-INVENTED repair premise, not a paper
    statement — is over-strong: it is indexed NON-POSITIONALLY, pairing every
    walk-reachable [P0]-part with the whole guess [ψa], while the derivation
    aligns [ψa] with ONE position only (here the domain, facing the inherited
    ∀ of [Q], where its tag is legitimately solved).  The repair would be a
    positional re-indexing, and it would have to be replayed through P6-Ss and
    P7b's two ForallL rows, which consume the current shape.

    Nothing here is committed to docs/PAPER-GAPS.md: no paper statement is
    refuted, and the realizability half is open. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_look_complete_sub_var.
Require Import src.frost.algo.prop_look_complete_sub_cstr.

Set Implicit Arguments.

Definition cexψ (e : atom) : uskl :=
  uskl_all_etag e (uskl_arrow (uskl_var_b 0) (uskl_var_b 0)).

(** THE STUCK LEAF.  A raw Θ0-flexible facing a TAGGED ∀ with a COMPOUND
    body admits no [flex_shield] rule at all: [fsh_clean] is blocked by the
    tag, [fsh_flexfree] by the flexible, [fsh_all_r] descends into
    [α → α] at [add α Δρ] where [fsh_clean] is blocked by α itself and
    every congruence by a shape mismatch. *)
Lemma flex_shield_raw_flex_tagged_arrow_stuck : forall Θ0 Ψ' Δρ f e,
  binds f abind_flex_mono Θ0 ->
  e `in` Ψ' ->
  ~ flex_shield Θ0 Ψ' Δρ (pskl_var_f f) (cexψ e).
Proof.
  intros Θ0 Ψ' Δρ f e Hb He Hs.
  unfold cexψ in Hs.
  inversion Hs; subst.
  - (* fsh_clean : the tag is in Ψ' *)
    match goal with
    | H : _ [=] empty |- _ => simpl in H; clear - H He; fsetdec
    end.
  - (* fsh_flexfree : f IS flexible *)
    match goal with
    | H : pskl_flex_free _ _ |- _ =>
        apply (H f); [ simpl; clear; fsetdec | left; exact Hb ]
    end.
  - (* fsh_all_r : descend, then nothing fires *)
    match goal with
    | H : forall α, α `notin` ?L -> _ |- _ =>
        destruct (atom_fresh L) as [α Hα];
        pose proof (H α Hα) as Hs2
    end.
    cbn in Hs2.
    inversion Hs2; subst.
    + (* fsh_clean : α is in both the payload's ftv and Δρ *)
      simpl in *. fsetdec.
    + (* fsh_flexfree : f IS flexible *)
      match goal with
      | H : pskl_flex_free _ _ |- _ =>
          apply (H f); [ simpl; clear; fsetdec | left; exact Hb ]
      end.
Qed.

(** …hence the shield FAILS for any [P0] whose [ss_walk] reaches such a
    flexible — the smallest is [(∀γ.γ) → α̂], which is exactly a [P0] with a
    ∀ AND a flexible, i.e. the documented residual. *)
Lemma sub_shield_forall_flex_p0_fails : forall Θ0 Ψ' f e,
  binds f abind_flex_mono Θ0 ->
  e `in` Ψ' ->
  ~ sub_shield Θ0 Ψ' empty
      (pskl_arrow (pskl_all_syn (pskl_var_b 0)) (pskl_var_f f)) (cexψ e).
Proof.
  intros Θ0 Ψ' f e Hb He Hsh.
  destruct (Hsh (pskl_var_f f) empty
              ltac:(eapply ssw_step; [ apply sss_arrow_r | apply ssw_refl ])
              ltac:(clear; fsetdec) ltac:(clear; fsetdec))
    as [_ Hfs].
  exact (flex_shield_raw_flex_tagged_arrow_stuck Hb He Hfs).
Qed.

Print Assumptions sub_shield_forall_flex_p0_fails.
