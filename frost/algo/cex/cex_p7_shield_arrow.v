(** ⚠️ [sub_shield] IS UNSATISFIABLE AT AN ARROW P0 AGAINST A TAGGED-IDENTITY
    GUESS — so P7's TASK 0 CANNOT be finished by supplying the premise; the
    premise itself has to move (or the configuration has to be shown
    unreachable).  This is a statement-level fact, independent of any proof
    effort.

    Recall (docs/DESIGN-completeness-subtyping.md §9.0) that P6-L carries
    [sub_shield Θ0 Ψa ∅ P0 ψa], and that §4-§5 of prop_sub_shield_supply.v
    discharge it for every P0 whose counterpart is mono-ish (a raw flexible
    included) and for [□] / [unit] / a rigid variable.  The residual was "P0 an
    ARROW with a non-mono-ish counterpart".  It is not merely unproved:

    [sub_shield]'s [flex_apart_walk] conjunct quantifies over the ρ-WALK, and
    the walk's [fastep_all_r] — the Sub-ForallL step, which P6-Sv's own ForallL
    row builds at prop_look_complete_sub_var.v:2470 — opens a TAGGED quantifier
    of the guess with a fresh β, adds β to Δρ, and LEAVES P0 ALONE.  So from
    ([∅], P0, [∀^ε β. β]) the walk reaches

        flex_apart Θ0 {β} P0 (uskl_var_f β)

    and at an ARROW P0 no rule of [flex_apart] applies: [fa_clean] wants
    [{β} ∩ {β} = ∅]; [fa_unit] / [fa_var_rigid] / [fa_hole] / [fa_tophole] want
    another P0; [fa_topholeg_r] wants a ∀◈ target; [fa_arrow] wants an ARROW
    target; [fa_all_etag] / [fa_all_syn] want a ∀ source.

    TWO WITNESSES, because they say different things:

    · §1 [P0 = ⟨⟩ → ⟨⟩] — FLEX-FREE.  Nothing here needs protecting at all, so
      this instance is an OVERSIGHT: [flex_shield] has a flex-free base rule
      ([fsh_flexfree]) and [flex_apart] simply does not.  Adding the mirror
      rule [fa_flexfree] would fix this instance.
    · §2 [P0 = (∀γ. γ→γ) → α̂] with α̂ a Θ0-flexible — NOT flex-free, and its
      counterpart is NOT mono-ish (the domain refines from a ∀, so it is an
      [all_inh]).  ⚠️ [fa_flexfree] does NOT fix this one.  So the repair is not
      a missing base rule: [fa_clean]'s "the WHOLE guess is Δρ-clean" is the
      wrong shape of condition for a non-aligned pair, and what is actually
      wanted is positional — the guess's Δρ-variables must not land opposite
      P0's FLEXIBLE positions.

    THE REPAIR IS IDENTIFIED, AND IT IS A MISSING MIRROR.  [flex_shield] has

        fsh_rho_var : α ∈ Δρ  →  flex_shield Θ0 Ψ' Δρ P0 (uskl_var_f α)

    (prop_look_complete_sub_var.v:226) whose own comment says exactly why —
    "a ρ-REPLACED RIGID VARIABLE is safe opposite ANY payload, flexible or not:
    this is P6-Cv's leaf, where the precision premise forces Pi to be that very
    variable, SolS-Var / SolE-Var keep it, and the conclusion's precision is the
    var rule, so no dirt reaches the payload however dirty the position is …
    WITHOUT this rule the premise is TOO STRONG".  [flex_apart] has no such
    rule, and the stuck state above is EXACTLY its shape.  Adding [fa_rho_var]
    kills both witnesses.

    ⚠️ WHY IT IS NOT DONE HERE.  [flex_apart] is P6-Cv's REPAIR PREMISE, which
    P6-Sv / P6-Ss / P6-L inherit — reshaping it is a change to a side condition
    the PAPER will have to adopt, so it is the authors' call.  It also has a
    real cost inside the mechanization, measured before backing out:

    · the ~8 [flex_apart] inversion lemmas each gain a case; all but one close
      with [apply fa_rho_var; assumption] (only [flex_apart_tophole_p0_inv]
      actually needed the bullet — the rest discriminate on the target shape);
    · ⚠️ [flex_apart_flex_var_clean] (prop_look_complete.v:2907) genuinely
      BREAKS.  It reads "a flexible P0 forces the guess Δρ-CLEAN", and
      [fa_rho_var] is a second way to hold, so it must weaken to a DISJUNCTION
      whose right arm is "the guess is a Δρ-variable under a stack of ∀◈s".
      Its single consumer — P6-Cs's Arrow row,
      prop_look_complete_cstr.v:2199 — feeds the cleanliness to
      [ad_pat_consis_rho_subst_psia_mono] to conclude "ψa is a mono paint,
      hence tag-free".  That conclusion SURVIVES the new arm (a Δρ-variable IS
      a mono paint) but only after the ∀◈ stack is peeled, which at [SK] is not
      free.  So the rework is real, not clerical.

    Registered in docs/PAPER-GAPS.md. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.def_tags.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_look_complete_cstr.
Require Import src.frost.algo.prop_look_complete_sub_var.
Require Import src.frost.algo.prop_look_complete_sub_cstr.   (* sub_shield *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  The guess, and the one walk step that does the damage                 *)
(* ===================================================================== *)

(** ψa = ∀^ε b. b — the DECORATED identity quantifier.  A legitimate ForallL
    guess: [is_tskl], ghost-free, and tagged by exactly {ε}. *)
Definition ψid (ε : atom) : uskl := uskl_all_etag ε (uskl_var_b 0).

Lemma ψid_tskl : forall ε, is_tskl (ψid ε).
Proof.
  intros ε; unfold ψid.
  apply is_tskl__all_etag with (L := empty); intros α _; cbn.
  apply is_tskl__var.
Qed.

Lemma ψid_tags : forall ε, d_tags_skl (singleton ε) (ψid ε).
Proof.
  intros ε; unfold ψid.
  apply d_tags_skl__all_etag with (L := empty) (Ψ0 := empty);
    [ intros α _; cbn; apply d_tags_skl__var; clear; fsetdec
    | clear; fsetdec
    | clear; fsetdec ].
Qed.

(** Sub-ForallL's walk step: the guess is instantiated at the fresh β, Δρ gains
    β — and P0 is UNTOUCHED. *)
Lemma the_step : forall β ε P0,
  fa_walk empty P0 (ψid ε) (add β empty) P0 (uskl_var_f β).
Proof.
  intros β ε P0. unfold ψid.
  eapply fw_step; [ | apply fw_refl ].
  replace (uskl_var_f β)
    with (open_uskl_wrt_uskl (uskl_var_b 0) (uskl_var_f β)) by reflexivity.
  apply fastep_all_r.
Qed.

(** …and after it, an ARROW source has no [flex_apart] rule left. *)
Lemma no_rule_at_arrow : forall Θ0 β Pa Pb,
  ~ flex_apart Θ0 (add β empty) (pskl_arrow Pa Pb) (uskl_var_f β).
Proof.
  intros Θ0 β Pa Pb H; inversion H; subst;
    (* every congruence row wants another shape; only [fa_clean] survives *)
    try discriminate.
  (* fa_clean : [{β} ∩ {β} = ∅] *)
  match goal with Hc : _ ∩ _ [=] empty |- _ =>
    cbn in Hc;
    assert (Hin : β `in` (singleton β) ∩ (add β empty))
      by (apply inter_3; clear; fsetdec);
    rewrite Hc in Hin; clear - Hin; fsetdec
  end.
Qed.

(** So the shield is unsatisfiable, for ANY arrow P0 and any tag context. *)
Lemma shield_unsatisfiable : forall Θ0 Ψa ε Pa Pb,
  ~ sub_shield Θ0 Ψa empty (pskl_arrow Pa Pb) (ψid ε).
Proof.
  intros Θ0 Ψa ε Pa Pb H.
  (* the walk's fresh Sub-ForallL binder — ANY atom will do *)
  pick fresh β.
  destruct (H (pskl_arrow Pa Pb) empty (ssw_refl _ _)
              ltac:(clear; fsetdec) ltac:(clear; fsetdec)) as [Hwalk _].
  apply (@no_rule_at_arrow Θ0 β Pa Pb).
  apply Hwalk. apply the_step.
Qed.

(* ===================================================================== *)
(*  §1  THE FLEX-FREE INSTANCE — an oversight [fa_flexfree] would fix     *)
(* ===================================================================== *)

(** [⟨⟩ → ⟨⟩] has no free variable at all, so [pskl_flex_free] holds
    vacuously: there is nothing for [flex_apart] to keep apart, and
    [flex_shield] says so with [fsh_flexfree].  [flex_apart] has no such rule,
    and that alone sinks the shield. *)
Theorem p7_shield_arrow_flexfree_is_unsatisfiable :
  forall Θ0 Ψa ε,
  ~ sub_shield Θ0 Ψa empty (pskl_arrow pskl_unit pskl_unit) (ψid ε).
Proof. intros Θ0 Ψa ε. apply shield_unsatisfiable. Qed.

(** …and the payload really is flex-free, so the [fsh_flexfree] mirror WOULD
    discharge it — this is the regression witness for adding [fa_flexfree]. *)
Lemma p7_shield_arrow_flexfree_payload : forall Θ0,
  pskl_flex_free Θ0 (pskl_arrow pskl_unit pskl_unit).
Proof.
  intros Θ0 α Hα. cbn in Hα. exfalso; clear - Hα; fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  THE INSTANCE [fa_flexfree] WOULD NOT FIX                          *)
(* ===================================================================== *)

(** [(∀γ. γ→γ) → α̂] with α̂ a Θ0-flexible: NOT flex-free, and its counterpart
    is not mono-ish either (the domain refines from a ∀, hence lands on an
    [all_inh] — §4 of prop_sub_shield_supply.v does not apply).  So neither the
    mono-counterpart route nor a [fa_flexfree] mirror reaches it. *)
Definition P0poly (a : atom) : pskl :=
  pskl_arrow (pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)))
             (pskl_var_f a).

Theorem p7_shield_arrow_poly_is_unsatisfiable :
  forall Θ0 Ψa a ε,
  ~ sub_shield Θ0 Ψa empty (P0poly a) (ψid ε).
Proof. intros Θ0 Ψa a ε. unfold P0poly. apply shield_unsatisfiable. Qed.

(** …and it is NOT flex-free, whenever α̂ really is a flexible of Θ0 — so the
    [fa_flexfree] mirror is provably not enough. *)
Lemma p7_shield_arrow_poly_not_flexfree : forall Θ0 a,
  binds a abind_flex_mono Θ0 ->
  ~ pskl_flex_free Θ0 (P0poly a).
Proof.
  intros Θ0 a Hb Hff.
  apply (Hff a); [ cbn; clear; fsetdec | left; exact Hb ].
Qed.

Print Assumptions p7_shield_arrow_flexfree_is_unsatisfiable.
Print Assumptions p7_shield_arrow_poly_is_unsatisfiable.
