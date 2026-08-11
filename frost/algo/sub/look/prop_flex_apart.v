(** P6 — FLEXIBLE APARTNESS, and the Arrow-case repair built on it.

    The second half of the P6 shared substrate; [prop_rho_relation.v] is the first.
    Where that file carries the ρ representation and the κ-extension /
    [solve_ext] packages, this one carries the invariant that makes the
    ARROW case go through:

    [flex_apart Θ0 Δρ P0 ψa] — every FLEXIBLE-variable position of the solve
    counterpart [P0] faces a Δρ-CLEAN part of [ψa], i.e. no ρ-replaced leaf
    sits below it.  It is the reachability fact the LE-FlexR freshening
    guarantees (cex/cex_p6_flex_freshened.v), it is VACUOUS at every ρ = id
    call site, and it is maintained inside the P6 cluster only.

    Also here, because they exist to serve that invariant: [pskl_flex_free]
    (raw flexible-freedom of a payload), [bskl_monoish], the P0-only walk
    [p0_step] / [p0_walk] (P6-Cs), [flex_apart_deep], and the tagged-∀ repair
    kit of DESIGN §6(l)/(m).

    ⚙ SPLIT 2026-08-09 out of prop_rho_relation.v — see that file's tail for why. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_subtyping.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.consis.prop_consis_precise.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.algo.sub.prop_completeness_sub_precise.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_compose.   (* a_inc_dom_flex, a_inc_lookup_mono *)
Require Import src.frost.algo.sub.look.prop_rho_relation.
Require Import src.frost.algo.sub.look.prop_solve_ext.

(* ⚠️ Per-FILE flag, and load-bearing: it was line 84 of the old prop_kit.v, so
   the split left this half without it.  Most lemmas here have the shape
   [forall Θ0 P.., Pred .. -> ..], whose leading arguments are strictly
   implicit; without the flag a call like [pskl_flex_free_arrow_inv Hff] reads
   [Hff] as the [aenv].  ⚙ Worse, the failure is SILENT inside [match goal]:
   the pattern matches, the branch BODY fails to typecheck, and the match then
   reports only "No matching clauses for match" at the enclosing tactic. *)
Set Implicit Arguments.

(* ===================================================================== *)
(*  The flexible-apartness premise (Arrow-case repair, option (i)).        *)
(*  [flex_apart Θ0 Δρ P0 ψa]: every FLEXIBLE-variable position of the      *)
(*  solve counterpart P0 faces a Δρ-CLEAN part of ψa (no ρ-replaced leaf   *)
(*  below it).  This is the reachability fact the LE-FlexR freshening      *)
(*  guarantees (cex_p6_flex_freshened.v): a raw Θ0-flex payload never      *)
(*  sits opposite a compound covering a ρ-substituted position.  It is     *)
(*  VACUOUS at every ρ = id call site (fa_clean with Δρ = ∅) and is        *)
(*  maintained internally by the P6 lemma cluster only.                    *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  Raw-flexible-freedom of a payload                                     *)
(* ===================================================================== *)

(** [pskl_flex_free Θ0 P]: no free variable of [P] is a FLEXIBLE of [Θ0]
    (declared or defined).  Stated over [ftvar_in_pskl] rather than
    structurally, so the opening / weakening facts below are set algebra
    instead of inductions. *)
Definition pskl_flex_free (Θ0 : aenv) (P : pskl) : Prop :=
  forall α, α `in` ftvar_in_pskl P -> ~ a_flex_tvar Θ0 α.

Lemma pskl_flex_free_arrow_inv : forall Θ0 P1 P2,
  pskl_flex_free Θ0 (pskl_arrow P1 P2) ->
  pskl_flex_free Θ0 P1 /\ pskl_flex_free Θ0 P2.
Proof.
  intros Θ0 P1 P2 H; split; intros α Hα; apply H; simpl; clear - Hα; fsetdec.
Qed.

Lemma pskl_flex_free_tophole_inv : forall Θ0 P,
  pskl_flex_free Θ0 (pskl_tophole P) -> pskl_flex_free Θ0 P.
Proof. intros Θ0 P H α Hα; apply H; simpl; exact Hα. Qed.

(** Substituting a NON-flexible variable preserves flex-freedom. *)
Lemma pskl_flex_free_subst : forall Θ0 P α1 α2,
  pskl_flex_free Θ0 P ->
  ~ a_flex_tvar Θ0 α2 ->
  pskl_flex_free Θ0 (subst_pskl_in_pskl (pskl_var_f α2) α1 P).
Proof.
  intros Θ0 P α1 α2 H H2 α Hα.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f α2) α1)
    as Hup.
  simpl in Hup.
  destruct (α == α2) as [-> | Hne]; [ exact H2 | ].
  apply H. clear - Hα Hup Hne; fsetdec.
Qed.

(** Opening a ∀-body with a fresh RIGID binder, in the context extended by
    that binder. *)
Lemma pskl_flex_free_open_tvar : forall Θ0 P γ,
  pskl_flex_free Θ0 (pskl_all_syn P) ->
  γ `notin` dom Θ0 ->
  pskl_flex_free ((γ ~ abind_tvar) ++ Θ0)
    (open_pskl_wrt_pskl P (pskl_var_f γ)).
Proof.
  intros Θ0 P γ H Hγ α Hα Hflex.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f γ)) as Hup.
  simpl in Hup.
  destruct (α == γ) as [-> | Hne].
  - (* the fresh binder is RIGID in the extended context *)
    destruct Hflex as [Hb | [τ Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
      solve [ discriminate Habs
            | exfalso; apply Hγ; eapply binds_In; exact Hb' ].
  - apply (H α); [ simpl; clear - Hα Hup Hne; fsetdec | ].
    destruct Hflex as [Hb | [τ Hb]];
      [ left | right; exists τ ];
      (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq _] | Hb'];
       [ contradiction | exact Hb' ]).
Qed.

Lemma pskl_flex_free_weaken_tvar : forall Θ0 P γ,
  pskl_flex_free Θ0 P ->
  pskl_flex_free ((γ ~ abind_tvar) ++ Θ0) P.
Proof.
  intros Θ0 P γ H α Hα Hflex.
  apply (H α Hα).
  destruct Hflex as [Hb | [τ Hb]];
    [ left | right; exists τ ];
    (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
     [ discriminate Habs | exact Hb' ]).
Qed.

Inductive flex_apart (Θ0 : aenv) (Δρ : atoms) : pskl -> uskl -> Prop :=
| fa_clean : forall P0 ψa,
    (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
    flex_apart Θ0 Δρ P0 ψa
| fa_unit : forall ψa, flex_apart Θ0 Δρ pskl_unit ψa
| fa_var_rigid : forall α ψa,
    binds α abind_tvar Θ0 ->
    flex_apart Θ0 Δρ (pskl_var_f α) ψa
| fa_hole : forall ψa, flex_apart Θ0 Δρ pskl_hole ψa
| fa_tophole : forall P0 ψa,
    flex_apart Θ0 Δρ P0 ψa ->
    flex_apart Θ0 Δρ (pskl_tophole P0) ψa
(* ⚠️ NO [fa_topholeg_t] ROW (DESIGN §10.5).  Letting a ∀◈ target inherit the
   guard from its body is the ONLY way a guard can hold at a ∀◈ that is neither
   [fa_clean] nor [fa_flexfree], and with [fa_rho_var] present that produces a
   "∀◈-STACK over a Δρ-variable" — a shape the flexible-P0 read-off then has to
   report and no consumer can use (it is not a mono paint, and there is no
   [var ⊑ᵖ topholeg] precision rule).  Dropping the row costs NOTHING: every
   producer was a transport re-applying it while rebuilding a derivation, never
   a consumer building one, and [flex_apart_topholeg_target_inv] — the direction
   that IS used, stripping a ∀◈ off the target — still holds, since [fa_clean]
   and [fa_flexfree] both survive the strip. *)
| fa_arrow : forall P1 P2 ψ1 ψ2,
    flex_apart Θ0 Δρ P1 ψ1 ->
    flex_apart Θ0 Δρ P2 ψ2 ->
    flex_apart Θ0 Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2)
| fa_all_tag : forall L ε P0 ψ,
    (forall α, α `notin` L ->
       flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0 (pskl_var_f α))
                        (open_uskl_wrt_uskl ψ (uskl_var_f α))) ->
    flex_apart Θ0 Δρ (pskl_all_syn P0) (uskl_all_tag ε ψ)
| fa_all_syn : forall L P0 ψ,
    (forall α, α `notin` L ->
       flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0 (pskl_var_f α))
                        (open_uskl_wrt_uskl ψ (uskl_var_f α))) ->
    flex_apart Θ0 Δρ (pskl_all_syn P0) (uskl_all_syn ψ)
(* ===================================================================== *)
(*  THE TWO BASE ROWS [flex_shield] HAS AND THIS ONE LACKED.              *)
(*                                                                        *)
(*  DESIGN §10: the two repair premises legitimately differ in their       *)
(*  DESCENT discipline — P6-Cv descends consistency, which matches ∀s in   *)
(*  LOCKSTEP ([fa_all_tag] / [fa_all_syn], Δρ fixed), while P6-Sv         *)
(*  descends subtyping, which INSTANTIATES ([fsh_all_r], Δρ grows).  That  *)
(*  difference is real and must stay.  Their BASE rows, on the other hand, *)
(*  say the same thing about the same hazard and must agree — and these    *)
(*  two were missing here:                                                 *)
(*                                                                        *)
(*   · [fa_flexfree] — nothing to keep apart when the payload has no raw   *)
(*     Θ0-flexible at all.  [fa_unit] / [fa_var_rigid] / [fa_hole] were    *)
(*     three special cases of it; the general rule was never written.      *)
(*   · [fa_rho_var] — a ρ-REPLACED RIGID VARIABLE is safe opposite ANY     *)
(*     payload.  This is P6-Cv's own leaf: the precision premise forces    *)
(*     [Pi] to be that very variable, SolS-Var / SolE-Var keep it, and the *)
(*     conclusion's precision is the var rule, so no dirt reaches the      *)
(*     payload however dirty the position is.  [flex_shield] states it as  *)
(*     [fsh_rho_var] for exactly this reason.                              *)
(*                                                                        *)
(*  ⚠️ WITHOUT them the premise is TOO STRONG — [sub_shield] is            *)
(*  UNSATISFIABLE at an ARROW P0 against a tagged-identity guess, because  *)
(*  Sub-ForallL's walk step makes the guess mention the very binder it put *)
(*  into Δρ and nothing was left to apply.  Machine-checked in             *)
(*  cex/cex_p7_shield_arrow.v (two witnesses: the first needs              *)
(*  [fa_flexfree], the second needs [fa_rho_var]).                         *)
(*                                                                        *)
(*  NEITHER disturbs the lockstep inversions: [fa_flexfree]'s conclusion   *)
(*  re-applies at any sub-payload (flex-freedom is inherited), and         *)
(*  [fa_rho_var]'s target is a bare variable, which every ∀ / arrow        *)
(*  inversion discriminates away.  An [fa_all_r] row WOULD have broken     *)
(*  them, which is why it is deliberately absent.                          *)
(* ===================================================================== *)
| fa_flexfree : forall P0 ψa,
    pskl_flex_free Θ0 P0 ->
    flex_apart Θ0 Δρ P0 ψa
| fa_rho_var : forall P0 α,
    α `in` Δρ ->
    flex_apart Θ0 Δρ P0 (uskl_var_f α).


(* Inversions used by the ∀◇/∀◈ congruence cases. *)
Lemma flex_apart_topholeg_target_inv : forall Θ0 Δρ P ψ,
  flex_apart Θ0 Δρ P (uskl_topholeg ψ) ->
  flex_apart Θ0 Δρ P ψ.
Proof.
  intros Θ0 Δρ P ψ H.
  remember (uskl_topholeg ψ) as t eqn:Heqt.
  revert ψ Heqt; induction H; intros ψ' Heqt;
    try discriminate Heqt; subst.
  - apply fa_clean.
    match goal with Hc : _ ∩ _ [=] empty |- _ =>
      simpl in Hc; exact Hc end.
  - apply fa_unit.
  - apply fa_var_rigid; assumption.
  - apply fa_hole.
  - apply fa_tophole; auto.
  - (* fa_flexfree : flex-freedom does not look at the target *)
    apply fa_flexfree; assumption.
Qed.

Lemma flex_apart_tophole_p0_inv : forall Θ0 Δρ P ψ,
  flex_apart Θ0 Δρ (pskl_tophole P) ψ ->
  flex_apart Θ0 Δρ P ψ.
Proof.
  intros Θ0 Δρ P ψ H.
  remember (pskl_tophole P) as t eqn:Heqt.
  revert P Heqt; induction H; intros P' Heqt;
    try discriminate Heqt; subst.
  - apply fa_clean; assumption.
  - inversion Heqt; subst; assumption.
  - (* fa_flexfree : ∀◇'s body inherits flex-freedom *)
    subst. apply fa_flexfree; eapply pskl_flex_free_tophole_inv; eassumption.
  - (* fa_rho_var : the target is a bare Δρ-variable, unchanged *)
    apply fa_rho_var; assumption.
Qed.

(** THE FLEX-P0 READ-OFF.  A [flex_apart] whose P0 is a FLEXIBLE variable has
    only two ways to hold.  [fa_var_rigid] wants that very variable RIGID and
    [fa_flexfree] wants it non-flexible, so both are excluded by the caller's
    own [a_flex_tvar]; the arrow / ∀ rows want another P0 shape; and
    and the ∀◈ target has its own row of the consumer's induction, so it is
    excluded here by a SHAPE side condition — exactly as [flex_shield_flex_leaf]
    does it on the shield side.  That leaves [fa_clean] — the guess is Δρ-CLEAN,
    i.e. ρ acts as the identity on it ([uskl_rho_clean_eq]) — and [fa_rho_var],
    where the guess IS a Δρ-variable.

    ⚠️ The second disjunct is NEW (DESIGN §10): before [fa_rho_var] existed
    this read-off was an equation, and the premise was correspondingly TOO
    STRONG.  It costs the consumer nothing, because a Δρ-VARIABLE is already a
    mono paint — which is exactly what the cleanliness was being used to
    establish (P6-Cs's Arrow row feeds it to
    [ad_pat_consis_rho_subst_psia_mono] to get "ψa is mono, hence tag-free"). *)
Lemma flex_apart_flex_var_clean : forall Θ0 Δρ β ψa,
  flex_apart Θ0 Δρ (pskl_var_f β) ψa ->
  ~ binds β abind_tvar Θ0 ->
  a_flex_tvar Θ0 β ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty
  \/ (exists α0, ψa = uskl_var_f α0 /\ α0 `in` Δρ).
Proof.
  intros Θ0 Δρ β ψa H.
  remember (pskl_var_f β) as t eqn:Heqt.
  revert β Heqt; induction H; intros β' Heqt Hnr Hflex;
    try discriminate Heqt; subst.
  - (* fa_clean *) left; assumption.
  - (* fa_var_rigid : the caller's own [a_flex_tvar] excludes it *)
    inversion Heqt; subst; contradiction.
  - (* fa_flexfree : IMPOSSIBLE — β is flexible, so P0 is not flex-free *)
    exfalso. apply (H β'); [ simpl; clear; fsetdec | exact Hflex ].
  - (* fa_rho_var : the guess IS a Δρ-variable — already a mono paint *)
    right; exists α; split; [ reflexivity | exact H ].
Qed.

(* ===================================================================== *)
(*  Arrow-case flex-subcase discharge (Phase B).                           *)
(*  (B1) On a Δρ-clean target the ρ-relation degenerates to equality;      *)
(*  (B2) a mono paint that refines the consistency counterpart is precise  *)
(*  against the (tag-sorted) consistency subject.                          *)
(* ===================================================================== *)

Lemma uskl_rho_clean_eq : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  (ftvar_in_uskl R) ∩ Δρ [=] empty ->
  R' = R /\ Ψρ [=] empty.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros Hclean.
  - split; [ reflexivity | assumption ].
  - (* leaf: the target variable is IN Δρ — contradiction with cleanliness *)
    exfalso. simpl in Hclean.
    match goal with Hα : α `in` Δρ |- _ => clear - Hα Hclean; fsetdec end.
  - (* arrow *)
    simpl in Hclean.
    destruct IHuskl_rho1 as [-> HΨ1]; [ clear - Hclean; fsetdec | ].
    destruct IHuskl_rho2 as [-> HΨ2]; [ clear - Hclean; fsetdec | ].
    split; [ reflexivity | ].
    match goal with HΨ : Ψρ [=] union _ _ |- _ =>
      clear - HΨ HΨ1 HΨ2; fsetdec end.
  - (* all_syn *)
    simpl in Hclean.
    pick fresh α for
      (L `union` Δρ `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    destruct (H0 α ltac:(solve_notin_auto)) as [Heq HΨ].
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
      simpl in *. clear - Hclean H1 Fr. fsetdec. }
    split; [ | exact HΨ ].
    f_equal.
    apply open_uskl_wrt_uskl_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | exact Heq ].
  - (* all_tag *)
    simpl in Hclean.
    pick fresh α for
      (L `union` Δρ `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    destruct (H0 α ltac:(solve_notin_auto)) as [Heq HΨ].
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)).
      simpl in *. clear - Hclean H1 Fr. fsetdec. }
    split; [ | exact HΨ ].
    f_equal.
    apply open_uskl_wrt_uskl_inj with (α1 := α);
      [ clear - Fr; fsetdec | clear - Fr; fsetdec | exact Heq ].
  - (* tophole *)
    simpl in Hclean.
    destruct IHuskl_rho as [-> HΨ]; [ exact Hclean | ].
    split; [ reflexivity | exact HΨ ].
  - (* topholeg *)
    simpl in Hclean.
    destruct IHuskl_rho as [-> HΨ]; [ exact Hclean | ].
    split; [ reflexivity | exact HΨ ].
Qed.

(* Mono paints never refine into a ∀-painted RHS. *)
Lemma ad_refine_mono_paint_allinh_rhs_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Q0, Q = bskl_all_inh Q0 ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  - (* all *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* hole *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

Lemma ad_refine_mono_paint_allsyn_rhs_absurd : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Q0, Q = bskl_all_syn Q0 ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  False.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros Q0' HeqQ τb HeqL Hmb;
    try discriminate HeqQ.
  - (* hole: RHS is a syn painting — could be all_syn; LHS □ not a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_fill *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* Counterpart shapes reachable by refining FROM a mono paint: the
   mono-ish bskl grammar (unit / any var / arrow). *)
Inductive bskl_monoish : bskl -> Prop :=
| bmi_unit : bskl_monoish bskl_unit
| bmi_var : forall α, bskl_monoish (bskl_var_f α)
| bmi_arrow : forall Q1 Q2,
    bskl_monoish Q1 -> bskl_monoish Q2 ->
    bskl_monoish (bskl_arrow Q1 Q2).

Lemma bskl_monoish_paint : forall τ,
  mono_ptyp τ -> bskl_monoish (ptyp_to_bskl_syn τ).
Proof. intros τ Hm; induction Hm; simpl; constructor; auto. Qed.

Lemma ad_refine_mono_paint_rhs_monoish : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  bskl_monoish Q.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros τb HeqL Hmb.
  - apply bmi_unit.
  - apply bmi_var.
  - (* arrow *)
    symmetry in HeqL.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqL)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    apply bmi_arrow;
      [ eapply IHad_refine_syn1;
          [ exact HwfΘ | exact Heq1 | inversion Hmb; assumption ]
      | eapply IHad_refine_syn2;
          [ exact HwfΘ | exact Heq2 | inversion Hmb; assumption ] ].
  - (* all: LHS all_inh, never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* hole: LHS □, never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_fill *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_keep *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | eapply a_wf_aenv_binds_def_mono; eauto ].
  - (* flex_r *) apply bmi_var.
Qed.

(* Against a mono-ish counterpart, a tag-sorted consistency subject is
   itself a mono paint and the derivation solves no tags. *)
Lemma ad_pat_consis_monoish_counterpart : forall Ψs Θ ψa Q,
  {{ Ψs ⨟ Θ ⊢ˢ ψa ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  is_tskl ψa ->
  bskl_monoish Q ->
  Ψs [=] empty /\
  exists τa, mono_ptyp τa /\ ψa = ptyp_to_uskl_syn τa.
Proof.
  intros Ψs Θ ψa Q H; induction H; intros HwfΘ Htsk Hmi.
  - (* unit *)
    split; [ assumption | exists ptyp_unit; split;
      [ apply mono_ptyp__unit | reflexivity ] ].
  - (* var *)
    split; [ assumption | exists (ptyp_var_f α); split;
      [ apply mono_ptyp__var | reflexivity ] ].
  - (* arrow *)
    inversion Hmi; subst.
    assert (Ht1 : is_tskl R1) by (inversion Htsk; assumption).
    assert (Ht2 : is_tskl R2) by (inversion Htsk; assumption).
    destruct (IHad_pat_consis1 HwfΘ Ht1 ltac:(assumption))
      as (HΨ1 & τ1 & Hm1 & ->).
    destruct (IHad_pat_consis2 HwfΘ Ht2 ltac:(assumption))
      as (HΨ2 & τ2 & Hm2 & ->).
    split.
    + match goal with HΨ : Ψ [=] union _ _ |- _ =>
        clear - HΨ HΨ1 HΨ2; fsetdec end.
    + exists (ptyp_arrow τ1 τ2); split;
        [ apply mono_ptyp__arrow; assumption | reflexivity ].
  - (* forall_inh_tagged: Q = all_inh, not mono-ish *) inversion Hmi.
  - (* forall_inh_untagged *) inversion Hmi.
  - (* forall_syn_tagged *) inversion Hmi.
  - (* forall_syn *) inversion Hmi.
  - (* ghostg: Q = hole *) inversion Hmi.
  - (* topholeg: Q = tophole *) inversion Hmi.
  - (* hole: subject not a tskl *) inversion Htsk.
  - (* tophole *) inversion Htsk.
  - (* tophole_inh *) inversion Htsk.
  - (* tophole_drop *) inversion Htsk.
  - (* flex_l: subject var α (defined) — itself a mono paint *)
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    destruct (IHad_pat_consis HwfΘ
                ltac:(apply is_tskl_mono_paint; exact Hmd) Hmi)
      as (HΨ & _).
    split; [ exact HΨ | ].
    exists (ptyp_var_f α); split; [ apply mono_ptyp__var | reflexivity ].
  - (* flex_r: unfold the counterpart definition — still mono-ish *)
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    apply IHad_pat_consis;
      [ exact HwfΘ | exact Htsk | apply bskl_monoish_paint; exact Hmd ].
Qed.
(* LHS flex_l-spine chases at concrete counterpart shapes, with the
   component/continuation obligations passed as functionals. *)
Lemma ppre_paint_arrow_chase : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Q1 Q2 (ψ1 ψ2 : uskl),
  Q = bskl_arrow Q1 Q2 ->
  (forall Δr' τ1, Δr' [=] empty -> mono_ptyp τ1 ->
     {{ Θ ⨟ Δr' ⊢ᵣ (ptyp_to_bskl_syn τ1) ⊳ Q1 }}ad ->
     forall Δ, {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τ1) ⊑ᵖ[ empty ] ψ1 }}ad) ->
  (forall Δr' τ2, Δr' [=] empty -> mono_ptyp τ2 ->
     {{ Θ ⨟ Δr' ⊢ᵣ (ptyp_to_bskl_syn τ2) ⊳ Q2 }}ad ->
     forall Δ, {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τ2) ⊑ᵖ[ empty ] ψ2 }}ad) ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  Δr [=] empty ->
  forall Δ, {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (uskl_arrow ψ1 ψ2) }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ H;
    induction H; intros Q1' Q2' ψ1 ψ2 HeqQ CONT1 CONT2 τb HeqL Hmb HΔr Δo;
    try discriminate HeqQ.
  - (* arrow *)
    inversion HeqQ; subst.
    symmetry in HeqL.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqL)
      as (τb1 & τb2 & -> & Heqb1 & Heqb2).
    assert (Hm1 : mono_ptyp τb1) by (inversion Hmb; assumption).
    assert (Hm2 : mono_ptyp τb2) by (inversion Hmb; assumption).
    simpl.
    apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ eapply CONT1;
          [ exact HΔr | exact Hm1 | rewrite <- Heqb1; eassumption ]
      | eapply CONT2;
          [ exact HΔr | exact Hm2 | rewrite <- Heqb2; eassumption ]
      | clear; fsetdec ].
  - (* hole: LHS never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    simpl.
    eapply ad_ppre__flex_l; [ eassumption | ].
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | exact CONT1 | exact CONT2
      | reflexivity | eapply a_wf_aenv_binds_def_mono; eauto | exact HΔr ].
Qed.

Lemma ppre_paint_flexvar_chase : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall α1 τα1 (ψa : uskl),
  Q = bskl_var_f α1 ->
  binds α1 (abind_flex_mono_def τα1) Θ ->
  (forall Δr' τc, Δr' [=] empty -> mono_ptyp τc ->
     {{ Θ ⨟ Δr' ⊢ᵣ (ptyp_to_bskl_syn τc) ⊳ (ptyp_to_bskl_syn τα1) }}ad ->
     forall Δ, {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τc) ⊑ᵖ[ empty ] ψa }}ad) ->
  forall τb, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  Δr [=] empty ->
  forall Δ, {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] ψa }}ad.
Proof.
  intros Θ Δr Q' Q HwfΘ H;
    induction H; intros α1 τα1 ψa HeqQ Hbγ CONT τb HeqL Hmb HΔr Δo;
    try discriminate HeqQ.
  - (* var: the counterpart variable itself *)
    inversion HeqQ; subst.
    symmetry in HeqL; apply ptyp_to_bskl_syn_var_inv in HeqL; subst.
    assert (Hmγ : mono_ptyp τα1)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact Hbγ ]).
    assert (Hwfγ : a_wf_ptyp Θ τα1)
      by (eapply a_wf_aenv_binds_def_wf; [ exact HwfΘ | exact Hbγ ]).
    simpl.
    eapply ad_ppre__flex_l; [ exact Hbγ | ].
    eapply CONT;
      [ exact HΔr | exact Hmγ
      | apply ad_refine_mono_paint_refl; [ exact Hwfγ | exact Hmγ ] ].
  - (* hole: LHS never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    simpl.
    eapply ad_ppre__flex_l; [ eassumption | ].
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity | exact Hbγ | exact CONT
      | reflexivity | eapply a_wf_aenv_binds_def_mono; eauto | exact HΔr ].
  - (* flex_r: the same definition by uniqueness *)
    inversion HeqQ; subst.
    match goal with
    | Hb2 : binds _ (abind_flex_mono_def ?t) Θ,
      Hr0 : {{ _ ⨟ _ ⊢ᵣ _ ⊳ ptyp_to_bskl_syn ?t }}ad |- _ =>
        pose proof (binds_unique _ _ _ _ _ Hb2 Hbγ (a_wf_aenv_uniq HwfΘ))
          as Hcc;
        injection Hcc; intros ->;
        eapply CONT; [ exact HΔr | exact Hmb | exact Hr0 ]
    end.
Qed.

(* (B2) The bridge: a mono paint refining the counterpart of a MONO-PAINT
   consistency subject is partially precise against that subject. *)
Lemma mono_paint_paint_refine_consis_ppre : forall Ψs Θ R Q,
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall τa, R = ptyp_to_uskl_syn τa -> mono_ptyp τa ->
  forall Δr τb, Δr [=] empty -> mono_ptyp τb ->
  {{ Θ ⨟ Δr ⊢ᵣ (ptyp_to_bskl_syn τb) ⊳ Q }}ad ->
  forall Δ, {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τb) ⊑ᵖ[ empty ] (ptyp_to_uskl_syn τa) }}ad.
Proof.
  intros Ψs Θ R Q H; induction H;
    intros HwfΘ τa HeqS Hma Δr τb HΔr Hmb Hrefine Δo.
  - (* unit *)
    symmetry in HeqS; apply ptyp_to_uskl_syn_unit_inv in HeqS; subst.
    eapply ad_refine_mono_paint_lhs_ppre with (τ := ptyp_unit);
      [ exact HwfΘ | exact HΔr | exact Hrefine | reflexivity | reflexivity
      | exact Hmb | apply mono_ptyp__unit ].
  - (* var *)
    symmetry in HeqS; apply ptyp_to_uskl_syn_var_inv in HeqS; subst.
    eapply ad_refine_mono_paint_lhs_ppre with (τ := ptyp_var_f α);
      [ exact HwfΘ | exact HΔr | exact Hrefine | reflexivity | reflexivity
      | exact Hmb | apply mono_ptyp__var ].
  - (* arrow *)
    symmetry in HeqS.
    destruct (ptyp_to_uskl_syn_arrow_inv _ HeqS)
      as (τa1 & τa2 & -> & Heqa1 & Heqa2).
    assert (Hma1 : mono_ptyp τa1) by (inversion Hma; assumption).
    assert (Hma2 : mono_ptyp τa2) by (inversion Hma; assumption).
    subst.
    eapply ppre_paint_arrow_chase with
      (ψ1 := ptyp_to_uskl_syn τa1) (ψ2 := ptyp_to_uskl_syn τa2);
      [ exact HwfΘ | exact Hrefine | reflexivity
      | intros Δr' τ1 HΔr' Hm1 Hr1 Δ1;
        eapply IHad_pat_consis1;
          [ exact HwfΘ | reflexivity | exact Hma1 | exact HΔr'
          | exact Hm1 | exact Hr1 ]
      | intros Δr' τ2 HΔr' Hm2 Hr2 Δ2;
        eapply IHad_pat_consis2;
          [ exact HwfΘ | reflexivity | exact Hma2 | exact HΔr'
          | exact Hm2 | exact Hr2 ]
      | reflexivity | exact Hmb | exact HΔr ].
  - (* forall_inh_tagged: subject all_tag never a mono paint *)
    exfalso; eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact HeqS.
  - (* forall_inh_untagged: subject all_syn, mono excluded *)
    destruct τa; simpl in HeqS; try discriminate HeqS. inversion Hma.
  - (* forall_syn_tagged *)
    exfalso; eapply ptyp_to_uskl_syn_all_tag_absurd; symmetry; exact HeqS.
  - (* forall_syn *)
    destruct τa; simpl in HeqS; try discriminate HeqS. inversion Hma.
  - (* ghostg: subject holeg never a paint *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* topholeg *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* hole *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* tophole *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* tophole_inh *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* tophole_drop *)
    destruct τa; simpl in HeqS; discriminate HeqS.
  - (* flex_l: subject var α (defined) *)
    symmetry in HeqS; apply ptyp_to_uskl_syn_var_inv in HeqS; subst.
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    simpl.
    eapply ad_ppre__flex_r; [ eassumption | ].
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hmd | exact HΔr
      | exact Hmb | exact Hrefine ].
  - (* flex_r: chase the counterpart definition *)
    eapply ad_partial_precise_psi_cong;
      [ eapply ppre_paint_flexvar_chase;
          [ exact HwfΘ | exact Hrefine | reflexivity | eassumption
          | intros Δr' τc HΔr' Hmc Hrc Δc;
            eapply IHad_pat_consis;
              [ exact HwfΘ | exact HeqS | exact Hma | exact HΔr'
              | exact Hmc | exact Hrc ]
          | reflexivity | exact Hmb | exact HΔr ]
      | clear; fsetdec ].
Qed.

(* ===================================================================== *)
(*  Arrow-case grid support (Phase C): component inversions at both-arrow *)
(*  nodes, the mono-SUBJECT tag-emptiness lemma (the [Pi = var] rows of   *)
(*  the CORE grids), and the [flex_apart] arrow inversion.                 *)
(* ===================================================================== *)

(** Component inversions at both-arrow nodes (names controlled by the
    caller, unlike a raw [inversion]). *)
Lemma ad_ppre_arrow_arrow_inv : forall Θ Δ Ψ P1 P2 ψ1 ψ2,
  {{ Θ ⨟ Δ ⊢ˢ (pskl_arrow P1 P2) ⊑ᵖ[ Ψ ] (uskl_arrow ψ1 ψ2) }}ad ->
  exists Ψ1 Ψ2, ({{ Θ ⨟ Δ ⊢ˢ P1 ⊑ᵖ[ Ψ1 ] ψ1 }}ad) /\ ({{ Θ ⨟ Δ ⊢ˢ P2 ⊑ᵖ[ Ψ2 ] ψ2 }}ad)
    /\ Ψ [=] Ψ1 `union` Ψ2.
Proof.
  intros Θ Δ Ψ P1 P2 ψ1 ψ2 H; inversion H; subst.
  match goal with
  | Hp1 : {{ Θ ⨟ Δ ⊢ˢ P1 ⊑ᵖ[ ?A ] ψ1 }}ad, Hp2 : {{ Θ ⨟ Δ ⊢ˢ P2 ⊑ᵖ[ ?B ] ψ2 }}ad |- _ =>
    exists A, B; split; [ exact Hp1 | split; [ exact Hp2 | assumption ] ]
  end.
Qed.

Lemma ad_refine_arrow_arrow_inv : forall Θ Δr Q1' Q2' Q1 Q2,
  {{ Θ ⨟ Δr ⊢ᵣ (bskl_arrow Q1' Q2') ⊳ (bskl_arrow Q1 Q2) }}ad ->
  ({{ Θ ⨟ Δr ⊢ᵣ Q1' ⊳ Q1 }}ad) /\ ({{ Θ ⨟ Δr ⊢ᵣ Q2' ⊳ Q2 }}ad).
Proof.
  intros Θ Δr Q1' Q2' Q1 Q2 H; inversion H; subst; split; assumption.
Qed.

(** A mono-paint SUBJECT forces an empty tag reading of the target: the
    precision rules reachable from a paint (unit/var/arrow congruences +
    the flex chains) only ever meet tag-free target shapes — a mono paint
    has no ∀, so [ad_ppre__forall] (the only tag producer) cannot fire.
    Discharges the [Pi = var] rows of the Arrow-case CORE grid
    (Ψ' [=] ∅ ⇒ Ψa [=] ∅) and, by the ε-membership contradiction, kills
    the [Pi = var] rows of the tagged-∀ cases. *)
Lemma ad_ppre_mono_subject_target_tags_empty : forall Θ Δ Ψ P ψ,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall τ, P = ptyp_to_pskl τ -> mono_ptyp τ ->
  forall Ψt, d_tags_skl Ψt ψ -> Ψt [=] empty.
Proof.
  intros Θ Δ Ψ P ψ HwfΘ H; induction H; intros τ0 HeqP Hm Ψt Hdt.
  - (* unit *) exact (d_tags_skl_unit_inv Hdt).
  - (* var *) exact (d_tags_skl_var_inv Hdt).
  - (* arrow *)
    destruct τ0; simpl in HeqP; try discriminate HeqP.
    inversion HeqP; subst.
    destruct (d_tags_skl_arrow_inv Hdt)
      as (Ψt1 & Ψt2 & Hd1 & Hd2 & _ & HeqΨt).
    assert (Hm1 : mono_ptyp τ0_1) by (inversion Hm; assumption).
    assert (Hm2 : mono_ptyp τ0_2) by (inversion Hm; assumption).
    pose proof (IHad_partial_precise1 HwfΘ _ eq_refl Hm1 _ Hd1) as He1.
    pose proof (IHad_partial_precise2 HwfΘ _ eq_refl Hm2 _ Hd2) as He2.
    clear - HeqΨt He1 He2; fsetdec.
  - (* forall: subject all_syn is never a mono paint *)
    destruct τ0; simpl in HeqP; try discriminate HeqP.
    inversion Hm.
  - (* hole: never a paint *)
    destruct τ0; simpl in HeqP; discriminate HeqP.
  - (* tophole_remove *)
    destruct τ0; simpl in HeqP; discriminate HeqP.
  - (* tophole_fill *)
    destruct τ0; simpl in HeqP; discriminate HeqP.
  - (* tophole_keep *)
    destruct τ0; simpl in HeqP; discriminate HeqP.
  - (* flex_l: chase the definition (still a mono paint) *)
    destruct τ0; simpl in HeqP; try discriminate HeqP.
    inversion HeqP; subst.
    eapply IHad_partial_precise;
      [ exact HwfΘ | reflexivity
      | eapply a_wf_aenv_binds_def_mono; eauto | exact Hdt ].
  - (* flex_r: target var carries no tags *)
    exact (d_tags_skl_var_inv Hdt).
Qed.

(** [flex_apart] inversion at a both-arrow node: the clean case distributes
    the free-variable condition; the arrow case is direct.  (Of the other
    constructors, none matches an arrow P0 against an arrow target.) *)
Lemma flex_apart_arrow_inv : forall Θ0 Δρ P1 P2 ψ1 ψ2,
  flex_apart Θ0 Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2) ->
  flex_apart Θ0 Δρ P1 ψ1 /\ flex_apart Θ0 Δρ P2 ψ2.
Proof.
  intros Θ0 Δρ P1 P2 ψ1 ψ2 H; inversion H; subst.
  - (* fa_clean *)
    match goal with
    | Hc : _ ∩ _ [=] empty |- _ => simpl in Hc;
        split; apply fa_clean; clear - Hc; fsetdec
    end.
  - (* fa_arrow *)
    split; assumption.
  - (* fa_flexfree : both components inherit flex-freedom *)
    match goal with Hff : pskl_flex_free _ _ |- _ =>
      destruct (pskl_flex_free_arrow_inv Hff) as [Hff1 Hff2] end.
    split; apply fa_flexfree; assumption.
Qed.

(* ===================================================================== *)
(*  REPAIR KIT (DESIGN §6(l)) — support lemmas for the tagged-∀ cases.    *)
(* ===================================================================== *)

(** Precision respects set-equality of Δ. *)
Lemma ad_partial_precise_delta_cong : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall Δ', Δ [=] Δ' ->
  {{ Θ ⨟ Δ' ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Δ' Heq.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb];
      [ left; clear - HΔ Heq; fsetdec | right; assumption ] end.
  - eapply ad_ppre__arrow; eauto.
  - eapply ad_ppre__forall with (L := L);
      [ intros α Hα; apply (H0 α Hα); clear - Heq; fsetdec | assumption ].
  - apply ad_ppre__hole; [ assumption | ].
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      clear - Hint Heq; fsetdec end.
  - apply ad_ppre__tophole_remove; auto.
  - eapply ad_ppre__tophole_fill with (L := L); eauto.
  - apply ad_ppre__tophole_keep; auto.
  - eapply ad_ppre__flex_l; eauto.
  - eapply ad_ppre__flex_r; eauto.
Qed.

(** Δ-weakening by variables fresh for the target and for Θ's definition
    images.  (Unconditional Δ-weakening is FALSE — the □-rule's
    Δ-disjointness is antitone — but target-fresh extensions never meet a
    □-instance's side condition.) *)
Lemma ad_partial_precise_delta_weaken_fresh : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall Δ',
  Δ' ∩ ftvar_in_uskl ψ [=] empty ->
  delta_def_fresh Δ' Θ ->
  {{ Θ ⨟ (Δ `union` Δ') ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Δ' HΔ' Hdf.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb];
      [ left; clear - HΔ; fsetdec | right; assumption ] end.
  - simpl in HΔ'.
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1; [ clear - HΔ'; fsetdec | exact Hdf ]
      | apply IHad_partial_precise2; [ clear - HΔ'; fsetdec | exact Hdf ]
      | assumption ].
  - (* forall *)
    simpl in HΔ'.
    eapply ad_ppre__forall with (L := L `union` Δ'); [ | eassumption ].
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      simpl in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    eapply ad_partial_precise_delta_cong;
      [ apply (H0 α0 ltac:(clear - Hα0; solve_notin_auto) Δ' HSX Hdf)
      | clear; fsetdec ].
  - (* hole *)
    apply ad_ppre__hole; [ assumption | ].
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      clear - Hint HΔ'; fsetdec end.
  - apply ad_ppre__tophole_remove; auto.
  - (* tophole_fill *)
    eapply ad_ppre__tophole_fill with (L := L `union` Δ').
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      simpl in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    assert (Hdf' : delta_def_fresh Δ' ((α0 ~ abind_tvar) ++ Θ)).
    { intros β α τ Hβ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | exact (Hdf β α τ Hβ Hb') ]. }
    apply (H0 α0 ltac:(clear - Hα0; solve_notin_auto) Δ' HSX Hdf').
  - (* tophole_keep *)
    simpl in HΔ'.
    apply ad_ppre__tophole_keep; apply IHad_partial_precise; auto.
  - eapply ad_ppre__flex_l; [ eassumption | ].
    apply IHad_partial_precise; auto.
  - (* flex_r: the target hops to the definition's paint *)
    eapply ad_ppre__flex_r; [ eassumption | ].
    apply IHad_partial_precise; [ | exact Hdf ].
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
    apply atoms_inter_empty_pointwise.
    intros y Hy. eapply Hdf; [ exact Hy | eassumption ].
Qed.

(** Moving a Δr-entry of the refinement into the aenv as a rigid tvar
    (mid-insertion general, for the fill rule's context growth). *)
Lemma ad_refine_syn_delta_to_tvar_mid : forall Θfull Δr Q' Q,
  {{ Θfull ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall α1 Θ1 Θ0 Δr', Θfull = Θ1 ++ Θ0 ->
  Δr [<=] add α1 Δr' ->
  {{ (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0) ⨟ Δr' ⊢ᵣ Q' ⊳ Q }}ad.
Proof.
  intros Θfull Δr Q' Q H; induction H;
    intros α2 Θ1 Θt Δr' HeqΘ Hsub; subst.
  - apply ad_refine_syn__unit.
  - (* var *)
    apply ad_refine_syn__var.
    match goal with Hor : _ \/ a_binds_tvar ?α _ |- _ =>
      destruct Hor as [HΔ | Hbt];
      [ destruct (α == α2) as [-> | Hne];
        [ right; left; unfold binds;
          apply in_or_app; right; left; reflexivity
        | left; clear - HΔ Hsub Hne; fsetdec ]
      | right;
        destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        [ left; apply binds_weaken; exact Hb
        | right; left; apply binds_weaken; exact Hb
        | right; right; exists τ0; apply binds_weaken; exact Hb ] ]
    end.
  - apply ad_refine_syn__arrow; eauto.
  - (* all *)
    apply ad_refine_syn__all with (L := L).
    intros α Hα.
    apply (H0 α Hα α2 Θ1 Θt (add α Δr') eq_refl).
    clear - Hsub; fsetdec.
  - (* hole *)
    apply ad_refine_syn__hole.
    eapply a_wf_pskl_weaken;
      [ intros x b Hb; apply binds_weaken; exact Hb | eassumption ].
  - apply ad_refine_syn__tophole_remove; auto.
  - (* tophole_fill: the aenv grows on the left *)
    apply ad_refine_syn__tophole_fill with (L := L).
    intros α Hα.
    apply (H0 α Hα α2 ((α ~ abind_tvar) ++ Θ1) Θt Δr' eq_refl Hsub).
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l;
      [ apply binds_weaken; eassumption | auto ].
  - eapply ad_refine_syn__flex_r;
      [ apply binds_weaken; eassumption | auto ].
Qed.

Lemma ad_refine_syn_delta_to_tvar : forall Θ Δr Q' Q α1 Δr',
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  Δr [<=] add α1 Δr' ->
  {{ ((α1 ~ abind_tvar) ++ Θ) ⨟ Δr' ⊢ᵣ Q' ⊳ Q }}ad.
Proof.
  intros Θ Δr Q' Q α1 Δr' H Hsub.
  exact (@ad_refine_syn_delta_to_tvar_mid _ _ _ _ H α1 nil Θ Δr'
           eq_refl Hsub).
Qed.

(** Free variables of a consistency SUBJECT are counterpart variables or
    Θ's defined flexibles / their definition images.  (The tight bound —
    rigid tvar entries never pollute it — which is what survives the
    ∀-descent's context extensions.) *)
Lemma ad_pat_consis_ftv_bound : forall Ψ Θ R' Q,
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Q }}ad ->
  forall α', α' `in` ftvar_in_uskl R' ->
  α' `in` ftvar_in_bskl Q \/
  (exists α τ, binds α (abind_flex_mono_def τ) Θ /\
     (α' = α \/ α' `in` ftvar_in_ptyp τ)).
Proof.
  intros Ψ Θ R' Q H; induction H; intros α0 HX0; simpl in HX0.
  - (* unit *) exfalso; clear - HX0; fsetdec.
  - (* var *) left; simpl; clear - HX0; fsetdec.
  - (* arrow *)
    apply union_iff in HX0; destruct HX0 as [HX0 | HX0];
      [ destruct (IHad_pat_consis1 α0 HX0) as [Hin | Hdef]
      | destruct (IHad_pat_consis2 α0 HX0) as [Hin | Hdef] ];
      solve [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  - (* forall_inh_tagged *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    assert (HX0' : α0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f β)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 β ltac:(clear - Fr; solve_notin_auto) α0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* forall_inh_untagged *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    assert (HX0' : α0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f β)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 β ltac:(clear - Fr; solve_notin_auto) α0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* forall_syn_tagged *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    assert (HX0' : α0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f β)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 β ltac:(clear - Fr; solve_notin_auto) α0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* forall_syn *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    assert (HX0' : α0 `in`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f β)))
      by (pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                        (uskl_var_f β)) as Hlow; clear - HX0 Hlow; fsetdec).
    destruct (H0 β ltac:(clear - Fr; solve_notin_auto) α0 HX0')
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* ghostg *) exfalso; clear - HX0; fsetdec.
  - (* topholeg *)
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  - (* hole *) exfalso; clear - HX0; fsetdec.
  - (* tophole *)
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ left; simpl; clear - Hin; fsetdec | right; exact Hdef ].
  - (* tophole_inh: subject fixed under the counterpart binder *)
    pick fresh β for
      (L `union` singleton α0 `union` ftvar_in_bskl Q).
    destruct (H0 β ltac:(clear - Fr; solve_notin_auto) α0 ltac:(simpl; exact HX0))
      as [Hin | (α & τ & Hb & Hor)].
    + left.
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q
                    (bskl_var_f β)) as Hup.
      simpl in *. clear - Hin Hup Fr. fsetdec.
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | right; exists α, τ; auto ].
  - (* tophole_drop *)
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ left; exact Hin | right; exact Hdef ].
  - (* flex_l: the subject variable is itself a defined flexible *)
    right; exists α, τ; split; [ assumption | left; clear - HX0; fsetdec ].
  - (* flex_r: unfolding the counterpart definition *)
    destruct (IHad_pat_consis α0 HX0) as [Hin | Hdef];
      [ | right; exact Hdef ].
    unfold ptyp_to_bskl_syn in Hin.
    rewrite ftvar_pskl_to_bskl_syn in Hin.
    right; exists α, τ; split;
      [ assumption
      | right;
        pose proof (ftvar_ptyp_to_pskl τ) as Hp;
        clear - Hin Hp; fsetdec ].
Qed.

(** ⭐ ρ IS CONGRUENT AT EVERY CONSTRUCTOR and non-trivial only at a bare
    VARIABLE of the guess ([urho__leaf]) — and a bare variable is itself a
    MONOTYPE.  So a mono-paint ρ-IMAGE forces a mono-paint GUESS, with no
    cleanliness premise: this is what replaces the [flex_apart]-supplied
    "ρ acts as the identity on the guess" step at P6-Cv's SE-FlexR row
    (2026-08-05). *)
Lemma uskl_rho_mono_target : forall NM Θ Δρ Ψρ ψsub ψa τ,
  uskl_rho NM Θ Δρ Ψρ ψsub ψa ->
  ψsub = ptyp_to_uskl_syn τ -> mono_ptyp τ ->
  exists τa, ψa = ptyp_to_uskl_syn τa /\ mono_ptyp τa.
Proof.
  intros NM Θ Δρ Ψρ ψsub ψa τ H. revert τ.
  induction H; intros τ Heq Hm.
  - (* refl *) exists τ; split; [ exact Heq | exact Hm ].
  - (* leaf: the guess IS a bare variable, hence a monotype *)
    exists (ptyp_var_f α); split; [ reflexivity | apply mono_ptyp__var ].
  - (* arrow *)
    destruct τ; simpl in Heq; try discriminate Heq.
    inversion Heq; subst.
    inversion Hm; subst.
    destruct (IHuskl_rho1 _ eq_refl ltac:(assumption)) as (τa1 & -> & Hm1).
    destruct (IHuskl_rho2 _ eq_refl ltac:(assumption)) as (τa2 & -> & Hm2).
    exists (ptyp_arrow τa1 τa2); split;
      [ reflexivity | apply mono_ptyp__arrow; assumption ].
  - (* all_syn : a mono paint is never a ∀ *)
    exfalso. destruct τ; simpl in Heq; try discriminate Heq. inversion Hm.
  - (* all_tag *) exfalso. destruct τ; simpl in Heq; discriminate Heq.
  - (* tophole *)  exfalso. destruct τ; simpl in Heq; discriminate Heq.
  - (* topholeg *) exfalso. destruct τ; simpl in Heq; discriminate Heq.
Qed.

(** ρ's target free variables are subject variables or replaced ones. *)
Lemma uskl_rho_ftv_target_bound : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  ftvar_in_uskl R [<=] ftvar_in_uskl R' `union` Δρ.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; simpl; try fsetdec.
  - (* all_syn *)
    pick fresh α for
      (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R' (uskl_var_f α)).
    simpl in *. clear - Hα H1 H2 Fr. fsetdec.
  - (* all_tag *)
    pick fresh α for
      (L `union` ftvar_in_uskl R' `union` ftvar_in_uskl R).
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto)) as Hα.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f α)).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R' (uskl_var_f α)).
    simpl in *. clear - Hα H1 H2 Fr. fsetdec.
Qed.

(** Cofinite inversions of the tag-sorting components at a tagged ∀. *)
Lemma is_tskl_all_tag_inv : forall ε ψ,
  is_tskl (uskl_all_tag ε ψ) ->
  exists L, forall α, α `notin` L ->
    is_tskl (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof. intros ε ψ H; inversion H; subst. eexists; eassumption. Qed.

(** [flex_apart] aenv weakening (binds-monotone).  ⚠️ Since [fa_flexfree]
    (DESIGN §10) reads the context NEGATIVELY, the map must also create no new
    flexibles — true of every RIGID extension, which is what all the callers do.
    A FLEXIBLE prefix needs the ftv-scoped twin below, exactly as on the
    [flex_shield] side. *)
Lemma flex_apart_weaken : forall Θ0 Δρ P ψ,
  flex_apart Θ0 Δρ P ψ ->
  forall Θ0', (forall x b, binds x b Θ0 -> binds x b Θ0') ->
  (forall α, a_flex_tvar Θ0' α -> a_flex_tvar Θ0 α) ->
  flex_apart Θ0' Δρ P ψ.
Proof.
  intros Θ0 Δρ P ψ H; induction H; intros Θ0' Hmon Hfx.
  - apply fa_clean; assumption.
  - apply fa_unit.
  - apply fa_var_rigid; auto.
  - apply fa_hole.
  - apply fa_tophole; auto.
  - apply fa_arrow; auto.
  - eapply fa_all_tag with (L := L); eauto.
  - eapply fa_all_syn with (L := L); eauto.
  - apply fa_flexfree; intros α Hα Hflex; apply (H α Hα); auto.
  - apply fa_rho_var; assumption.
Qed.

(** …and the FLEXIBLE-prefix twin ([flex_shield_weaken_flex_prefix]'s mirror):
    a payload variable outside [dom Ξ] keeps its Θ0 binding, so flex-freedom
    survives.  The opened binder in the ∀ rows must miss [dom Ξ] too. *)
Lemma flex_apart_weaken_flex_prefix : forall Θ0 Δρ P ψ,
  flex_apart Θ0 Δρ P ψ ->
  forall Ξ, (ftvar_in_pskl P) ∩ (dom Ξ) [=] empty ->
  flex_apart (Ξ ++ Θ0) Δρ P ψ.
Proof.
  intros Θ0 Δρ P ψ H; induction H; intros Ξ Hfr.
  - apply fa_clean; assumption.
  - apply fa_unit.
  - apply fa_var_rigid; apply binds_app_3; assumption.
  - apply fa_hole.
  - simpl in Hfr. apply fa_tophole; apply IHflex_apart; exact Hfr.
  - simpl in Hfr. apply fa_arrow;
      [ apply IHflex_apart1 | apply IHflex_apart2 ]; clear - Hfr; fsetdec.
  - apply fa_all_tag with (L := L `union` dom Ξ); intros α Hα.
    apply H0; [ clear - Hα; solve_notin | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as Hup.
    simpl in Hup, Hfr. clear - Hup Hfr Hα; fsetdec.
  - apply fa_all_syn with (L := L `union` dom Ξ); intros α Hα.
    apply H0; [ clear - Hα; solve_notin | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as Hup.
    simpl in Hup, Hfr. clear - Hup Hfr Hα; fsetdec.
  - (* flexfree: a payload variable outside [dom Ξ] keeps its Θ0 binding *)
    apply fa_flexfree. intros α Hα Hflex.
    assert (HαΞ : α `notin` dom Ξ) by (clear - Hfr Hα; fsetdec).
    apply (H α Hα).
    destruct Hflex as [Hb | [τ Hb]];
      [ left | right; exists τ ];
      (destruct (binds_app_1 _ _ _ _ _ Hb) as [Hb' | Hb'];
        [ exfalso; apply HαΞ; eapply binds_In; exact Hb' | exact Hb' ]).
  - apply fa_rho_var; assumption.
Qed.

(* ===================================================================== *)
(* ===================================================================== *)
(*  ⚠️ WHY THE HEREDITARY [flex_apart_deep] AND NOT A WALK ALONG THE       *)
(*  SUBTYPING DESCENT.  A walk indexing [flex_apart] along the descent has *)
(*  no guess-fixed ARROW rows, and adding them makes it UNSATISFIABLE when *)
(*  composed with a [∀]-right descent (a raw Θ0-flexible facing the opened *)
(*  body at [β ∈ Δρ]).  That is why such a premise had to be ASSUMED       *)
(*  rather than derived, whereas [flex_apart_deep] — whose [p0_step] DOES  *)
(*  have the arrow rows — is derivable                                     *)
(*  ([flex_apart_deep_sub_shield], sub/look/prop_sub_cstr.v).              *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  The P0-ONLY walk (P6-Cs).                                             *)
(*                                                                        *)
(*  P6-Cs descends P0 alone — ψa is the single guess for the looked-up α  *)
(*  and NEVER moves — so it needs [flex_apart] only at the P0-subterms it  *)
(*  actually reaches, at a CONSTANT Δρ.  That is strictly weaker than      *)
(*  [flex_apart_walk], whose [fastep_all_r] can grow Δρ, and the           *)
(*  difference is what makes the paper-faithful ρ = identity corollary of  *)
(*  P6-Cs PREMISE-FREE: at Δρ = ∅ every reachable state is [fa_clean].     *)
(*  ⚠️ P6-Ss carries this closure as its OWN [sub_shield] conjunct — it is  *)
(*  NOT derivable from [flex_apart_walk], and the two rows that once made   *)
(*  it so are what sank that premise (DESIGN §14.3; see the ⚠️ note on      *)
(*  [fa_step]).                                                            *)
(* ===================================================================== *)

(** ⚠️ The walk carries an AVOID SET [A], and the ∀-descent's binder must miss
    it — exactly as [ss_step] does (sub/look/prop_sub_cstr.v:90) and for
    exactly the same reason.  Without it the walk reaches states mentioning an
    ARBITRARY γ, and [flex_apart_deep] could then not be transported across a
    FLEXIBLE PREFIX at all: [fa_flexfree] is anti-monotone in the context, so
    its transport needs [ftv P0' ∩ dom Ξ = ∅], which only holds if the opened
    binders miss [dom Ξ].  [flex_apart_deep] instantiates [A := dom Θ0], and
    every call site picks its binder fresh for the context anyway — so the
    condition costs nothing and buys [flex_apart_deep_weaken_flex_prefix]. *)
Inductive p0_step (A : atoms) : pskl -> pskl -> Prop :=
| p0step_arrow_l : forall P1 P2, p0_step A (pskl_arrow P1 P2) P1
| p0step_arrow_r : forall P1 P2, p0_step A (pskl_arrow P1 P2) P2
| p0step_all     : forall P0 γ,
    γ `notin` A ->
    p0_step A (pskl_all_syn P0) (open_pskl_wrt_pskl P0 (pskl_var_f γ))
| p0step_tophole : forall P0, p0_step A (pskl_tophole P0) P0.

Inductive p0_walk (A : atoms) : pskl -> pskl -> Prop :=
| p0w_refl : forall P0, p0_walk A P0 P0
| p0w_step : forall P0 P1 P2,
    p0_step A P0 P1 -> p0_walk A P1 P2 -> p0_walk A P0 P2.

(** Shrinking the avoid set only admits MORE walks. *)
Lemma p0_walk_mono : forall A A' P0 P1,
  p0_walk A P0 P1 -> A' [<=] A -> p0_walk A' P0 P1.
Proof.
  intros A A' P0 P1 H; induction H; intros Hsub; [ apply p0w_refl | ].
  eapply p0w_step; [ | apply IHp0_walk; exact Hsub ].
  destruct H;
    [ apply p0step_arrow_l | apply p0step_arrow_r
    | apply p0step_all; clear - H Hsub; fsetdec
    | apply p0step_tophole ].
Qed.

(** …and the endpoint's free variables still miss [A]. *)
Lemma p0_walk_ftv : forall A P0 P1,
  p0_walk A P0 P1 -> (ftvar_in_pskl P0) ∩ A [=] empty ->
  (ftvar_in_pskl P1) ∩ A [=] empty.
Proof.
  intros A P0 P1 H; induction H; intros Hfr; [ exact Hfr | ].
  apply IHp0_walk. destruct H; simpl in Hfr;
    try solve [ clear - Hfr; fsetdec ].
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f γ)) as Hup.
  simpl in Hup. clear - Hup Hfr H; fsetdec.
Qed.

(** ⭐ [flex_apart_deep]: [flex_apart] HEREDITARILY — at [P0] and at every
    subterm the recursion can descend to, against the SAME fixed guess.

    ⚙ It was called [flex_apart_p0] until 2026-08-05, which read as "at P0"
    and is exactly what it does NOT mean.  The [p0] in [p0_walk] below is
    right, though: that relation really is the descent the COUNTERPART [P0]
    makes, one constructor at a time. *)
Definition flex_apart_deep (Θ0 : aenv) (Δρ : atoms) (P0 : pskl) (ψa : uskl)
  : Prop :=
  forall P0', p0_walk (dom Θ0) P0 P0' -> flex_apart Θ0 Δρ P0' ψa.

Lemma flex_apart_deep_here : forall Θ0 Δρ P0 ψa,
  flex_apart_deep Θ0 Δρ P0 ψa -> flex_apart Θ0 Δρ P0 ψa.
Proof. intros Θ0 Δρ P0 ψa H; apply H; apply p0w_refl. Qed.

Lemma flex_apart_deep_step : forall Θ0 Δρ P0 ψa P1,
  flex_apart_deep Θ0 Δρ P0 ψa -> p0_step (dom Θ0) P0 P1 ->
  flex_apart_deep Θ0 Δρ P1 ψa.
Proof.
  intros Θ0 Δρ P0 ψa P1 H Hs P0' Hw.
  apply H; eapply p0w_step; [ exact Hs | exact Hw ].
Qed.

Lemma flex_apart_deep_weaken : forall Θ0 Δρ P0 ψa,
  flex_apart_deep Θ0 Δρ P0 ψa ->
  forall Θ0', (forall x b, binds x b Θ0 -> binds x b Θ0') ->
  (forall α, a_flex_tvar Θ0' α -> a_flex_tvar Θ0 α) ->
  (dom Θ0) [<=] (dom Θ0') ->
  flex_apart_deep Θ0' Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa H Θ0' Hmon Hfx Hdom P0' Hw.
  eapply flex_apart_weaken;
    [ apply H; eapply p0_walk_mono; [ exact Hw | exact Hdom ]
    | exact Hmon | exact Hfx ].
Qed.

Lemma flex_apart_deep_weaken_tvar : forall Θ0 Δρ P0 ψa β,
  flex_apart_deep Θ0 Δρ P0 ψa ->
  flex_apart_deep ((β ~ abind_tvar) ++ Θ0) Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa β H.
  eapply flex_apart_deep_weaken;
    [ exact H | intros x b Hb; apply binds_app_3; exact Hb
    | apply a_flex_tvar_strip_tvar | simpl; clear; fsetdec ].
Qed.

(** The FLEXIBLE-prefix transport (the [sub_shield_weaken_flex_prefix] mirror):
    the walk misses [dom Ξ] throughout, so its endpoint does, and [fa_flexfree]
    survives.  This is what the avoid set on [p0_step] was added for. *)
Lemma flex_apart_deep_weaken_flex_prefix : forall Θ0 Δρ P0 ψa Ξ,
  flex_apart_deep Θ0 Δρ P0 ψa ->
  (ftvar_in_pskl P0) ∩ (dom Ξ) [=] empty ->
  flex_apart_deep (Ξ ++ Θ0) Δρ P0 ψa.
Proof.
  intros Θ0 Δρ P0 ψa Ξ H HfrP0 P0' Hw.
  assert (HwΞ : p0_walk (dom Ξ) P0 P0')
    by (eapply p0_walk_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  assert (Hw0 : p0_walk (dom Θ0) P0 P0')
    by (eapply p0_walk_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  assert (HfrP0' : (ftvar_in_pskl P0') ∩ (dom Ξ) [=] empty)
    by (eapply p0_walk_ftv; [ exact HwΞ | exact HfrP0 ]).
  eapply flex_apart_weaken_flex_prefix; [ apply H; exact Hw0 | exact HfrP0' ].
Qed.

(** A Δρ-CLEAN guess shields every P0-subterm at once — in particular at
    Δρ = ∅, which is what the ρ = identity corollary of P6-Cs uses. *)
(** …and [flex_apart] tolerates a Δρ that grows by variables the guess does
    not mention.  Only two rows read Δρ: [fa_clean], whose disjointness the
    growth condition preserves, and [fa_rho_var], which is monotone. *)
Lemma flex_apart_delta_grow : forall Θ0 Δρ Δρ' P0 ψa,
  flex_apart Θ0 Δρ P0 ψa ->
  Δρ [<=] Δρ' -> Δρ' ∩ ftvar_in_uskl ψa [<=] Δρ ->
  flex_apart Θ0 Δρ' P0 ψa.
Proof.
  intros Θ0 Δρ Δρ' P0 ψa H; induction H; intros Hle Hcl.
  - apply fa_clean. clear - H Hcl; fsetdec.
  - apply fa_unit.
  - apply fa_var_rigid; assumption.
  - apply fa_hole.
  - apply fa_tophole; auto.
  - apply fa_arrow;
      [ apply IHflex_apart1 | apply IHflex_apart2 ];
      solve [ exact Hle | cbn [ftvar_in_uskl] in Hcl; clear - Hcl; fsetdec ].
  - (* ⚠️ the binder must dodge [Δρ'] too: the growth condition only bounds
       [Δρ' ∩ ftv ψa], and opening puts the binder INTO the payload's ftv. *)
    eapply fa_all_tag with (L := L `union` Δρ'); intros α0 Hα0.
    apply H0; [ clear - Hα0; fsetdec | exact Hle | ].
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0)) as Hup.
    cbn [ftvar_in_uskl] in Hcl, Hup. clear - Hcl Hup Hα0; fsetdec.
  - (* ⚠️ the binder must dodge [Δρ'] too: the growth condition only bounds
       [Δρ' ∩ ftv ψa], and opening puts the binder INTO the payload's ftv. *)
    eapply fa_all_syn with (L := L `union` Δρ'); intros α0 Hα0.
    apply H0; [ clear - Hα0; fsetdec | exact Hle | ].
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0)) as Hup.
    cbn [ftvar_in_uskl] in Hcl, Hup. clear - Hcl Hup Hα0; fsetdec.
  - apply fa_flexfree; assumption.
  - apply fa_rho_var. clear - H Hle; fsetdec.
Qed.

(** …and the same for the P0-only closure, which is Δρ-CONSTANT: the growth is
    pointwise.  This is what Sub-ForallL needs, where the row's fresh rigid β
    joins Δρ and is fresh for the guess. *)
Lemma flex_apart_deep_delta_grow : forall Θ0 Δρ Δρ' P0 ψa,
  flex_apart_deep Θ0 Δρ P0 ψa ->
  Δρ [<=] Δρ' -> Δρ' ∩ ftvar_in_uskl ψa [<=] Δρ ->
  flex_apart_deep Θ0 Δρ' P0 ψa.
Proof.
  intros Θ0 Δρ Δρ' P0 ψa H Hle Hcl P0' Hw.
  eapply flex_apart_delta_grow; [ apply H; exact Hw | exact Hle | exact Hcl ].
Qed.

Lemma flex_apart_deep_clean : forall Θ0 Δρ P0 ψa,
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  flex_apart_deep Θ0 Δρ P0 ψa.
Proof. intros Θ0 Δρ P0 ψa Hc P0' _; apply fa_clean; exact Hc. Qed.

(** ⚠️ There is NO [flex_apart_walk_p0] (DESIGN §14.3, 2026-08-03).  P6-Ss's
    walk used to imply this closure, via the two guess-fixed P0 arrow steps
    [fa_step] carried for exactly that purpose — and those steps made
    [flex_apart_walk] unsatisfiable at a reachable P7b node (see the ⚠️ note
    on [fa_step]).  [flex_apart_deep] is now an INDEPENDENT [sub_shield]
    conjunct: P6-Ss reads it off directly instead of deriving it.  The two
    closures are compatible at a [sub_shield] position precisely because the
    Δρ' quantifier there keeps the guess CLEAN for the grown part of Δρ',
    which the guess-OPENING step [fastep_all_r] does not. *)

(** [flex_apart] binder descent at a tagged-∀ target with a ∀-source. *)
Lemma flex_apart_all_tag_forall_inv : forall Θ0 Δρ ε P0 ψ,
  flex_apart Θ0 Δρ (pskl_all_syn P0) (uskl_all_tag ε ψ) ->
  exists L, forall α, α `notin` L ->
    flex_apart Θ0 Δρ (open_pskl_wrt_pskl P0 (pskl_var_f α))
                     (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros Θ0 Δρ ε P0 ψ H; inversion H; subst.
  - (* fa_clean: bodies stay clean at fresh openings *)
    match goal with Hc : _ ∩ _ [=] empty |- _ =>
      exists Δρ; intros α Hα; apply fa_clean;
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                    (uskl_var_f α)) as Hup;
      simpl in *; clear - Hc Hup Hα; fsetdec
    end.
  - (* fa_all_tag: the cofinite family, directly *)
    match goal with
    | Hf : forall α, α `notin` ?L0 -> flex_apart _ _ _ _ |- _ =>
      exists L0; exact Hf
    end.
  - (* fa_flexfree : the ∀-body inherits flex-freedom at any fresh opener *)
    match goal with Hff : pskl_flex_free _ _ |- _ =>
      exists (ftvar_in_pskl P0 `union` dom Θ0); intros α Hα;
      apply fa_flexfree; intros α0 Hα0 Hflex;
      apply (Hff α0); [ | exact Hflex ];
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0
                    (pskl_var_f α)) as Hup;
      simpl in Hup |- *;
      assert (Hne : α0 <> α)
        by (intro; subst; destruct Hflex as [Hb | [τ Hb]];
            apply binds_In in Hb; clear - Hα Hb; fsetdec);
      clear - Hup Hα0 Hne; fsetdec
    end.
Qed.


(** Absorb Δr-entries that are rigid tvars of the aenv (the Δr-refinement
    → statement-form transfer, given Δr ⊆ dom Θtv and Θ ⊇ Θtv). *)
Lemma ad_refine_syn_delta_absorb : forall Θ Δr Q' Q,
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Δr', (forall α2, α2 `in` Δr -> α2 `in` Δr' \/ binds α2 abind_tvar Θ) ->
  {{ Θ ⨟ Δr' ⊢ᵣ Q' ⊳ Q }}ad.
Proof.
  intros Θ Δr Q' Q H; induction H; intros Δr' Habs.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
    match goal with Hor : _ \/ a_binds_tvar ?α _ |- _ =>
      destruct Hor as [HΔ | Hbt];
      [ destruct (Habs _ HΔ) as [HΔ' | Hb];
        [ left; exact HΔ' | right; left; exact Hb ]
      | right; exact Hbt ] end.
  - apply ad_refine_syn__arrow; auto.
  - apply ad_refine_syn__all with (L := L).
    intros α Hα. apply (H0 α Hα (add α Δr')).
    intros α2 Hα2.
    destruct (AtomSetProperties.In_dec α2 (add α Δr')) as [Hin | Hnin];
      [ left; exact Hin | ].
    destruct (Habs α2 ltac:(clear - Hα2 Hnin; solve_notin_auto)) as [HΔ' | Hb];
      [ left; clear - HΔ' Hnin; fsetdec | right; exact Hb ].
  - apply ad_refine_syn__hole; assumption.
  - apply ad_refine_syn__tophole_remove; auto.
  - apply ad_refine_syn__tophole_fill with (L := L).
    intros α Hα. apply (H0 α Hα Δr').
    intros α2 Hα2.
    destruct (Habs α2 Hα2) as [HΔ' | Hb];
      [ left; exact HΔ' | right; apply binds_cons_3; exact Hb ].
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l; eauto.
  - eapply ad_refine_syn__flex_r; eauto.
Qed.

(* ⚙ [pskl_no_hole] (hole-free skeletons — for them partial precision is fully
   Δ-MONOTONE, since the □-rule, the only Δ-antitone one, never fires) is
   DEFINED in prop_completeness_consis.v, which this file imports; so is
   [ptyp_to_pskl_no_hole].  The rest of the family — _open, _open_rec, their
   _inv converses, _close, and the msubst_* transports — is below, and has no
   counterpart there. *)

Lemma pskl_no_hole_open_rec : forall P P' k,
  pskl_no_hole P -> pskl_no_hole P' ->
  pskl_no_hole (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k HP HV; simpl in *; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
  - destruct HP; split; auto.
Qed.

Lemma pskl_no_hole_open : forall P α,
  pskl_no_hole P ->
  pskl_no_hole (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof.
  intros P α HP. apply pskl_no_hole_open_rec; simpl; auto.
Qed.

(* [ptyp_to_pskl_no_hole] likewise — prop_completeness_consis.v:1074. *)

Lemma ad_ppre_no_hole_subject_delta_mono : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  pskl_no_hole P ->
  forall Δ', Δ [<=] Δ' ->
  {{ Θ ⨟ Δ' ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Hnh Δ' Hsub.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb];
      [ left; clear - HΔ Hsub; fsetdec | right; assumption ] end.
  - simpl in Hnh; destruct Hnh.
    eapply ad_ppre__arrow; eauto.
  - simpl in Hnh.
    eapply ad_ppre__forall with (L := L); [ | eassumption ].
    intros α Hα.
    apply (H0 α Hα); [ apply pskl_no_hole_open; exact Hnh | ].
    clear - Hsub; fsetdec.
  - simpl in Hnh; contradiction.
  - simpl in Hnh.
    apply ad_ppre__tophole_remove; auto.
  - simpl in Hnh.
    eapply ad_ppre__tophole_fill with (L := L); eauto.
  - simpl in Hnh.
    apply ad_ppre__tophole_keep; auto.
  - eapply ad_ppre__flex_l; [ eassumption | ].
    apply IHad_partial_precise;
      [ apply ptyp_to_pskl_no_hole | exact Hsub ].
  - eapply ad_ppre__flex_r; [ eassumption | ]. auto.
Qed.

(** Refinement's target free variables are source variables or Θ-scoped
    (fills are wf at empty Δ; definitions are Θ-scoped). *)
Lemma ad_refine_syn_ftv_rhs_bound : forall Θ Δr Qh Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Qh ⊳ Q }}ad ->
  ftvar_in_bskl Q [<=] ftvar_in_bskl Qh `union` dom Θ.
Proof.
  intros Θ Δr Qh Q HwfΘ H; induction H; simpl; try (clear; fsetdec).
  - (* arrow *)
    clear - IHad_refine_syn1 IHad_refine_syn2 HwfΘ.
    specialize (IHad_refine_syn1 HwfΘ).
    specialize (IHad_refine_syn2 HwfΘ).
    fsetdec.
  - (* all *)
    pick fresh α for
      (L `union` ftvar_in_bskl Q `union` ftvar_in_bskl P
         `union` dom Θ).
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto) HwfΘ) as Hα.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower P (bskl_var_f α))
      as Hlow.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f α))
      as Hup.
    simpl in *. clear - Hα Hlow Hup Fr. fsetdec.
  - (* hole: the fill is wf at empty Δ *)
    pose proof (a_wf_pskl_ftv_dom H) as Hd.
    rewrite ftvar_pskl_to_bskl_syn.
    clear - Hd; fsetdec.
  - (* tophole_remove *)
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  - (* tophole_fill *)
    pick fresh α for
      (L `union` ftvar_in_bskl P `union` ftvar_in_bskl Q
         `union` dom Θ).
    assert (HwfΘ' : {{ ⊢ ((α ~ abind_tvar) ++ Θ) }}a)
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact HwfΘ ]).
    pose proof (H0 α ltac:(clear - Fr; solve_notin_auto) HwfΘ') as Hα.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower P (bskl_var_f α))
      as Hlow.
    simpl in *. clear - Hα Hlow Fr. fsetdec.
  - (* tophole_keep *)
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  - (* flex_l: the definition image is Θ-scoped *)
    specialize (IHad_refine_syn HwfΘ).
    assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
      by (eapply a_wf_aenv_def_ftv_dom; eauto).
    unfold ptyp_to_bskl_syn in IHad_refine_syn.
    rewrite ftvar_pskl_to_bskl_syn in IHad_refine_syn.
    pose proof (ftvar_ptyp_to_pskl τ) as Hp.
    clear - IHad_refine_syn Hd Hp; fsetdec.
  - (* flex_r *)
    match goal with Hb : binds _ _ _ |- _ =>
      pose proof (binds_In _ _ _ _ Hb) as Hdom end.
    clear - Hdom; fsetdec.
Qed.

(* ===================================================================== *)
(*  PHASE-2 KIT (repair, §6(m)) — no_hole solve/refine facts, the         *)
(*  primary→plain refinement transfer, and the Δ-monotone leaf closer.    *)
(* ===================================================================== *)

(** Defined-flex bindings live in the Θr part of the split. *)
Lemma binds_def_split : forall Θtv Θr α τ,
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  binds α (abind_flex_mono_def τ) (Θtv ++ Θr) ->
  binds α (abind_flex_mono_def τ) Θr.
Proof.
  intros Θtv Θr α τ Htvs Hb.
  unfold binds in *.
  apply in_app_or in Hb; destruct Hb as [Hb | Hb]; [ | exact Hb ].
  exfalso. pose proof (Htvs _ _ Hb) as Hc. discriminate Hc.
Qed.

(** The primary (Θr, Δr)-refinement in statement form (Θ, ∅). *)
Lemma refine_primary_to_plain : forall Θtv Θr Δr Q' Q,
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  Δr [=] dom Θtv ->
  {{ Θr ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  {{ (Θtv ++ Θr) ⨟ empty ⊢ᵣ Q' ⊳ Q }}ad.
Proof.
  intros Θtv Θr Δr Q' Q Htvs HΔr H.
  eapply ad_refine_syn_delta_absorb with (Δr := Δr).
  - eapply ad_refine_syn_weaken; [ exact H | ].
    intros x b Hb. unfold binds in *. apply in_or_app; right; exact Hb.
  - intros α2 Hα2. right.
    assert (HZd : α2 `in` dom Θtv) by (clear - Hα2 HΔr; fsetdec).
    apply binds_In_inv in HZd; destruct HZd as [b Hb].
    pose proof (Htvs _ _ Hb) as Heqb; subst b.
    unfold binds in *. apply in_or_app; left; exact Hb.
Qed.

(** no_hole is reflected by opening. *)
Lemma pskl_no_hole_open_rec_inv : forall P P' k,
  pskl_no_hole (open_pskl_wrt_pskl_rec k P' P) -> pskl_no_hole P.
Proof.
  induction P; intros P' k H; simpl in *; auto.
  - destruct H as [H1 H2]; split; eauto.
  - eauto.
  - eauto.
Qed.

Lemma pskl_no_hole_open_inv : forall P V,
  pskl_no_hole (open_pskl_wrt_pskl P V) -> pskl_no_hole P.
Proof.
  intros P V H. eapply pskl_no_hole_open_rec_inv; exact H.
Qed.

(** no_hole survives ABSTRACTION — needed now that the solve ∀-rules close
    their outputs explicitly (DESIGN §4.3): [close] only ever swaps a free
    variable for a bound index, and neither is a hole. *)
Lemma pskl_no_hole_close_rec : forall P β k,
  pskl_no_hole P -> pskl_no_hole (close_pskl_wrt_pskl_rec k β P).
Proof.
  induction P; intros β k H; simpl in *; auto.
  - (* var_b *) destruct (lt_ge_dec n k); simpl; auto.
  - (* var_f *) destruct (β == α); simpl; auto.
  - (* arrow *) destruct H; split; auto.
Qed.

Lemma pskl_no_hole_close : forall P β,
  pskl_no_hole P -> pskl_no_hole (close_pskl_wrt_pskl β P).
Proof.
  intros P β H; unfold close_pskl_wrt_pskl;
    apply pskl_no_hole_close_rec; exact H.
Qed.

(** msubst preserves and reflects no_hole (images are paints). *)
Lemma msubst_pskl_no_hole : forall κ P,
  pskl_no_hole P -> pskl_no_hole (msubst_pskl κ P).
Proof.
  intros κ; induction P; intros H; simpl in *; auto.
  - apply ptyp_to_pskl_no_hole.
  - destruct H; split; auto.
Qed.

Lemma msubst_pskl_no_hole_inv : forall κ P,
  pskl_no_hole (msubst_pskl κ P) -> pskl_no_hole P.
Proof.
  intros κ; induction P; intros H; simpl in *; auto.
  destruct H; split; auto.
Qed.

(** The solve output is hole-free whenever the counterpart is: holes in
    the output only ever come from a □-counterpart (VacuousR).

    ⭐ The repaired SE-FlexR strengthens rather than threatens this: its
    output is [guess^TY]'s, a PAINT, and a paint has no holes by
    construction — that is the whole point of running the pattern through
    [guess^TY] before it is assigned.  (The old row returned the flexible,
    which was hole-free for the duller reason that a variable is.) *)
Lemma a_solve_eq_no_hole_p0 : forall Θ Pi P0 Ξ Pa,
  {{ Θ ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a ->
  pskl_no_hole P0 ->
  pskl_no_hole Pa.
Proof.
  intros Θ Pi P0 Ξ Pa H; induction H; intros Hnh; simpl in *; auto.
  - (* flex_r: guess^TY's output is a paint *) apply ptyp_to_pskl_no_hole.
  - (* hole_r: the counterpart is □ — excluded *) contradiction.
  - (* arrow *) destruct Hnh; split; auto.
  - (* forall *)
    apply pskl_no_hole_close.
    apply IHa_solve_eq. apply pskl_no_hole_open_rec; simpl; auto.
  - (* tophole_l_all (GhostForall) *)
    apply pskl_no_hole_close.
    apply IHa_solve_eq. apply pskl_no_hole_open_rec; simpl; auto.
  - (* all_l_tophole (ForallGhost) *)
    apply pskl_no_hole_close.
    apply IHa_solve_eq; exact Hnh.
Qed.

(** A refinement into a Δr-binder variable (α0 outside the refinement's
    aenv) forces a hole-free source: the □-fill would have to BE that
    variable, which is not Θr-wf; flex hops never reach it. *)
Lemma ad_refine_inh_deltar_var_rhs_no_hole : forall Θr Δr Q' Q,
  {{ Θr ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall α0 P', Q = bskl_var_f α0 -> Q' = pskl_to_bskl_inh P' ->
  α0 `notin` dom Θr ->
  pskl_no_hole P'.
Proof.
  intros Θr Δr Q' Q H; induction H; intros α0 P' HeqQ HeqL HX0;
    try discriminate HeqQ.
  - (* var *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    simpl; exact I.
  - (* hole: the fill would be the binder variable — not Θr-wf *)
    exfalso.
    destruct P; simpl in HeqQ; try discriminate HeqQ.
    inversion HeqQ; subst.
    match goal with Hwf : {{ _ ⨟ _ ⊢ₚₛ pskl_var_f _ }}a |- _ =>
      inversion Hwf; subst end.
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [Hin | [Hb | [Hb | [τ0 Hb]]]];
      [ clear - Hin; fsetdec
      | apply HX0; eapply binds_In; exact Hb
      | apply HX0; eapply binds_In; exact Hb
      | apply HX0; eapply binds_In; exact Hb ] end.
  - (* tophole_remove *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    simpl. eapply IHad_refine_syn; eauto.
  - (* flex_l: the source is a bare variable *)
    destruct P'; simpl in HeqL; try discriminate HeqL.
    simpl; exact I.
  - (* flex_r: the target variable would be Θr-defined *)
    inversion HeqQ; subst.
    exfalso. apply HX0.
    match goal with Hb : binds _ (abind_flex_mono_def _) _ |- _ =>
      eapply binds_In; exact Hb end.
Qed.

(** The consistency subject's variables under the split: counterpart
    variables or Θr-scoped flex-definition data (the Θtv binders never
    pollute the bound). *)
Lemma consis_subject_ftv_split_bound : forall Ψ Θ R Q Θtv Θr,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  Θ = Θtv ++ Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  {{ ⊢ Θ }}a ->
  ftvar_in_uskl R [<=] ftvar_in_bskl Q `union` dom Θr.
Proof.
  intros Ψ Θ R Q Θtv Θr H HeqΘ Htvs Hwf.
  assert (HwfΘr : {{ ⊢ Θr }}a)
    by (apply a_wf_aenv_app_r with (Θp := Θtv);
        rewrite <- HeqΘ; exact Hwf).
  intros x Hx.
  destruct (ad_pat_consis_ftv_bound H Hx) as [Hin | (α & τ & Hb & Hor)].
  - clear - Hin; fsetdec.
  - subst Θ.
    assert (Hbr : binds α (abind_flex_mono_def τ) Θr)
      by (eapply binds_def_split; [ exact Htvs | exact Hb ]).
    destruct Hor as [-> | Hτ].
    + pose proof (binds_In _ _ _ _ Hbr) as Hd. clear - Hd; fsetdec.
    + assert (Hd : ftvar_in_ptyp τ [<=] dom Θr)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact HwfΘr | exact Hbr ]).
      clear - Hτ Hd; fsetdec.
Qed.

(** Rigid-variable-source refinement into a non-variable target is absurd,
    sub-context version (the def-lookup transports along binds-inclusion
    into the full context, where uniqueness kills it). *)
Lemma ad_refine_syn_rigid_var_nonvar_absurd_sub : forall Θr Δr β Q,
  {{ Θr ⨟ Δr ⊢ᵣ (bskl_var_f β) ⊳ Q }}ad ->
  forall Θfull, (forall x b, binds x b Θr -> binds x b Θfull) ->
  uniq Θfull ->
  binds β abind_tvar Θfull ->
  (forall β0, Q <> bskl_var_f β0) ->
  False.
Proof.
  intros Θr Δr β Q H; inversion H; subst; intros Θfull Hmon Hu Hb Hnv.
  - eapply Hnv; reflexivity.
  - match goal with Hbd : binds _ (abind_flex_mono_def _) _ |- _ =>
      pose proof (Hmon _ _ Hbd) as Hbd';
      pose proof (binds_unique _ _ _ _ _ Hb Hbd' Hu) as Hc;
      discriminate Hc end.
  - eapply Hnv; reflexivity.
Qed.

(** Δ-monotone variant of the leaf closer (the target is a replaced rigid
    variable; the var rule is Δ-positive). *)
Lemma p6cv_close_leaf_mono :
  forall NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0,
  {{ ⊢ Θ }}a ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  rho_leaf NM Θ Δρ Ψρ ψsub ψa ->
  (* closes by SE-Var, so the block is [nil] and no κ-extension arises *)
  exists Pa, {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ nil ⨾ Pa }}a /\
    forall Δ', Δ [<=] Δ' ->
    {{ Θ ⨟ Δ' ⊢ˢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad.
Proof.
  intros NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa ψsub ψa Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf.
  destruct Hleaf as (α & Ψ'' & Heqψa & HαΔρ & Htagsub & Hwfsub & HΨρ).
  subst ψa.
  pose proof (Hfresh α HαΔρ) as (HXb & Hκav & Hdef).
  assert (HαΔ : α `in` Δ) by (clear - Hdelta HαΔρ; fsetdec).
  pose proof (Hapart α HαΔρ) as Hsh.
  destruct (ad_ppre_delta_var_inv Hpre eq_refl HwfΘ HαΔ HXb Hdef Hsh)
    as (Heqm & HΨie).
  assert (HeqPi : Pi = pskl_var_f α)
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
  assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
  exists Pi. split.
  - rewrite HeqPi. apply a_solve_eq__var.
  - intros Δ' Hsub'.
    rewrite Heqm.
    apply ad_ppre__var;
      [ clear - HΨie HΨae; fsetdec
      | left; clear - HαΔ Hsub'; fsetdec ].
Qed.

(* [wf-side-condition] delta_def_fresh Δ Θ — the paper's implicit wf of the
   Δ-extended precision context: Δ's binders postdate Θ's definition images.
   Discovered NECESSARY at the Var case (P6-Cv): with a defined-flex target
   var α whose definition mentions β ∈ Δ, the Pi = □ subcase's conclusion
   precision needs the □-rule at the definition's paint, whose Δ-disjointness
   premise fails — a machine-checked counterexample against the Δ-free
   statement (see DESIGN §6(h)).  All call sites satisfy it: ForallInh
   binders are fresh w.r.t. dom Θ ⊇ def-ftvs (a_wf_aenv_def_ftv_dom), Δρ
   carries it in rho_fresh, and the initial Δ obeys the same discipline. *)

(* ===================================================================== *)
(*  PHASE-3 KIT — the precision RENAME (the ∀-cases' cofinite bodies come *)
(*  from renaming the single fresh-α run: the solve is not deterministic, *)
(*  so per-α reruns would return unrelated outputs) + the msubst/subst    *)
(*  commutation.                                                           *)
(* ===================================================================== *)

(* ⚙ RENAMED from [msubst_pskl_subst_var] 2026-08-09 (cleanup audit §8.1c): it collided with a
   DIFFERENT lemma of that name, and this one takes its image side condition PAIRED (forall p, In p κ -> .. (snd p)); prop_completeness_consis.v's takes it curried. *)
Lemma msubst_pskl_subst_var_paired : forall κ P' α' β,
  α' `notin` dom κ -> β `notin` dom κ ->
  (forall p, In p κ -> α' `notin` ftvar_in_ptyp (snd p)) ->
  subst_pskl_in_pskl (pskl_var_f β) α' (msubst_pskl κ P')
  = msubst_pskl κ (subst_pskl_in_pskl (pskl_var_f β) α' P').
Proof.
  intros κ P' α' β Hα Hβ Hav; induction P'; simpl;
    try (f_equal; auto; fail).
  (* var_f *)
  destruct (α == α') as [-> | Hne].
    + rewrite (msubst_lookup_notin_dom _ Hα).
      simpl.
      rewrite (msubst_lookup_notin_dom _ Hβ).
      default_simp.
    + assert (Hfr : α' `notin`
                ftvar_in_pskl (ptyp_to_pskl (msubst_lookup κ α))).
      { rewrite ftvar_ptyp_to_pskl.
        intros Hc.
        assert (Heq : α = α')
          by (eapply msubst_lookup_ftv_avoid; [ exact Hav | exact Hc ]).
        auto. }
      rewrite (subst_pskl_in_pskl_fresh_eq _ _ _ Hfr).
      reflexivity.
Qed.

(** Renaming a Δ-variable in a partial-precision derivation.  [α] is a
    Δ-only variable (outside Θ and its definition images), [β] globally
    fresh; the □-rule survives because its Δ-disjointness already forces
    α out of the local target. *)
Lemma ad_partial_precise_rename : forall Θ Δ Ψ P ψ,
  {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
  forall αr βr,
  αr `in` Δ ->
  αr `notin` dom Θ ->
  βr `notin` dom Θ -> βr `notin` Δ ->
  βr `notin` ftvar_in_pskl P -> βr `notin` ftvar_in_uskl ψ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     αr `notin` ftvar_in_ptyp τ /\ βr `notin` ftvar_in_ptyp τ) ->
  {{ Θ ⨟ (add βr (remove αr Δ)) ⊢ˢ
    (subst_pskl_in_pskl (pskl_var_f βr) αr P)
    ⊑ᵖ[ Ψ ] (subst_uskl_in_uskl (uskl_var_f βr) αr ψ) }}ad.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros αr βr HαΔ HαΘ HβΘ HβΔ HYP Hβψ Hdefs; simpl in *.
  - (* unit *) apply ad_ppre__unit; assumption.
  - (* var *)
    destruct (eq_var α αr) as [-> | Hne].
    + destruct_if as [_ | Hc]; [ | exfalso; auto ].
      apply ad_ppre__var; [ assumption | left; clear; fsetdec ].
    + destruct_if as [Hc | _]; [ exfalso; auto | ].
      apply ad_ppre__var; [ assumption | ].
      match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
        destruct Hor as [HΔ | Hb];
        [ left; clear - HΔ Hne; fsetdec | right; assumption ] end.
  - (* arrow *)
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1; auto
      | apply IHad_partial_precise2; auto
      | assumption ].
  - (* forall *)
    eapply ad_ppre__forall
      with (L := L `union` singleton αr `union` singleton βr
                   `union` Δ `union` dom Θ); [ | eassumption ].
    intros α2 Hα2.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα2; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    eapply ad_partial_precise_delta_cong;
      [ apply (H0 α2 ltac:(clear - Hα2; solve_notin_auto) αr βr);
        [ clear - HαΔ; fsetdec
        | exact HαΘ | exact HβΘ
        | clear - HβΔ Hα2; fsetdec
        | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P
                        (pskl_var_f α2)) as Hup;
          simpl in Hup; clear - HYP Hα2 Hup; fsetdec
        | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                        (uskl_var_f α2)) as Hup;
          simpl in Hup; clear - Hβψ Hα2 Hup; fsetdec
        | exact Hdefs ]
      | clear - Hα2; fsetdec ].
  - (* hole: α is already out of the local target *)
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      assert (Hαψ : αr `notin` ftvar_in_uskl ψ)
        by (clear - Hint HαΔ; fsetdec);
      rewrite (subst_uskl_in_uskl_fresh_eq _ _ _ Hαψ);
      apply ad_ppre__hole; [ assumption | clear - Hint Hβψ; fsetdec ]
    end.
  - (* tophole_remove *)
    apply ad_ppre__tophole_remove.
    apply IHad_partial_precise; auto.
  - (* tophole_fill *)
    eapply ad_ppre__tophole_fill
      with (L := L `union` singleton αr `union` singleton βr
                   `union` Δ `union` dom Θ).
    intros α2 Hα2.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    replace (pskl_tophole (subst_pskl_in_pskl (pskl_var_f βr) αr P))
      with (subst_pskl_in_pskl (pskl_var_f βr) αr (pskl_tophole P))
      by reflexivity.
    apply (H0 α2 ltac:(clear - Hα2; solve_notin_auto) αr βr).
    + exact HαΔ.
    + simpl. clear - HαΘ Hα2; fsetdec.
    + simpl. clear - HβΘ Hα2; fsetdec.
    + exact HβΔ.
    + simpl. simpl in HYP. exact HYP.
    + pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                    (uskl_var_f α2)) as Hup;
      simpl in Hup; clear - Hβψ Hα2 Hup; fsetdec.
    + intros α τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | exact (Hdefs _ _ Hb') ].
  - (* tophole_keep *)
    apply ad_ppre__tophole_keep.
    apply IHad_partial_precise; auto.
  - (* flex_l *)
    assert (Hne : α <> αr).
    { intros ->. apply HαΘ. eapply binds_In; eassumption. }
    destruct_if as [Hc | _]; [ exfalso; auto | ].
    destruct (Hdefs _ _ H) as [Hατ Hβτ].
    eapply ad_ppre__flex_l; [ eassumption | ].
    assert (Hfr : αr `notin` ftvar_in_pskl (ptyp_to_pskl τ))
      by (rewrite ftvar_ptyp_to_pskl; exact Hατ).
    rewrite <- (subst_pskl_in_pskl_fresh_eq
                  (ptyp_to_pskl τ) (pskl_var_f βr) αr Hfr).
    apply IHad_partial_precise; auto.
    rewrite ftvar_ptyp_to_pskl. exact Hβτ.
  - (* flex_r *)
    assert (Hne : α <> αr).
    { intros ->. apply HαΘ. eapply binds_In; eassumption. }
    destruct_if as [Hc | _]; [ exfalso; auto | ].
    destruct (Hdefs _ _ H) as [Hατ Hβτ].
    eapply ad_ppre__flex_r; [ eassumption | ].
    assert (Hfr : αr `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ))
      by (rewrite ftvar_in_uskl_ptyp_to_uskl_syn; exact Hατ).
    rewrite <- (subst_uskl_in_uskl_fresh_eq
                  (ptyp_to_uskl_syn τ) (uskl_var_f βr) αr Hfr).
    apply IHad_partial_precise; auto.
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn. exact Hβτ.
Qed.

(* ===================================================================== *)
(*  ⭐ THE [Θw] TRANSPORT AT AN SE-FlexR NODE (2026-08-04).                *)
(*                                                                        *)
(*  [a_guess_ty_witness_mono] reports the κ-extension's payloads           *)
(*  well-formed in [Θw] — the context that stays FIXED as a P6 induction   *)
(*  goes under ∀ binders — while a P6 row has the counterpart monotype's   *)
(*  well-formedness only in [Θ], which under a ∀ row is [Θw] EXTENDED by   *)
(*  the bound rigid.  The four lemmas below are the transport, and each    *)
(*  P6 file's own FLEX block runs the same three steps:                    *)
(*                                                                        *)
(*    ftv (ψa1 → ψa2)  ⊆ ftv (Q1 → Q2) ∪ dom Θw   [consis_subject_ftv_defs_bound]
      ftv (Q1 → Q2)    ⊆ dom Θw                   [ad_refine_mono_paint_ftv_bound]
      a_wf_ptyp Θ τ + ftv τ ⊆ dom Θw ⟹ a_wf_ptyp Θw τ                            *)
(*                                                                        *)
(*  The point of the middle step is that BOTH bounds are stated over the   *)
(*  DEFINITIONS of the context, never over its domain: a bound rigid       *)
(*  carries no definition, so it can never enter either bound.  The naive  *)
(*  route through [dom Θr] fails — the [forall_syn_tagged] row puts its    *)
(*  binder on the Θr side.                                                 *)
(* ===================================================================== *)

(** ⭐ Refining a MONO PAINT introduces no variable the source and the
    context's DEFINITIONS do not already have.  The [dom Θ] of
    [ad_refine_syn_ftv_rhs_bound] is over-generous by exactly the hole rule
    — whose fill is only [Θ]-scoped — and a mono paint has no hole. *)
Lemma ad_refine_mono_paint_ftv_bound : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall τb S, Q' = ptyp_to_bskl_syn τb -> mono_ptyp τb ->
  ftvar_in_ptyp τb [<=] S ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     α `in` S /\ ftvar_in_ptyp τ0 [<=] S) ->
  ftvar_in_bskl Q [<=] S.
Proof.
  intros Θ Δr Q' Q HwfΘ H; induction H; intros τb S HeqL Hmb Hsub Hdefs.
  - (* unit *) simpl. clear; fsetdec.
  - (* var: the paint IS that variable *)
    symmetry in HeqL. apply ptyp_to_bskl_syn_var_inv in HeqL; subst τb.
    simpl in *. clear - Hsub; fsetdec.
  - (* arrow *)
    symmetry in HeqL.
    destruct (ptyp_to_bskl_syn_arrow_inv _ HeqL)
      as (τ1 & τ2 & -> & Heq1 & Heq2).
    simpl in Hsub.
    assert (Hm1 : mono_ptyp τ1) by (inversion Hmb; assumption).
    assert (Hm2 : mono_ptyp τ2) by (inversion Hmb; assumption).
    assert (Hb1 : ftvar_in_bskl P1 [<=] S)
      by (eapply IHad_refine_syn1;
            [ exact HwfΘ | exact Heq1 | exact Hm1
            | clear - Hsub; fsetdec | exact Hdefs ]).
    assert (Hb2 : ftvar_in_bskl P2 [<=] S)
      by (eapply IHad_refine_syn2;
            [ exact HwfΘ | exact Heq2 | exact Hm2
            | clear - Hsub; fsetdec | exact Hdefs ]).
    simpl. clear - Hb1 Hb2; fsetdec.
  - (* all: LHS all_inh, never a paint *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* hole: LHS □, never a paint — THIS is the case the bound needs shut *)
    destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_remove *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_fill *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* tophole_keep *) destruct τb; simpl in HeqL; discriminate HeqL.
  - (* flex_l: the source variable's DEFINITION becomes the new paint *)
    destruct τb; simpl in HeqL; try discriminate HeqL.
    inversion HeqL; subst.
    destruct (Hdefs _ _ H) as [_ Hτ].
    eapply IHad_refine_syn;
      [ exact HwfΘ | reflexivity
      | eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact H ]
      | exact Hτ | exact Hdefs ].
  - (* flex_r: the target IS a DEFINED variable *)
    destruct (Hdefs _ _ H) as [Hα _]. simpl. clear - Hα; fsetdec.
Qed.

(** The [consis_subject_ftv_bag_bound] of P6-Cv, but over the DEFINITIONS
    of [Θ] rather than over a domain — same reason as above. *)
Lemma consis_subject_ftv_defs_bound : forall Ψ Θ R Q S,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  (forall α τ0, binds α (abind_flex_mono_def τ0) Θ ->
     α `in` S /\ ftvar_in_ptyp τ0 [<=] S) ->
  ftvar_in_uskl R [<=] ftvar_in_bskl Q `union` S.
Proof.
  intros Ψ Θ R Q S H Hdefs x Hx.
  destruct (ad_pat_consis_ftv_bound H Hx) as [Hin | (α & τ & Hb & Hor)].
  - clear - Hin; fsetdec.
  - destruct (Hdefs _ _ Hb) as [Hα Hτ].
    destruct Hor as [-> | Hxτ];
      [ clear - Hα; fsetdec | clear - Hxτ Hτ; fsetdec ].
Qed.

(* ===================================================================== *)
(*  ⭐ READING THE PACKAGE'S wf COMPONENT (2026-08-04).                    *)
(*  A P6 ∀ row hands its body's extension [κ'] back out and then works     *)
(*  under [κ' ++ κ]; both moves below are what that costs.                 *)
(* ===================================================================== *)

(** A binds-level inclusion is a domain inclusion. *)
Lemma aenv_binds_dom_sub : forall (Θ Θ' : aenv),
  (forall x b, binds x b Θ -> binds x b Θ') ->
  dom Θ [<=] dom Θ'.
Proof.
  intros Θ Θ' Hmon x Hx.
  apply binds_In_inv in Hx; destruct Hx as [b Hb].
  eapply binds_In; apply Hmon; exact Hb.
Qed.

(** The package's payloads are context-SCOPED — the form
    [msubst_pskl_subst_var_paired] and the ∀-row renamings ask for. *)
Lemma forall_wf_mono_images_dom : forall (Θ : aenv) (κ' : metasubst),
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' ->
  forall p, In p κ' -> ftvar_in_ptyp (snd p) [<=] dom Θ.
Proof.
  intros Θ κ' HF p Hp.
  rewrite Forall_forall in HF.
  destruct (HF p Hp) as [Hw _].
  eapply a_wf_ptyp_ftv_dom; exact Hw.
Qed.

Lemma msubst_lc_app_wf : forall Θ κa κb,
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa ->
  msubst_lc κb ->
  msubst_lc (κa ++ κb).
Proof.
  intros Θ κa κb Hall Hlc; unfold msubst_lc in *; intros α.
  induction κa as [ | [α1 τ1] κa' IH ]; cbn; [ apply Hlc | ].
  inversion Hall as [ | ph pt [Hwf1 Hm1] Hall' ]; subst; cbn in Hwf1.
  destruct (α == α1) as [-> | Hne];
    [ eapply a_wf_ptyp_lc; exact Hwf1 | apply IH; exact Hall' ].
Qed.
