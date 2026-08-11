(** ⚠️ DO NOT MERGE THIS INTO [prop_precise.v].  No cycle — but it imports
    [algo/consis/prop_soundness_consis.v] (5610 lines), and [prop_precise] has
    24 consumers, so the merge would put that dependency on all of them and
    make every edit to consistency soundness rebuild the precision layer and
    everything above it.  Checked 2026-08-09 during the file-reorg pass. *)

(** PRECISION RECOVERY at the flexible consistency nodes
    (Flex / FlexL / FlexR of [a_consis]).

    ------------------------------------------------------------------------
    THE OBLIGATION (docs/PAPER-GAPS.md §9.1, "§1's flexible cases").

    [thm:complete-consistency]'s OPTIMALITY half concludes, for a consistency
    node, a PRECISION statement

        {{ Θ ⨟ (Δ₁ ∪ Δ₂) ⊢ₚᵣ (msubst_bskl ζ Qt) ⊑ (bskl_to_pskl Qb) }}ad

    (see [consis_optimal_post], algo/prop_consis_complete.v:189).  For the
    three flexible rules the algorithmic OUTPUT painting is [Qt = α̂] (a
    flexible variable): the rule assigns/unifies [α̂] and returns it.  The
    consistency paper dismisses these three cases in one sentence —
    "handled by the other two parts of the lemma" (consistency-proofs.tex
    :2568-2569) — but the §2/§3 (unification/assignment) optimality IHs
    produce NO precision statement at all.  So [Θ ⊢ ζα̂ ⊑ Qb] must be proved
    SEPARATELY.  THAT is this file.  It is a genuine [paper-gap] (the sentence
    hides real work); we fill it.

    ------------------------------------------------------------------------
    THE ARGUMENT.

    A flexible variable is assigned a MONOTYPE (guess^TY returns a monotype),
    so both the algorithm's ζ-solved output [ζα̂] and the competing solution's
    join [Qb] are monotype paintings, and PRECISION between monotype INHERITED
    paintings collapses (via [ptyp_to_bskl_inh_syn_eq]) to the plain
    refinement [{{ … ⊢ᵣ syn(ζα̂) ⊳ syn(Qb) }}ad].  The whole thing reduces to a TYPE
    EQUIVALENCE [{{ Θ ⊢ ζα̂ ≡ᵗ Qb }}a], recovered as follows:

      * the COMPETING solution's join / Δ-refinement, run through the mono
        bridge ([consis_mono_join] / [refine_mono_join], algo/prop_mono_bridge.v),
        gives [{{ Θ ⊢ κα̂ ≡ᵗ C }}a] with [Qb = syn C];
      * the factoring [a_inc_equiv Θ₀ κ (ζ∘κ₁) Θ] handed over by the §2/§3 IH,
        together with the algorithm's [κ₁ = identity] (a_isub), gives
        [{{ Θ ⊢ κα̂ ≡ᵗ ζα̂ }}a];
      * transitivity closes [{{ Θ ⊢ ζα̂ ≡ᵗ C }}a], and the mono→precision core
        ([tyequiv_mono_precise]) turns it back into the precision goal.

    The reusable core [tyequiv_mono_precise] is the exact converse of the
    already-green [refine_mono_join]: it BUILDS refinement between two
    monotype paintings from their equivalence.  We obtain it for free by
    composing the converse bridge [tyequiv_mono_consis] with the
    consistency→refinement mono lemma [ad_pat_consis_refine_syn_f_mono].

    NOTE ON [κ₁].  [consis_optimal_post] quantifies the algorithmic solution
    [κ₁] universally (only [κ₁ ∷ Θ₀ ⊑ Θ₁]).  The recovery genuinely needs
    [κ₁] to act as the identity on [α̂] — [msubst_lookup κ₁ α = ptyp_var_f α]
    — which is how the (OPT) proof instantiates it (the algorithm's own
    solution is the identity metasubstitution [a_isub]; DESIGN-completeness-
    measure.md §7.3 L10).  We take that as an explicit hypothesis of the
    per-node lemmas; it is discharged at the call site from [Θ₀ ⊴ Θ₁].
    Without it the statement is FALSE (a non-identity [κ₁] can route [α̂]
    through an unrelated fresh flex; see the report). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.decorated_algo.prop_decorate.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.prop_precise.

Set Implicit Arguments.

(* ===================================================================== *)
(*  CORE: type equivalence of monotypes  ⟹  precision of their paintings   *)
(*                                                                         *)
(*  The exact converse of [refine_mono_join] (prop_mono_bridge.v:191).     *)
(*  Obtained by composing the converse bridge [tyequiv_mono_consis] with    *)
(*  the consistency→refinement mono lemma [ad_pat_consis_refine_syn_f_mono].*)
(* ===================================================================== *)

Lemma tyequiv_mono_refine_syn : forall Θ Δ A A',
  {{ ⊢ Θ }}a ->
  mono_ptyp A -> mono_ptyp A' ->
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  (forall α, α `in` ftvar_in_ptyp A -> a_binds_tvar α Θ) ->
  {{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn A) ⊳ (ptyp_to_bskl_syn A') }}ad.
Proof.
  intros Θ Δ A A' Hwf HmA HmB Heq Hvis.
  assert (Hc : {{ empty ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn A) ∼ (ptyp_to_bskl_syn A') }}ad)
    by (apply tyequiv_mono_consis; auto).
  eapply (ad_refine_syn_f_forget (F := empty)).
  replace (ptyp_to_bskl_syn A)
    with (pskl_to_bskl_inh (uskl_to_pskl (ptyp_to_uskl_syn A))).
  2:{ rewrite uskl_to_pskl_ptyp. apply ptyp_to_bskl_inh_syn_eq; auto. }
  eapply ad_pat_consis_refine_syn_f_mono;
    [ exact Hc | exact Hwf | apply mono_ptyp_to_bskl_syn; auto | | ].
  - clear. fsetdec.
  - intros β τ Hb. clear. fsetdec.
Qed.

(* ===================================================================== *)
(*  CORE: the monotype precision goal, in the exact shape the flexible     *)
(*  optimality nodes present it (subject [msubst_bskl ζ α̂], target [Qb]).  *)
(* ===================================================================== *)

Lemma consis_precise_core : forall Θ Δ ζ α Qb A,
  {{ ⊢ Θ }}a ->
  mono_ptyp (msubst_lookup ζ α) ->
  (forall α0, α0 `in` ftvar_in_ptyp (msubst_lookup ζ α) -> a_binds_tvar α0 Θ) ->
  mono_ptyp A ->
  Qb = ptyp_to_bskl_syn A ->
  {{ Θ ⊢ (msubst_lookup ζ α) ≡ᵗ A }}a ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb) }}ad.
Proof.
  intros Θ Δ ζ α Qb A Hwf HmA Hvis HmC HQb Heq.
  unfold ad_precise.
  (* left painting reduces to the syn painting of the monotype [ζα] *)
  replace (bskl_to_pskl (msubst_bskl ζ (bskl_var_f α)))
    with (ptyp_to_pskl (msubst_lookup ζ α)).
  2:{ change (msubst_bskl ζ (bskl_var_f α))
        with (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ζ α))).
      rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity. }
  rewrite (ptyp_to_bskl_inh_syn_eq HmA).
  (* right painting reduces to [Qb = syn A] *)
  subst Qb.
  replace (bskl_to_pskl (ptyp_to_bskl_syn A)) with (ptyp_to_pskl A).
  2:{ unfold ptyp_to_bskl_syn. rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity. }
  rewrite (ptyp_to_bskl_inh_syn_eq HmC).
  apply tyequiv_mono_refine_syn; auto.
Qed.

(* ===================================================================== *)
(*  a_inc_equiv, per-variable: the two metasubstitutions agree (up to ≡ᵗ)   *)
(*  on every flexible source variable.  Mirrors [a_inc_lookup_def]         *)
(*  (prop_compose.v:489).                                                  *)
(* ===================================================================== *)

Lemma a_inc_equiv_lookup : forall Θ0 κ1 κ2 Θ,
  a_inc_equiv Θ0 κ1 κ2 Θ ->
  forall α, a_flex_tvar Θ0 α ->
  {{ Θ ⊢ (msubst_lookup κ1 α) ≡ᵗ (msubst_lookup κ2 α) }}a.
Proof.
  intros Θ0 κ1 κ2 Θ H; induction H; intros α0 Hflex.
  - (* empty : no flexible variable in the empty context *)
    destruct Hflex as [Hb | [τ Hb]]; inversion Hb.
  - (* flex head *)
    simpl. destruct (α0 == α) as [->|Hne]; [ exact H0 | ].
    apply IHa_inc_equiv.
    destruct Hflex as [Hb | [τ Hb]].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqα _] | Hb'];
        [ congruence | left; exact Hb' ].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | right; exists τ; exact Hb' ].
  - (* flex_def head *)
    simpl. destruct (α0 == α) as [->|Hne]; [ exact H0 | ].
    apply IHa_inc_equiv.
    destruct Hflex as [Hb | [τ0 Hb]].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | left; exact Hb' ].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqα _] | Hb'];
        [ congruence | right; exists τ0; exact Hb' ].
  - (* var_typ head : κ1/κ2 unchanged, target grows — weaken *)
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds; apply in_or_app; right; simpl; right; exact Hby | ].
    apply IHa_inc_equiv.
    destruct Hflex as [Hb | [τ Hb]].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | left; exact Hb' ].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | right; exists τ; exact Hb' ].
  - (* var_skl head *)
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds; apply in_or_app; right; simpl; right; exact Hby | ].
    apply IHa_inc_equiv.
    destruct Hflex as [Hb | [τ Hb]].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | left; exact Hb' ].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | right; exists τ; exact Hb' ].
  - (* tvar head *)
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds; apply in_or_app; right; simpl; right; exact Hby | ].
    apply IHa_inc_equiv.
    destruct Hflex as [Hb | [τ Hb]].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | left; exact Hb' ].
    + destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
        [ discriminate | right; exists τ; exact Hb' ].
Qed.

(** The factoring [κ ≡ ζ∘κ₁], evaluated at the still-live flexible [α̂]:
    when [κ₁] is the identity on [α̂] (the (OPT) instantiation), the
    composite collapses to [ζ], so the competing [κα̂] and the algorithmic
    [ζα̂] are equivalent. *)
Lemma a_inc_equiv_compose_id_at : forall Θ0 κ κ1 ζ Θ α,
  a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ ->
  a_flex_tvar Θ0 α ->
  α `in` dom κ1 ->
  msubst_lookup κ1 α = ptyp_var_f α ->
  {{ Θ ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup ζ α) }}a.
Proof.
  intros Θ0 κ κ1 ζ Θ α Hie Hflex Hdom Hid.
  pose proof (a_inc_equiv_lookup Hie Hflex) as He.
  rewrite (msubst_lookup_compose ζ κ1 (or_introl Hdom)) in He.
  rewrite Hid in He. simpl in He.
  exact He.
Qed.

(* ===================================================================== *)
(*  Per-node precision recovery.                                            *)
(*                                                                         *)
(*  Two shapes, by where the competing monotype [C] comes from:            *)
(*    - [consis_precise_via_join]   : the SUBJECT is [α̂] (rules Flex, FlexL)*)
(*      — read [C] off the competing consistency JOIN of [κα̂];             *)
(*    - [consis_precise_via_refine] : the INPUT is [α̂]   (rule FlexR)       *)
(*      — read [C] off the competing Δ₁-REFINEMENT of [κα̂].                 *)
(*  Both conclude the [consis_optimal_post] precision conjunct verbatim.    *)
(* ===================================================================== *)

(** Shared tail: given [κα̂ ≡ᵗ C], [Qb = syn C], and the factoring, close the
    precision goal. *)
Lemma consis_precise_close : forall Θ0 Θ1 Θ Δ κ κ1 ζ α Qb A,
  {{ ⊢ Θ }}a ->
  a_flex_tvar Θ0 α ->
  a_binds_tvar α Θ1 ->
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ ->
  α `in` dom κ1 ->
  msubst_lookup κ1 α = ptyp_var_f α ->
  mono_ptyp A ->
  Qb = ptyp_to_bskl_syn A ->
  {{ Θ ⊢ (msubst_lookup κ α) ≡ᵗ A }}a ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb) }}ad.
Proof.
  intros Θ0 Θ1 Θ Δ κ κ1 ζ α Qb A
         Hwf Hflex HbΘ1 HζΘ Hwf1 Hie Hdom Hid HmC HQb HeqκαC.
  assert (Hζκ : {{ Θ ⊢ (msubst_lookup κ α) ≡ᵗ (msubst_lookup ζ α) }}a)
    by (eapply a_inc_equiv_compose_id_at; eauto).
  assert (HmζA : mono_ptyp (msubst_lookup ζ α))
    by (eapply a_inc_lookup_mono; exact HζΘ).
  assert (HvisζA : forall α0,
             α0 `in` ftvar_in_ptyp (msubst_lookup ζ α) -> a_binds_tvar α0 Θ).
  { intros α0 Hα0. eapply a_wf_ptyp_ftv_tvarish;
      [ eapply a_inc_lookup_wf; eauto | exact Hα0 ]. }
  eapply consis_precise_core with (A := A); eauto.
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact Hζκ | exact HeqκαC ].
Qed.

(** Rules Flex / FlexL: the SUBJECT painting is [α̂], so the competing
    consistency judgment's subject is [κα̂]; its join is the monotype [C]. *)
Lemma consis_precise_via_join : forall Θ0 Θ1 Θ Δ κ κ1 ζ α Qb,
  {{ ⊢ Θ }}a ->
  a_flex_tvar Θ0 α ->
  κ ∷ Θ0 ⊑ Θ ->
  a_binds_tvar α Θ1 ->
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ ->
  α `in` dom κ1 ->
  msubst_lookup κ1 α = ptyp_var_f α ->
  {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ (pskl_var_f α))) ∼ Qb }}ad ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb) }}ad.
Proof.
  intros Θ0 Θ1 Θ Δ κ κ1 ζ α Qb
         Hwf Hflex HκΘ HbΘ1 HζΘ Hwf1 Hie Hdom Hid Hjoin.
  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact HκΘ).
  replace (msubst_pskl κ (pskl_var_f α))
    with (ptyp_to_pskl (msubst_lookup κ α)) in Hjoin by reflexivity.
  rewrite pskl_to_uskl_ptyp in Hjoin.
  destruct (consis_mono_join Hjoin Hwf (A := msubst_lookup κ α) eq_refl Hmκα)
    as [C [HmC [HQb HeqκαC]]].
  eapply consis_precise_close; eauto.
Qed.

(** Rule FlexR: the INPUT painting is [α̂], so the competing Δ₁-refinement's
    source is [inh(κα̂)]; refine_mono_join reads off the monotype [C]. *)
Lemma consis_precise_via_refine : forall Θ0 Θ1 Θ Δ Δ1 κ κ1 ζ α Qb,
  {{ ⊢ Θ }}a ->
  a_flex_tvar Θ0 α ->
  κ ∷ Θ0 ⊑ Θ ->
  a_binds_tvar α Θ1 ->
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ ->
  α `in` dom κ1 ->
  msubst_lookup κ1 α = ptyp_var_f α ->
  ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f α))) Qb ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb) }}ad.
Proof.
  intros Θ0 Θ1 Θ Δ Δ1 κ κ1 ζ α Qb
         Hwf Hflex HκΘ HbΘ1 HζΘ Hwf1 Hie Hdom Hid Hrs.
  assert (Hmκα : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact HκΘ).
  apply ad_refine_syn_f_forget in Hrs.
  replace (msubst_pskl κ (pskl_var_f α))
    with (ptyp_to_pskl (msubst_lookup κ α)) in Hrs by reflexivity.
  rewrite (ptyp_to_bskl_inh_syn_eq Hmκα) in Hrs.
  destruct (refine_mono_join Hrs Hwf (A := msubst_lookup κ α) eq_refl Hmκα)
    as [C [HmC [HQb HeqκαC]]].
  eapply consis_precise_close; eauto.
Qed.
