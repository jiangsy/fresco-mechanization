(** PRECISION RECOVERY at the flexible consistency nodes
    (Flex / FlexL / FlexR of [a_consis]).

    ------------------------------------------------------------------------
    THE OBLIGATION (docs/PAPER-GAPS.md §9.1, "§1's flexible cases").

    [thm:complete-consistency]'s OPTIMALITY half concludes, for a consistency
    node, a PRECISION statement

        Θ ⨟ (Δ₁ ∪ Δ₂) ⊢ₚᵣᵃ (msubst_bskl ζ Qt) ⊑ (bskl_to_pskl Qb)

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
    refinement [⊢ᵣᵃ syn(ζα̂) ⊳ syn(Qb)].  The whole thing reduces to a TYPE
    EQUIVALENCE [Θ ⊢ ζα̂ ≡ᵗ Qb], recovered as follows:

      * the COMPETING solution's join / Δ-refinement, run through the mono
        bridge ([consis_mono_join] / [refine_mono_join], algo/prop_mono_bridge.v),
        gives [Θ ⊢ θα̂ ≡ᵗ C] with [Qb = syn C];
      * the factoring [a_inc_equiv Θ₀ θ (ζ∘θ₁) Θ] handed over by the §2/§3 IH,
        together with the algorithm's [θ₁ = identity] (a_isub), gives
        [Θ ⊢ θα̂ ≡ᵗ ζα̂];
      * transitivity closes [Θ ⊢ ζα̂ ≡ᵗ C], and the mono→precision core
        ([tyequiv_mono_precise]) turns it back into the precision goal.

    The reusable core [tyequiv_mono_precise] is the exact converse of the
    already-green [refine_mono_join]: it BUILDS refinement between two
    monotype paintings from their equivalence.  We obtain it for free by
    composing the converse bridge [tyequiv_mono_consis] with the
    consistency→refinement mono lemma [ad_pat_consis_refine_syn_f_mono].

    NOTE ON [θ₁].  [consis_optimal_post] quantifies the algorithmic solution
    [θ₁] universally (only [Θ₀ ≤[θ₁] Θ₁]).  The recovery genuinely needs
    [θ₁] to act as the identity on [α̂] — [msubst_lookup θ₁ α = ptyp_var_f α]
    — which is how the (OPT) proof instantiates it (the algorithm's own
    solution is the identity metasubstitution [a_isub]; DESIGN-completeness-
    measure.md §7.3 L10).  We take that as an explicit hypothesis of the
    per-node lemmas; it is discharged at the call site from [Θ₀ ⊴ Θ₁].
    Without it the statement is FALSE (a non-identity [θ₁] can route [α̂]
    through an unrelated fresh flex; see the report). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_precise.

Set Implicit Arguments.

(* ===================================================================== *)
(*  CORE: type equivalence of monotypes  ⟹  precision of their paintings   *)
(*                                                                         *)
(*  The exact converse of [refine_mono_join] (prop_mono_bridge.v:191).     *)
(*  Obtained by composing the converse bridge [tyequiv_mono_consis] with    *)
(*  the consistency→refinement mono lemma [ad_pat_consis_refine_syn_f_mono].*)
(* ===================================================================== *)

Lemma tyequiv_mono_refine_syn : forall Θ Δ A B,
  a_wf_aenv Θ ->
  mono_ptyp A -> mono_ptyp B ->
  Θ ⊢ A ≡ᵗ B ->
  (forall X, X `in` ftvar_in_ptyp A -> a_binds_tvar X Θ) ->
  Θ ⨟ Δ ⊢ᵣᵃ (ptyp_to_bskl_syn A) ⊳ (ptyp_to_bskl_syn B).
Proof.
  intros Θ Δ A B Hwf HmA HmB Heq Hvis.
  assert (Hc : empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn A) ≈ (ptyp_to_bskl_syn B))
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

Lemma consis_precise_core : forall Θ Δ ζ α Qb C,
  a_wf_aenv Θ ->
  mono_ptyp (msubst_lookup ζ α) ->
  (forall X, X `in` ftvar_in_ptyp (msubst_lookup ζ α) -> a_binds_tvar X Θ) ->
  mono_ptyp C ->
  Qb = ptyp_to_bskl_syn C ->
  Θ ⊢ (msubst_lookup ζ α) ≡ᵗ C ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb).
Proof.
  intros Θ Δ ζ α Qb C Hwf HmA Hvis HmC HQb Heq.
  unfold ad_precise.
  (* left painting reduces to the syn painting of the monotype [ζα] *)
  replace (bskl_to_pskl (msubst_bskl ζ (bskl_var_f α)))
    with (ptyp_to_pskl (msubst_lookup ζ α)).
  2:{ change (msubst_bskl ζ (bskl_var_f α))
        with (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ζ α))).
      rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity. }
  rewrite (ptyp_to_bskl_inh_syn_eq HmA).
  (* right painting reduces to [Qb = syn C] *)
  subst Qb.
  replace (bskl_to_pskl (ptyp_to_bskl_syn C)) with (ptyp_to_pskl C).
  2:{ unfold ptyp_to_bskl_syn. rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity. }
  rewrite (ptyp_to_bskl_inh_syn_eq HmC).
  apply tyequiv_mono_refine_syn; auto.
Qed.

(* ===================================================================== *)
(*  a_inc_equiv, per-variable: the two metasubstitutions agree (up to ≡ᵗ)   *)
(*  on every flexible source variable.  Mirrors [a_inc_lookup_def]         *)
(*  (prop_compose.v:489).                                                  *)
(* ===================================================================== *)

Lemma a_inc_equiv_lookup : forall Θ0 θ1 θ2 Θ,
  a_inc_equiv Θ0 θ1 θ2 Θ ->
  forall α, a_flex_tvar Θ0 α ->
  Θ ⊢ (msubst_lookup θ1 α) ≡ᵗ (msubst_lookup θ2 α).
Proof.
  intros Θ0 θ1 θ2 Θ H; induction H; intros α0 Hflex.
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
  - (* var_typ head : θ1/θ2 unchanged, target grows — weaken *)
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

(** The factoring [θ ≡ ζ∘θ₁], evaluated at the still-live flexible [α̂]:
    when [θ₁] is the identity on [α̂] (the (OPT) instantiation), the
    composite collapses to [ζ], so the competing [θα̂] and the algorithmic
    [ζα̂] are equivalent. *)
Lemma a_inc_equiv_compose_id_at : forall Θ0 θ θ1 ζ Θ α,
  a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ ->
  a_flex_tvar Θ0 α ->
  α `in` dom θ1 ->
  msubst_lookup θ1 α = ptyp_var_f α ->
  Θ ⊢ (msubst_lookup θ α) ≡ᵗ (msubst_lookup ζ α).
Proof.
  intros Θ0 θ θ1 ζ Θ α Hie Hflex Hdom Hid.
  pose proof (a_inc_equiv_lookup Hie Hflex) as He.
  rewrite (msubst_lookup_compose ζ θ1 (or_introl Hdom)) in He.
  rewrite Hid in He. simpl in He.
  exact He.
Qed.

(* ===================================================================== *)
(*  Per-node precision recovery.                                            *)
(*                                                                         *)
(*  Two shapes, by where the competing monotype [C] comes from:            *)
(*    - [consis_precise_via_join]   : the SUBJECT is [α̂] (rules Flex, FlexL)*)
(*      — read [C] off the competing consistency JOIN of [θα̂];             *)
(*    - [consis_precise_via_refine] : the INPUT is [α̂]   (rule FlexR)       *)
(*      — read [C] off the competing Δ₁-REFINEMENT of [θα̂].                 *)
(*  Both conclude the [consis_optimal_post] precision conjunct verbatim.    *)
(* ===================================================================== *)

(** Shared tail: given [θα̂ ≡ᵗ C], [Qb = syn C], and the factoring, close the
    precision goal. *)
Lemma consis_precise_close : forall Θ0 Θ1 Θ Δ θ θ1 ζ α Qb C,
  a_wf_aenv Θ ->
  a_flex_tvar Θ0 α ->
  a_binds_tvar α Θ1 ->
  Θ1 ≤[ ζ ] Θ ->
  a_wf_aenv Θ1 ->
  a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ ->
  α `in` dom θ1 ->
  msubst_lookup θ1 α = ptyp_var_f α ->
  mono_ptyp C ->
  Qb = ptyp_to_bskl_syn C ->
  Θ ⊢ (msubst_lookup θ α) ≡ᵗ C ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb).
Proof.
  intros Θ0 Θ1 Θ Δ θ θ1 ζ α Qb C
         Hwf Hflex HbΘ1 HζΘ Hwf1 Hie Hdom Hid HmC HQb HeqθαC.
  assert (Hζθ : Θ ⊢ (msubst_lookup θ α) ≡ᵗ (msubst_lookup ζ α))
    by (eapply a_inc_equiv_compose_id_at; eauto).
  assert (HmζA : mono_ptyp (msubst_lookup ζ α))
    by (eapply a_inc_lookup_mono; exact HζΘ).
  assert (HvisζA : forall X,
             X `in` ftvar_in_ptyp (msubst_lookup ζ α) -> a_binds_tvar X Θ).
  { intros X HX. eapply a_wf_ptyp_ftv_tvarish;
      [ eapply a_inc_lookup_wf; eauto | exact HX ]. }
  eapply consis_precise_core with (C := C); eauto.
  eapply a_tyequiv__trans;
    [ apply a_tyequiv__sym; exact Hζθ | exact HeqθαC ].
Qed.

(** Rules Flex / FlexL: the SUBJECT painting is [α̂], so the competing
    consistency judgment's subject is [θα̂]; its join is the monotype [C]. *)
Lemma consis_precise_via_join : forall Θ0 Θ1 Θ Δ θ θ1 ζ α Qb,
  a_wf_aenv Θ ->
  a_flex_tvar Θ0 α ->
  Θ0 ≤[ θ ] Θ ->
  a_binds_tvar α Θ1 ->
  Θ1 ≤[ ζ ] Θ ->
  a_wf_aenv Θ1 ->
  a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ ->
  α `in` dom θ1 ->
  msubst_lookup θ1 α = ptyp_var_f α ->
  empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl θ (pskl_var_f α))) ≈ Qb ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb).
Proof.
  intros Θ0 Θ1 Θ Δ θ θ1 ζ α Qb
         Hwf Hflex HθΘ HbΘ1 HζΘ Hwf1 Hie Hdom Hid Hjoin.
  assert (Hmθα : mono_ptyp (msubst_lookup θ α))
    by (eapply a_inc_lookup_mono; exact HθΘ).
  replace (msubst_pskl θ (pskl_var_f α))
    with (ptyp_to_pskl (msubst_lookup θ α)) in Hjoin by reflexivity.
  rewrite pskl_to_uskl_ptyp in Hjoin.
  destruct (consis_mono_join Hjoin Hwf (A := msubst_lookup θ α) eq_refl Hmθα)
    as [C [HmC [HQb HeqθαC]]].
  eapply consis_precise_close; eauto.
Qed.

(** Rule FlexR: the INPUT painting is [α̂], so the competing Δ₁-refinement's
    source is [inh(θα̂)]; refine_mono_join reads off the monotype [C]. *)
Lemma consis_precise_via_refine : forall Θ0 Θ1 Θ Δ Δ1 θ θ1 ζ α Qb,
  a_wf_aenv Θ ->
  a_flex_tvar Θ0 α ->
  Θ0 ≤[ θ ] Θ ->
  a_binds_tvar α Θ1 ->
  Θ1 ≤[ ζ ] Θ ->
  a_wf_aenv Θ1 ->
  a_inc_equiv Θ0 θ (msubst_compose ζ θ1) Θ ->
  α `in` dom θ1 ->
  msubst_lookup θ1 α = ptyp_var_f α ->
  ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl θ (pskl_var_f α))) Qb ->
  Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_bskl ζ (bskl_var_f α)) ⊑ (bskl_to_pskl Qb).
Proof.
  intros Θ0 Θ1 Θ Δ Δ1 θ θ1 ζ α Qb
         Hwf Hflex HθΘ HbΘ1 HζΘ Hwf1 Hie Hdom Hid Hrs.
  assert (Hmθα : mono_ptyp (msubst_lookup θ α))
    by (eapply a_inc_lookup_mono; exact HθΘ).
  apply ad_refine_syn_f_forget in Hrs.
  replace (msubst_pskl θ (pskl_var_f α))
    with (ptyp_to_pskl (msubst_lookup θ α)) in Hrs by reflexivity.
  rewrite (ptyp_to_bskl_inh_syn_eq Hmθα) in Hrs.
  destruct (refine_mono_join Hrs Hwf (B := msubst_lookup θ α) eq_refl Hmθα)
    as [C [HmC [HQb HeqθαC]]].
  eapply consis_precise_close; eauto.
Qed.
