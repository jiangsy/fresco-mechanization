(* ===================================================================== *)
(*  COMPLETENESS of consistency / unification / assignment                *)
(*  (thm:complete-consistency; paper proof: consistency-proofs.tex        *)
(*  :2225-3167 "Completeness of Consistency", all three parts).           *)
(*                                                                        *)
(*  The paper proceeds "by mutual induction for the three parts":         *)
(*    part 1 (consistency)  — case analysis on the last rule of the       *)
(*      declarative join derivation, with the special cases peeled first  *)
(*      (:2566-2580): P₀ = ◇ → GhostR; P₀ = ⊤◇.P₀' with P guarded →       *)
(*      UnivGhostR; P or P₀ flexible → parts 2/3.                          *)
(*    part 2 (unification)  — walk of the context Θ₀.                      *)
(*    part 3 (assignment)   — walk of the context pair Θ₀ ∣ Ξ.             *)
(*                                                                        *)
(*  [paper-gap] The paper's three stated induction subjects do NOT        *)
(*  combine into a well-founded order (docs/DESIGN-completeness-          *)
(*  measure.md §3): the back-edges Flex-Flex-Assign / Assign-Assign hand  *)
(*  part 1 a declarative derivation that can be strictly LARGER than the  *)
(*  caller's, and UnivGhostR recurses with the SAME one.  The repaired    *)
(*  measure (design doc §4, infrastructure green in prop_consis_exist.v)  *)
(*                                                                        *)
(*      μ = (V, n, t, k)   lexicographic on ℕ⁴                            *)
(*                                                                        *)
(*  runs on V = the size of the node's two skeletons AS THE SOLUTION      *)
(*  SEES THEM (⇓ˢ[Θ] ∘ θ): V strictly decreases on every consistency-      *)
(*  internal edge, is exactly constant on every cross/back-edge — where   *)
(*  n = |Θ₀| (resp. |Ξ|+|Θ₀|) then strictly decreases; t breaks the       *)
(*  consis→unify/assign tie; k breaks Assign-Depend.  All 21 edges are    *)
(*  verified in the design doc §5.                                        *)
(*                                                                        *)
(*  The statement is the paper's FUSED one (:2246-2255): existence of the *)
(*  algorithmic derivation TOGETHER WITH the factoring (ζ, a_inc_equiv)   *)
(*  and — for consistency — the PRECISION of the output (⊑ against the    *)
(*  competing solution's join target), on the AUGMENTED problem           *)
(*  (Δ₁;Δ₂;Ψ;Θ₀;P₀;S) of :2230-2242.  WIP flagship — honest admits on     *)
(*  unfinished (true) cases.                                              *)
(* ===================================================================== *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_precise_recover.
Require Import src.frost.algo.prop_consis_exist.
Require Import src.frost.algo.prop_consis_rename.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  The three node measures                                           *)
(* ===================================================================== *)

Definition mu_consis (Θ : aenv) (ρ : metasubst) (P0 P : pskl)
    (Θ0 : aenv) : mu_ty :=
  (V_consis Θ ρ P0 P, (length Θ0, (1, 0))).

Definition mu_unify (Θ : aenv) (ρ : metasubst) (α β : atom)
    (Θ0 : aenv) : mu_ty :=
  (V_unify Θ ρ α β, (length Θ0, (0, 0))).

Definition mu_assign (Θ : aenv) (ρ : metasubst) (α : atom) (P : pskl)
    (Ξ Θ0 : aenv) : mu_ty :=
  (V_assign Θ ρ α P, (length Ξ + length Θ0, (0, length Θ0))).

(* ===================================================================== *)
(*  §1b  HYGIENIC PRECISION                                               *)
(*                                                                        *)
(*  The paper's precision [⊑] carries an implicit hole-fill discipline:   *)
(*  fills never mention the ∀-variables in scope (the same EXTERNAL       *)
(*  side-condition family as wf; without it the C-ForallInh cofinite      *)
(*  precision reassembly is unprovable — the [__hole] rule demands the    *)
(*  fill wf at [⨟ ∅], so a fill mentioning the freshly bound variable     *)
(*  kills every renamed instance).  We therefore state the completeness   *)
(*  precision in the hygiene-carrying [_f] form at [F := Δ1 ∪ Δ2] —       *)
(*  exactly the sets the GIVEN refinements [Hrs]/[Hrp] already police —   *)
(*  and recover the paper's plain form by [ad_refine_syn_f_forget].       *)
(* ===================================================================== *)

Definition ad_precise_f (F : atoms) (Θ : aenv) (Δ : atoms)
    (P Q : pskl) : Prop :=
  ad_refine_syn_f F Θ Δ (pskl_to_bskl_inh P) (pskl_to_bskl_inh Q).

Lemma ad_precise_f_forget : forall F Θ Δ P Q,
  ad_precise_f F Θ Δ P Q -> Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ Q.
Proof.
  intros * H. apply ad_refine_syn_f_forget in H. exact H.
Qed.

(** Hole-free skeletons: the [__hole] rule can never fire on them, so a
    plain refinement lifts to the [_f] form at ANY [F]. *)
Fixpoint bskl_no_hole (Q : bskl) : Prop :=
  match Q with
  | bskl_unit => True
  | bskl_var_b _ => True
  | bskl_var_f _ => True
  | bskl_arrow Q1 Q2 => bskl_no_hole Q1 /\ bskl_no_hole Q2
  | bskl_all_syn Q0 => bskl_no_hole Q0
  | bskl_all_inh Q0 => bskl_no_hole Q0
  | bskl_hole => False
  | bskl_tophole Q0 => bskl_no_hole Q0
  end.

Fixpoint pskl_no_hole (P : pskl) : Prop :=
  match P with
  | pskl_unit => True
  | pskl_var_b _ => True
  | pskl_var_f _ => True
  | pskl_arrow P1 P2 => pskl_no_hole P1 /\ pskl_no_hole P2
  | pskl_all_syn P0 => pskl_no_hole P0
  | pskl_hole => False
  | pskl_tophole P0 => pskl_no_hole P0
  end.

Lemma bskl_no_hole_open_rec : forall Q X k,
  bskl_no_hole Q ->
  bskl_no_hole (open_bskl_wrt_bskl_rec k (bskl_var_f X) Q).
Proof.
  induction Q; simpl; intros X k Hnh; try contradiction; try exact I;
    try solve [ apply IHQ; assumption ];
    try solve [ destruct Hnh; split;
                [ apply IHQ1 | apply IHQ2 ]; assumption ].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; exact I.
Qed.

Lemma bskl_no_hole_open : forall Q X,
  bskl_no_hole Q ->
  bskl_no_hole (open_bskl_wrt_bskl Q (bskl_var_f X)).
Proof. intros. apply bskl_no_hole_open_rec. assumption. Qed.

Lemma ptyp_to_pskl_no_hole : forall A, pskl_no_hole (ptyp_to_pskl A).
Proof. induction A; simpl; tauto. Qed.

Lemma pskl_to_bskl_syn_no_hole : forall P,
  pskl_no_hole P -> bskl_no_hole (pskl_to_bskl_syn P).
Proof. induction P; simpl; tauto. Qed.

Lemma pskl_to_bskl_inh_no_hole : forall P,
  pskl_no_hole P -> bskl_no_hole (pskl_to_bskl_inh P).
Proof. induction P; simpl; tauto. Qed.

Lemma bskl_to_pskl_no_hole : forall Q,
  bskl_no_hole Q -> pskl_no_hole (bskl_to_pskl Q).
Proof. induction Q; simpl; tauto. Qed.

Lemma ptyp_to_bskl_syn_no_hole : forall A,
  bskl_no_hole (ptyp_to_bskl_syn A).
Proof.
  intros. unfold ptyp_to_bskl_syn.
  apply pskl_to_bskl_syn_no_hole, ptyp_to_pskl_no_hole.
Qed.

Lemma msubst_bskl_no_hole : forall ζ Q,
  bskl_no_hole Q -> bskl_no_hole (msubst_bskl ζ Q).
Proof.
  intros ζ Q; induction Q; simpl; intros Hnh; try tauto.
  apply ptyp_to_bskl_syn_no_hole.
Qed.

Lemma ad_refine_syn_f_of_plain_no_hole : forall Θ Δ Q P,
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P ->
  bskl_no_hole Q ->
  forall F, ad_refine_syn_f F Θ Δ Q P.
Proof.
  intros * H; induction H; intros Hnh F; simpl in Hnh.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - destruct Hnh. apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros X HX.
    apply H0; [ exact HX | apply bskl_no_hole_open; assumption ].
  - destruct Hnh.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L). intros X HX.
    apply H0; [ exact HX | exact Hnh ].
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; [ eassumption | ].
    apply IHad_refine_syn. apply ptyp_to_bskl_syn_no_hole.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    apply IHad_refine_syn. exact Hnh.
Qed.

Lemma ftvar_in_pskl_bskl_to_pskl : forall Q,
  ftvar_in_pskl (bskl_to_pskl Q) [=] ftvar_in_bskl Q.
Proof. induction Q; simpl; fsetdec. Qed.

(** F-extension along ftv-avoidance of the TARGET: every hole fill is a
    target subterm, so new [F]-atoms that avoid the target's free names —
    and every definition of the context (the [flex_r] unfolding can route
    the target through a definition) — cannot show up in a fill. *)
Lemma ad_refine_syn_f_fextend_ftv : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  forall F',
  (forall γ, γ `in` F' -> γ `in` F \/
     (γ `notin` ftvar_in_bskl P /\
      (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
         γ `notin` ftvar_in_ptyp τ))) ->
  ad_refine_syn_f F' Θ Δ Q P.
Proof.
  intros * H; induction H; intros F' Hcond; simpl in *.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - apply ad_refine_syn_f__arrow.
    + apply IHad_refine_syn_f1. intros γ Hγ.
      destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
        [ left; exact HinF | right; split; [ | exact Hd ] ].
      clear - Hf. fsetdec.
    + apply IHad_refine_syn_f2. intros γ Hγ.
      destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
        [ left; exact HinF | right; split; [ | exact Hd ] ].
      clear - Hf. fsetdec.
  - apply ad_refine_syn_f__all with (L := L `union` F').
    intros X HX.
    apply H0; [ clear - HX; fsetdec | ].
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
      [ left; exact HinF | right; split; [ | exact Hd ] ].
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                  P (bskl_var_f X)) as Hup.
    simpl in Hup.
    assert (γ <> X) by (clear - HX Hγ; fsetdec).
    clear - Hf Hup H1. fsetdec.
  - apply ad_refine_syn_f__hole; [ | assumption ].
    apply inter_empty_pointwise. intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]].
    + intro Hc.
      assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl P))
        by (apply AtomSetImpl.inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + rewrite ftvar_in_bskl_syn in Hf. exact Hf.
  - apply ad_refine_syn_f__tophole_remove. apply IHad_refine_syn_f.
    exact Hcond.
  - apply ad_refine_syn_f__tophole_fill with (L := L `union` F').
    intros X HX.
    apply H0; [ clear - HX; fsetdec | ].
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
      [ left; exact HinF | right ].
    split.
    + pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper
                    P (bskl_var_f X)) as Hup.
      simpl in Hup.
      assert (γ <> X) by (clear - HX Hγ; fsetdec).
      clear - Hf Hup H1. fsetdec.
    + intros β τ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
        [ discriminate | exact (Hd β τ Hb') ].
  - apply ad_refine_syn_f__tophole_keep; [ assumption | ].
    apply IHad_refine_syn_f.
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
      [ left; exact HinF | right; split; [ | exact Hd ] ].
    clear - Hf. fsetdec.
  - eapply ad_refine_syn_f__flex_l; [ eassumption | ].
    apply IHad_refine_syn_f. exact Hcond.
  - eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    apply IHad_refine_syn_f.
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | [Hf Hd]];
      [ left; exact HinF | right; split; [ | exact Hd ] ].
    rewrite ftvar_in_bskl_ptyp_syn. exact (Hd _ _ H).
Qed.

(** A hole-source Δ2-refinement polices its WHOLE target against rigid
    [F]-atoms: the [__hole] rule checks the fill (= the target) directly,
    and the only other applicable rule, [__flex_r], routes the target
    through a DEFINED (hence non-rigid) variable. *)
Lemma ad_refine_pskl_f_hole_src_target_ftv : forall F Θ Δ Qt,
  ad_refine_pskl_f F Θ Δ pskl_hole Qt ->
  a_wf_aenv Θ ->
  forall γ, γ `in` F -> binds γ abind_tvar Θ ->
  γ `notin` ftvar_in_pskl Qt.
Proof.
  intros * H.
  remember pskl_hole as S eqn:HeqS.
  induction H; intros Hwf γ HγF Hbγ; try discriminate HeqS.
  - (* __hole : the fill is the target *)
    intro Hc.
    assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl Q))
      by (apply AtomSetImpl.inter_3; assumption).
    rewrite H in Hin. clear - Hin. fsetdec.
  - (* __flex_r : target is a defined flexible, not the rigid γ *)
    simpl. intro Hc.
    assert (Heqγ : γ = α) by (clear - Hc; fsetdec). subst α.
    pose proof (binds_unique _ _ _ _ _ H Hbγ (a_wf_aenv_uniq Hwf)) as Hcon.
    discriminate.
Qed.

(** The syn-side twin: a hole-source Δ1-refinement polices its whole
    target against rigid [F]-atoms. *)
Lemma ad_refine_syn_f_hole_src_target_ftv : forall F Θ Δ Qt,
  ad_refine_syn_f F Θ Δ bskl_hole Qt ->
  a_wf_aenv Θ ->
  forall γ, γ `in` F -> binds γ abind_tvar Θ ->
  γ `notin` ftvar_in_bskl Qt.
Proof.
  intros * H.
  remember bskl_hole as S eqn:HeqS.
  induction H; intros Hwf γ HγF Hbγ; try discriminate HeqS.
  - (* __hole : the fill is the target *)
    rewrite ftvar_in_bskl_syn.
    intro Hc.
    assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl P))
      by (apply AtomSetImpl.inter_3; assumption).
    rewrite H in Hin. clear - Hin. fsetdec.
  - (* __flex_r : target is a defined flexible, not the rigid γ *)
    simpl. intro Hc.
    assert (Heqγ : γ = α) by (clear - Hc; fsetdec). subst α.
    pose proof (binds_unique _ _ _ _ _ H Hbγ (a_wf_aenv_uniq Hwf)) as Hcon.
    discriminate.
Qed.

(* ===================================================================== *)
(*  §1c  ∀-case transports: weakening / F-extension / Δ↔context moves     *)
(* ===================================================================== *)

(** Free variables of a wf skeleton are scoped by its Δ and context. *)
Lemma ad_wf_pskl_ftv_dom : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  ftvar_in_pskl P [<=] (Δ `union` dom Θ).
Proof.
  intros * H; induction H; simpl; try solve [ clear; fsetdec ].
  - (* var *)
    destruct H as [HΔ | Hbt]; [ clear - HΔ; fsetdec | ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]]; apply binds_In in Hb;
      clear - Hb; fsetdec.
  - (* arrow *) clear - IHad_wf_pskl1 IHad_wf_pskl2. fsetdec.
  - (* all *)
    pick fresh X for (L `union` ftvar_in_pskl P `union` Δ
                        `union` dom Θ).
    assert (HXL : X `notin` L) by (clear - Fr; fsetdec).
    pose proof (H0 X HXL) as Hsub.
    intros Z HZ.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower
                  P (pskl_var_f X)) as Hlo.
    assert (HZ' : Z `in` (add X Δ `union` dom Θ))
      by (apply Hsub; clear - HZ Hlo; fsetdec).
    assert (Hne : Z <> X) by (clear - HZ Fr; fsetdec).
    clear - HZ' Hne. fsetdec.
  - (* tophole *) clear - IHad_wf_pskl. fsetdec.
Qed.

(** Context weakening (binds-monotone) for the hygienic refinements. *)
Lemma ad_refine_syn_f_weaken_ctx : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  forall Θ', (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  ad_refine_syn_f F Θ' Δ Q P.
Proof.
  intros * H; induction H; intros Θ' Hmon.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Hbt]; [ left; exact HΔ | right ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros X HX. auto.
  - apply ad_refine_syn_f__hole; [ exact H | ].
    eapply ad_wf_pskl_weaken; eassumption.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L). intros X HX.
    apply H0; [ exact HX | ].
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
      [ subst; unfold binds; left; reflexivity
      | apply binds_cons_3; apply Hmon; exact Hb' ].
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; [ apply Hmon; eassumption | auto ].
  - eapply ad_refine_syn_f__flex_r; [ apply Hmon; eassumption | auto ].
Qed.

Lemma ad_refine_pskl_f_weaken_ctx : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  forall Θ', (forall x (b : abind), binds x b Θ -> binds x b Θ') ->
  ad_refine_pskl_f F Θ' Δ P Q.
Proof.
  intros * H; induction H; intros Θ' Hmon.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var.
    destruct H as [HΔ | Hbt]; [ left; exact HΔ | right ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ]; apply Hmon; exact Hb.
  - apply ad_refine_pskl_f__arrow; auto.
  - apply ad_refine_pskl_f__all with (L := L). intros X HX. auto.
  - apply ad_refine_pskl_f__hole; [ exact H | ].
    eapply ad_wf_pskl_weaken; eassumption.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - apply ad_refine_pskl_f__tophole_fill with (L := L). intros X HX.
    apply H0; [ exact HX | ].
    intros x b Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
      [ subst; unfold binds; left; reflexivity
      | apply binds_cons_3; apply Hmon; exact Hb' ].
  - apply ad_refine_pskl_f__tophole_keep; auto.
  - eapply ad_refine_pskl_f__flex_l; [ apply Hmon; eassumption | auto ].
  - eapply ad_refine_pskl_f__flex_r; [ apply Hmon; eassumption | auto ].
Qed.

(** F-extension by names outside the context: hole fills are wf at their
    local context, so new [F]-atoms outside every reachable context's
    domain never collide with a fill. *)
Lemma ad_refine_syn_f_fextend_dom : forall F Θ Δ Q P,
  ad_refine_syn_f F Θ Δ Q P ->
  forall F', (forall γ, γ `in` F' -> γ `in` F \/ γ `notin` dom Θ) ->
  ad_refine_syn_f F' Θ Δ Q P.
Proof.
  intros * H; induction H; intros F' Hcond.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var; assumption.
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros X HX. auto.
  - apply ad_refine_syn_f__hole; [ | exact H0 ].
    apply inter_empty_pointwise. intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | Hnd].
    + intro Hc.
      assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl P))
        by (apply AtomSetImpl.inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + pose proof (ad_wf_pskl_ftv_dom H0) as Hsc.
      clear - Hnd Hsc. fsetdec.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with (L := L `union` F').
    intros X HX.
    apply H0; [ clear - HX; fsetdec | ].
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | Hnd]; [ left; exact HinF | right ].
    simpl dom.
    assert (γ <> X) by (clear - HX Hγ; fsetdec).
    clear - Hnd H1. fsetdec.
  - apply ad_refine_syn_f__tophole_keep; auto.
  - eapply ad_refine_syn_f__flex_l; [ eassumption | auto ].
  - eapply ad_refine_syn_f__flex_r; [ eassumption | auto ].
Qed.

Lemma ad_refine_pskl_f_fextend_dom : forall F Θ Δ P Q,
  ad_refine_pskl_f F Θ Δ P Q ->
  forall F', (forall γ, γ `in` F' -> γ `in` F \/ γ `notin` dom Θ) ->
  ad_refine_pskl_f F' Θ Δ P Q.
Proof.
  intros * H; induction H; intros F' Hcond.
  - apply ad_refine_pskl_f__unit.
  - apply ad_refine_pskl_f__var; assumption.
  - apply ad_refine_pskl_f__arrow; auto.
  - apply ad_refine_pskl_f__all with (L := L). intros X HX. auto.
  - apply ad_refine_pskl_f__hole; [ | exact H0 ].
    apply inter_empty_pointwise. intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | Hnd].
    + intro Hc.
      assert (Hin : γ `in` AtomSetImpl.inter F (ftvar_in_pskl Q))
        by (apply AtomSetImpl.inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec.
    + pose proof (ad_wf_pskl_ftv_dom H0) as Hsc.
      clear - Hnd Hsc. fsetdec.
  - apply ad_refine_pskl_f__tophole_remove; auto.
  - apply ad_refine_pskl_f__tophole_fill with (L := L `union` F').
    intros X HX.
    apply H0; [ clear - HX; fsetdec | ].
    intros γ Hγ.
    destruct (Hcond γ Hγ) as [HinF | Hnd]; [ left; exact HinF | right ].
    simpl dom.
    assert (γ <> X) by (clear - HX Hγ; fsetdec).
    clear - Hnd H1. fsetdec.
  - apply ad_refine_pskl_f__tophole_keep; auto.
  - eapply ad_refine_pskl_f__flex_l; [ eassumption | auto ].
  - eapply ad_refine_pskl_f__flex_r; [ eassumption | auto ].
Qed.

(** Moving a Δ-variable of a wf skeleton into the context as a rigid. *)
Lemma ad_wf_pskl_delta_to_tvar : forall Θ Δ0 P,
  Θ ⨟ Δ0 ⊢ₚₛᵃ P ->
  forall X Δ, Δ0 [<=] add X Δ ->
  ((X ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros * H; induction H; intros Y Δ' Hsub.
  - apply ad_wf_pskl__unit.
  - destruct H as [HΔ | Hbt].
    + destruct (X == Y) as [-> | Hne].
      * apply ad_wf_pskl__var. right. left.
        unfold binds. left. reflexivity.
      * apply ad_wf_pskl__var. left. clear - HΔ Hsub Hne. fsetdec.
    + apply ad_wf_pskl__var. right.
      apply a_binds_tvar_weaken_cons. exact Hbt.
  - apply ad_wf_pskl__arrow; auto.
  - apply ad_wf_pskl__all with (L := L `union` singleton Y).
    intros Z HZ.
    apply H0; [ clear - HZ; fsetdec | clear - Hsub HZ; fsetdec ].
  - apply ad_wf_pskl__hole.
  - apply ad_wf_pskl__tophole; [ exact H | ].
    apply IHad_wf_pskl. clear. fsetdec.
Qed.

(** A guarded source never refines to an inherited quantifier (the mirror
    of [ad_refine_syn_f_all_inh_guarded_absurd]): the rules with an
    [all_inh] target need an [all_inh] source or a defined-flexible whose
    monotype unfolding is guarded again. *)
Lemma ad_refine_syn_f_guarded_src_all_inh_absurd : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ Q (bskl_all_inh R) ->
  guarded_bskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (bskl_all_inh R) as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT.
  - (* __all : the source is an inherited quantifier, not guarded *)
    inversion Hg.
  - (* __hole : a syn painting is never an inherited quantifier *)
    destruct P; simpl in HeqT; discriminate.
  - (* __tophole_remove : a ⊤◇ source is not guarded *)
    inversion Hg.
  - (* __flex_l : unfold to the (guarded) monotype *)
    apply IHHr; [ exact Hwf | exact HeqT | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** Mirror: a guarded source never refines to a ∀-syn target either
    (that target only arises by [tophole_fill], whose source is a ⊤◇). *)
Lemma ad_refine_syn_f_guarded_src_all_syn_absurd : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ Q (bskl_all_syn R) ->
  guarded_bskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (bskl_all_syn R) as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT;
    try solve [ inversion Hg ].
  apply IHHr; [ exact Hwf | exact HeqT | ].
  apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
  eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** The pskl-side mirror. *)
Lemma ad_refine_pskl_f_guarded_src_all_syn_absurd : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_pskl_f F Θ Δ Q (pskl_all_syn R) ->
  guarded_pskl Q ->
  False.
Proof.
  intros * Hwf Hr.
  remember (pskl_all_syn R) as T eqn:HeqT.
  induction Hr; intros Hg; try discriminate HeqT;
    try solve [ inversion Hg ].
  apply IHHr; [ exact Hwf | exact HeqT | ].
  apply mono_ptyp_to_pskl_guarded.
  eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** Moving the rigid mid entry into the Δ-slot of a HYGIENIC refinement
    ([α ∈ F] guarantees no fill mentions it, which is exactly what lets
    the fills' wf strengthen past the removed entry). *)
Lemma ad_refine_syn_f_ctx_to_delta : forall F Θfull Δ Q P,
  ad_refine_syn_f F Θfull Δ Q P ->
  forall Θ1 α Θ0, Θfull = Θ1 ++ (α ~ abind_tvar) ++ Θ0 ->
  α `in` F ->
  uniq Θfull ->
  ad_refine_syn_f F (Θ1 ++ Θ0) (add α Δ) Q P.
Proof.
  intros F Θfull Δ Q P H; induction H;
    intros Θ1 α0 Θt HeqΘ HαF Hu; subst Θ.
  - apply ad_refine_syn_f__unit.
  - apply ad_refine_syn_f__var.
    destruct H as [HΔ | Hbt]; [ left; clear - HΔ; fsetdec | ].
    destruct (X == α0) as [-> | Hne];
      [ left; clear; fsetdec | right ].
    eapply a_binds_tvar_strip_mid;
      [ exact Hbt
      | intro Hc; inversion Hc; congruence
      | intro Hc; inversion Hc
      | intros τ0 Hc; inversion Hc ].
  - apply ad_refine_syn_f__arrow; auto.
  - apply ad_refine_syn_f__all with (L := L). intros X HX.
    eapply ad_refine_syn_f_delta_mono;
      [ apply (H0 X HX Θ1 α0 Θt eq_refl HαF Hu) | clear; fsetdec ].
  - apply ad_refine_syn_f__hole; [ exact H | ].
    assert (HαP : α0 `notin` ftvar_in_pskl P).
    { intro Hc.
      assert (Hin : α0 `in` AtomSetImpl.inter F (ftvar_in_pskl P))
        by (apply AtomSetImpl.inter_3; assumption).
      rewrite H in Hin. clear - Hin. fsetdec. }
    pose proof (ad_wf_pskl_ftv_dom H0) as Hsc.
    eapply ad_wf_pskl_strengthen;
      [ exact H0 | exact Hu
      | intros x Hx; exfalso; clear - Hx; fsetdec
      | intros x b Hb; apply binds_weaken; exact Hb
      | ].
    intros X HX. right.
    assert (Hd : X `in` dom (Θ1 ++ (α0 ~ abind_tvar) ++ Θt))
      by (clear - Hsc HX; fsetdec).
    assert (Hne : X <> α0) by (intro; subst; contradiction).
    repeat rewrite dom_app in *. simpl dom in Hd.
    clear - Hd Hne. fsetdec.
  - apply ad_refine_syn_f__tophole_remove; auto.
  - apply ad_refine_syn_f__tophole_fill with
      (L := L `union` dom (Θ1 ++ (α0 ~ abind_tvar) ++ Θt)).
    intros X HX.
    apply (H0 X ltac:(clear - HX; fsetdec)
             ((X ~ abind_tvar) ++ Θ1) α0 Θt eq_refl HαF).
    apply uniq_push; [ exact Hu | clear - HX; fsetdec ].
  - apply ad_refine_syn_f__tophole_keep; auto.
  - assert (Hne : α <> α0).
    { intros ->.
      assert (Hbα0 : binds α0 abind_tvar
                       (Θ1 ++ (α0 ~ abind_tvar) ++ Θt))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbα0 Hu) as Hcon.
      discriminate. }
    eapply ad_refine_syn_f__flex_l;
      [ eapply binds_remove_mid; [ exact H | exact Hne ] | auto ].
  - assert (Hne : α <> α0).
    { intros ->.
      assert (Hbα0 : binds α0 abind_tvar
                       (Θ1 ++ (α0 ~ abind_tvar) ++ Θt))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbα0 Hu) as Hcon.
      discriminate. }
    eapply ad_refine_syn_f__flex_r;
      [ eapply binds_remove_mid; [ exact H | exact Hne ] | auto ].
Qed.

(* ===================================================================== *)
(*  §1d  Rename-vs-embedding/metasubstitution commutations               *)
(* ===================================================================== *)

Lemma pskl_to_bskl_inh_subst_var : forall X α P,
  subst_bskl_in_bskl (bskl_var_f X) α (pskl_to_bskl_inh P)
  = pskl_to_bskl_inh (subst_pskl_in_pskl (pskl_var_f X) α P).
Proof.
  intros X α P; induction P; simpl;
    try solve [ reflexivity
              | rewrite IHP; reflexivity
              | rewrite IHP1, IHP2; reflexivity ].
  match goal with |- context [ if ?t then _ else _ ] => destruct t end;
    reflexivity.
Qed.

Lemma bskl_to_pskl_subst_var : forall X α Q,
  subst_pskl_in_pskl (pskl_var_f X) α (bskl_to_pskl Q)
  = bskl_to_pskl (subst_bskl_in_bskl (bskl_var_f X) α Q).
Proof.
  intros X α Q; induction Q; simpl;
    try solve [ reflexivity
              | rewrite IHQ; reflexivity
              | rewrite IHQ1, IHQ2; reflexivity ].
  match goal with |- context [ if ?t then _ else _ ] => destruct t end;
    reflexivity.
Qed.

Lemma msubst_lookup_in_or : forall (ζ : metasubst) (β : atom),
  In (β, msubst_lookup ζ β) ζ \/
  (β `notin` dom ζ /\ msubst_lookup ζ β = ptyp_var_f β).
Proof.
  induction ζ as [ | [γ τ] ζ' IH ]; intros β; simpl.
  - right. split; [ fsetdec | reflexivity ].
  - destruct (β == γ) as [-> | Hne].
    + left. left. reflexivity.
    + destruct (IH β) as [Hin | [Hni Heq]];
        [ left; right; exact Hin
        | right; split; [ clear - Hni Hne; fsetdec | exact Heq ] ].
Qed.

(** Renaming a rigid [α ↦ X] commutes with a metasubstitution that does
    not touch either name (its images avoid [α]; both are off its
    domain). *)
Lemma msubst_pskl_subst_var : forall ζ α X P,
  α `notin` dom ζ ->
  X `notin` dom ζ ->
  (forall γ τ, In (γ, τ) ζ -> α `notin` ftvar_in_ptyp τ) ->
  subst_pskl_in_pskl (pskl_var_f X) α (msubst_pskl ζ P)
  = msubst_pskl ζ (subst_pskl_in_pskl (pskl_var_f X) α P).
Proof.
  intros ζ α X P Hαd HXd Him;
    induction P as [ | n | β | Pa IHa Pb IHb | Pb IHb | | Pt IHt ]; simpl;
    try solve [ reflexivity
              | rewrite IHb; reflexivity
              | rewrite IHt; reflexivity
              | rewrite IHa, IHb; reflexivity ].
  (* var *)
  match goal with |- context [ if ?t then _ else _ ] =>
    destruct t as [-> | Hne] end.
  - (* the renamed variable: off the domain on both sides *)
    rewrite (msubst_lookup_notin ζ Hαd). simpl.
    match goal with |- context [ if ?t then _ else _ ] =>
      destruct t as [_ | Hc]; [ | congruence ] end.
    cbn [msubst_pskl].
    rewrite (msubst_lookup_notin ζ HXd). reflexivity.
  - (* any other variable: the image is α-free *)
    cbn [msubst_pskl].
    destruct (msubst_lookup_in_or ζ β) as [Hin | [Hni Heq]].
    + apply subst_pskl_in_pskl_fresh_eq.
      pose proof (Him _ _ Hin) as Hfr.
      pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup ζ β)) as Hfe.
      clear - Hfr Hfe. fsetdec.
    + rewrite Heq. simpl.
      match goal with |- context [ if ?t then _ else _ ] =>
        destruct t as [Hc | _]; [ congruence | reflexivity ] end.
Qed.

(** Images of an information increase are scoped by the target. *)
Lemma a_inc_images_ftv_dom : forall Θ0 ζ Θ,
  Θ0 ≤[ ζ ] Θ ->
  forall γ τ, In (γ, τ) ζ -> ftvar_in_ptyp τ [<=] dom Θ.
Proof.
  intros Θ0 ζ Θ H; induction H; intros γ0 τ0 Hin.
  - inversion Hin.
  - destruct Hin as [Heq | Hin];
      [ inversion Heq; subst; apply a_wf_ptyp_ftv_dom; assumption
      | eapply IHa_inc; exact Hin ].
  - destruct Hin as [Heq | Hin];
      [ inversion Heq; subst; apply a_wf_ptyp_ftv_dom; assumption
      | eapply IHa_inc; exact Hin ].
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros Z HZ. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub Z HZ). clear - H2. fsetdec.
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros Z HZ. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub Z HZ). clear - H2. fsetdec.
  - pose proof (IHa_inc _ _ Hin) as Hsub.
    intros Z HZ. repeat rewrite dom_app. simpl dom.
    pose proof (Hsub Z HZ). clear - H1. fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  The three completeness statements AT A MEASURE                    *)
(*                                                                        *)
(*  Hypotheses mirror the AUGMENTED problem/solution of consistency-      *)
(*  proofs.tex:2230-2242 exactly as [consis_optimal_post] does (the       *)
(*  competing-solution shape of the green soundness bundle); the          *)
(*  conclusion is the fused existence+optimality of :2246-2255, with the  *)
(*  algorithm's own id-witness quantified as in [a_consis_optimal].       *)
(* ===================================================================== *)

Definition consis_complete_at (m : mu_ty) : Prop :=
  forall F Δ1 Δ2 Θ0 P0 P ρ Θ Ψ Qb,
    m = mu_consis Θ ρ P0 P Θ0 ->
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    Ψ ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis F Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           ad_precise_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb)).

Definition unify_complete_at (m : mu_ty) : Prop :=
  forall F Θ0 α β ρ Θ,
    m = mu_unify Θ ρ α β Θ0 ->
    a_wf_aenv Θ0 ->
    a_flex_tvar Θ0 α ->
    a_flex_tvar Θ0 β ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    Θ ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β) ->
    exists Θ1,
      Θ0 ⊲[ F ] α ≈ᵘ β ⊣ Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ).

Definition assign_complete_at (m : mu_ty) : Prop :=
  forall F Θ0 Ξ α P ρ Θ,
    m = mu_assign Θ ρ α P Ξ Θ0 ->
    a_decls Ξ ->
    a_wf_aenv (Ξ ++ Θ0) ->
    a_flex_tvar Θ0 α ->
    (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P ->
    a_non_flex (Ξ ++ Θ0) P ->
    dom Ξ [<=] ftvar_in_pskl P ->
    (Ξ ++ Θ0) ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P))
                 ≈ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup ρ α))) ->
    exists Θ1,
      Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> (Ξ ++ Θ0) ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv (Ξ ++ Θ0) ρ (msubst_compose ζ ρ1) Θ).

Definition complete_at (m : mu_ty) : Prop :=
  consis_complete_at m /\ unify_complete_at m /\ assign_complete_at m.

(* ===================================================================== *)
(*  §2b  Small shared helpers (measure intro, head-stripping, embeddings) *)
(* ===================================================================== *)

(** Componentwise introduction of the lexicographic order. *)
Lemma mu_lt_intro : forall (V' V n' n t' t k' k : nat),
  (V' < V \/
   (V' = V /\ (n' < n \/ (n' = n /\ (t' < t \/ (t' = t /\ k' < k)))))) ->
  mu_lt (V', (n', (t', k'))) (V, (n, (t, k))).
Proof.
  intros. unfold mu_lt, lex; simpl.
  destruct H as [HV | [-> [Hn | [-> [Ht | [-> Hk]]]]]].
  - left; exact HV.
  - right; split; [ reflexivity | left; exact Hn ].
  - right; split; [ reflexivity | right; split;
      [ reflexivity | left; exact Ht ] ].
  - right; split; [ reflexivity | right; split;
      [ reflexivity | right; split; [ reflexivity | exact Hk ] ] ].
Qed.

(** A hatted variable other than the head is hatted in the tail. *)
Lemma a_flex_tvar_strip_head : forall (γ : atom) b Θ0 δ,
  δ <> γ ->
  a_flex_tvar ((γ ~ b) ++ Θ0) δ ->
  a_flex_tvar Θ0 δ.
Proof.
  intros γ b Θ0 δ Hne [Hb | [τ Hb]];
    apply binds_cons_1 in Hb as [[Heq _] | Hb];
    solve [ exfalso; auto | left; exact Hb | right; exists τ; exact Hb ].
Qed.

(** The [V]-measure of an embedded monotype is its type-level measure. *)
Lemma Vpskl_ptyp_to_pskl : forall Θ θ A,
  Vpskl Θ θ (ptyp_to_pskl A) = Vptyp Θ θ A.
Proof.
  intros. unfold Vpskl, Vptyp.
  rewrite msubst_pskl_ptyp_to_pskl. rewrite msubst_pskl_ptyp_to_pskl.
  apply size_ptyp_to_pskl.
Qed.

(** [Vvar] ignores a target prefix the image cannot mention (the walk cases
    for rigid / term-variable heads truncate the solution target). *)
Lemma Vvar_strengthen_mid : forall Ξ (c : atom) b Θt ρ α,
  uniq (Ξ ++ (c ~ b) ++ Θt) ->
  a_wf_ptyp Θt (msubst_lookup ρ α) ->
  Vvar (Ξ ++ (c ~ b) ++ Θt) ρ α = Vvar Θt ρ α.
Proof.
  intros Ξ c b Θt ρ α Huniq Hwf. unfold Vvar.
  rewrite <- app_assoc in Huniq |- *.
  rewrite (downarrow_app_agree_ptyp _ _ _ Huniq
             (a_wf_ptyp_ftv_dom Hwf)).
  reflexivity.
Qed.

(** A variable outside the metasubstitution's domain keeps its free
    occurrences under it (substitution only adds or preserves them). *)
Lemma msubst_pskl_ftv_keep : forall ρ P X,
  X `notin` dom ρ ->
  X `in` ftvar_in_pskl P ->
  X `in` ftvar_in_pskl (msubst_pskl ρ P).
Proof.
  intros ρ P X Hnd;
    induction P as [ | n | x | P1 IH1 P2 IH2 | Pb IHb | | Pt IHt ];
    simpl; intros Hin; try solve [ fsetdec ].
  (* var_f : the occurrence IS X, whose lookup is itself *)
  assert (Heq : X = x) by (clear - Hin; fsetdec). subst x.
  rewrite (msubst_lookup_notin ρ Hnd). simpl. fsetdec.
Qed.

(** Extending Θ with a fresh rigid entry preserves the three fixed
    hypotheses of the ftv-survival inductions below. *)
Local Ltac ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY :=
  assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
    by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]);
  assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
    by (apply binds_cons_3; exact HbX);
  assert (HdefsY : forall β τ,
            binds β (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
            X `notin` ftvar_in_ptyp τ)
    by (intros β τ Hb;
        apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | exact (Hdefs _ _ Hb) ]).

(** Rigid free variables survive fill-hygienic refinement RIGHT-TO-LEFT:
    a rigid [X] (never mentioned by a Θ-definition) absent from the target
    is absent from the source.  This is the ftv-chase behind Ghost's
    [Δ2 ∩ ftv(P0) = ∅] side condition (and GhostR's mirror). *)
Lemma ad_refine_syn_f_rigid_ftv_rev : forall F Θ Δ Qs Qt X,
  a_wf_aenv Θ ->
  binds X abind_tvar Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
               X `notin` ftvar_in_ptyp τ) ->
  ad_refine_syn_f F Θ Δ Qs Qt ->
  X `notin` ftvar_in_bskl Qt ->
  X `notin` ftvar_in_bskl Qs.
Proof.
  intros F Θ Δ Qs Qt X Hwf HbX Hdefs Hr.
  induction Hr; intros Hout; simpl in *.
  - (* unit *) clear; fsetdec.
  - (* var *) clear - Hout; fsetdec.
  - (* arrow *)
    assert (Hn1 : X `notin` ftvar_in_bskl Q1)
      by (apply IHHr1;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    assert (Hn2 : X `notin` ftvar_in_bskl Q2)
      by (apply IHHr2;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    clear - Hn1 Hn2; fsetdec.
  - (* all (cofinite; Θ unchanged) *)
    pick fresh Y for (L `union` singleton X `union` ftvar_in_bskl P
                        `union` ftvar_in_bskl Q).
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) Hwf HbX Hdefs HnT) as HnS.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* hole *) clear; fsetdec.
  - (* tophole_remove *) exact (IHHr Hwf HbX Hdefs Hout).
  - (* tophole_fill (cofinite; Θ grows by the fresh rigid Y) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_bskl P `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl P (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    simpl in HnS. clear - HnS. fsetdec.
  - (* tophole_keep *) exact (IHHr Hwf HbX Hdefs Hout).
  - (* flex_l : the source is a defined flexible, never the rigid X *)
    assert (Hne : X <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc;
        discriminate. }
    clear - Hne; fsetdec.
  - (* flex_r : unfold the target definition; its ftv avoids X *)
    apply IHHr; [ assumption | assumption | assumption | ].
    rewrite ftvar_in_bskl_ptyp_syn.
    apply (Hdefs _ _ H).
Qed.

(** The mirror on the JOIN: a rigid [X] absent from the join target is
    absent from the (painted) subject.  Drives GhostR's side condition. *)
Lemma ad_pat_consis_rigid_ftv_rev : forall Ψ Θ S Qt X,
  a_wf_aenv Θ ->
  binds X abind_tvar Θ ->
  (forall β τ, binds β (abind_flex_mono_def τ) Θ ->
               X `notin` ftvar_in_ptyp τ) ->
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  X `notin` ftvar_in_bskl Qt ->
  X `notin` ftvar_in_uskl S.
Proof.
  intros Ψ Θ S Qt X Hwf HbX Hdefs Hc.
  induction Hc; intros Hout; simpl in *.
  - (* unit *) clear; fsetdec.
  - (* var *) clear - Hout; fsetdec.
  - (* arrow *)
    assert (Hn1 : X `notin` ftvar_in_uskl R1)
      by (apply IHHc1;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    assert (Hn2 : X `notin` ftvar_in_uskl R2)
      by (apply IHHc2;
          [ assumption | assumption | assumption | clear - Hout; fsetdec ]).
    clear - Hn1 Hn2; fsetdec.
  - (* forall_inh_tagged (cofinite; Θ grows) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_inh_untagged (cofinite; Θ grows) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn_tagged (cofinite; Θ grows) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn (cofinite; Θ grows) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* ghostg *) clear; fsetdec.
  - (* topholeg *) exact (IHHc Hwf HbX Hdefs Hout).
  - (* hole : the subject is the ghost hole, no free variables *)
    clear; fsetdec.
  - (* tophole *) exact (IHHc Hwf HbX Hdefs Hout).
  - (* tophole_inh (cofinite target; Θ grows; subject fixed) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    ftv_rev_extend X Fr Y Θ Hwf HbX Hdefs HwfY HbXY HdefsY.
    assert (HnT : X `notin`
              ftvar_in_bskl (open_bskl_wrt_bskl Q (bskl_var_f Y))).
    { pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup Fr. fsetdec. }
    pose proof (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY HdefsY HnT) as HnS.
    simpl in HnS. clear - HnS. fsetdec.
  - (* tophole_drop *) exact (IHHc Hwf HbX Hdefs Hout).
  - (* flex_l : the subject is a defined flexible, never the rigid X *)
    assert (Hne : X <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc';
        discriminate. }
    clear - Hne; fsetdec.
  - (* flex_r : unfold the join definition; its ftv avoids X *)
    apply IHHc; [ assumption | assumption | assumption | ].
    rewrite ftvar_in_bskl_ptyp_syn.
    apply (Hdefs _ _ H).
Qed.

(** SCOPED variant of the join ftv-survival: the definition side condition
    only holds for definitions REACHABLE from the target's scope [D] (the
    truncated context of the SkipRigid stuck-check).  A rigid [X] outside
    [D] absent from a [D]-scoped target is absent from the subject. *)
Lemma ad_pat_consis_rigid_ftv_rev_scoped : forall Ψ Θ S Qt X D,
  a_wf_aenv Θ ->
  binds X abind_tvar Θ ->
  X `notin` D ->
  (forall γ τ, binds γ (abind_flex_mono_def τ) Θ -> γ `in` D ->
               ftvar_in_ptyp τ [<=] D) ->
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  ftvar_in_bskl Qt [<=] D ->
  X `notin` ftvar_in_uskl S.
Proof.
  intros Ψ Θ S Qt X D Hwf HbX HXD Hdefs Hc.
  revert D HXD Hdefs.
  induction Hc; intros D HXD Hdefs Hout; simpl in *.
  - (* unit *) clear; fsetdec.
  - (* var *) clear - Hout HXD; fsetdec.
  - (* arrow *)
    assert (Hn1 : X `notin` ftvar_in_uskl R1)
      by (apply (IHHc1 Hwf HbX D HXD Hdefs); clear - Hout; fsetdec).
    assert (Hn2 : X `notin` ftvar_in_uskl R2)
      by (apply (IHHc2 Hwf HbX D HXD Hdefs); clear - Hout; fsetdec).
    clear - Hn1 Hn2; fsetdec.
  - (* forall_inh_tagged (cofinite; Θ and D grow by the fresh Y) *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y))).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_inh_untagged *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y))).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn_tagged *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y))).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* forall_syn *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin`
              ftvar_in_uskl (open_uskl_wrt_uskl R (uskl_var_f Y))).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R (uskl_var_f Y))
      as Hlo.
    clear - HnS Hlo. fsetdec.
  - (* ghostg *) clear; fsetdec.
  - (* topholeg *) apply (IHHc Hwf HbX D HXD Hdefs Hout).
  - (* hole *) clear; fsetdec.
  - (* tophole *) apply (IHHc Hwf HbX D HXD Hdefs Hout).
  - (* tophole_inh *)
    pick fresh Y for (L `union` dom Θ `union` singleton X `union` D
                        `union` ftvar_in_uskl R `union` ftvar_in_bskl Q).
    assert (HwfY : a_wf_aenv ((Y ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - Fr; fsetdec | exact Hwf ]).
    assert (HbXY : binds X abind_tvar ((Y ~ abind_tvar) ++ Θ))
      by (apply binds_cons_3; exact HbX).
    assert (HdefsY' : forall γ τ,
              binds γ (abind_flex_mono_def τ) ((Y ~ abind_tvar) ++ Θ) ->
              γ `in` (add Y D) -> ftvar_in_ptyp τ [<=] (add Y D)).
    { intros γ τ Hb HγD.
      apply binds_cons_1 in Hb as [[_ Heqb] | Hb];
        [ discriminate Heqb | ].
      assert (Hγne : γ <> Y).
      { intro Heq; subst γ. apply binds_In in Hb.
        clear - Hb Fr. fsetdec. }
      assert (HγD' : γ `in` D) by (clear - HγD Hγne; fsetdec).
      pose proof (Hdefs _ _ Hb HγD') as Hs. clear - Hs. fsetdec. }
    assert (HnS : X `notin` ftvar_in_uskl (uskl_tophole R)).
    { apply (H0 Y ltac:(clear - Fr; fsetdec) HwfY HbXY (add Y D)
               ltac:(clear - HXD Fr; fsetdec) HdefsY').
      pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q (bskl_var_f Y))
        as Hup.
      simpl in Hup. clear - Hout Hup. fsetdec. }
    simpl in HnS. clear - HnS. fsetdec.
  - (* tophole_drop *) apply (IHHc Hwf HbX D HXD Hdefs Hout).
  - (* flex_l : the subject is a defined flexible, never the rigid X *)
    assert (Hne : X <> α).
    { intro Heq; subst α.
      pose proof (binds_unique _ _ _ _ _ HbX H (a_wf_aenv_uniq Hwf)) as Hc';
        discriminate. }
    clear - Hne; fsetdec.
  - (* flex_r : the defined join is IN [D], so its definition is too *)
    apply (IHHc Hwf HbX D HXD Hdefs).
    rewrite ftvar_in_bskl_ptyp_syn.
    apply (Hdefs _ _ H). clear - Hout. fsetdec.
Qed.

(** Well-formedness of a metasubstitution image: the solution's images are
    wf in the target, rigid occurrences stay put.  Δ-variables must avoid
    the substitution's domain (locally-opened binders are chosen fresh). *)
Lemma ad_wf_pskl_msubst_inc : forall Θ0 ρ Θ Δ P,
  Θ0 ≤[ ρ ] Θ ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ Δ ⊢ₚₛᵃ P ->
  (forall X, X `in` Δ -> X `notin` dom ρ) ->
  Θ ⨟ Δ ⊢ₚₛᵃ (msubst_pskl ρ P).
Proof.
  intros Θ0 ρ Θ Δ P Hinc Hwf0 Hwf; induction Hwf; intros HΔ; simpl.
  - apply ad_wf_pskl__unit.
  - (* var : rigid occurrences stay; flexibles map to wf target types *)
    destruct H as [HXΔ | Hbt].
    + rewrite (msubst_lookup_notin ρ (HΔ _ HXΔ)). simpl.
      apply ad_wf_pskl__var; left; exact HXΔ.
    + apply a_wf_ptyp_to_wf_pskl.
      eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf0 | exact Hbt ].
  - apply ad_wf_pskl__arrow;
      [ apply IHHwf1 | apply IHHwf2 ]; try assumption.
  - (* all : open with a binder fresh from the substitution *)
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; eauto).
    apply ad_wf_pskl__all with (L := L `union` dom ρ).
    intros X HX.
    rewrite <- msubst_pskl_open_lc_local;
      [ | exact Hlcρ | clear - HX; fsetdec ].
    apply H0; [ clear - HX; fsetdec | exact Hinc | exact Hwf0 | ].
    intros Y HY.
    destruct (Y == X) as [-> | Hne].
    + clear - HX; fsetdec.
    + apply HΔ. clear - HY Hne; fsetdec.
  - apply ad_wf_pskl__hole.
  - (* tophole : the body is guarded and closed under Δ = ∅ *)
    apply ad_wf_pskl__tophole.
    + eapply guarded_pskl_msubst_inc; eauto.
    + apply IHHwf; [ exact Hinc | exact Hwf0 | ].
      intros Y HY. exfalso. clear - HY. fsetdec.
Qed.

(** The non-mono RE-INHERIT bridge (the OPT C-GhostR plan,
    prop_consis_complete.v:1752): an uncoloured refinement [A ⊳ B] whose two
    sides are JOINED at the syn painting re-inherits to the coloured
    refinement of the inh paintings.  [Θr] is the refinement context; [Θj]
    the join context, which extends [Θr] by rigid opens only (at the top
    level Θj = Θr).  The wf of [A] supplies guardedness of ⊤◇-bodies, which
    is what forces the join to strip/keep wrappers in lockstep with the
    refinement. *)
Lemma refine_join_reinherit : forall F Θr Δ A B,
  ad_refine_pskl_f F Θr Δ A B ->
  forall Θj,
  a_wf_aenv Θr ->
  a_wf_aenv Θj ->
  (forall x b, binds x b Θr -> binds x b Θj) ->
  Θr ⨟ Δ ⊢ₚₛᵃ A ->
  empty ⨟ Θj ⊨ₛᵃ (pskl_to_uskl A) ≈ (pskl_to_bskl_syn B) ->
  ad_refine_syn_f F Θr Δ (pskl_to_bskl_inh A) (pskl_to_bskl_inh B).
Proof.
  intros F Θr Δ A B Hr.
  induction Hr; intros Θj Hwfr Hwf Hincl HwfA Hj; simpl in Hj |- *.
  - (* unit *) apply ad_refine_syn_f__unit.
  - (* var *) apply ad_refine_syn_f__var; exact H.
  - (* arrow *)
    inversion HwfA; subst.
    inversion Hj; subst.
    apply ad_refine_syn_f__arrow;
      [ eapply IHHr1 | eapply IHHr2 ]; try eassumption;
      (eapply ad_pat_consis_psi_cong; [ eassumption | fsetdec ]).
  - (* all (forall_syn) *)
    inversion HwfA; subst.
    inversion Hj; subst.
    match goal with
    | Hn : forall _, _ -> ad_pat_consis _ _ _ _ |- _ => rename Hn into Hsub
    end.
    match goal with
    | Hn : forall _, _ -> ad_wf_pskl _ _ _ |- _ => rename Hn into Hwfb
    end.
    simpl.
    match type of Hsub with
    | forall _, _ `notin` ?LL -> _ =>
        match type of Hwfb with
        | forall _, _ `notin` ?LW -> _ =>
            apply ad_refine_syn_f__all with
              (L := L `union` LL `union` LW `union` dom Θ `union` dom Θj
                    `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        end
    end.
    intros X HX.
    rewrite <- pskl_to_bskl_inh_open, <- pskl_to_bskl_inh_open.
    apply (H0 X ltac:(clear - HX; fsetdec) ((X ~ abind_tvar) ++ Θj) Hwfr).
    + apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ].
    + intros x b Hb. apply binds_cons_3. apply Hincl; exact Hb.
    + apply Hwfb. clear - HX; fsetdec.
    + rewrite pskl_to_uskl_open_var, pskl_to_bskl_syn_open.
      apply Hsub. clear - HX; fsetdec.
  - (* hole : the join forces the fill to be inh-invariant *)
    pose proof (consis_hole_target_inh Hj) as Hqi.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hqi.
    rewrite Hqi. apply ad_refine_syn_f__hole; [ exact H | exact H0 ].
  - (* tophole_remove : the join strips its subject ⊤◇ in lockstep *)
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    assert (HwfP : Θ ⨟ empty ⊢ₚₛᵃ P) by (inversion HwfA; assumption).
    assert (HwfPΔ : Θ ⨟ Δ ⊢ₚₛᵃ P)
      by (eapply ad_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]).
    apply ad_refine_syn_f__tophole_remove.
    apply (IHHr Θj Hwfr Hwf Hincl HwfPΔ).
    (* the join: ⊤◇⌊P⌋ ≈ syn Q must strip the subject wrapper *)
    inversion Hj; subst.
    + (* __tophole : the target would be a ⊤◇ — but the guarded [P]
         refines to it, contradiction *)
      exfalso.
      match goal with
      | HeqQ : pskl_to_bskl_syn Q = bskl_tophole _ |- _ =>
          destruct Q; simpl in HeqQ; try discriminate
      | HeqQ : bskl_tophole _ = pskl_to_bskl_syn Q |- _ =>
          destruct Q; simpl in HeqQ; try discriminate
      end.
      pose proof (ad_refine_pskl_f_guarded_r Hwfr Hr HgP) as Hbad.
      inversion Hbad.
    + (* __tophole_inh : a syn painting is never an inherited ∀ *)
      exfalso.
      match goal with
      | HeqQ : pskl_to_bskl_syn Q = bskl_all_inh _ |- _ =>
          destruct Q; simpl in HeqQ; discriminate
      | HeqQ : bskl_all_inh _ = pskl_to_bskl_syn Q |- _ =>
          destruct Q; simpl in HeqQ; discriminate
      end.
    + (* __tophole_drop : exactly the stripped join *)
      assumption.
    + (* __flex_r : a defined-flex target is guarded; strip via the
         guarded inversion *)
      match goal with
      | HeqQ : pskl_to_bskl_syn Q = bskl_var_f _ |- _ =>
          destruct Q; simpl in HeqQ; try discriminate;
          inversion HeqQ; subst
      | HeqQ : bskl_var_f _ = pskl_to_bskl_syn Q |- _ =>
          destruct Q; simpl in HeqQ; try discriminate;
          inversion HeqQ; subst
      end.
      eapply ad_pat_consis_tophole_guarded_inv;
        [ exact Hwf | | exact HgP | apply guarded_bskl__var ].
      eapply ad_pat_consis__flex_r; eassumption.
  - (* tophole_fill : VACUOUS — no join matches a ⊤◇ subject against a
       ∀-syn target *)
    exfalso.
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    pick fresh X for (L `union` dom Θ).
    assert (HlcQX : lc_pskl (open_pskl_wrt_pskl Q (pskl_var_f X)))
      by (eapply ad_refine_pskl_f_lc_r; apply H; clear - Fr; fsetdec).
    assert (HlcQ : lc_bskl (pskl_to_bskl_syn (pskl_all_syn Q))).
    { apply pskl_to_bskl_syn_lc.
      apply (lc_pskl_all_syn_exists X). exact HlcQX. }
    inversion Hj; subst.
    (* only __tophole_drop survives the target shape; its stripped subject
       is guarded against a ∀-syn target *)
    match goal with
    | Hdrop : _ ⨟ _ ⊨ₛᵃ (pskl_to_uskl P) ≈ _ |- _ =>
        pose proof (ad_pat_consis_guarded_r Hdrop Hwf eq_refl HgP HlcQ)
          as Hbad
    end.
    inversion Hbad.
  - (* tophole_keep : the join keeps (or cannot drop) the wrapper *)
    assert (HgP : guarded_pskl P) by (inversion HwfA; assumption).
    assert (HwfP : Θ ⨟ empty ⊢ₚₛᵃ P) by (inversion HwfA; assumption).
    assert (HwfPΔ : Θ ⨟ Δ ⊢ₚₛᵃ P)
      by (eapply ad_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]).
    apply ad_refine_syn_f__tophole_keep;
      [ apply guarded_pskl_to_bskl_inh; exact H | ].
    apply (IHHr Θj Hwfr Hwf Hincl HwfPΔ).
    inversion Hj; subst.
    + (* __tophole : both wrappers strip *) assumption.
    + (* __tophole_drop : the guarded stripped subject cannot join a ⊤◇ *)
      exfalso.
      assert (HlcQt : lc_bskl (bskl_tophole (pskl_to_bskl_syn Q))).
      { apply lc_bskl_tophole. apply pskl_to_bskl_syn_lc.
        eapply ad_refine_pskl_f_lc_r; exact Hr. }
      match goal with
      | Hdrop : _ ⨟ _ ⊨ₛᵃ (pskl_to_uskl P) ≈ _ |- _ =>
          pose proof (ad_pat_consis_guarded_r Hdrop Hwf eq_refl HgP HlcQt)
            as Hbad
      end.
      inversion Hbad.
  - (* flex_l : unfold α̂ in the output and in the join SUBJECT *)
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact H ]).
    apply ad_refine_syn_f__flex_l with (τ := τ); [ exact H | ].
    rewrite <- (mono_inh_eq_syn Hmτ).
    eapply IHHr; try eassumption.
    + apply a_wf_ptyp_to_wf_pskl.
      eapply a_wf_aenv_binds_def_wf; [ exact Hwfr | exact H ].
    + rewrite pskl_to_uskl_ptyp.
      eapply consis_unfold_def_subject;
        [ exact Hj | exact Hwf | reflexivity | apply Hincl; exact H ].
  - (* flex_r : unfold α̂ in the output and in the join TARGET *)
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwfr | exact H ]).
    apply ad_refine_syn_f__flex_r with (τ := τ); [ exact H | ].
    rewrite <- (mono_inh_eq_syn Hmτ).
    eapply IHHr; try eassumption.
    unfold ptyp_to_bskl_syn.
    eapply consis_unfold_def_join;
      [ exact Hj | exact Hwf | reflexivity | apply Hincl; exact H ].
Qed.

(* --------------------------------------------------------------------- *)
(*  The ≡ˢ-SUBJECT TRANSPORT of the join (general skeletons).             *)
(*                                                                        *)
(*  This is the step the paper's C-Arrow glosses as `the right-component  *)
(*  premises can be rewritten with θ₁` (:2744) and Assign-Assign's        *)
(*  soundness needed as the ≡ˢ-subject transport: a join is invariant     *)
(*  under replacing its subject by an ≡ˢ-equivalent skeleton (the         *)
(*  equational theory only unfolds flexible definitions and is a          *)
(*  congruence elsewhere).  Mirrors [tyequiv_mono_consis_transport],      *)
(*  which covers only monotype subjects.                                  *)
(* --------------------------------------------------------------------- *)

(** Transport a ∀-syn subject componentwise: only [forall_inh_untagged] /
    [forall_syn] / [flex_r] can have an [all_syn] subject. *)
Lemma consis_forall_subject_transport : forall Ψ Θ S Qt,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  forall S0 T0 L0,
  S = uskl_all_syn S0 ->
  (forall X, X `notin` L0 -> forall Ψ' Q',
     Ψ' ⨟ ((X ~ abind_tvar) ++ Θ) ⊨ₛᵃ
       (open_uskl_wrt_uskl S0 (uskl_var_f X)) ≈ Q' ->
     Ψ' ⨟ ((X ~ abind_tvar) ++ Θ) ⊨ₛᵃ
       (open_uskl_wrt_uskl T0 (uskl_var_f X)) ≈ Q') ->
  Ψ ⨟ Θ ⊨ₛᵃ (uskl_all_syn T0) ≈ Qt.
Proof.
  intros Ψ Θ S Qt Hc; induction Hc; intros S0 T0 L0 HeqS Htr;
    try discriminate HeqS.
  - (* forall_inh_untagged *)
    inversion HeqS; subst.
    apply ad_pat_consis__forall_inh_untagged with (L := L `union` L0).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | ].
    apply H; clear - HX; fsetdec.
  - (* forall_syn *)
    inversion HeqS; subst.
    apply ad_pat_consis__forall_syn with (L := L `union` L0).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | ].
    apply H; clear - HX; fsetdec.
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

(** Transport a ⊤◇ subject componentwise.  The component transport is
    context-generalized because [tophole_inh] keeps the SAME subject under
    an extended context. *)
Lemma consis_tophole_subject_transport : forall Ψ Θ S Qt,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  a_wf_aenv Θ ->
  forall S0 T0,
  S = uskl_tophole S0 ->
  (forall Θ' Ψ' Q',
     a_wf_aenv Θ' ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     Ψ' ⨟ Θ' ⊨ₛᵃ S0 ≈ Q' -> Ψ' ⨟ Θ' ⊨ₛᵃ T0 ≈ Q') ->
  Ψ ⨟ Θ ⊨ₛᵃ (uskl_tophole T0) ≈ Qt.
Proof.
  intros Ψ Θ S Qt Hc; induction Hc; intros HwfΘ S0 T0 HeqS Htr;
    try discriminate HeqS.
  - (* tophole *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc ].
  - (* tophole_inh : same subject, extended context *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole_inh with (L := L `union` dom Θ).
    intros X HX.
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact HwfΘ ]).
    apply (H0 X ltac:(clear - HX; fsetdec) HwfX S0 T0 eq_refl).
    intros Θ' Ψ' Q' Hwf' Hincl' Hc'.
    apply (Htr Θ' Ψ' Q' Hwf'); [ | exact Hc' ].
    intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  - (* tophole_drop *)
    inversion HeqS; subst.
    apply ad_pat_consis__tophole_drop.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hc ].
  - (* flex_r *)
    eapply ad_pat_consis__flex_r; [ eassumption | ].
    eapply IHHc; eauto.
Qed.

(** THE TRANSPORT: for [Θ ⊢ A ≡ˢ B], joins re-subject between [⌊A⌋] and
    [⌊B⌋] in BOTH directions, in any conservative extension [Θ'] of the
    equivalence's context (the generality the ∀/⊤◇ congruences need). *)
Lemma skl_tyequiv_consis_transport : forall Θ A B,
  Θ ⊢ A ≡ˢ B ->
  forall Θ',
  a_wf_aenv Θ' ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall Ψ Qt, Ψ ⨟ Θ' ⊨ₛᵃ (pskl_to_uskl A) ≈ Qt ->
                Ψ ⨟ Θ' ⊨ₛᵃ (pskl_to_uskl B) ≈ Qt) /\
  (forall Ψ Qt, Ψ ⨟ Θ' ⊨ₛᵃ (pskl_to_uskl B) ≈ Qt ->
                Ψ ⨟ Θ' ⊨ₛᵃ (pskl_to_uskl A) ≈ Qt).
Proof.
  intros Θ A B Heq; induction Heq; intros Θ' Hwf' Hincl.
  - (* refl *) split; intros Ψ Qt Hc; exact Hc.
  - (* sym : swap *)
    destruct (IHHeq Θ' Hwf' Hincl) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - (* trans : compose *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Ψ Qt Hc; [ apply H2l, H1l, Hc | apply H1r, H2r, Hc ].
  - (* flex_def : α̂ ≡ˢ ⌊τ⌋ with α̂ ≔ τ *)
    split; intros Ψ Qt Hc.
    + (* unfold the subject definition *)
      rewrite pskl_to_uskl_ptyp.
      eapply consis_unfold_def_subject;
        [ exact Hc | exact Hwf' | reflexivity | apply Hincl; exact H ].
    + (* fold : one lookup rule *)
      simpl.
      eapply ad_pat_consis__flex_l; [ apply Hincl; exact H | ].
      rewrite pskl_to_uskl_ptyp in Hc. exact Hc.
  - (* arrow : componentwise *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros Ψ Qt Hc; simpl in Hc |- *.
    + eapply consis_arrow_subject_transport;
        [ exact Hc | reflexivity | exact H1l | exact H2l ].
    + eapply consis_arrow_subject_transport;
        [ exact Hc | reflexivity | exact H1r | exact H2r ].
  - (* all : componentwise, under a fresh rigid open *)
    split; intros Ψ Qt Hc; simpl in Hc |- *.
    + eapply consis_forall_subject_transport with (L0 := L `union` dom Θ');
        [ exact Hc | reflexivity | ].
      intros X HX Ψ' Q' Hc'.
      assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ'))
        by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ]).
      assert (HinclX : forall x b, binds x b Θ ->
                binds x b ((X ~ abind_tvar) ++ Θ'))
        by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb).
      destruct (H0 X ltac:(clear - HX; fsetdec)
                  ((X ~ abind_tvar) ++ Θ') HwfX HinclX) as [Hl _].
      rewrite <- pskl_to_uskl_open_var in Hc'.
      rewrite <- pskl_to_uskl_open_var.
      apply Hl. exact Hc'.
    + eapply consis_forall_subject_transport with (L0 := L `union` dom Θ');
        [ exact Hc | reflexivity | ].
      intros X HX Ψ' Q' Hc'.
      assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ'))
        by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf' ]).
      assert (HinclX : forall x b, binds x b Θ ->
                binds x b ((X ~ abind_tvar) ++ Θ'))
        by (intros x b Hb; apply binds_cons_3; apply Hincl; exact Hb).
      destruct (H0 X ltac:(clear - HX; fsetdec)
                  ((X ~ abind_tvar) ++ Θ') HwfX HinclX) as [_ Hr].
      rewrite <- pskl_to_uskl_open_var in Hc'.
      rewrite <- pskl_to_uskl_open_var.
      apply Hr. exact Hc'.
  - (* tophole : componentwise, context-generalized *)
    split; intros Ψ Qt Hc; simpl in Hc |- *.
    + eapply consis_tophole_subject_transport;
        [ exact Hc | exact Hwf' | reflexivity | ].
      intros Θ'' Ψ' Q' Hwf'' Hincl' Hc'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [Hl _].
      apply Hl. exact Hc'.
    + eapply consis_tophole_subject_transport;
        [ exact Hc | exact Hwf' | reflexivity | ].
      intros Θ'' Ψ' Q' Hwf'' Hincl' Hc'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [_ Hr].
      apply Hr. exact Hc'.
Qed.

(** Reflexivity of fill-hygienic refinement on a monotype's syn painting. *)
Lemma ad_refine_syn_f_mono_refl : forall F Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  ad_refine_syn_f F Θ Δ (ptyp_to_bskl_syn τ) (ptyp_to_bskl_syn τ).
Proof.
  intros F Θ Δ τ Hm Hwf.
  rewrite <- (mono_inh_eq_syn Hm).
  apply ad_refine_syn_f_refl_inh.
  apply ad_wf_pskl_mono_ptyp; assumption.
Qed.

(** Reflexivity of the uncoloured fill-hygienic refinement on a monotype. *)
Lemma ad_refine_pskl_f_mono_refl : forall F Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  ad_refine_pskl_f F Θ Δ (ptyp_to_pskl τ) (ptyp_to_pskl τ).
Proof.
  intros F Θ Δ τ Hm Hwf.
  apply ad_refine_pskl_f_refl.
  apply ad_wf_pskl_mono_ptyp; assumption.
Qed.

(* --------------------------------------------------------------------- *)
(*  The ≡ˢ-SOURCE TRANSPORTS of the two refinement judgments — the        *)
(*  companions of [skl_tyequiv_consis_transport] for C-Arrow's (g)/(i)    *)
(*  premises and Assign-Assign.  Same architecture: per-source-shape      *)
(*  helpers (each chasing the [flex_r] target chains), then the main      *)
(*  induction on [≡ˢ].                                                    *)
(* --------------------------------------------------------------------- *)

(** Unfold a DEFINED source variable inside a Δ1-refinement: only [var] /
    [flex_l] / [flex_r] can have source [γ̂]. *)
Lemma ad_refine_syn_f_unfold_def_source : forall F Θ Δ S Qt,
  ad_refine_syn_f F Θ Δ S Qt ->
  a_wf_aenv Θ ->
  forall γ τ, S = bskl_var_f γ ->
  binds γ (abind_flex_mono_def τ) Θ ->
  ad_refine_syn_f F Θ Δ (ptyp_to_bskl_syn τ) Qt.
Proof.
  intros F Θ Δ S Qt Hr Hwf; induction Hr; intros γ0 τ0 HeqS Hb;
    try discriminate HeqS.
  - (* var : the target is the same variable; fold it with [flex_r] *)
    inversion HeqS; subst.
    eapply ad_refine_syn_f__flex_r; [ exact Hb | ].
    apply ad_refine_syn_f_mono_refl;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
  - (* flex_l : the unfolding is the derivation's own *)
    inversion HeqS; subst.
    pose proof (binds_unique _ _ _ _ _ H Hb (a_wf_aenv_uniq Hwf)) as Heqd.
    inversion Heqd; subst.
    exact Hr.
  - (* flex_r : the target unfolds; recurse and re-wrap *)
    eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport an arrow source componentwise. *)
Lemma ad_refine_syn_f_arrow_source_transport : forall F Θ Δ S Qt,
  ad_refine_syn_f F Θ Δ S Qt ->
  forall S1 S2 T1 T2,
  S = bskl_arrow S1 S2 ->
  (forall Qt', ad_refine_syn_f F Θ Δ S1 Qt' ->
               ad_refine_syn_f F Θ Δ T1 Qt') ->
  (forall Qt', ad_refine_syn_f F Θ Δ S2 Qt' ->
               ad_refine_syn_f F Θ Δ T2 Qt') ->
  ad_refine_syn_f F Θ Δ (bskl_arrow T1 T2) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros S1' S2' T1 T2 HeqS Htr1 Htr2;
    try discriminate HeqS.
  - (* arrow *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__arrow; [ apply Htr1 | apply Htr2 ]; assumption.
  - (* flex_r *)
    eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport an inherited-∀ source componentwise (the [__all] premise
    grows Δ, so the component transport is Δ-generalized). *)
Lemma ad_refine_syn_f_forall_source_transport : forall F Θ Δ S Qt,
  ad_refine_syn_f F Θ Δ S Qt ->
  forall S0 T0 L0,
  S = bskl_all_inh S0 ->
  (forall X, X `notin` L0 -> forall Δ' Qt',
     ad_refine_syn_f F Θ Δ'
       (open_bskl_wrt_bskl S0 (bskl_var_f X)) Qt' ->
     ad_refine_syn_f F Θ Δ'
       (open_bskl_wrt_bskl T0 (bskl_var_f X)) Qt') ->
  ad_refine_syn_f F Θ Δ (bskl_all_inh T0) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros S0 T0 L0 HeqS Htr;
    try discriminate HeqS.
  - (* all *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__all with (L := L `union` L0).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | ].
    apply H; clear - HX; fsetdec.
  - (* flex_r *)
    eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport a ⊤◇ source componentwise.  Context-generalized: the
    [tophole_fill] premise keeps the SAME source under an extended Θ. *)
Lemma ad_refine_syn_f_tophole_source_transport : forall F Θ Δ S Qt,
  ad_refine_syn_f F Θ Δ S Qt ->
  a_wf_aenv Θ ->
  forall S0 T0,
  S = bskl_tophole S0 ->
  (forall Θ' Qt',
     a_wf_aenv Θ' ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     ad_refine_syn_f F Θ' Δ S0 Qt' ->
     ad_refine_syn_f F Θ' Δ T0 Qt') ->
  ad_refine_syn_f F Θ Δ (bskl_tophole T0) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros HwfΘ S0 T0 HeqS Htr;
    try discriminate HeqS.
  - (* tophole_remove *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__tophole_remove.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* tophole_fill : same source, extended context *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__tophole_fill with (L := L `union` dom Θ).
    intros X HX.
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact HwfΘ ]).
    apply (H0 X ltac:(clear - HX; fsetdec) HwfX S0 T0 eq_refl).
    intros Θ' Qt' Hwf' Hincl' Hr'.
    apply (Htr Θ' Qt' Hwf'); [ | exact Hr' ].
    intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  - (* tophole_keep *)
    inversion HeqS; subst.
    apply ad_refine_syn_f__tophole_keep; [ exact H | ].
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* flex_r *)
    eapply ad_refine_syn_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** THE SYN TRANSPORT: for [Θ ⊢ A ≡ˢ B], Δ1-refinements re-source between
    [inh A] and [inh B], in both directions, in any conservative
    extension. *)
Lemma skl_tyequiv_refine_syn_f_transport : forall Θ A B,
  Θ ⊢ A ≡ˢ B ->
  forall Θ',
  a_wf_aenv Θ' ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall F Δ Qt,
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh A) Qt ->
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh B) Qt) /\
  (forall F Δ Qt,
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh B) Qt ->
     ad_refine_syn_f F Θ' Δ (pskl_to_bskl_inh A) Qt).
Proof.
  intros Θ A B Heq; induction Heq; intros Θ' Hwf' Hincl.
  - (* refl *) split; intros F Δ Qt Hr; exact Hr.
  - (* sym *)
    destruct (IHHeq Θ' Hwf' Hincl) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - (* trans *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros F Δ Qt Hr;
      [ apply H2l, H1l, Hr | apply H1r, H2r, Hr ].
  - (* flex_def *)
    assert (HbΘ' : binds α (abind_flex_mono_def τ) Θ')
      by (apply Hincl; exact H).
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact Hwf' | exact HbΘ' ]).
    split; intros F Δ Qt Hr.
    + (* unfold : the source's own definition *)
      rewrite (mono_inh_eq_syn Hmτ).
      eapply ad_refine_syn_f_unfold_def_source;
        [ exact Hr | exact Hwf' | reflexivity | exact HbΘ' ].
    + (* fold : one lookup rule *)
      simpl.
      eapply ad_refine_syn_f__flex_l; [ exact HbΘ' | ].
      rewrite (mono_inh_eq_syn Hmτ) in Hr. exact Hr.
  - (* arrow *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros F Δ Qt Hr; simpl in Hr |- *.
    + eapply ad_refine_syn_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1l | apply H2l ].
    + eapply ad_refine_syn_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1r | apply H2r ].
  - (* all *)
    split; intros F Δ Qt Hr; simpl in Hr |- *.
    + eapply ad_refine_syn_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros X HX Δ' Qt' Hr'.
      destruct (H0 X ltac:(clear - HX; fsetdec) Θ' Hwf' Hincl) as [Hl _].
      rewrite <- pskl_to_bskl_inh_open in Hr'.
      rewrite <- pskl_to_bskl_inh_open.
      apply Hl. exact Hr'.
    + eapply ad_refine_syn_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros X HX Δ' Qt' Hr'.
      destruct (H0 X ltac:(clear - HX; fsetdec) Θ' Hwf' Hincl) as [_ Hrr].
      rewrite <- pskl_to_bskl_inh_open in Hr'.
      rewrite <- pskl_to_bskl_inh_open.
      apply Hrr. exact Hr'.
  - (* tophole *)
    split; intros F Δ Qt Hr; simpl in Hr |- *.
    + eapply ad_refine_syn_f_tophole_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_syn_f_tophole_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [_ Hrr].
      apply Hrr. exact Hr'.
Qed.

(** Unfold a DEFINED source variable inside a Δ2-refinement. *)
Lemma ad_refine_pskl_f_unfold_def_source : forall F Θ Δ S Qt,
  ad_refine_pskl_f F Θ Δ S Qt ->
  a_wf_aenv Θ ->
  forall γ τ, S = pskl_var_f γ ->
  binds γ (abind_flex_mono_def τ) Θ ->
  ad_refine_pskl_f F Θ Δ (ptyp_to_pskl τ) Qt.
Proof.
  intros F Θ Δ S Qt Hr Hwf; induction Hr; intros γ0 τ0 HeqS Hb;
    try discriminate HeqS.
  - (* var *)
    inversion HeqS; subst.
    eapply ad_refine_pskl_f__flex_r; [ exact Hb | ].
    apply ad_refine_pskl_f_mono_refl;
      [ eapply a_wf_aenv_binds_def_mono; eauto
      | eapply a_wf_aenv_binds_def_wf; eauto ].
  - (* flex_l *)
    inversion HeqS; subst.
    pose proof (binds_unique _ _ _ _ _ H Hb (a_wf_aenv_uniq Hwf)) as Heqd.
    inversion Heqd; subst.
    exact Hr.
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport an arrow source componentwise (uncoloured). *)
Lemma ad_refine_pskl_f_arrow_source_transport : forall F Θ Δ S Qt,
  ad_refine_pskl_f F Θ Δ S Qt ->
  forall S1 S2 T1 T2,
  S = pskl_arrow S1 S2 ->
  (forall Qt', ad_refine_pskl_f F Θ Δ S1 Qt' ->
               ad_refine_pskl_f F Θ Δ T1 Qt') ->
  (forall Qt', ad_refine_pskl_f F Θ Δ S2 Qt' ->
               ad_refine_pskl_f F Θ Δ T2 Qt') ->
  ad_refine_pskl_f F Θ Δ (pskl_arrow T1 T2) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros S1' S2' T1 T2 HeqS Htr1 Htr2;
    try discriminate HeqS.
  - (* arrow *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__arrow; [ apply Htr1 | apply Htr2 ]; assumption.
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport a ∀-syn source componentwise (uncoloured; Δ grows). *)
Lemma ad_refine_pskl_f_forall_source_transport : forall F Θ Δ S Qt,
  ad_refine_pskl_f F Θ Δ S Qt ->
  forall S0 T0 L0,
  S = pskl_all_syn S0 ->
  (forall X, X `notin` L0 -> forall Δ' Qt',
     ad_refine_pskl_f F Θ Δ'
       (open_pskl_wrt_pskl S0 (pskl_var_f X)) Qt' ->
     ad_refine_pskl_f F Θ Δ'
       (open_pskl_wrt_pskl T0 (pskl_var_f X)) Qt') ->
  ad_refine_pskl_f F Θ Δ (pskl_all_syn T0) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros S0 T0 L0 HeqS Htr;
    try discriminate HeqS.
  - (* all *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__all with (L := L `union` L0).
    intros X HX.
    apply Htr; [ clear - HX; fsetdec | ].
    apply H; clear - HX; fsetdec.
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** Transport a ⊤◇ source componentwise (uncoloured; context-generalized
    for [tophole_fill]). *)
Lemma ad_refine_pskl_f_tophole_source_transport : forall F Θ Δ S Qt,
  ad_refine_pskl_f F Θ Δ S Qt ->
  a_wf_aenv Θ ->
  forall S0 T0,
  S = pskl_tophole S0 ->
  (forall Θ' Qt',
     a_wf_aenv Θ' ->
     (forall x b, binds x b Θ -> binds x b Θ') ->
     ad_refine_pskl_f F Θ' Δ S0 Qt' ->
     ad_refine_pskl_f F Θ' Δ T0 Qt') ->
  ad_refine_pskl_f F Θ Δ (pskl_tophole T0) Qt.
Proof.
  intros F Θ Δ S Qt Hr; induction Hr; intros HwfΘ S0 T0 HeqS Htr;
    try discriminate HeqS.
  - (* tophole_remove *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__tophole_remove.
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* tophole_fill *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__tophole_fill with (L := L `union` dom Θ).
    intros X HX.
    assert (HwfX : a_wf_aenv ((X ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact HwfΘ ]).
    apply (H0 X ltac:(clear - HX; fsetdec) HwfX S0 T0 eq_refl).
    intros Θ' Qt' Hwf' Hincl' Hr'.
    apply (Htr Θ' Qt' Hwf'); [ | exact Hr' ].
    intros x b Hb. apply Hincl'. apply binds_cons_3. exact Hb.
  - (* tophole_keep *)
    inversion HeqS; subst.
    apply ad_refine_pskl_f__tophole_keep; [ exact H | ].
    apply (Htr Θ); [ exact HwfΘ | intros x b Hb; exact Hb | exact Hr ].
  - (* flex_r *)
    eapply ad_refine_pskl_f__flex_r; [ eassumption | ].
    eapply IHHr; eauto.
Qed.

(** THE PSKL TRANSPORT: for [Θ ⊢ A ≡ˢ B], Δ2-refinements re-source between
    [A] and [B], in both directions, in any conservative extension. *)
Lemma skl_tyequiv_refine_pskl_f_transport : forall Θ A B,
  Θ ⊢ A ≡ˢ B ->
  forall Θ',
  a_wf_aenv Θ' ->
  (forall x b, binds x b Θ -> binds x b Θ') ->
  (forall F Δ Qt,
     ad_refine_pskl_f F Θ' Δ A Qt ->
     ad_refine_pskl_f F Θ' Δ B Qt) /\
  (forall F Δ Qt,
     ad_refine_pskl_f F Θ' Δ B Qt ->
     ad_refine_pskl_f F Θ' Δ A Qt).
Proof.
  intros Θ A B Heq; induction Heq; intros Θ' Hwf' Hincl.
  - (* refl *) split; intros F Δ Qt Hr; exact Hr.
  - (* sym *)
    destruct (IHHeq Θ' Hwf' Hincl) as [Hd1 Hd2].
    split; [ exact Hd2 | exact Hd1 ].
  - (* trans *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros F Δ Qt Hr;
      [ apply H2l, H1l, Hr | apply H1r, H2r, Hr ].
  - (* flex_def *)
    assert (HbΘ' : binds α (abind_flex_mono_def τ) Θ')
      by (apply Hincl; exact H).
    split; intros F Δ Qt Hr.
    + eapply ad_refine_pskl_f_unfold_def_source;
        [ exact Hr | exact Hwf' | reflexivity | exact HbΘ' ].
    + eapply ad_refine_pskl_f__flex_l; [ exact HbΘ' | exact Hr ].
  - (* arrow *)
    destruct (IHHeq1 Θ' Hwf' Hincl) as [H1l H1r].
    destruct (IHHeq2 Θ' Hwf' Hincl) as [H2l H2r].
    split; intros F Δ Qt Hr.
    + eapply ad_refine_pskl_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1l | apply H2l ].
    + eapply ad_refine_pskl_f_arrow_source_transport;
        [ exact Hr | reflexivity | apply H1r | apply H2r ].
  - (* all *)
    split; intros F Δ Qt Hr.
    + eapply ad_refine_pskl_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros X HX Δ' Qt' Hr'.
      destruct (H0 X ltac:(clear - HX; fsetdec) Θ' Hwf' Hincl) as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_pskl_f_forall_source_transport with (L0 := L);
        [ exact Hr | reflexivity | ].
      intros X HX Δ' Qt' Hr'.
      destruct (H0 X ltac:(clear - HX; fsetdec) Θ' Hwf' Hincl) as [_ Hrr].
      apply Hrr. exact Hr'.
  - (* tophole *)
    split; intros F Δ Qt Hr.
    + eapply ad_refine_pskl_f_tophole_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [Hl _].
      apply Hl. exact Hr'.
    + eapply ad_refine_pskl_f_tophole_source_transport;
        [ exact Hr | exact Hwf' | reflexivity | ].
      intros Θ'' Qt' Hwf'' Hincl' Hr'.
      destruct (IHHeq Θ'' Hwf''
                  (fun x b Hb => Hincl' x b (Hincl x b Hb))) as [_ Hrr].
      apply Hrr. exact Hr'.
Qed.

(** Bridge to the Δ-free skeleton wf (the form the ≡ˢ/V lemmas take):
    Δ-variables must be tvar-ish in the receiving context. *)
Lemma ad_wf_pskl_to_a_wf_pskl : forall Θ Δ P,
  ad_wf_pskl Θ Δ P ->
  forall Θa,
  (forall x b, binds x b Θ -> binds x b Θa) ->
  (forall X, X `in` Δ -> a_binds_tvar X Θa) ->
  a_wf_pskl Θa P.
Proof.
  intros Θ Δ P Hwfd; induction Hwfd; intros Θa Hincl HΔ.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HXΔ | Hbt]; [ apply HΔ; exact HXΔ | ].
    destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ];
      apply Hincl; exact Hb.
  - apply a_wf_pskl__arrow;
      [ apply IHHwfd1 | apply IHHwfd2 ]; assumption.
  - apply a_wf_pskl__all with (L := L).
    intros X HX.
    apply H0; [ exact HX | | ].
    + intros x b Hb. apply binds_cons_3. apply Hincl; exact Hb.
    + intros Y HY. destruct (Y == X) as [-> | Hne].
      * left. unfold binds. left. reflexivity.
      * destruct (HΔ Y ltac:(clear - HY Hne; fsetdec))
          as [Hb | [Hb | [τ Hb]]];
          [ left | right; left | right; right; exists τ ];
          apply binds_cons_3; exact Hb.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole.
    apply IHHwfd; [ exact Hincl | ].
    intros Y HY. exfalso. clear - HY. fsetdec.
Qed.

(** The join's target erases to a well-formed (Δ-free) skeleton — the
    output-regularity C-Arrow's precision transport needs. *)
Lemma ad_pat_consis_target_wf : forall Ψ Θ S Qt,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qt ->
  a_wf_pskl Θ (bskl_to_pskl Qt).
Proof.
  intros Ψ Θ S Qt Hc; induction Hc; simpl.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var; exact H0.
  - apply a_wf_pskl__arrow; assumption.
  - (* forall_inh_tagged *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - (* forall_inh_untagged *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - (* forall_syn_tagged *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - (* forall_syn *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; assumption.
  - (* hole : the fill is wf by the rule's own premise *)
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    eapply ad_wf_pskl_to_a_wf_pskl;
      [ exact H0 | intros x b Hb; exact Hb
      | intros Y HY; exfalso; clear - HY; fsetdec ].
  - apply a_wf_pskl__tophole; assumption.
  - (* tophole_inh *)
    apply a_wf_pskl__all with (L := L).
    intros X HX. rewrite <- bskl_to_pskl_open. apply H0; exact HX.
  - (* tophole_drop *) assumption.
  - (* flex_l *) assumption.
  - (* flex_r *)
    apply a_wf_pskl__var. right; right; exists τ; exact H.
Qed.

(** The empty hygiene set is free: the plain refinement IS the
    fill-hygienic one at [F = ∅] (the hole rule's ∅-disjointness is
    trivial).  Lets the precision goal reuse the [_f] transports. *)
Lemma ad_refine_syn_f_of_plain : forall Θ Δ Q P,
  Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P ->
  ad_refine_syn_f empty Θ Δ Q P.
Proof.
  intros Θ Δ Q P H; induction H;
    try solve [ eauto using ad_refine_syn_f ].
  apply ad_refine_syn_f__hole; [ clear; fsetdec | exact H ].
Qed.

(** An inherited quantifier never refines to a guarded skeleton (the target
    of every rule applicable to an [all_inh] source is an [all_inh] or a
    defined flexible whose unfolding is a monotype painting — itself guarded,
    recursing).  Kills the [P0 = ∀.P0'] sub-case of C-UnivGhost2. *)
Lemma ad_refine_syn_f_all_inh_guarded_absurd : forall F Θ Δ Q R,
  a_wf_aenv Θ ->
  ad_refine_syn_f F Θ Δ (bskl_all_inh Q) R ->
  guarded_bskl R ->
  False.
Proof.
  intros F Θ Δ Q R Hwf Hr.
  remember (bskl_all_inh Q) as S eqn:HeqS.
  induction Hr; intros Hg; try discriminate HeqS.
  - (* __all : target is an inherited quantifier, not guarded *)
    inversion Hg.
  - (* __flex_r : unfold the target definition (a monotype, guarded) *)
    apply IHHr; [ exact Hwf | exact HeqS | ].
    apply mono_bskl_guarded, mono_ptyp_to_bskl_syn.
    eapply a_wf_aenv_binds_def_mono; eauto.
Qed.

(** Target-side definition unfolding for the fill-hygienic Δ1-refinement:
    a refinement into a DEFINED flexible target is a refinement into its
    definition's painting (the C-FlexR transport of the core's [flex_r]
    join case).  The [F]-disjointness premise is the [no_flex_dep]
    invariant instantiated at the definition. *)
Lemma ad_refine_syn_f_flex_target_unfold : forall F Θ Δ S α τ,
  a_wf_aenv Θ ->
  binds α (abind_flex_mono_def τ) Θ ->
  (forall X, X `in` Δ -> binds X abind_tvar Θ) ->
  AtomSetImpl.inter F (ftvar_in_ptyp τ) [=] empty ->
  ad_refine_syn_f F Θ Δ S (bskl_var_f α) ->
  ad_refine_syn_f F Θ Δ S (ptyp_to_bskl_syn τ).
Proof.
  intros F Θ Δ S α τ Hwf Hbα HΔ Hdisj Hr.
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  assert (Hwfτ : a_wf_ptyp Θ τ) by (eapply a_wf_aenv_binds_def_wf; eauto).
  remember (bskl_var_f α) as T eqn:HeqT.
  induction Hr; try discriminate HeqT.
  - (* __var : the source IS the defined flexible; unfold it on the left *)
    inversion HeqT; subst X.
    assert (Hbtα : binds α abind_tvar Θ \/ binds α abind_flex_mono Θ \/
                   (exists τ', binds α (abind_flex_mono_def τ') Θ)).
    { destruct H as [HinΔ | Hbt]; [ left; apply HΔ; exact HinΔ | exact Hbt ]. }
    destruct Hbtα as [Hb | [Hb | [τ' Hb]]];
      try solve [ pose proof (binds_unique _ _ _ _ _ Hb Hbα
                                (a_wf_aenv_uniq Hwf)) as Hcon; discriminate ].
    eapply ad_refine_syn_f__flex_l; [ exact Hbα | ].
    apply ad_refine_syn_f_mono_refl; assumption.
  - (* __hole : the fill is the defined flexible; refill with its definition *)
    destruct P as [ | n | δ | | | | ]; simpl in HeqT; try discriminate.
    inversion HeqT; subst δ.
    replace (ptyp_to_bskl_syn τ)
      with (pskl_to_bskl_syn (ptyp_to_pskl τ)) by reflexivity.
    apply ad_refine_syn_f__hole.
    + rewrite ftvar_in_ptyp_to_pskl. exact Hdisj.
    + apply a_wf_ptyp_to_wf_pskl. exact Hwfτ.
  - (* __tophole_remove : arbitrary target; recurse under the source strip *)
    apply ad_refine_syn_f__tophole_remove.
    apply IHHr; assumption.
  - (* __flex_l : source-side unfolding; recurse and re-wrap *)
    eapply ad_refine_syn_f__flex_l; [ exact H | ].
    apply IHHr; assumption.
  - (* __flex_r : the target unfolding itself; definitions agree by uniq *)
    inversion HeqT; subst α0.
    pose proof (binds_unique _ _ _ _ _ H Hbα (a_wf_aenv_uniq Hwf)) as Heq.
    inversion Heq; subst τ0.
    exact Hr.
Qed.

(** Uncoloured version of the target-side definition unfolding. *)
Lemma ad_refine_pskl_f_flex_target_unfold : forall F Θ Δ S α τ,
  a_wf_aenv Θ ->
  binds α (abind_flex_mono_def τ) Θ ->
  (forall X, X `in` Δ -> binds X abind_tvar Θ) ->
  AtomSetImpl.inter F (ftvar_in_ptyp τ) [=] empty ->
  ad_refine_pskl_f F Θ Δ S (pskl_var_f α) ->
  ad_refine_pskl_f F Θ Δ S (ptyp_to_pskl τ).
Proof.
  intros F Θ Δ S α τ Hwf Hbα HΔ Hdisj Hr.
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  assert (Hwfτ : a_wf_ptyp Θ τ) by (eapply a_wf_aenv_binds_def_wf; eauto).
  remember (pskl_var_f α) as T eqn:HeqT.
  induction Hr; try discriminate HeqT.
  - (* __var *)
    inversion HeqT; subst X.
    assert (Hbtα : binds α abind_tvar Θ \/ binds α abind_flex_mono Θ \/
                   (exists τ', binds α (abind_flex_mono_def τ') Θ)).
    { destruct H as [HinΔ | Hbt]; [ left; apply HΔ; exact HinΔ | exact Hbt ]. }
    destruct Hbtα as [Hb | [Hb | [τ' Hb]]];
      try solve [ pose proof (binds_unique _ _ _ _ _ Hb Hbα
                                (a_wf_aenv_uniq Hwf)) as Hcon; discriminate ].
    eapply ad_refine_pskl_f__flex_l; [ exact Hbα | ].
    apply ad_refine_pskl_f_mono_refl; assumption.
  - (* __hole *)
    inversion HeqT; subst Q.
    apply ad_refine_pskl_f__hole.
    + rewrite ftvar_in_ptyp_to_pskl. exact Hdisj.
    + apply a_wf_ptyp_to_wf_pskl. exact Hwfτ.
  - (* __tophole_remove *)
    apply ad_refine_pskl_f__tophole_remove.
    apply IHHr; assumption.
  - (* __flex_l *)
    eapply ad_refine_pskl_f__flex_l; [ exact H | ].
    apply IHHr; assumption.
  - (* __flex_r *)
    inversion HeqT; subst α0.
    pose proof (binds_unique _ _ _ _ _ H Hbα (a_wf_aenv_uniq Hwf)) as Heq.
    inversion Heq; subst τ0.
    exact Hr.
Qed.

(* ===================================================================== *)
(*  §3  The three induction steps (one per part of the paper's proof)     *)
(* ===================================================================== *)

(** Part 2 of the paper's proof (:2260-2401): unification of flexible
    variables, by a walk of the context [Θ0] (n strictly decreases on the
    walk edges; the Flex-Flex-Assign back-edge re-enters part 1 with [V]
    exactly constant and [n] one smaller). *)
Lemma unify_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  unify_complete_at m.
Proof.
  intros m IH. unfold unify_complete_at.
  intros F Θ0 α β ρ Θ Hm Hwf Hfα Hfβ Hinc Hwfth Heq. subst m.
  destruct (α == β) as [-> | Hne].
  { (* Flex-Flex-Id : axiom, Θ1 = Θ0; ζ := ρ. *)
    exists Θ0. split; [ apply a_unify__flex_id; exact Hfα | ].
    intros ρ1 Hid Hinc1. exists ρ.
    exact (opt_axiom_factor Hwf Hid Hinc1 Hinc). }
  assert (Hβα : β <> α) by auto.
  destruct Θ0 as [ | [γ b] Θ0' ].
  { exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb. }
  destruct b as [ | A | Q | | τdef ].
  - (* head [γ ~ tvar] : Flex-Flex-Skip' (rigid). *)
    inversion Hwf as [ | | | | | γh Θh Hnd Hwf0 ]; subst.
    assert (Hγα : α <> γ)
      by (intros ->; destruct Hfα as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hγβ : β <> γ)
      by (intros ->; destruct Hfβ as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hfα0 : a_flex_tvar Θ0' α)
      by (eapply a_flex_tvar_strip_head; [ exact Hγα | exact Hfα ]).
    assert (Hfβ0 : a_flex_tvar Θ0' β)
      by (eapply a_flex_tvar_strip_head; [ exact Hγβ | exact Hfβ ]).
    assert (Hbtα : a_binds_tvar α Θ0') by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0') by (right; exact Hfβ0).
    apply a_inc_tvar_inv in Hinc as [Ξ [Θ2 [-> [HΞ Hinc']]]].
    assert (Hwfth2 : a_wf_aenv Θ2)
      by (rewrite <- app_assoc in Hwfth;
          apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
    assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup ρ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]).
    assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup ρ β))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]).
    assert (Heq2 : Θ2 ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
    { eapply a_tyequiv_strengthen_mono_mid;
        [ exact Hwfth | exact Hwflα
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Hwflβ
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Heq ]. }
    assert (Huniq : uniq (Ξ ++ (γ ~ abind_tvar) ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hlt : mu_lt (mu_unify Θ2 ρ α β Θ0')
                        (mu_unify (Ξ ++ (γ ~ abind_tvar) ++ Θ2) ρ α β
                                  ((γ ~ abind_tvar) ++ Θ0'))).
    { unfold mu_unify. apply mu_lt_intro. right. split.
      - unfold V_unify.
        rewrite (@Vvar_strengthen_mid Ξ γ abind_tvar Θ2 ρ α Huniq Hwflα).
        rewrite (@Vvar_strengthen_mid Ξ γ abind_tvar Θ2 ρ β Huniq Hwflβ).
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add γ F) Θ0' α β ρ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu Hopt']].
    exists ((γ ~ abind_tvar) ++ Θ1'). split.
    { apply a_unify__skip_other; [ left; reflexivity | exact Hu ]. }
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : Θ0' ≤[ ρ1 ] Θ1')
      by (eapply a_inc_id_mid_strip; [ left; reflexivity | exact Hinc1 ]).
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + apply a_inc__tvar; [ exact Hζ' | exact HΞ ].
    + apply a_inc_equiv__tvar; [ exact Hie' | exact HΞ ].
  - (* head [x ~ var_typ A] : Flex-Flex-Skip' (semantic type middle). *)
    destruct (a_wf_aenv_var_typ_inv Hwf) as [Hnd [HwfA Hwf0]].
    assert (Hγα : α <> γ)
      by (intros ->; destruct Hfα as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hγβ : β <> γ)
      by (intros ->; destruct Hfβ as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hfα0 : a_flex_tvar Θ0' α)
      by (eapply a_flex_tvar_strip_head; [ exact Hγα | exact Hfα ]).
    assert (Hfβ0 : a_flex_tvar Θ0' β)
      by (eapply a_flex_tvar_strip_head; [ exact Hγβ | exact Hfβ ]).
    assert (Hbtα : a_binds_tvar α Θ0') by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0') by (right; exact Hfβ0).
    apply a_inc_var_inv in Hinc as [Ξ [A' [Θ2 [-> [HA'eq [HΞ Hinc']]]]]].
    assert (Hwfth2 : a_wf_aenv Θ2)
      by (rewrite <- app_assoc in Hwfth;
          apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
    assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup ρ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]).
    assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup ρ β))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]).
    assert (Heq2 : Θ2 ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
    { eapply a_tyequiv_strengthen_mono_mid;
        [ exact Hwfth | exact Hwflα
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Hwflβ
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Heq ]. }
    assert (Huniq : uniq (Ξ ++ (γ ~ abind_var_typ A') ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hlt : mu_lt (mu_unify Θ2 ρ α β Θ0')
                        (mu_unify (Ξ ++ (γ ~ abind_var_typ A') ++ Θ2) ρ α β
                                  ((γ ~ abind_var_typ A) ++ Θ0'))).
    { unfold mu_unify. apply mu_lt_intro. right. split.
      - unfold V_unify.
        rewrite (@Vvar_strengthen_mid Ξ γ (abind_var_typ A') Θ2 ρ α Huniq Hwflα).
        rewrite (@Vvar_strengthen_mid Ξ γ (abind_var_typ A') Θ2 ρ β Huniq Hwflβ).
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add γ F) Θ0' α β ρ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu Hopt']].
    exists ((γ ~ abind_var_typ A) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ right; left; exists A; reflexivity | exact Hu ]. }
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : Θ0' ≤[ ρ1 ] Θ1')
      by (eapply a_inc_id_mid_strip;
          [ right; left; exists A; reflexivity | exact Hinc1 ]).
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    destruct (a_unify_sound Hu Hwf0)
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hbridge : Θ2 ⊢ A' ≡ᵗ (msubst_ptyp ζ' A)).
    { eapply a_tyequiv__trans; [ exact HA'eq | ].
      rewrite <- (msubst_compose_id_ptyp Hwf0 Hwf1' Hid Hinc1' Hζ' HwfA).
      eapply a_inc_equiv_msubst_ptyp;
        [ exact HwfA | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hid ] ]. }
    exists ζ'. split.
    + apply a_inc__var; [ exact Hζ' | exact Hbridge | exact HΞ ].
    + apply a_inc_equiv__var; [ exact Hie' | exact HA'eq | exact HΞ ].
  - (* head [x ~ var_skl Q] : Flex-Flex-Skip' (semantic skeleton middle). *)
    destruct (a_wf_aenv_var_skl_inv Hwf) as [Hnd [HwfQ Hwf0]].
    assert (Hγα : α <> γ)
      by (intros ->; destruct Hfα as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hγβ : β <> γ)
      by (intros ->; destruct Hfβ as [Hb | [τ Hb]];
          apply binds_cons_1 in Hb as [[_ Hb] | Hb];
          solve [ discriminate | apply binds_In in Hb; auto ]).
    assert (Hfα0 : a_flex_tvar Θ0' α)
      by (eapply a_flex_tvar_strip_head; [ exact Hγα | exact Hfα ]).
    assert (Hfβ0 : a_flex_tvar Θ0' β)
      by (eapply a_flex_tvar_strip_head; [ exact Hγβ | exact Hfβ ]).
    assert (Hbtα : a_binds_tvar α Θ0') by (right; exact Hfα0).
    assert (Hbtβ : a_binds_tvar β Θ0') by (right; exact Hfβ0).
    apply a_inc_var_skl_inv in Hinc as [Ξ [P' [Θ2 [-> [HP'eq [HΞ Hinc']]]]]].
    assert (Hwfth2 : a_wf_aenv Θ2)
      by (rewrite <- app_assoc in Hwfth;
          apply a_wf_aenv_strip_prefix_local in Hwfth; exact Hwfth).
    assert (Hwflα : a_wf_ptyp Θ2 (msubst_lookup ρ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtα ]).
    assert (Hwflβ : a_wf_ptyp Θ2 (msubst_lookup ρ β))
      by (eapply a_inc_lookup_wf; [ exact Hinc' | exact Hwf0 | exact Hbtβ ]).
    assert (Heq2 : Θ2 ⊢ (msubst_lookup ρ α) ≡ᵗ (msubst_lookup ρ β)).
    { eapply a_tyequiv_strengthen_mono_mid;
        [ exact Hwfth | exact Hwflα
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Hwflβ
        | eapply a_inc_lookup_mono; exact Hinc'
        | exact Heq ]. }
    assert (Huniq : uniq (Ξ ++ (γ ~ abind_var_skl P') ++ Θ2))
      by (apply a_wf_aenv_uniq; exact Hwfth).
    assert (Hlt : mu_lt (mu_unify Θ2 ρ α β Θ0')
                        (mu_unify (Ξ ++ (γ ~ abind_var_skl P') ++ Θ2) ρ α β
                                  ((γ ~ abind_var_skl Q) ++ Θ0'))).
    { unfold mu_unify. apply mu_lt_intro. right. split.
      - unfold V_unify.
        rewrite (@Vvar_strengthen_mid Ξ γ (abind_var_skl P') Θ2 ρ α Huniq Hwflα).
        rewrite (@Vvar_strengthen_mid Ξ γ (abind_var_skl P') Θ2 ρ β Huniq Hwflβ).
        reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [_ [HuIH _]].
    destruct (HuIH (add γ F) Θ0' α β ρ Θ2 eq_refl Hwf0 Hfα0 Hfβ0
                   Hinc' Hwfth2 Heq2) as [Θ1' [Hu Hopt']].
    exists ((γ ~ abind_var_skl Q) ++ Θ1'). split.
    { apply a_unify__skip_other;
        [ right; right; exists Q; reflexivity | exact Hu ]. }
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : Θ0' ≤[ ρ1 ] Θ1')
      by (eapply a_inc_id_mid_strip;
          [ right; right; exists Q; reflexivity | exact Hinc1 ]).
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ' [Hζ' Hie']].
    destruct (a_unify_sound Hu Hwf0)
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hbridge : Θ2 ⊢ P' ≡ˢ (msubst_pskl ζ' Q)).
    { eapply a_pskl_tyequiv__trans; [ exact HP'eq | ].
      rewrite <- (msubst_compose_id_pskl Hwf0 Hwf1' Hid Hinc1' Hζ' HwfQ).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HwfQ | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hid ] ]. }
    exists ζ'. split.
    + apply a_inc__var_skl; [ exact Hζ' | exact Hbridge | exact HΞ ].
    + apply a_inc_equiv__var_skl; [ exact Hie' | exact HP'eq | exact HΞ ].
  - (* head [γ̂] undefined flexible : Flex-Flex-L / Flex-Flex-R / Skip. *)
    inversion Hwf as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
    destruct (γ == α) as [-> | Hγα].
    + (* Flex-Flex-L : α̂ ≔ β̂; axiom, ζ := ρ. *)
      inversion Hinc as [ | Θs ρs Θt αs τ Hinc' Hwfτ Hmτ [Heqα Heqρ] Heqt
                        | | | | ]; subst.
      assert (Hfβ0 : a_flex_tvar Θ0' β)
        by (eapply a_flex_tvar_strip_head; [ exact Hβα | exact Hfβ ]).
      exists ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0'). split.
      { apply a_unify__flex_l; [ exact Hne | exact Hfβ0 ]. }
      intros ρ1 Hid Hinc1. exists ((α, τ) :: ρs). split.
      * apply a_inc__flex_def; auto.
        rewrite msubst_lookup_cons_eq in Heq.
        rewrite (msubst_lookup_cons_neq τ ρs Hβα) in Heq.
        exact Heq.
      * rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
        apply a_inc_equiv_refl; exact Hinc.
    + destruct (γ == β) as [-> | Hγβ].
      * (* Flex-Flex-R : β̂ ≔ α̂; axiom, ζ := ρ. *)
        inversion Hinc as [ | Θs ρs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqρ] Heqt
                          | | | | ]; subst.
        assert (Hγα' : α <> β) by exact Hne.
        assert (Hfα0 : a_flex_tvar Θ0' α)
          by (eapply a_flex_tvar_strip_head; [ exact Hne | exact Hfα ]).
        exists ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0'). split.
        { apply a_unify__flex_r; [ exact Hne | exact Hfα0 ]. }
        intros ρ1 Hid Hinc1. exists ((β, τ) :: ρs). split.
        -- apply a_inc__flex_def; auto.
           rewrite msubst_lookup_cons_eq in Heq.
           rewrite (msubst_lookup_cons_neq τ ρs Hγα') in Heq.
           apply a_tyequiv__sym; exact Heq.
        -- rewrite (msubst_compose_is_id_r Hwf Hid Hinc1 Hinc).
           apply a_inc_equiv_refl; exact Hinc.
      * (* Flex-Flex-Skip : γ̂ ∉ {α̂, β̂} walked past. *)
        inversion Hinc as [ | Θs ρs Θt γs τγ Hincs Hwfτ Hmτ [Heqγ Heqρ] Heqt
                          | | | | ]; subst.
        assert (Hαγ : α <> γ) by auto.
        assert (Hβγ : β <> γ) by auto.
        assert (Hfα0 : a_flex_tvar Θ0' α)
          by (eapply a_flex_tvar_strip_head; [ exact Hαγ | exact Hfα ]).
        assert (Hfβ0 : a_flex_tvar Θ0' β)
          by (eapply a_flex_tvar_strip_head; [ exact Hβγ | exact Hfβ ]).
        rewrite (msubst_lookup_cons_neq τγ ρs Hαγ) in Heq.
        rewrite (msubst_lookup_cons_neq τγ ρs Hβγ) in Heq.
        assert (Hlt : mu_lt (mu_unify Θ ρs α β Θ0')
                            (mu_unify Θ ((γ, τγ) :: ρs) α β
                                      ((γ ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_unify. apply mu_lt_intro. right. split.
          - unfold V_unify, Vvar.
            rewrite (msubst_lookup_cons_neq τγ ρs Hαγ).
            rewrite (msubst_lookup_cons_neq τγ ρs Hβγ).
            reflexivity.
          - left. simpl. lia. }
        destruct (IH _ Hlt) as [_ [HuIH _]].
        destruct (HuIH (add γ F) Θ0' α β ρs Θ eq_refl Hwf0 Hfα0 Hfβ0
                       Hincs Hwfth Heq) as [Θ1' [Hu Hopt']].
        exists ((γ ~ abind_flex_mono) ++ Θ1'). split.
        { apply a_unify__flex_skip;
            [ auto | auto | exact Hu ]. }
        intros ρ1 Hid Hinc1.
        inversion Hinc1 as [ | Θp ρp Θq γp τp Hincp Hwfp Hmp [Heqγ1 Heqρ1] Heqt1
                           | | | | ]; subst.
        apply is_id_msubst_inv in Hid as [Heqτp Hid']; subst τp.
        destruct (a_unify_sound Hu Hwf0)
          as [[[w [Hidw Hincw]] _] _].
        assert (Hw : ρp = w)
          by (eapply is_id_inc_unique; eauto).
        subst w.
        assert (Hγw : γ `notin` dom ρp)
          by (pose proof (a_inc_dom_sub Hincw) as Hs; clear - Hs Hnd; fsetdec).
        destruct (Hopt' ρp Hid' Hincw) as [ζ' [Hζ' Hie']].
        exists ((γ, τγ) :: ζ'). split.
        -- apply a_inc__flex; auto.
        -- assert (Heqc : msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp)
                         = (γ, τγ) :: msubst_compose ζ' ρp).
           { change (msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp))
               with ((γ, msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                     :: msubst_compose ((γ, τγ) :: ζ') ρp).
             rewrite (msubst_compose_cons_l_id τγ ζ' Hid' Hγw).
             change (msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
               with (msubst_lookup ((γ, τγ) :: ζ') γ).
             rewrite msubst_lookup_cons_eq. reflexivity. }
           rewrite Heqc.
           apply a_inc_equiv__flex; [ exact Hie' | ].
           apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτ.
  - (* head [γ̂ ≔ τdef] : Flex-Flex-Assign, the back-edge into part 1. *)
    inversion Hwf as [ | | γh τh Θh Hnd Hwfτd Hmτd Hwf0 | | | ]; subst.
    inversion Hinc as [ | | Θs ρs Θt γs τd τγ Hinc' Hwfτγ Hmτγ Heqd
                          [Heqγ Heqρ] Heqt | | | ]; subst.
    (* the substituted subjects and their facts, uniformly in the variable *)
    assert (Hgen : forall δ,
        a_flex_tvar ((γ ~ abind_flex_mono_def τdef) ++ Θ0') δ ->
        a_wf_ptyp Θ0' (subst_ptyp_in_ptyp τdef γ (ptyp_var_f δ)) /\
        mono_ptyp (subst_ptyp_in_ptyp τdef γ (ptyp_var_f δ)) /\
        Θ ⊢ (msubst_ptyp ρs (subst_ptyp_in_ptyp τdef γ (ptyp_var_f δ)))
          ≡ᵗ (msubst_lookup ((γ, τγ) :: ρs) δ)).
    { intros δ Hfδ. cbn [subst_ptyp_in_ptyp].
      match goal with
      | |- context [if ?s then _ else _] => destruct s as [-> | Hδγ]
      end.
      - repeat split;
          [ exact Hwfτd | exact Hmτd
          | rewrite msubst_lookup_cons_eq;
            apply a_tyequiv__sym; exact Heqd ].
      - assert (Hfδ' : a_flex_tvar Θ0' δ)
          by (eapply a_flex_tvar_strip_head; [ exact Hδγ | exact Hfδ ]).
        repeat split.
        + apply a_wf_ptyp__var. right. exact Hfδ'.
        + apply mono_ptyp__var.
        + rewrite (msubst_lookup_cons_neq τγ ρs Hδγ).
          cbn [msubst_ptyp].
          apply a_tyequiv__refl. apply mono_ptyp_lc.
          eapply a_inc_lookup_mono; exact Hinc'. }
    destruct (Hgen α Hfα) as [HwfAσ [HmAσ HeqAρ]].
    destruct (Hgen β Hfβ) as [HwfBσ [HmBσ HeqBρ]].
    clear Hgen.
    set (Aσ := subst_ptyp_in_ptyp τdef γ (ptyp_var_f α)) in *.
    set (Bσ := subst_ptyp_in_ptyp τdef γ (ptyp_var_f β)) in *.
    (* the sub-node's solution facts *)
    assert (HmA' : mono_ptyp (msubst_ptyp ρs Aσ))
      by (eapply mono_ptyp_msubst; [ exact Hinc' | exact HmAσ ]).
    assert (HmB' : mono_ptyp (msubst_ptyp ρs Bσ))
      by (eapply mono_ptyp_msubst; [ exact Hinc' | exact HmBσ ]).
    assert (HwfA' : a_wf_ptyp Θ (msubst_ptyp ρs Aσ))
      by (eapply a_wf_ptyp_msubst; [ exact HwfAσ | exact Hwf0 | exact Hinc' ]).
    assert (HwfB' : a_wf_ptyp Θ (msubst_ptyp ρs Bσ))
      by (eapply a_wf_ptyp_msubst; [ exact HwfBσ | exact Hwf0 | exact Hinc' ]).
    assert (HeqAB : Θ ⊢ (msubst_ptyp ρs Aσ) ≡ᵗ (msubst_ptyp ρs Bσ)).
    { eapply a_tyequiv__trans; [ exact HeqAρ | ].
      eapply a_tyequiv__trans; [ exact Heq | ].
      apply a_tyequiv__sym; exact HeqBρ. }
    assert (Hjoin0 : empty ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn (msubst_ptyp ρs Aσ))
                       ≈ (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ))).
    { apply tyequiv_mono_consis;
        [ exact HeqAB | exact Hwfth | exact HmA'
        | intros X HX; eapply a_wf_ptyp_ftv_tvarish;
            [ exact HwfA' | exact HX ] ]. }
    assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρs (ptyp_to_pskl Aσ)))
              ≈ (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ)))
      by (rewrite msubst_pskl_ptyp_to_pskl, pskl_to_uskl_ptyp; exact Hjoin0).
    assert (Hrs' : ad_refine_syn_f empty Θ empty
              (pskl_to_bskl_inh (msubst_pskl ρs (ptyp_to_pskl Bσ)))
              (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ))).
    { rewrite msubst_pskl_ptyp_to_pskl.
      replace (pskl_to_bskl_inh (ptyp_to_pskl (msubst_ptyp ρs Bσ)))
        with (pskl_to_bskl_inh (uskl_to_pskl (ptyp_to_uskl_syn (msubst_ptyp ρs Bσ))))
        by (rewrite uskl_to_pskl_ptyp; reflexivity).
      eapply ad_pat_consis_refine_syn_f_mono;
        [ apply consis_mono_refl;
            [ exact HmB'
            | intros X HX; eapply a_wf_ptyp_ftv_tvarish;
                [ exact HwfB' | exact HX ] ]
        | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmB'
        | clear; fsetdec
        | intros β0 τ0 Hb0; clear; fsetdec ]. }
    assert (Hrp' : ad_refine_pskl_f empty Θ empty
              (msubst_pskl ρs (ptyp_to_pskl Aσ))
              (bskl_to_pskl (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ)))).
    { rewrite msubst_pskl_ptyp_to_pskl.
      replace (ptyp_to_pskl (msubst_ptyp ρs Aσ))
        with (uskl_to_pskl (ptyp_to_uskl_syn (msubst_ptyp ρs Aσ)))
        by (apply uskl_to_pskl_ptyp).
      eapply ad_pat_consis_refine_pskl_f_mono;
        [ exact Hjoin0 | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmB'
        | clear; fsetdec
        | intros β0 τ0 Hb0; clear; fsetdec ]. }
    assert (Hpsi : (empty : atoms) [=] empty) by fsetdec.
    assert (HwfPA : Θ0' ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Aσ))
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfAσ).
    assert (HwfPB : Θ0' ⨟ empty ⊢ₚₛᵃ (ptyp_to_pskl Bσ))
      by (apply a_wf_ptyp_to_wf_pskl; exact HwfBσ).
    (* the measure: V constant (the back-edge unfolds a definition the
       solution had already unfolded), n one smaller. *)
    assert (Hlt : mu_lt
        (mu_consis Θ ρs (ptyp_to_pskl Bσ) (ptyp_to_pskl Aσ) Θ0')
        (mu_unify Θ ((γ, τγ) :: ρs) α β
                  ((γ ~ abind_flex_mono_def τdef) ++ Θ0'))).
    { unfold mu_consis, mu_unify. apply mu_lt_intro. right. split.
      - unfold V_consis, V_unify.
        rewrite (Vpskl_ptyp_to_pskl Θ ρs Aσ).
        rewrite (Vpskl_ptyp_to_pskl Θ ρs Bσ).
        unfold Aσ, Bσ.
        rewrite (@Vvar_backedge Θ ρs γ τdef τγ α Hwfth Heqd).
        rewrite (@Vvar_backedge Θ ρs γ τdef τγ β Hwfth Heqd).
        unfold Vvar, Vptyp; cbn [msubst_ptyp]; reflexivity.
      - left. simpl. lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH (add γ F) empty empty Θ0' (ptyp_to_pskl Bσ)
                   (ptyp_to_pskl Aσ) ρs Θ empty
                   (ptyp_to_bskl_syn (msubst_ptyp ρs Bσ))
                   eq_refl Hwf0 HwfPB HwfPA
                   ltac:(intros X HX; exfalso; clear - HX; fsetdec)
                   ltac:(repeat intro; fsetdec)
                   ltac:(repeat intro; fsetdec)
                   Hinc' Hwfth
                   ltac:(repeat intro; fsetdec)
                   Hpsi Hjoin' Hrs' Hrp')
      as [P1 [Θ1' [Hcons Hopt']]].
    exists ((γ ~ abind_flex_mono_def τdef) ++ Θ1'). split.
    { eapply a_unify__flex_assign;
        [ exact Hfα | exact Hfβ | exact Hcons ]. }
    intros ρ1 Hid Hinc1.
    inversion Hinc1 as [ | | Θp ρp Θq γp τd1 τ1 Hincp Hwf1p Hm1p Heq1p
                           [Heqγ1 Heqρ1] Heqt1 | | | ]; subst.
    apply is_id_msubst_inv in Hid as [Heqτ1 Hid']; subst τ1.
    (* the sub-derivation's own soundness: id-witness + target wf *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ _ Hcons
                Hwf0 HwfPB HwfPA
                ltac:(intros X HX; exfalso; clear - HX; fsetdec)
                ltac:(repeat intro; fsetdec)
                ltac:(repeat intro; fsetdec))
      as [[[w [Hidw Hincw]] _] [Hwf1' _]].
    assert (Hw : ρp = w) by (eapply is_id_inc_unique; eauto).
    subst w.
    assert (Hγw : γ `notin` dom ρp)
      by (pose proof (a_inc_dom_sub Hincw) as Hs; clear - Hs Hnd; fsetdec).
    destruct (Hopt' ρp Hid' Hincw) as [ζ' [Hζ' [Hie' _]]].
    exists ((γ, τγ) :: ζ'). split.
    + apply a_inc__flex_def; [ exact Hζ' | exact Hwfτγ | exact Hmτγ | ].
      (* the definition's image transports across the equivalent increments *)
      eapply a_tyequiv__trans; [ exact Heqd | ].
      rewrite <- (msubst_compose_id_ptyp Hwf0 Hwf1' Hid' Hincw Hζ' Hwfτd).
      eapply a_inc_equiv_msubst_ptyp;
        [ exact Hwfτd | exact Hie' | exact Hwf0
        | eapply a_inc_msubst_lc; exact Hinc'
        | eapply msubst_lc_compose;
            [ eapply a_inc_msubst_lc; exact Hζ'
            | eapply is_id_msubst_values_lc; exact Hidw ] ].
    + assert (Heqc : msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp)
                     = (γ, τγ) :: msubst_compose ζ' ρp).
      { change (msubst_compose ((γ, τγ) :: ζ') ((γ, ptyp_var_f γ) :: ρp))
          with ((γ, msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                :: msubst_compose ((γ, τγ) :: ζ') ρp).
        rewrite (msubst_compose_cons_l_id τγ ζ' Hid' Hγw).
        change (msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
          with (msubst_lookup ((γ, τγ) :: ζ') γ).
        rewrite msubst_lookup_cons_eq. reflexivity. }
      rewrite Heqc.
      apply a_inc_equiv__flex_def;
        [ exact Hie'
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτγ
        | exact Heqd ].
Qed.

(** Part 3 of the paper's proof (:2403-2559): assignment, by a walk of the
    context pair [Θ0 ∣ Ξ] ([n = |Ξ|+|Θ0|] on the skips, [k = |Θ0|] on
    Assign-Depend; the Assign-Assign back-edge re-enters part 1 with [V]
    constant and [n] one smaller). *)
(** Decidable equality of skeletons (for the UnivGhost-Id shape test). *)
Lemma pskl_eq_dec : forall (P Q : pskl), sumbool (P = Q) (P <> Q).
Proof.
  decide equality; solve [ apply Nat.eq_dec | apply eq_var ].
Qed.

Lemma assign_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  assign_complete_at m.
Proof.
  intros m IH. unfold assign_complete_at.
  intros F Θ0 Ξ α P ρ Θ Hm Hdecl Hwf Hfα HwfP Hnf Hdomξ Hinc Hwfth Hjoin.
  subst m.
  destruct Θ0 as [ | [γ b] Θ0' ].
  { exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb. }
  destruct b as [ | A | Q | | τdef ].
  - (* head [γ ~ tvar] RIGID. *)
    destruct (AtomSetProperties.In_dec γ (ftvar_in_pskl P)) as [Hγin | Hγni].
    + (* γ ∈ ftv(P) : NO RULE fires — the STUCK-CHECK (design doc §9.2,
         [paper-gap]: the paper never proves the walk cannot reach this
         head) refutes the solution.  [a_inc] peels γ before reaching α̂
         ([a_inc_tvar_inv]), so θα̂ is wf BELOW γ; γ survives the solution
         into θP ([rigid_survives_solution]) while the join confines the
         subject's rigid ftv to θα̂'s scope
         ([ad_pat_consis_rigid_ftv_rev_scoped]) — contradiction. *)
      exfalso.
      (* decompose the competing increment at the rigid head *)
      destruct (@a_inc_strip_decls_prefix Ξ ((γ, abind_tvar) :: Θ0') ρ Θ
                  Hdecl Hinc)
        as [ρa [ρb [Heqρ [Hdρa Hincb]]]].
      destruct (a_inc_tvar_inv Hincb)
        as [Ξv [Θt [HeqΘ [HsufΞv Hincb']]]].
      assert (Huq : uniq (Ξ ++ (γ, abind_tvar) :: Θ0'))
        by (apply a_wf_aenv_uniq; exact Hwf).
      assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
      assert (Hbγ : binds γ abind_tvar (Ξ ++ (γ, abind_tvar) :: Θ0')).
      { apply binds_app_3. left. reflexivity. }
      assert (HbγΘ : binds γ abind_tvar Θ)
        by (eapply a_inc_binds_tvar; [ exact Hinc | exact Hbγ ]).
      assert (HγΘt : γ `notin` dom Θt).
      { rewrite HeqΘ in HuqΘ. clear - HuqΘ.
        simpl_env in HuqΘ. solve_uniq. }
      (* θα̂ is well-formed in the truncated target Θt, below γ *)
      assert (Hfα0 : a_flex_tvar Θ0' α).
      { destruct Hfα as [Hb | [τ0 Hb]].
        - apply binds_cons_1 in Hb as [[_ Heq2] | Hb];
            [ discriminate Heq2 | left; exact Hb ].
        - apply binds_cons_1 in Hb as [[_ Heq2] | Hb];
            [ discriminate Heq2 | right; exists τ0; exact Hb ]. }
      assert (Hbtα0 : a_binds_tvar α Θ0')
        by (destruct Hfα0 as [Hb | [τ0 Hb]];
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]).
      assert (HαΘ0' : α `in` dom Θ0')
        by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
      assert (Hαρa : α `notin` dom ρa).
      { rewrite Hdρa. clear - Huq HαΘ0'.
        simpl_env in Huq. solve_uniq. }
      assert (Hwf2 : a_wf_aenv ((Ξ ++ (γ ~ abind_tvar)) ++ Θ0'))
        by (simpl_env; exact Hwf).
      assert (Hwf0' : a_wf_aenv Θ0')
        by (eapply a_wf_aenv_app_r; exact Hwf2).
      assert (Hwfα : a_wf_ptyp Θt (msubst_lookup ρ α)).
      { rewrite Heqρ. rewrite (msubst_lookup_app_notin ρa ρb Hαρa).
        eapply a_inc_lookup_wf;
          [ exact Hincb' | exact Hwf0' | exact Hbtα0 ]. }
      assert (Hftvα : ftvar_in_ptyp (msubst_lookup ρ α) [<=] dom Θt)
        by (apply a_wf_ptyp_ftv_dom; exact Hwfα).
      (* definitions visible in dom Θt are Θt's own, scoped to Θt *)
      assert (HwfΘt : a_wf_aenv Θt).
      { rewrite HeqΘ in Hwfth.
        assert (Hwtmp : a_wf_aenv ((Ξv ++ (γ ~ abind_tvar)) ++ Θt))
          by (simpl_env; simpl_env in Hwfth; exact Hwfth).
        eapply a_wf_aenv_app_r; exact Hwtmp. }
      assert (Hdefs : forall δ τ, binds δ (abind_flex_mono_def τ) Θ ->
                δ `in` dom Θt -> ftvar_in_ptyp τ [<=] dom Θt).
      { intros δ τ Hb HδD.
        assert (Hbt : binds δ (abind_flex_mono_def τ) Θt).
        { rewrite HeqΘ in Hb.
          assert (Hb2 : binds δ (abind_flex_mono_def τ)
                    ((Ξv ++ (γ ~ abind_tvar)) ++ Θt))
            by (simpl_env; simpl_env in Hb; exact Hb).
          apply binds_app_iff in Hb2.
          destruct Hb2 as [Hb2 | Hb2]; [ exfalso | exact Hb2 ].
          apply binds_In in Hb2.
          rewrite HeqΘ in HuqΘ.
          assert (Hu2 : uniq ((Ξv ++ (γ ~ abind_tvar)) ++ Θt))
            by (simpl_env; simpl_env in HuqΘ; exact HuqΘ).
          apply uniq_app_iff in Hu2. destruct Hu2 as [_ [_ Hdisj]].
          clear - Hdisj Hb2 HδD. unfold disjoint in Hdisj. fsetdec. }
        apply a_wf_ptyp_ftv_dom.
        eapply a_wf_aenv_binds_def_wf_local; [ exact HwfΘt | exact Hbt ]. }
      (* γ survives the solution into θP … *)
      assert (HγθP : γ `in` ftvar_in_pskl (msubst_pskl ρ P))
        by (eapply rigid_survives_solution;
            [ exact Hinc | exact Hwf | exact Hbγ | exact Hγin ]).
      (* … but the join confines the subject's rigid ftv to dom Θt *)
      assert (HγnS : γ `notin`
                ftvar_in_uskl (pskl_to_uskl (msubst_pskl ρ P))).
      { eapply ad_pat_consis_rigid_ftv_rev_scoped with (D := dom Θt);
          [ exact Hwfth | exact HbγΘ | exact HγΘt | exact Hdefs
          | exact Hjoin | ].
        pose proof (ftvar_in_bskl_syn
                      (ptyp_to_pskl (msubst_lookup ρ α))) as Hf1.
        pose proof (ftvar_in_ptyp_to_pskl (msubst_lookup ρ α)) as Hf2.
        clear - Hf1 Hf2 Hftvα. fsetdec. }
      pose proof (ftvar_in_uskl_pskl (msubst_pskl ρ P)) as Hf3.
      clear - HγnS HγθP Hf3. fsetdec.
    + (* γ ∉ ftv(P) — Assign-SkipRigid; the walk truncates the solution
         target (a_inc__tvar inserts a suffix), so the sub-solution's JOIN
         must be strengthened to the truncated target: the
         [join_pskl_downarrow_mono_scoped] + [ad_pat_consis_strengthen]
         normalization of the OPT twin [skip_tm_var_case]
         (prop_consis_complete.v:990).  TRUE, mechanical, heavy. *)
      admit.
  - (* head [x ~ var_typ A] : Assign-SkipTmVar.  TRUE; the EX twin of the
       CLOSED OPT case [skip_tm_var_case] (prop_consis_complete.v:990) —
       ⇓-normalize the competing increment below the middle, strengthen
       the join, recurse, rebuild with the semantic middle.  Heavy. *)
    admit.
  - (* head [x ~ var_skl Q] : Assign-SkipTmSkl; as SkipTmVar with ≡ˢ. *)
    admit.
  - (* head [γ̂] undefined flexible *)
    destruct (γ == α) as [-> | Hγα].
    + (* the head IS the subject α̂ *)
      destruct (pskl_eq_dec P (pskl_tophole (pskl_var_f α))) as [-> | HneP].
      * (* Assign-UnivGhost-Id : axiom, Θ1 = Θ0, Ξ forced nil. *)
        assert (HΞnil : Ξ = nil).
        { destruct Ξ as [ | [ξ bξ] Ξ' ]; [ reflexivity | exfalso ].
          assert (Hξ : ξ `in` ftvar_in_pskl (pskl_tophole (pskl_var_f α)))
            by (apply Hdomξ; simpl; fsetdec).
          simpl in Hξ.
          assert (Heqξ : ξ = α) by (clear - Hξ; fsetdec). subst ξ.
          pose proof (a_wf_aenv_uniq Hwf) as Hu.
          clear - Hu. simpl_env in Hu. solve_uniq. }
        subst Ξ. simpl_env in *.
        exists ((α ~ abind_flex_mono) ++ Θ0'). split.
        { apply a_assign__univ_ghost_id. }
        intros ρ1 Hid Hinc1. exists ρ.
        exact (opt_axiom_factor Hwf Hid Hinc1 Hinc).
      * (* Assign-SolveM.  TRUE; not yet closed.  The solution supplies the
           two premises the paper leaves implicit (design doc §9.2):
           occurs [α ∉ ftv P] (else ⇓[Θ](θP) strictly contains ⇓[Θ](θα̂)
           while the join forces them ≡ᵗ — a size contradiction) and
           [guess^TY(P) = (β̄; τ) with τ mono] (P joins against the MONOTYPE
           θα̂, so P has no ∀ under the erasure and every ghost sits at a
           monotype position).  The factoring ζ extends ρ with the guessed
           β̄ ↦ the corresponding subterms of θα̂. *)
        admit.
    + (* γ̂ ≠ α̂ : Assign-Depend (γ ∈ ftv P) / Assign-Skip (γ ∉ ftv P) *)
      assert (Hαγ : α <> γ) by auto.
      assert (Hwfmid : a_wf_aenv ((γ ~ abind_flex_mono) ++ Θ0'))
        by (eapply a_wf_aenv_app_r; exact Hwf).
      inversion Hwfmid as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
      assert (Hfα0 : a_flex_tvar Θ0' α)
        by (eapply a_flex_tvar_strip_head; [ exact Hαγ | exact Hfα ]).
      destruct (AtomSetProperties.In_dec γ (ftvar_in_pskl P)) as [Hγin | Hγni].
      * (* Assign-Depend : γ̂ moves to the tail of Ξ; pure re-association. *)
        assert (Hdecl' : a_decls (Ξ ++ (γ ~ abind_flex_mono)))
          by (apply a_decls_app;
              [ exact Hdecl | apply (a_decls__cons γ); apply a_decls__nil ]).
        assert (Hdomξ' : dom (Ξ ++ (γ ~ abind_flex_mono)) [<=] ftvar_in_pskl P)
          by (rewrite dom_app; simpl; clear - Hdomξ Hγin; fsetdec).
        assert (Hwf2 : a_wf_aenv ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0'))
          by (simpl_env; exact Hwf).
        assert (HwfP2 : ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
          by (simpl_env; exact HwfP).
        assert (Hnf2 : a_non_flex ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0') P)
          by (simpl_env; exact Hnf).
        assert (Hinc2 : ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0') ≤[ ρ ] Θ)
          by (simpl_env; exact Hinc).
        assert (Hlt : mu_lt (mu_assign Θ ρ α P (Ξ ++ (γ ~ abind_flex_mono)) Θ0')
                            (mu_assign Θ ρ α P Ξ ((γ ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_assign. apply mu_lt_intro. right. split; [ reflexivity | ].
          right. split.
          - rewrite length_app. simpl. lia.
          - right. split; [ reflexivity | simpl; lia ]. }
        destruct (IH _ Hlt) as [_ [_ HaIH]].
        destruct (HaIH F Θ0' (Ξ ++ (γ ~ abind_flex_mono)) α P ρ Θ eq_refl
                       Hdecl' Hwf2 Hfα0 HwfP2 Hnf2 Hdomξ' Hinc2 Hwfth Hjoin)
          as [Θ1 [Ha' Hopt']].
        exists Θ1. split.
        { apply a_assign__depend; [ exact Hαγ | exact Hγin | exact Ha' ]. }
        intros ρ1 Hid Hinc1.
        assert (Hinc1' : ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0') ≤[ ρ1 ] Θ1)
          by (simpl_env; exact Hinc1).
        destruct (Hopt' ρ1 Hid Hinc1') as [ζ [Hζ Hie]].
        exists ζ. split; [ exact Hζ | ].
        simpl_env in Hie. exact Hie.
      * (* Assign-Skip : γ̂ dropped from the walked context (mid-strip). *)
        destruct (a_inc_mid_strip_flex γ Θ0' Hdecl Hinc)
          as [ρa [τγ [ρb [Heqρ [Hdρa [Hincb Hincab]]]]]].
        assert (Hwf' : a_wf_aenv (Ξ ++ Θ0'))
          by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact Hwf ]).
        assert (HwfP' : (Ξ ++ Θ0') ⨟ empty ⊢ₚₛᵃ P)
          by (eapply ad_wf_pskl_strip_mid; [ exact HwfP | exact Hγni ]).
        assert (Hbw : forall (δ : atom) (bb : abind),
                  binds δ bb (Ξ ++ Θ0') ->
                  binds δ bb (Ξ ++ (γ ~ abind_flex_mono) ++ Θ0')).
        { intros δ bb Hb. unfold binds in *.
          apply in_app_or in Hb. apply in_or_app.
          destruct Hb as [Hb | Hb];
            [ left; exact Hb | right; simpl; right; exact Hb ]. }
        assert (Hnf' : a_non_flex (Ξ ++ Θ0') P).
        { destruct Hnf as [Hlc Hnfl]. split; [ exact Hlc | ].
          intro Hfl. apply Hnfl.
          inversion Hfl as [Θf δ Hb | Θf δ τ0 Hb]; subst;
            [ apply a_flex__var; apply Hbw; exact Hb
            | eapply a_flex__var_def; apply Hbw; exact Hb ]. }
        assert (HeqP : msubst_pskl (ρa ++ ρb) P = msubst_pskl ρ P).
        { rewrite Heqρ. apply msubst_pskl_agree. intros X HX.
          symmetry. apply msubst_lookup_mid_drop.
          clear - HX Hγni. intro; subst X; contradiction. }
        assert (Hlkα : msubst_lookup (ρa ++ ρb) α = msubst_lookup ρ α)
          by (rewrite Heqρ; symmetry; apply msubst_lookup_mid_drop; exact Hαγ).
        assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
                  (pskl_to_uskl (msubst_pskl (ρa ++ ρb) P))
                ≈ (pskl_to_bskl_syn (ptyp_to_pskl
                     (msubst_lookup (ρa ++ ρb) α))))
          by (rewrite HeqP, Hlkα; exact Hjoin).
        assert (Hlt : mu_lt (mu_assign Θ (ρa ++ ρb) α P Ξ Θ0')
                            (mu_assign Θ ρ α P Ξ
                                       ((γ ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_assign. apply mu_lt_intro. right. split.
          - unfold V_assign, Vpskl, Vvar. rewrite HeqP, Hlkα. reflexivity.
          - left. simpl. lia. }
        destruct (IH _ Hlt) as [_ [_ HaIH]].
        destruct (HaIH (add γ F) Θ0' Ξ α P (ρa ++ ρb) Θ eq_refl
                       Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hincab Hwfth Hjoin')
          as [Θ1' [Ha' Hopt']].
        exists ((γ ~ abind_flex_mono) ++ Θ1'). split.
        { apply a_assign__skip; [ exact Hαγ | exact Hγni | exact Ha' ]. }
        intros ρ1 Hid Hinc1.
        destruct (a_inc_mid_strip_flex γ Θ0' Hdecl Hinc1)
          as [ρ1a [τ1 [ρ1b [Heqρ1 [Hdρ1a [Hinc1b Hinc1ab]]]]]].
        rewrite Heqρ1 in Hid.
        apply Forall_app in Hid as [Hida Hidtail].
        pose proof (Forall_inv Hidtail) as Heγ1.
        pose proof (Forall_inv_tail Hidtail) as Hidb.
        unfold is_id_entry in Heγ1; simpl in Heγ1; subst τ1.
        assert (Hidab : is_id_msubst (ρ1a ++ ρ1b))
          by (apply Forall_app; split; assumption).
        destruct (a_assign_sound Ha' Hdecl Hwf' HwfP')
          as [[[w [Hidw Hincw]] _] _].
        assert (Hweq : w = ρ1a ++ ρ1b)
          by (eapply is_id_inc_unique;
              [ exact Hincw | exact Hidw | exact Hinc1ab | exact Hidab ]).
        subst w.
        destruct (Hopt' (ρ1a ++ ρ1b) Hidab Hincw) as [ζ' [Hζ' Hie']].
        (* facts about the dropped image τγ *)
        assert (Huqf : uniq (Ξ ++ (γ ~ abind_flex_mono) ++ Θ0'))
          by (apply a_wf_aenv_uniq; exact Hwf).
        assert (Hγρa : γ `notin` dom ρa)
          by (rewrite Hdρa; clear - Huqf; simpl_env in Huqf; solve_uniq).
        assert (Hlkγ : msubst_lookup ρ γ = τγ)
          by (rewrite Heqρ; rewrite msubst_lookup_app_notin by exact Hγρa;
              apply msubst_lookup_cons_eq).
        assert (Hmτγ : mono_ptyp τγ)
          by (rewrite <- Hlkγ; eapply a_inc_lookup_mono; exact Hinc).
        assert (Hbtγ : a_binds_tvar γ (Ξ ++ (γ ~ abind_flex_mono) ++ Θ0'))
          by (right; left; unfold binds; apply in_or_app; right; left;
              reflexivity).
        assert (Hwfτγ : a_wf_ptyp Θ τγ)
          by (rewrite <- Hlkγ;
              eapply a_inc_lookup_wf;
              [ exact Hinc | exact Hwf | exact Hbtγ ]).
        assert (Hγρ1a : γ `notin` dom ρ1a)
          by (rewrite Hdρ1a; clear - Huqf; simpl_env in Huqf; solve_uniq).
        assert (Hγρ1b : γ `notin` dom ρ1b)
          by (pose proof (a_inc_dom_sub Hinc1b) as Hs;
              clear - Hs Hnd; fsetdec).
        exists ((γ, τγ) :: ζ'). split.
        -- apply a_inc__flex; [ exact Hζ' | exact Hwfτγ | exact Hmτγ ].
        -- (* compute ζ ∘ ρ1 = (ζ' ∘ ρ1a) ++ (γ,τγ) :: (ζ' ∘ ρ1b), then
              mid-insert the matching flex pair *)
           assert (Heqc : msubst_compose ((γ, τγ) :: ζ')
                            (ρ1a ++ (γ, ptyp_var_f γ) :: ρ1b)
                        = msubst_compose ζ' ρ1a
                          ++ (γ, τγ) :: msubst_compose ζ' ρ1b).
           { rewrite msubst_compose_app. f_equal.
             - apply (msubst_compose_cons_l_id τγ ζ' Hida Hγρ1a).
             - change (msubst_compose ((γ, τγ) :: ζ')
                         ((γ, ptyp_var_f γ) :: ρ1b))
                 with ((γ, msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                       :: msubst_compose ((γ, τγ) :: ζ') ρ1b).
               rewrite (msubst_compose_cons_l_id τγ ζ' Hidb Hγρ1b).
               change (msubst_ptyp ((γ, τγ) :: ζ') (ptyp_var_f γ))
                 with (msubst_lookup ((γ, τγ) :: ζ') γ).
               rewrite msubst_lookup_cons_eq. reflexivity. }
           rewrite Heqρ1, Heqρ, Heqc.
           apply a_inc_equiv_mid_insert_flex;
             [ exact Hdecl
             | apply a_wf_aenv_uniq; exact Hwf'
             | exact Hdρa
             | rewrite dom_msubst_compose; exact Hdρ1a
             | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτγ
             | ].
           rewrite <- msubst_compose_app. exact Hie'.
  - (* head [γ̂ ≔ τdef] DEFINED : Assign-Assign, the back-edge into part 1
       over the merged context Ξ ++ Θ0' with both sides substituted by
       [τdef/γ̂].  TRUE; not yet closed.  Needs (a) the mid-strip of the
       DEFINED head off the competing increment (the flex_def twin of
       [a_inc_mid_strip_flex]) and (b) a transport of the competing JOIN
       across the ≡ˢ-rewrite [msubst ρ' (P[τdef/γ̂]) ≡ˢ msubst ρ P] of the
       SUBJECT — the general-skeleton analogue of the mono transport
       [tyequiv_mono_consis_transport]; neither helper exists yet.  The
       measure edge is verified: V constant ([Vpskl_backedge]), n one
       smaller (design doc §5.4, A3). *)
    admit.
Admitted.

(** Part 1 of the paper's proof (:2561-3167): consistency.  The special
    cases are peeled first (:2566-2580) — [P] or [P0] flexible → parts 2/3
    ([t] breaks the tie); [P0 = ◇] → GhostR (axiom); [P0 = ⊤◇.P0'] with [P]
    guarded → UnivGhostR ([V] decreases on the input side) — and the main
    dispatch is on the last rule of the declarative join derivation, each
    structural sub-node at strictly smaller [V]. *)
(** Decidability of "is a hatted variable of Θ" (the layer-0 dispatch). *)
Lemma a_flex_tvar_dec : forall Θ (δ : atom),
  a_flex_tvar Θ δ \/ ~ a_flex_tvar Θ δ.
Proof.
  induction Θ as [ | [x b] Θ' IHΘ ]; intros δ.
  - right. intros [Hb | [τ Hb]]; inversion Hb.
  - destruct (IHΘ δ) as [Hyes | Hno].
    { left. destruct Hyes as [Hb | [τ Hb]];
        [ left | right; exists τ ]; unfold binds in *; simpl; right; exact Hb. }
    destruct b as [ | A | Q | | τd ];
      try (destruct (δ == x) as [-> | Hne];
           [ | right; intros [Hb | [τ Hb]];
               apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
               solve [ exfalso; auto | discriminate Hbe
                     | apply Hno; solve [ left; exact Hb
                                        | right; exists τ; exact Hb ] ] ]).
    + (* x ~ tvar, δ = x *)
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    + (* x ~ var_typ, δ = x *)
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    + (* x ~ var_skl, δ = x *)
      right. intros [Hb | [τ Hb]];
        apply binds_cons_1 in Hb as [[Heq Hbe] | Hb];
        solve [ discriminate Hbe
              | apply Hno; solve [ left; exact Hb
                                 | right; exists τ; exact Hb ] ].
    + (* x ~ flex, δ = x *)
      left. left. left. reflexivity.
    + (* x ~ flex_def τd, δ = x *)
      left. right. exists τd. left. reflexivity.
Qed.

(** Layer-0 shape dispatch: a well-formed skeleton is a hatted variable of
    [Θ] or non-flex. *)
Lemma a_flex_shape_dec : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  (exists β, P = pskl_var_f β /\ a_flex_tvar Θ β) \/ a_non_flex Θ P.
Proof.
  intros Θ Δ P HwfP.
  pose proof (ad_wf_pskl_lc HwfP) as Hlc.
  destruct P as [ | n | δ | Pa Pb | Pb | | Pt ];
    try (right; split; [ exact Hlc | intro Hfl; solve [ inversion Hfl ] ]).
  destruct (a_flex_tvar_dec Θ δ) as [Hf | Hnf'].
  - left. exists δ. split; [ reflexivity | exact Hf ].
  - right. split; [ exact Hlc | ].
    intro Hfl. apply Hnf'.
    inversion Hfl; subst; [ left | right; eexists ]; eassumption.
Qed.

(** Part 1's MAIN DISPATCH (paper :2582-3167), by induction on the last rule
    of the declarative join derivation, ASSUMING the layer-0 special cases
    (flexible subject / flexible input / P0 = ◇ / P0 = ⊤◇ with P guarded)
    have been peeled by [consis_complete_step] below.  The induction (rather
    than a case analysis) is needed ONLY for the target-side definition
    unfolds [flex_r] — those keep the measure constant but shrink the join.
    All structural sub-nodes recurse through the measure hypothesis [IH]. *)
Lemma consis_complete_core : forall Ψ Θ S Qb,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qb ->
  forall F Δ1 Δ2 Θ0 P0 P ρ,
    (forall m', mu_lt m' (mu_consis Θ ρ P0 P Θ0) -> complete_at m') ->
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    S = pskl_to_uskl (msubst_pskl ρ P) ->
    a_non_flex Θ0 P ->
    a_non_flex Θ0 P0 ->
    P0 <> pskl_hole ->
    (forall P0', P0 = pskl_tophole P0' -> ~ guarded_pskl P) ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis F Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           ad_precise_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb)).
Proof.
  intros Ψ Θ S Qb Hj.
  induction Hj; intros F Δ1 Δ2 Θ0 PP0 PP ρ
    IH Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth
    HΨ HeqS HnfP HnfP0 HneP0hole Hnthg Hrs Hrp.
  (* ------------------------------------------------------------- unit *)
  - (* SUBJECT: PP = unit (var subjects are rigid, hence not unit). *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    2:{ (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    (* INPUT: PP0 = unit. *)
    destruct PP0 as [ | n0 | δ0 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    2:{ inversion Hrs. }
    2:{ (* var δ0 : rigid; a rigid variable does not refine to unit *)
      exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
            as Hcon; discriminate
      end. }
    2:{ inversion Hrs. }
    2:{ inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ exfalso; apply (Hnthg Pt0 eq_refl); apply guarded_pskl__unit. }
    (* both unit: the axiom node *)
    exists pskl_unit, Θ0. split.
    { apply a_consis__unit. }
    intros ρ1 Hid Hinc1. exists ρ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    cbn [pskl_to_bskl_syn msubst_bskl bskl_to_pskl].
    unfold ad_precise_f.
    apply ad_refine_syn_f_of_plain_no_hole; [ | simpl; exact I ].
    apply consis_precise_mono_join with (A := ptyp_unit) (Qb := bskl_unit);
      [ exact Hwfth | apply mono_ptyp__unit
      | intros X HX; simpl in HX; clear - HX; fsetdec
      | apply ad_pat_consis__unit; clear; fsetdec ].
  (* -------------------------------------------------------------- var *)
  - (* SUBJECT: PP = var δ with δ RIGID; forces X = δ, PP0 = var δ. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    assert (Hbtδ : binds δ abind_tvar Θ0).
    { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
      destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
        [ exfalso; clear - HΔ; fsetdec
        | exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          apply a_flex__var; exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          eapply a_flex__var_def; exact Hb ]. }
    assert (Hδρ : δ `notin` dom ρ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
    simpl in HeqS. inversion HeqS; subst X. clear HeqS.
    assert (HbtΘ : binds δ abind_tvar Θ)
      by (eapply a_inc_binds_tvar; eauto).
    (* INPUT: PP0 = var δ. *)
    destruct PP0 as [ | n0 | δ0 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso.
        inversion Hrs; subst.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    1:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso. inversion Hrs; subst.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr (a_wf_aenv_uniq Hwfth))
              as Hcon; discriminate
        end. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ exfalso; apply (Hnthg Pt0 eq_refl); apply guarded_pskl__var. }
    (* var δ0 rigid; the refinement forces δ0 = δ *)
    assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
    { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
      destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
        [ exfalso; clear - HΔ; fsetdec
        | exact Hb
        | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
          apply a_flex__var; exact Hb
        | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
          eapply a_flex__var_def; exact Hb ]. }
    assert (Hδρ0 : δ0 `notin` dom ρ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
    simpl in Hrs.
    assert (Heqδ : δ0 = δ).
    { inversion Hrs; subst.
      - reflexivity.
      - exfalso.
        match goal with
        | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
            assert (HbtΘ0' : binds δ0 abind_tvar Θ)
              by (eapply a_inc_binds_tvar; eauto);
            pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                          (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
        end.
      - exfalso.
        match goal with
        | Hbr : binds δ (abind_flex_mono_def _) Θ |- _ =>
            pose proof (binds_unique _ _ _ _ _ HbtΘ Hbr
                          (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
        end. }
    subst δ0.
    exists (pskl_var_f δ), Θ0. split.
    { apply a_consis__rigid. exact Hbtδ. }
    intros ρ1 Hid Hinc1. exists ρ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    unfold ad_precise_f.
    cbn [pskl_to_bskl_syn msubst_bskl].
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    rewrite (msubst_lookup_notin ρ Hδρ).
    apply ad_refine_syn_f_of_plain_no_hole;
      [ | apply pskl_to_bskl_inh_no_hole, ptyp_to_pskl_no_hole ].
    apply consis_precise_mono_join with (A := ptyp_var_f δ)
                                        (Qb := bskl_var_f δ);
      [ exact Hwfth | apply mono_ptyp__var
      | intros X HX; simpl in HX;
        assert (HXδ : X = δ) by (clear - HX; fsetdec); subst X;
        left; exact HbtΘ
      | apply ad_pat_consis__var; [ clear; fsetdec | left; exact HbtΘ ] ].
  (* ------------------------------------------------------------ arrow *)
  - (* C-Arrow (paper :2691-2775): two structural sub-nodes at strictly
       smaller V.  The second runs at the first's OUTPUT Θ1 with metasubst
       ζ1 (the first's factoring at the soundness ⊴ id-witness); its
       premises transport from ρ to ζ1 by the ≡ˢ-transport layer; the two
       factorings compose by [a_inc_equiv_glue]; the first component's
       precision transports from ζ1 to ζ2 the same way. *)
    match goal with
    | Hpm : ?x ⨟ _ ⊨ₛᵃ R1 ≈ _ |- _ => rename Hpm into Hj1
    end.
    match goal with
    | Hpm : ?x ⨟ _ ⊨ₛᵃ R2 ≈ _ |- _ => rename Hpm into Hj2
    end.
    match goal with
    | Hpe : Ψ [=] union _ _ |- _ => rename Hpe into HΨu
    end.
    assert (HΨ1e : Ψ1 [=] empty) by (clear - HΨ HΨu; fsetdec).
    assert (HΨ2e : Ψ2 [=] empty) by (clear - HΨ HΨu; fsetdec).
    (* SUBJECT: PP = arrow PPa PPb. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R1 R2. clear HeqS.
    assert (HwfPPa : Θ0 ⨟ empty ⊢ₚₛᵃ PPa) by (inversion HwfP; assumption).
    assert (HwfPPb : Θ0 ⨟ empty ⊢ₚₛᵃ PPb) by (inversion HwfP; assumption).
    assert (HlcP : lc_pskl (pskl_arrow PPa PPb))
      by (eapply ad_wf_pskl_lc; exact HwfP).
    (* INPUT: PP0 = arrow P0a P0b. *)
    destruct PP0 as [ | n0 | δ0 | P0a P0b | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ (* var δ0 : rigid; a rigid variable does not refine to an arrow *)
      exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr (a_wf_aenv_uniq Hwfth))
            as Hcon; discriminate
      end. }
    2:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ (* ⊤◇ input against a GUARDED (arrow) subject was peeled in layer 0d *)
      exfalso. apply (Hnthg Pt0 eq_refl).
      inversion HlcP; subst.
      apply guarded_pskl__arrow; assumption. }
    (* both arrows: invert the two refinements *)
    assert (HwfP0a : Θ0 ⨟ empty ⊢ₚₛᵃ P0a) by (inversion HwfP0; assumption).
    assert (HwfP0b : Θ0 ⨟ empty ⊢ₚₛᵃ P0b) by (inversion HwfP0; assumption).
    inversion Hrs; subst.
    match goal with
    | Ha : ad_refine_syn_f Δ1 Θ Δ1
             (pskl_to_bskl_inh (msubst_pskl ρ P0a)) Q1,
      Hb : ad_refine_syn_f Δ1 Θ Δ1
             (pskl_to_bskl_inh (msubst_pskl ρ P0b)) Q2 |- _ =>
        rename Ha into Hrs1; rename Hb into Hrs2
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_arrow (msubst_pskl ρ PPa) (msubst_pskl ρ PPb))
              (pskl_arrow (bskl_to_pskl Q1) (bskl_to_pskl Q2))) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Ha : ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ PPa) (bskl_to_pskl Q1),
      Hb : ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ PPb) (bskl_to_pskl Q2)
      |- _ =>
        rename Ha into Hrp1; rename Hb into Hrp2
    end.
    (* ---- first component, at (Θ0, ρ); V strictly drops ---- *)
    assert (Hlt1 : mu_lt (mu_consis Θ ρ P0a PPa Θ0)
                         (mu_consis Θ ρ (pskl_arrow P0a P0b)
                                        (pskl_arrow PPa PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      pose proof (Vpskl_arrow_lt1 Θ ρ PPa PPb).
      pose proof (Vpskl_arrow_lt1 Θ ρ P0a P0b). lia. }
    destruct (IH _ Hlt1) as [HcIH1 _].
    destruct (HcIH1 F Δ1 Δ2 Θ0 P0a PPa ρ Θ Ψ1 Q1 eq_refl Hwf0 HwfP0a HwfPPa
                    Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ1e Hj1 Hrs1 Hrp1)
      as [PA1 [Θ1 [Hc1 Hopt1]]].
    (* the first node's soundness: id-witness, wf, Δ-invariants *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ _ Hc1
                Hwf0 HwfP0a HwfPPa Hrig Hnfd0 Hfaf)
      as [Hle1 [Hwf1 [Hdom1 [Hfr1 [Hinv1 [Hsol1 _]]]]]].
    destruct Hle1 as [[w1 [Hidw1 Hincw1]] Hdefs1].
    destruct (Hopt1 w1 Hidw1 Hincw1) as [ζ1 [Hζ1 [Hie1 Hprec1]]].
    assert (HΔdom : (Δ1 `union` Δ2) [<=] (F `union` dom Θ0)).
    { intros X HX. pose proof (Hrig X HX) as Hb.
      apply binds_In in Hb. clear - Hb. fsetdec. }
    destruct (Hinv1 (Δ1 `union` Δ2) Hnfd0 Hfaf HΔdom
                ltac:(intros X HX HnX; exfalso; pose proof (Hrig X HX) as Hb;
                      apply binds_In in Hb; exact (HnX Hb)))
      as [Hnfd1 [Hfaf1 _]].
    assert (HrigΘ1 : forall X, X `in` (Δ1 `union` Δ2) ->
              binds X abind_tvar Θ1)
      by (intros X HX; eapply a_inc_binds_tvar;
          [ exact Hincw1 | apply Hrig; exact HX ]).
    assert (HwfP0b1 : Θ1 ⨟ empty ⊢ₚₛᵃ P0b).
    { eapply ad_wf_pskl_isub; [ exact HwfP0b | ].
      split; [ exists w1; split; assumption | exact Hdefs1 ]. }
    assert (HwfPPb1 : Θ1 ⨟ empty ⊢ₚₛᵃ PPb).
    { eapply ad_wf_pskl_isub; [ exact HwfPPb | ].
      split; [ exists w1; split; assumption | exact Hdefs1 ]. }
    (* ---- transport the second component's premises from ρ to ζ1 ---- *)
    assert (HawfPPb : a_wf_pskl Θ0 PPb).
    { eapply ad_wf_pskl_to_a_wf_pskl;
        [ exact HwfPPb | intros x b Hb; exact Hb
        | intros Y HY; exfalso; clear - HY; fsetdec ]. }
    assert (HawfP0b : a_wf_pskl Θ0 P0b).
    { eapply ad_wf_pskl_to_a_wf_pskl;
        [ exact HwfP0b | intros x b Hb; exact Hb
        | intros Y HY; exfalso; clear - HY; fsetdec ]. }
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hlcζ1 : msubst_lc ζ1) by (eapply a_inc_msubst_lc; exact Hζ1).
    assert (Hlcc1 : msubst_lc (msubst_compose ζ1 w1))
      by (apply msubst_lc_compose;
          [ exact Hlcζ1 | eapply is_id_msubst_values_lc; exact Hidw1 ]).
    assert (Heqb : Θ ⊢ (msubst_pskl ρ PPb) ≡ˢ (msubst_pskl ζ1 PPb)).
    { replace (msubst_pskl ζ1 PPb)
        with (msubst_pskl (msubst_compose ζ1 w1) PPb)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
            | exact Hζ1 | exact HawfPPb ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfPPb | exact Hie1 | exact Hwf0
        | exact Hlcρ | exact Hlcc1 ]. }
    assert (Heqb0 : Θ ⊢ (msubst_pskl ρ P0b) ≡ˢ (msubst_pskl ζ1 P0b)).
    { replace (msubst_pskl ζ1 P0b)
        with (msubst_pskl (msubst_compose ζ1 w1) P0b)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf0 | exact Hwf1 | exact Hidw1 | exact Hincw1
            | exact Hζ1 | exact HawfP0b ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfP0b | exact Hie1 | exact Hwf0
        | exact Hlcρ | exact Hlcc1 ]. }
    destruct (skl_tyequiv_consis_transport Heqb Hwfth
                (fun x b Hb => Hb)) as [Hjt _].
    assert (Hj2' : Ψ2 ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ζ1 PPb)) ≈ Q2)
      by (apply Hjt; exact Hj2).
    destruct (skl_tyequiv_refine_syn_f_transport Heqb0 Hwfth
                (fun x b Hb => Hb)) as [Hrst _].
    pose proof (Hrst _ _ _ Hrs2) as Hrs2'.
    destruct (skl_tyequiv_refine_pskl_f_transport Heqb Hwfth
                (fun x b Hb => Hb)) as [Hrpt _].
    pose proof (Hrpt _ _ _ Hrp2) as Hrp2'.
    (* ---- second component, at (Θ1, ζ1); V constant by M1 then drops --- *)
    assert (HVb : Vpskl Θ ζ1 PPb = Vpskl Θ ρ PPb).
    { transitivity (Vpskl Θ (msubst_compose ζ1 w1) PPb).
      - unfold Vpskl.
        erewrite (msubst_compose_id_pskl (P := PPb));
          [ reflexivity | exact Hwf0 | exact Hwf1 | exact Hidw1
          | exact Hincw1 | exact Hζ1 | exact HawfPPb ].
      - symmetry.
        eapply Vpskl_inc_equiv;
          [ exact Hie1 | exact Hwf0 | exact Hwfth | exact HawfPPb ]. }
    assert (HVb0 : Vpskl Θ ζ1 P0b = Vpskl Θ ρ P0b).
    { transitivity (Vpskl Θ (msubst_compose ζ1 w1) P0b).
      - unfold Vpskl.
        erewrite (msubst_compose_id_pskl (P := P0b));
          [ reflexivity | exact Hwf0 | exact Hwf1 | exact Hidw1
          | exact Hincw1 | exact Hζ1 | exact HawfP0b ].
      - symmetry.
        eapply Vpskl_inc_equiv;
          [ exact Hie1 | exact Hwf0 | exact Hwfth | exact HawfP0b ]. }
    assert (Hlt2 : mu_lt (mu_consis Θ ζ1 P0b PPb Θ1)
                         (mu_consis Θ ρ (pskl_arrow P0a P0b)
                                        (pskl_arrow PPa PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite HVb. rewrite HVb0.
      pose proof (Vpskl_arrow_lt2 Θ ρ PPa PPb).
      pose proof (Vpskl_arrow_lt2 Θ ρ P0a P0b). lia. }
    destruct (IH _ Hlt2) as [HcIH2 _].
    destruct (HcIH2 F Δ1 Δ2 Θ1 P0b PPb ζ1 Θ Ψ2 Q2 eq_refl Hwf1 HwfP0b1
                    HwfPPb1 HrigΘ1 Hnfd1 Hfaf1 Hζ1 Hwfth Hnfdth HΨ2e
                    Hj2' Hrs2' Hrp2')
      as [PA2 [Θ2 [Hc2 Hopt2]]].
    (* ---- assemble the node ---- *)
    exists (pskl_arrow PA1 PA2), Θ2. split.
    { eapply a_consis__arrow; [ exact Hc1 | exact Hc2 ]. }
    intros ρf Hidf Hincf.
    (* the second node's soundness id-witness *)
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ _ Hc2
                Hwf1 HwfP0b1 HwfPPb1 HrigΘ1 Hnfd1 Hfaf1)
      as [Hle2 [Hwf2 [Hdom2 [Hfr2 [Hinv2 [Hsol2 _]]]]]].
    destruct Hle2 as [[w2 [Hidw2 Hincw2]] Hdefs2].
    destruct (Hopt2 w2 Hidw2 Hincw2) as [ζ2 [Hζ2 [Hie2 Hprec2]]].
    (* the algorithm's composite id-witness IS w1 (uniqueness) *)
    assert (Heqw : w1 = ρf) by (eapply is_id_inc_unique; eauto).
    subst ρf.
    exists ζ2. split; [ exact Hζ2 | ]. split.
    { (* factoring composition *)
      eapply a_inc_equiv_glue with
        (Θmid := Θ1) (Θfin := Θ2) (ρ1b := w2) (ζ1 := ζ1);
        [ exact Hwf0 | exact Hwf1 | exact Hwf2 | exact Hwfth
        | exact Hidw1 | exact Hidw2
        | (* dom w1 ⊆ dom w2 : Θ0's flexes stay flexible in Θ1 *)
          intros α Hα;
          pose proof (a_inc_dom_flex Hincw1 Hα) as Hfα0';
          eapply a_inc_flex_dom; [ exact Hincw2 | exact Hwf1 | ];
          eapply (proj2 (proj2 a_assign_unify_consis_flex_preserve));
            [ exact Hc1 | exact Hfα0' ]
        | exact Hincw1 | exact Hincw2 | exact Hζ1 | exact Hζ2
        | exact Hie1 | exact Hie2 ]. }
    (* ---- precision: componentwise, first component ζ1 → ζ2 ---- *)
    assert (HawfPA1 : a_wf_pskl Θ1 PA1).
    { destruct Hsol1 as [Qt1 [HeqQt1 [Hjoin1s _]]].
      rewrite <- HeqQt1.
      eapply ad_pat_consis_target_wf; exact Hjoin1s. }
    assert (Hlcζ2 : msubst_lc ζ2) by (eapply a_inc_msubst_lc; exact Hζ2).
    assert (Hlcc2 : msubst_lc (msubst_compose ζ2 w2))
      by (apply msubst_lc_compose;
          [ exact Hlcζ2 | eapply is_id_msubst_values_lc; exact Hidw2 ]).
    assert (Heqζ : Θ ⊢ (msubst_pskl ζ1 PA1) ≡ˢ (msubst_pskl ζ2 PA1)).
    { replace (msubst_pskl ζ2 PA1)
        with (msubst_pskl (msubst_compose ζ2 w2) PA1)
        by (eapply msubst_compose_id_pskl;
            [ exact Hwf1 | exact Hwf2 | exact Hidw2 | exact Hincw2
            | exact Hζ2 | exact HawfPA1 ]).
      eapply a_inc_equiv_msubst_pskl;
        [ exact HawfPA1 | exact Hie2 | exact Hwf1
        | exact Hlcζ1 | exact Hlcc2 ]. }
    unfold ad_precise_f in Hprec1, Hprec2 |- *.
    rewrite !bskl_to_pskl_msubst_bskl in Hprec1, Hprec2.
    rewrite !bskl_to_pskl_pskl_to_bskl_syn in Hprec1, Hprec2.
    change (ad_refine_syn_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
      (bskl_arrow
         (pskl_to_bskl_inh
            (bskl_to_pskl (msubst_bskl ζ2 (pskl_to_bskl_syn PA1))))
         (pskl_to_bskl_inh
            (bskl_to_pskl (msubst_bskl ζ2 (pskl_to_bskl_syn PA2)))))
      (bskl_arrow (pskl_to_bskl_inh (bskl_to_pskl Q1))
                  (pskl_to_bskl_inh (bskl_to_pskl Q2)))).
    apply ad_refine_syn_f__arrow.
    + (* first component : transport the precision source ζ1 → ζ2 *)
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      destruct (skl_tyequiv_refine_syn_f_transport Heqζ Hwfth
                  (fun x b Hb => Hb)) as [Hpt _].
      apply Hpt. exact Hprec1.
    + (* second component : already at ζ2 *)
      rewrite bskl_to_pskl_msubst_bskl.
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      exact Hprec2.
  (* ------------------------------------------- forall_inh (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* --------------------------------------------- forall_inh_untagged *)
  - (* C-ForallInh (paper :2777-2851): open with a fresh rigid α added to
       Θ0, Δ1, Δ2; the recursive call goes through the μ-IH at strictly
       smaller V ([Vpskl_open] + the binder strip); L8 shapes its output
       as [(α~tvar) ++ Θ1] and L9 renames the single instance to the
       cofinite premise of [a_consis__forall_inh]. *)
    match goal with
    | Hpm : forall X, X `notin` _ -> _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ =>
        rename Hpm into Hjoin
    end.
    (* SUBJECT: PP = ∀ PPb. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.
    (* INPUT: PP0 = ∀ P0b. *)
    destruct PP0 as [ | n0 | δ0 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ (* rigid input var never refines to an inherited ∀ *)
      exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                        (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ (* ⊤◇ input: its guarded body never refines to an inherited ∀ *)
      exfalso.
      assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
      assert (Hgρ0 : guarded_pskl (msubst_pskl ρ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      inversion Hrs; subst.
      eapply ad_refine_syn_f_guarded_src_all_inh_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgρ0 ]. }
    (* both ∀ : invert the two refinements and the wf of the bodies *)
    inversion Hrs; subst.
    match goal with
    | Hn : forall X, X `notin` ?LA ->
             ad_refine_syn_f _ _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_all_syn (msubst_pskl ρ PPb))
              (pskl_all_syn (bskl_to_pskl Q))) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Hn : forall X, X `notin` ?LB ->
             ad_refine_pskl_f _ _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb0 : exists Lw0, forall X, X `notin` Lw0 ->
              Θ0 ⨟ (add X empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl P0b (pskl_var_f X))).
    { inversion HwfP0; subst. eexists. eassumption. }
    destruct Hwfb0 as [Lw0 Hwfb0].
    assert (Hwfb : exists Lw, forall X, X `notin` Lw ->
              Θ0 ⨟ (add X empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl PPb (pskl_var_f X))).
    { inversion HwfP; subst. eexists. eassumption. }
    destruct Hwfb as [Lw Hwfb].
    (* the fresh rigid α *)
    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw0 `union` Lw
                        `union` dom Θ0 `union` dom Θ `union` dom ρ
                        `union` F `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPb
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hαρ : α `notin` dom ρ) by (clear - Fr; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
    (* the measure strictly drops *)
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) ρ Pz
                            = Vpskl Θ ρ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) ρ
           (open_pskl_wrt_pskl P0b (pskl_var_f α))
           (open_pskl_wrt_pskl PPb (pskl_var_f α))
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ ρ (pskl_all_syn P0b) (pskl_all_syn PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open P0b Hwfth Hlcρ Hαρ HαΘ).
      rewrite (Vpskl_open PPb Hwfth Hlcρ Hαρ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ ρ P0b).
      pose proof (Vpskl_all_syn_lt Θ ρ PPb). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    (* premises of the opened problem *)
    assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (open_pskl_wrt_pskl P0b (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_to_tvar;
        [ apply Hwfb0; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl PPb (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_to_tvar;
        [ apply Hwfb; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (Hrig' : forall Z, Z `in` (add α Δ1 `union` add α Δ2) ->
              binds Z abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros Z HZ. destruct (Z == α) as [-> | Hne];
        [ unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hrig; clear - HZ Hne; fsetdec ]. }
    assert (Hnfd0' : no_flex_dep (add α Δ1 `union` add α Δ2)
                       ((α ~ abind_tvar) ++ Θ0)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwf0 | exact Hnfd0 | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hfaf' : flex_above_free (add α Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { eapply faf_cong;
        [ | eapply faf_open_tvar; [ exact Hfaf | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hinc' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ ]
                      ((α ~ abind_tvar) ++ Θ)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc).
      apply a_decls_suffix. apply a_decls__nil. }
    assert (Hwfth' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwfth ]).
    assert (Hnfdth' : no_flex_dep (add α Δ1 `union` add α Δ2)
                        ((α ~ abind_tvar) ++ Θ)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwfth | exact Hnfdth | exact HαΘ ] ].
      clear. fsetdec. }
    assert (Hjα : Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ
                 (open_pskl_wrt_pskl PPb (pskl_var_f α))))
              ≈ (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { pose proof (Hjoin α ltac:(clear - Fr; fsetdec)) as Hj0.
      rewrite (msubst_pskl_open_lc PPb Hlcρ Hαρ).
      rewrite pskl_to_uskl_open_var.
      exact Hj0. }
    assert (Hrsα : ad_refine_syn_f (add α Δ1) ((α ~ abind_tvar) ++ Θ)
              (add α Δ1)
              (pskl_to_bskl_inh (msubst_pskl ρ
                 (open_pskl_wrt_pskl P0b (pskl_var_f α))))
              (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { rewrite (msubst_pskl_open_lc P0b Hlcρ Hαρ).
      rewrite pskl_to_bskl_inh_open.
      eapply ad_refine_syn_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_syn_f_fextend_dom;
        [ apply Hrs1; clear - Fr; fsetdec | ].
      intros γ Hγ. destruct (γ == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hγ Hne; fsetdec ]. }
    assert (Hrpα : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ)
              (add α Δ2)
              (msubst_pskl ρ (open_pskl_wrt_pskl PPb (pskl_var_f α)))
              (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)))).
    { rewrite (msubst_pskl_open_lc PPb Hlcρ Hαρ).
      rewrite bskl_to_pskl_open.
      eapply ad_refine_pskl_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_pskl_f_fextend_dom;
        [ apply Hrp1; clear - Fr; fsetdec | ].
      intros γ Hγ. destruct (γ == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hγ Hne; fsetdec ]. }
    destruct (HcIH F (add α Δ1) (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
                (open_pskl_wrt_pskl P0b (pskl_var_f α))
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) ρ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα)
      as [P1 [Θ1' [Hc Hopt']]].
    (* L8 : the output re-attaches the rigid head *)
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _
                _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.
    (* assemble the cofinite node by renaming the α-instance (L9) *)
    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; fsetdec).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    { apply a_consis__forall_inh with
        (L := L `union` dom Θ0 `union` dom Θ1 `union` dom Θ
              `union` singleton α `union` F `union` Δ1 `union` Δ2
              `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPb
              `union` ftvar_in_pskl P1).
      intros X HX.
      assert (HXα : X <> α) by (clear - HX; fsetdec).
      assert (HXΘ0 : X `notin` dom Θ0) by (clear - HX; fsetdec).
      assert (HXΘ1 : X `notin` dom Θ1) by (clear - HX; fsetdec).
      assert (HXΔ1 : X `notin` Δ1) by (clear - HX; fsetdec).
      assert (HXΔ2 : X `notin` Δ2) by (clear - HX; fsetdec).
      assert (HXP0b : X `notin` ftvar_in_pskl P0b)
        by (clear - HX; fsetdec).
      assert (HXPPb : X `notin` ftvar_in_pskl PPb)
        by (clear - HX; fsetdec).
      assert (HXP1 : X `notin` ftvar_in_pskl P1)
        by (clear - HX; fsetdec).
      destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α X))
                  _ _ _ _ _ _ _ _ Hc nil Θ0 eq_refl tvar_prefix_nil
                  Huq0
                  ltac:(simpl; clear - HXΘ0 HXα; fsetdec)
                  ltac:(simpl; clear - HXΘ1 HXα; fsetdec)
                  ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          P0b (pskl_var_f α)) as Hup;
                        simpl in Hup;
                        clear - HXα HXP0b Hup; fsetdec)
                  ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          PPb (pskl_var_f α)) as Hup;
                        simpl in Hup;
                        clear - HXα HXPPb Hup; fsetdec)
                  ltac:(clear - HXP1; fsetdec)
                  ltac:(clear - HXα HXΔ1; fsetdec)
                  ltac:(clear - HXα HXΔ2; fsetdec))
        as [Θt [HeqΘt Hren]].
      simpl in HeqΘt. inversion HeqΘt. subst Θt.
      assert (Ho0 : open_pskl_wrt_pskl P0b (pskl_var_f X)
                  = subst_pskl_in_pskl (pskl_var_f X) α
                      (open_pskl_wrt_pskl P0b (pskl_var_f α)))
        by (apply subst_pskl_in_pskl_intro; clear - Fr; fsetdec).
      assert (Ho1 : open_pskl_wrt_pskl PPb (pskl_var_f X)
                  = subst_pskl_in_pskl (pskl_var_f X) α
                      (open_pskl_wrt_pskl PPb (pskl_var_f α)))
        by (apply subst_pskl_in_pskl_intro; clear - Fr; fsetdec).
      rewrite <- Ho0, <- Ho1 in Hren.
      rewrite (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α) in Hren.
      eapply (proj2 (proj2 a_assign_unify_consis_compat));
        [ exact Hren
        | intros γ Hγ; left; exact Hγ
        | apply rn_set_add_same; exact HαΔ1
        | apply rn_set_add_same; exact HαΔ2 ].
    }
    (* optimality *)
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ1 ]
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
      apply a_decls_suffix. apply a_decls__nil. }
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
    exists ζ.
    (* strip the rigid head off the algorithm-side increments *)
    assert (Hζ' : Θ1 ≤[ ζ ] Θ).
    { destruct (a_inc_tvar_inv Hζ) as [Ξs [Θ2 [HeqT [Hsuf Hinc2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hinc2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    assert (Hie' : a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ).
    { destruct (a_inc_equiv_tvar_inv Hie) as [Ξs [Θ2 [HeqT [Hsuf Hie2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hie2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    split; [ exact Hζ' | ]. split; [ exact Hie' | ].
    (* precision : rebind the quantifier *)
    assert (Hlcζ : msubst_lc ζ) by (eapply a_inc_msubst_lc; exact Hζ').
    assert (Huq1' : uniq ((α ~ abind_tvar) ++ Θ1))
      by (destruct (auc_uniq_consis Hc Huq0) as [Hu1 _]; exact Hu1).
    assert (HαΘ1 : α `notin` dom Θ1) by solve_uniq.
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Himg : forall γ τ, In (γ, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros γ τ Hin.
      pose proof (a_inc_images_ftv_dom Hζ' _ _ Hin) as Hsc.
      clear - Hsc HαΘ. fsetdec. }
    unfold ad_precise_f in Hprec |- *.
    rewrite bskl_to_pskl_msubst_bskl in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec |- *.
    change (ad_refine_syn_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
      (bskl_all_inh (pskl_to_bskl_inh
         (msubst_pskl ζ (close_pskl_wrt_pskl α P1))))
      (bskl_all_inh (pskl_to_bskl_inh (bskl_to_pskl Q)))).
    apply ad_refine_syn_f__all with
      (L := singleton α `union` dom Θ `union` dom Θ1
            `union` Δ1 `union` Δ2
            `union` ftvar_in_bskl Q `union` ftvar_in_pskl P1).
    intros X HX.
    assert (HXζ : X `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HX; fsetdec. }
    rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ HXζ).
    rewrite <- (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α).
    rewrite <- bskl_to_pskl_open.
    (* transport the α-instance: ctx-α to Δ, then rename α ↦ X *)
    pose proof (ad_refine_syn_f_ctx_to_delta Hprec nil Θ eq_refl
                  ltac:(clear; fsetdec)
                  (a_wf_aenv_uniq Hwfth')) as Hp1.
    simpl in Hp1.
    assert (HαF : α `in` (add α Δ1 `union` add α Δ2))
      by (clear; fsetdec).
    assert (Hdefsθ : forall β τ,
              binds β (abind_flex_mono_def τ) Θ ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hsc HαΘ. fsetdec. }
    pose proof (ad_refine_syn_f_rename X Hp1 HαF HαΘ Hdefsθ) as Hp2.
    rewrite !pskl_to_bskl_inh_subst_var in Hp2.
    rewrite (msubst_pskl_subst_var ζ P1 Hαζ HXζ Himg) in Hp2.
    rewrite bskl_to_pskl_subst_var in Hp2.
    assert (HoQ : open_bskl_wrt_bskl Q (bskl_var_f X)
                = subst_bskl_in_bskl (bskl_var_f X) α
                    (open_bskl_wrt_bskl Q (bskl_var_f α)))
      by (apply subst_bskl_in_bskl_intro; clear - Fr; fsetdec).
    rewrite <- HoQ in Hp2.
    eapply ad_refine_syn_f_fmono;
      [ | eapply ad_refine_syn_f_delta_mono; [ exact Hp2 | ] ].
    { clear - HαΔ1 HαΔ2. fsetdec. }
    { clear - HαΔ1 HαΔ2 HX. fsetdec. }
  (* ------------------------------------------- forall_syn (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* ------------------------------------------------------ forall_syn *)
  - (* C-ForallSyn (paper :2853-2926): as C-ForallInh with the opened α
       added to Δ2 only and the input ⊤◇.P0' carried unchanged (the
       Δ1-refinement's [tophole_fill] premise arrives ALREADY at the
       α-extended context). *)
    match goal with
    | Hpm : forall X, X `notin` _ -> _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ =>
        rename Hpm into Hjoin
    end.
    (* SUBJECT: PP = ∀ PPb. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.
    (* INPUT: PP0 = ⊤◇ Pt0 (a ∀-syn target only arises by tophole_fill) *)
    destruct PP0 as [ | n0 | δ0 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                        (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; apply HneP0hole; reflexivity. }
    (* invert the two refinements; wf of the pieces *)
    assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
    assert (Hwft0 : Θ0 ⨟ empty ⊢ₚₛᵃ Pt0) by (inversion HwfP0; assumption).
    inversion Hrs; subst.
    1:{ (* __tophole_remove : the guarded body would refine to a ∀-syn *)
      exfalso.
      assert (Hgρ0 : guarded_pskl (msubst_pskl ρ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      eapply ad_refine_syn_f_guarded_src_all_syn_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgρ0 ]. }
    match goal with
    | Hn : forall X, X `notin` ?LA ->
             ad_refine_syn_f _ _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_all_syn (msubst_pskl ρ PPb))
              (pskl_all_syn (bskl_to_pskl Q))) in Hrp.
    inversion Hrp; subst.
    match goal with
    | Hn : forall X, X `notin` ?LB ->
             ad_refine_pskl_f _ _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb : exists Lw, forall X, X `notin` Lw ->
              Θ0 ⨟ (add X empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl PPb (pskl_var_f X))).
    { inversion HwfP; subst. eexists. eassumption. }
    destruct Hwfb as [Lw Hwfb].
    (* the fresh rigid α *)
    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw
                        `union` dom Θ0 `union` dom Θ `union` dom ρ
                        `union` F `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl Pt0 `union` ftvar_in_pskl PPb
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hαρ : α `notin` dom ρ) by (clear - Fr; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) ρ Pz
                            = Vpskl Θ ρ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) ρ
           (pskl_tophole Pt0)
           (open_pskl_wrt_pskl PPb (pskl_var_f α))
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ ρ (pskl_tophole Pt0) (pskl_all_syn PPb) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open PPb Hwfth Hlcρ Hαρ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ ρ PPb). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (pskl_tophole Pt0)).
    { eapply ad_wf_pskl_weaken; [ | exact HwfP0 ].
      intros x b Hb. apply binds_cons_3. exact Hb. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl PPb (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_to_tvar;
        [ apply Hwfb; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (Hrig' : forall Z, Z `in` (Δ1 `union` add α Δ2) ->
              binds Z abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros Z HZ. destruct (Z == α) as [-> | Hne];
        [ unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hrig; clear - HZ Hne; fsetdec ]. }
    assert (Hnfd0' : no_flex_dep (Δ1 `union` add α Δ2)
                       ((α ~ abind_tvar) ++ Θ0)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwf0 | exact Hnfd0 | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hfaf' : flex_above_free (Δ1 `union` add α Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { eapply faf_cong;
        [ | eapply faf_open_tvar; [ exact Hfaf | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hinc' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ ]
                      ((α ~ abind_tvar) ++ Θ)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc).
      apply a_decls_suffix. apply a_decls__nil. }
    assert (Hwfth' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwfth ]).
    assert (Hnfdth' : no_flex_dep (Δ1 `union` add α Δ2)
                        ((α ~ abind_tvar) ++ Θ)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwfth | exact Hnfdth | exact HαΘ ] ].
      clear. fsetdec. }
    assert (Hjα : Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ
                 (open_pskl_wrt_pskl PPb (pskl_var_f α))))
              ≈ (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { pose proof (Hjoin α ltac:(clear - Fr; fsetdec)) as Hj0.
      rewrite (msubst_pskl_open_lc PPb Hlcρ Hαρ).
      rewrite pskl_to_uskl_open_var.
      exact Hj0. }
    assert (Hrsα : ad_refine_syn_f Δ1 ((α ~ abind_tvar) ++ Θ) Δ1
              (pskl_to_bskl_inh (msubst_pskl ρ (pskl_tophole Pt0)))
              (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { simpl. apply Hrs1. clear - Fr. fsetdec. }
    assert (Hrpα : ad_refine_pskl_f (add α Δ2) ((α ~ abind_tvar) ++ Θ)
              (add α Δ2)
              (msubst_pskl ρ (open_pskl_wrt_pskl PPb (pskl_var_f α)))
              (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)))).
    { rewrite (msubst_pskl_open_lc PPb Hlcρ Hαρ).
      rewrite bskl_to_pskl_open.
      eapply ad_refine_pskl_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_pskl_f_fextend_dom;
        [ apply Hrp1; clear - Fr; fsetdec | ].
      intros γ Hγ. destruct (γ == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hγ Hne; fsetdec ]. }
    destruct (HcIH F Δ1 (add α Δ2) ((α ~ abind_tvar) ++ Θ0)
                (pskl_tophole Pt0)
                (open_pskl_wrt_pskl PPb (pskl_var_f α)) ρ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα)
      as [P1 [Θ1' [Hc Hopt']]].
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _
                _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.
    (* assemble the cofinite node by renaming the α-instance (L9) *)
    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; fsetdec).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    { apply a_consis__forall_syn with
        (L := L `union` dom Θ0 `union` dom Θ1 `union` dom Θ
              `union` singleton α `union` F `union` Δ1 `union` Δ2
              `union` ftvar_in_pskl Pt0 `union` ftvar_in_pskl PPb
              `union` ftvar_in_pskl P1).
      intros X HX.
      assert (HXα : X <> α) by (clear - HX; fsetdec).
      assert (HXΘ0 : X `notin` dom Θ0) by (clear - HX; fsetdec).
      assert (HXΘ1 : X `notin` dom Θ1) by (clear - HX; fsetdec).
      assert (HXΔ1 : X `notin` Δ1) by (clear - HX; fsetdec).
      assert (HXΔ2 : X `notin` Δ2) by (clear - HX; fsetdec).
      assert (HXPt0 : X `notin` ftvar_in_pskl Pt0)
        by (clear - HX; fsetdec).
      assert (HXPPb : X `notin` ftvar_in_pskl PPb)
        by (clear - HX; fsetdec).
      assert (HXP1 : X `notin` ftvar_in_pskl P1)
        by (clear - HX; fsetdec).
      destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α X))
                  _ _ _ _ _ _ _ _ Hc nil Θ0 eq_refl tvar_prefix_nil
                  Huq0
                  ltac:(simpl; clear - HXΘ0 HXα; fsetdec)
                  ltac:(simpl; clear - HXΘ1 HXα; fsetdec)
                  ltac:(simpl; clear - HXα HXPt0; fsetdec)
                  ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          PPb (pskl_var_f α)) as Hup;
                        simpl in Hup;
                        clear - HXα HXPPb Hup; fsetdec)
                  ltac:(clear - HXP1; fsetdec)
                  ltac:(clear - HXα HXΔ1; fsetdec)
                  ltac:(clear - HXα HXΔ2; fsetdec))
        as [Θt [HeqΘt Hren]].
      simpl in HeqΘt. inversion HeqΘt. subst Θt.
      assert (Ht0 : subst_pskl_in_pskl (pskl_var_f X) α
                      (pskl_tophole Pt0) = pskl_tophole Pt0)
        by (apply subst_pskl_in_pskl_fresh_eq; simpl;
            clear - Fr; fsetdec).
      assert (Ho1 : open_pskl_wrt_pskl PPb (pskl_var_f X)
                  = subst_pskl_in_pskl (pskl_var_f X) α
                      (open_pskl_wrt_pskl PPb (pskl_var_f α)))
        by (apply subst_pskl_in_pskl_intro; clear - Fr; fsetdec).
      rewrite Ht0 in Hren. rewrite <- Ho1 in Hren.
      rewrite (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α) in Hren.
      eapply (proj2 (proj2 a_assign_unify_consis_compat));
        [ exact Hren
        | intros γ Hγ; left; exact Hγ
        | apply rn_set_notin; exact HαΔ1
        | apply rn_set_add_same; exact HαΔ2 ].
    }
    (* optimality *)
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ1 ]
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
      apply a_decls_suffix. apply a_decls__nil. }
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
    exists ζ.
    assert (Hζ' : Θ1 ≤[ ζ ] Θ).
    { destruct (a_inc_tvar_inv Hζ) as [Ξs [Θ2 [HeqT [Hsuf Hinc2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hinc2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    assert (Hie' : a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ).
    { destruct (a_inc_equiv_tvar_inv Hie) as [Ξs [Θ2 [HeqT [Hsuf Hie2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hie2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    split; [ exact Hζ' | ]. split; [ exact Hie' | ].
    (* precision : rebind the quantifier *)
    assert (Hlcζ : msubst_lc ζ) by (eapply a_inc_msubst_lc; exact Hζ').
    assert (Huq1' : uniq ((α ~ abind_tvar) ++ Θ1))
      by (destruct (auc_uniq_consis Hc Huq0) as [Hu1 _]; exact Hu1).
    assert (HαΘ1 : α `notin` dom Θ1) by solve_uniq.
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Himg : forall γ τ, In (γ, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros γ τ Hin.
      pose proof (a_inc_images_ftv_dom Hζ' _ _ Hin) as Hsc.
      clear - Hsc HαΘ. fsetdec. }
    unfold ad_precise_f in Hprec |- *.
    rewrite bskl_to_pskl_msubst_bskl in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec |- *.
    change (ad_refine_syn_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
      (bskl_all_inh (pskl_to_bskl_inh
         (msubst_pskl ζ (close_pskl_wrt_pskl α P1))))
      (bskl_all_inh (pskl_to_bskl_inh (bskl_to_pskl Q)))).
    apply ad_refine_syn_f__all with
      (L := singleton α `union` dom Θ `union` dom Θ1
            `union` Δ1 `union` Δ2
            `union` ftvar_in_bskl Q `union` ftvar_in_pskl P1).
    intros X HX.
    assert (HXζ : X `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HX; fsetdec. }
    rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ HXζ).
    rewrite <- (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α).
    rewrite <- bskl_to_pskl_open.
    pose proof (ad_refine_syn_f_ctx_to_delta Hprec nil Θ eq_refl
                  ltac:(clear; fsetdec)
                  (a_wf_aenv_uniq Hwfth')) as Hp1.
    simpl in Hp1.
    assert (HαF : α `in` (Δ1 `union` add α Δ2))
      by (clear; fsetdec).
    assert (Hdefsθ : forall β τ,
              binds β (abind_flex_mono_def τ) Θ ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hsc HαΘ. fsetdec. }
    pose proof (ad_refine_syn_f_rename X Hp1 HαF HαΘ Hdefsθ) as Hp2.
    rewrite !pskl_to_bskl_inh_subst_var in Hp2.
    rewrite (msubst_pskl_subst_var ζ P1 Hαζ HXζ Himg) in Hp2.
    rewrite bskl_to_pskl_subst_var in Hp2.
    assert (HoQ : open_bskl_wrt_bskl Q (bskl_var_f X)
                = subst_bskl_in_bskl (bskl_var_f X) α
                    (open_bskl_wrt_bskl Q (bskl_var_f α)))
      by (apply subst_bskl_in_bskl_intro; clear - Fr; fsetdec).
    rewrite <- HoQ in Hp2.
    eapply ad_refine_syn_f_fmono;
      [ | eapply ad_refine_syn_f_delta_mono; [ exact Hp2 | ] ].
    { clear - HαΔ1 HαΔ2. fsetdec. }
    { clear - HαΔ1 HαΔ2 HX. fsetdec. }
  (* ---------------------------------------------- ghostg (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* -------------------------------------------- topholeg (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* ------------------------------------------------------------- hole *)
  - (* C-Ghost (paper :2583-2613): subject ◇, axiom node [a_consis__ghost].
       The side condition [Δ2 ∩ ftv(P0) = ∅] is the rigid-ftv chase: a
       Δ2-variable of ftv(P0) would survive the metasubstitution
       ([msubst_pskl_ftv_keep]) and the competing Δ1-refinement
       right-to-left ([ad_refine_syn_f_rigid_ftv_rev]) into the join's
       fill, whose ftv the Δ2-refinement's hole rule excludes.  Precision
       IS the competing Δ1-refinement. *)
    rename H into HΨfill. rename H0 into HwfFill.
    (* SUBJECT: PP = ◇ (var subjects are rigid, their image a var). *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    (* the Δ2-refinement bounds the fill's free variables *)
    change (ad_refine_pskl_f Δ2 Θ Δ2 pskl_hole
              (bskl_to_pskl (pskl_to_bskl_inh P))) in Hrp.
    rewrite bskl_to_pskl_pskl_to_bskl_inh in Hrp.
    (* the ftv chase for the Ghost side condition *)
    assert (Hside : forall X, X `in` Δ2 -> X `notin` ftvar_in_pskl PP0).
    { intros X HinΔ2 HinP0.
      assert (HbX0 : binds X abind_tvar Θ0)
        by (apply Hrig; clear - HinΔ2; fsetdec).
      assert (HbX : binds X abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      assert (HXnd : X `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      assert (Hdefs : forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                                  X `notin` ftvar_in_ptyp τ).
      { intros β τ Hb. pose proof (Hnfdth _ _ Hb) as Hd.
        clear - Hd HinΔ2. fsetdec. }
      assert (HninP : X `notin` ftvar_in_pskl P).
      { inversion Hrp; subst.
        - (* hole : the Δ2-hygiene of the fill *)
          match goal with
          | Hint : AtomSetImpl.inter Δ2 (ftvar_in_pskl P) [=] empty |- _ =>
              clear - Hint HinΔ2; fsetdec
          end.
        - (* flex_r : the fill is a defined flexible, never the rigid X *)
          simpl.
          match goal with
          | Hbr : binds ?α0 (abind_flex_mono_def _) Θ |- _ =>
              assert (Hne : X <> α0)
                by (intro Heq; subst;
                    pose proof (binds_unique _ _ _ _ _ HbX Hbr
                                  (a_wf_aenv_uniq Hwfth)) as Hcon;
                    discriminate)
          end.
          clear - Hne; fsetdec. }
      assert (HinθP0 : X `in` ftvar_in_pskl (msubst_pskl ρ PP0))
        by (apply msubst_pskl_ftv_keep; assumption).
      assert (HninSrc : X `notin`
                ftvar_in_bskl (pskl_to_bskl_inh (msubst_pskl ρ PP0))).
      { eapply ad_refine_syn_f_rigid_ftv_rev;
          [ exact Hwfth | exact HbX | exact Hdefs | exact Hrs | ].
        pose proof (ftvar_in_bskl_inh P) as Hfe.
        clear - HninP Hfe. fsetdec. }
      pose proof (ftvar_in_bskl_inh (msubst_pskl ρ PP0)) as Hfe2.
      clear - HninSrc HinθP0 Hfe2. fsetdec. }
    exists PP0, Θ0. split.
    { apply a_consis__ghost.
      apply inter_empty_pointwise. exact Hside. }
    intros ρ1 Hid Hinc1. exists ρ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    (* precision: exactly the competing Δ1-refinement, F-extended to the
       Δ2 half by the hole-source Δ2-refinement's own target hygiene *)
    unfold ad_precise_f.
    rewrite bskl_to_pskl_msubst_bskl.
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    rewrite bskl_to_pskl_pskl_to_bskl_inh.
    eapply ad_refine_syn_f_delta_mono with (Δ0 := Δ1);
      [ | clear; fsetdec ].
    eapply ad_refine_syn_f_fextend_ftv; [ exact Hrs | ].
    intros γ Hγ.
    destruct (AtomSetProperties.In_dec γ Δ1) as [HγΔ1 | HγΔ1];
      [ left; exact HγΔ1 | right ].
    assert (HγΔ2 : γ `in` Δ2) by (clear - Hγ HγΔ1; fsetdec).
    assert (Hbγ : binds γ abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | ];
          apply Hrig; clear - HγΔ2; fsetdec).
    split.
    + assert (Hnq : γ `notin` ftvar_in_pskl P)
        by (eapply ad_refine_pskl_f_hole_src_target_ftv;
            [ exact Hrp | exact Hwfth
            | clear - HγΔ2; fsetdec | exact Hbγ ]).
      pose proof (ftvar_in_bskl_inh P) as Hfe.
      clear - Hnq Hfe. fsetdec.
    + intros β τ Hb.
      pose proof (Hnfdth β τ Hb) as Hi.
      clear - Hi HγΔ2. fsetdec.
  (* ---------------------------------------------------------- tophole *)
  - (* C-UnivGhost (paper :2928-2993): both sides strip one ⊤◇; wf forces
       the input to be a ⊤◇ as well (a guarded input's refinement target is
       guarded, never a ⊤◇); V drops by 2, recurse through the μ-IH. *)
    match goal with
    | Hpm : _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ => rename Hpm into Hj
    end.
    (* SUBJECT: PP = ⊤◇PPt (var subjects are rigid, their image a var). *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R. clear HeqS.
    assert (HgPPt : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPPt : Θ0 ⨟ empty ⊢ₚₛᵃ PPt) by (inversion HwfP; assumption).
    assert (HgρP : guarded_pskl (msubst_pskl ρ PPt))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (HlcQ : lc_bskl Q).
    { assert (Hlct : lc_bskl (bskl_tophole Q))
        by (eapply ad_refine_syn_f_lc_r; exact Hrs).
      inversion Hlct; assumption. }
    assert (HgQ : guarded_bskl Q).
    { eapply ad_pat_consis_guarded_r;
        [ exact Hj | exact Hwfth | reflexivity | exact HgρP | exact HlcQ ]. }
    (* INPUT: PP0 = ⊤◇P0t (every other head's target is not a ⊤◇). *)
    destruct PP0 as [ | n0 | δ0 | Pa0 Pb0 | Pb0 | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ (* var δ0 : rigid; a rigid variable does not refine to a ⊤◇ *)
      exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr (a_wf_aenv_uniq Hwfth))
            as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; apply HneP0hole; reflexivity. }
    (* PP0 = ⊤◇Pt0 : strip the ⊤◇ on all three judgments. *)
    assert (Hg0t : guarded_pskl Pt0) by (inversion HwfP0; assumption).
    assert (HwfP0t : Θ0 ⨟ empty ⊢ₚₛᵃ Pt0) by (inversion HwfP0; assumption).
    assert (Hgρ0 : guarded_pskl (msubst_pskl ρ Pt0))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
              (pskl_to_bskl_inh (msubst_pskl ρ Pt0)) Q).
    { eapply ad_refine_syn_f_tophole_keep_inv;
        [ exact Hwfth | | exact Hrs ].
      apply guarded_pskl_to_bskl_inh. exact Hgρ0. }
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl ρ PPt))
              (pskl_tophole (bskl_to_pskl Q))) in Hrp.
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl ρ PPt) (bskl_to_pskl Q))
      by (eapply ad_refine_pskl_f_tophole_keep_inv;
            [ exact Hwfth | exact HgρP | exact Hrp ]).
    assert (Hlt : mu_lt (mu_consis Θ ρ Pt0 PPt Θ0)
                        (mu_consis Θ ρ (pskl_tophole Pt0)
                                       (pskl_tophole PPt) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      pose proof (Vpskl_tophole_lt Θ ρ Pt0).
      pose proof (Vpskl_tophole_lt Θ ρ PPt). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH F Δ1 Δ2 Θ0 Pt0 PPt ρ Θ Ψ Q eq_refl Hwf0 HwfP0t HwfPPt
                   Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs' Hrp')
      as [P1 [Θ1 [Hc Hopt']]].
    exists (pskl_tophole P1), Θ1. split.
    { apply a_consis__univ_ghost. exact Hc. }
    intros ρ1 Hid Hinc1.
    destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    unfold ad_precise_f in *. simpl.
    apply ad_refine_syn_f__tophole_keep; [ | exact Hprec ].
    apply guarded_pskl_to_bskl_inh, guarded_bskl_to_pskl. exact HgQ.
  (* ------------------------------------------------------ tophole_inh *)
  - (* C-UnivGhost1 (paper :2995-3070): the input's ∀ opens with a fresh
       rigid α added to Θ0 and Δ1; the subject ⊤◇.PPt is carried
       unchanged through the μ-IH and the L9 rename. *)
    match goal with
    | Hpm : forall X, X `notin` _ -> _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ =>
        rename Hpm into Hjoin
    end.
    (* SUBJECT: PP = ⊤◇ PPt. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS. subst R. clear HeqS.
    (* INPUT: PP0 = ∀ P0b. *)
    destruct PP0 as [ | n0 | δ0 | P0a P0b | P0b | | Pt0 ]; simpl in Hrs.
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso; inversion Hrs. }
    1:{ exfalso.
      assert (Hbtδ0 : binds δ0 abind_tvar Θ0).
      { inversion HwfP0 as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP0 as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ0 : δ0 `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ0) in Hrs.
      simpl in Hrs.
      assert (HbtΘ0' : binds δ0 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      inversion Hrs; subst.
      match goal with
      | Hbr : binds δ0 (abind_flex_mono_def _) Θ |- _ =>
          pose proof (binds_unique _ _ _ _ _ HbtΘ0' Hbr
                        (a_wf_aenv_uniq Hwfth)) as Hcon; discriminate
      end. }
    1:{ exfalso; inversion Hrs. }
    2:{ exfalso; apply HneP0hole; reflexivity. }
    2:{ exfalso.
      assert (Hg0 : guarded_pskl Pt0) by (inversion HwfP0; assumption).
      assert (Hgρ0 : guarded_pskl (msubst_pskl ρ Pt0))
        by (eapply guarded_pskl_msubst_inc; eauto).
      inversion Hrs; subst.
      eapply ad_refine_syn_f_guarded_src_all_inh_absurd;
        [ exact Hwfth | eassumption
        | apply guarded_pskl_to_bskl_inh; exact Hgρ0 ]. }
    (* ∀ input, ⊤◇ subject : invert the refinements, wf pieces *)
    assert (HgP : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPt : Θ0 ⨟ empty ⊢ₚₛᵃ PPt) by (inversion HwfP; assumption).
    inversion Hrs; subst.
    match goal with
    | Hn : forall X, X `notin` ?LA ->
             ad_refine_syn_f _ _ _ _ _ |- _ => rename Hn into Hrs1
    end.
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl ρ PPt))
              (pskl_all_syn (bskl_to_pskl Q))) in Hrp.
    inversion Hrp; subst.
    1:{ (* __tophole_remove : the guarded subject body vs a ∀-syn *)
      exfalso.
      assert (HgρP : guarded_pskl (msubst_pskl ρ PPt))
        by (eapply guarded_pskl_msubst_inc; eauto).
      eapply ad_refine_pskl_f_guarded_src_all_syn_absurd;
        [ exact Hwfth | eassumption | exact HgρP ]. }
    match goal with
    | Hn : forall X, X `notin` ?LB ->
             ad_refine_pskl_f _ _ _ _ _ |- _ => rename Hn into Hrp1
    end.
    assert (Hwfb0 : exists Lw0, forall X, X `notin` Lw0 ->
              Θ0 ⨟ (add X empty) ⊢ₚₛᵃ
                (open_pskl_wrt_pskl P0b (pskl_var_f X))).
    { inversion HwfP0; subst. eexists. eassumption. }
    destruct Hwfb0 as [Lw0 Hwfb0].
    (* the fresh rigid α *)
    match type of Hrs1 with
    | forall _, _ `notin` ?LA -> _ =>
    match type of Hrp1 with
    | forall _, _ `notin` ?LB -> _ =>
      pick fresh α for (L `union` LA `union` LB `union` Lw0
                        `union` dom Θ0 `union` dom Θ `union` dom ρ
                        `union` F `union` Δ1 `union` Δ2
                        `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPt
                        `union` ftvar_in_bskl Q)
    end end.
    assert (Hlcρ : msubst_lc ρ) by (eapply a_inc_msubst_lc; exact Hinc).
    assert (Hαρ : α `notin` dom ρ) by (clear - Fr; fsetdec).
    assert (HαΘ : α `notin` dom Θ) by (clear - Fr; fsetdec).
    assert (HαΘ0 : α `notin` dom Θ0) by (clear - Fr; fsetdec).
    assert (HVeq : forall Pz, Vpskl ((α ~ abind_tvar) ++ Θ) ρ Pz
                            = Vpskl Θ ρ Pz)
      by (intro Pz; unfold Vpskl; rewrite aenv_msubst_tvar; reflexivity).
    assert (Hlt : mu_lt
        (mu_consis ((α ~ abind_tvar) ++ Θ) ρ
           (open_pskl_wrt_pskl P0b (pskl_var_f α))
           (pskl_tophole PPt)
           ((α ~ abind_tvar) ++ Θ0))
        (mu_consis Θ ρ (pskl_all_syn P0b) (pskl_tophole PPt) Θ0)).
    { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
      rewrite !HVeq.
      rewrite (Vpskl_open P0b Hwfth Hlcρ Hαρ HαΘ).
      pose proof (Vpskl_all_syn_lt Θ ρ P0b). lia. }
    destruct (IH _ Hlt) as [HcIH _].
    assert (Hwf0' : a_wf_aenv ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv__tvar; [ exact HαΘ0 | exact Hwf0 ]).
    assert (HwfP0α : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                       (open_pskl_wrt_pskl P0b (pskl_var_f α))).
    { eapply ad_wf_pskl_delta_to_tvar;
        [ apply Hwfb0; clear - Fr; fsetdec | clear; fsetdec ]. }
    assert (HwfPα : ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                      (pskl_tophole PPt)).
    { eapply ad_wf_pskl_weaken; [ | exact HwfP ].
      intros x b Hb. apply binds_cons_3. exact Hb. }
    assert (Hrig' : forall Z, Z `in` (add α Δ1 `union` Δ2) ->
              binds Z abind_tvar ((α ~ abind_tvar) ++ Θ0)).
    { intros Z HZ. destruct (Z == α) as [-> | Hne];
        [ unfold binds; left; reflexivity
        | apply binds_cons_3; apply Hrig; clear - HZ Hne; fsetdec ]. }
    assert (Hnfd0' : no_flex_dep (add α Δ1 `union` Δ2)
                       ((α ~ abind_tvar) ++ Θ0)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwf0 | exact Hnfd0 | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hfaf' : flex_above_free (add α Δ1 `union` Δ2)
                      ((α ~ abind_tvar) ++ Θ0)).
    { eapply faf_cong;
        [ | eapply faf_open_tvar; [ exact Hfaf | exact HαΘ0 ] ].
      clear. fsetdec. }
    assert (Hinc' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ ]
                      ((α ~ abind_tvar) ++ Θ)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc).
      apply a_decls_suffix. apply a_decls__nil. }
    assert (Hwfth' : a_wf_aenv ((α ~ abind_tvar) ++ Θ))
      by (apply a_wf_aenv__tvar; [ exact HαΘ | exact Hwfth ]).
    assert (Hnfdth' : no_flex_dep (add α Δ1 `union` Δ2)
                        ((α ~ abind_tvar) ++ Θ)).
    { eapply no_flex_dep_cong;
        [ | eapply no_flex_dep_open_tvar;
            [ exact Hwfth | exact Hnfdth | exact HαΘ ] ].
      clear. fsetdec. }
    assert (Hjα : Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ (pskl_tophole PPt)))
              ≈ (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { simpl. apply Hjoin. clear - Fr. fsetdec. }
    assert (Hrsα : ad_refine_syn_f (add α Δ1) ((α ~ abind_tvar) ++ Θ)
              (add α Δ1)
              (pskl_to_bskl_inh (msubst_pskl ρ
                 (open_pskl_wrt_pskl P0b (pskl_var_f α))))
              (open_bskl_wrt_bskl Q (bskl_var_f α))).
    { rewrite (msubst_pskl_open_lc P0b Hlcρ Hαρ).
      rewrite pskl_to_bskl_inh_open.
      eapply ad_refine_syn_f_weaken_ctx;
        [ | intros x b Hb; apply binds_cons_3; exact Hb ].
      eapply ad_refine_syn_f_fextend_dom;
        [ apply Hrs1; clear - Fr; fsetdec | ].
      intros γ Hγ. destruct (γ == α) as [-> | Hne];
        [ right; exact HαΘ | left; clear - Hγ Hne; fsetdec ]. }
    assert (Hrpα : ad_refine_pskl_f Δ2 ((α ~ abind_tvar) ++ Θ) Δ2
              (msubst_pskl ρ (pskl_tophole PPt))
              (bskl_to_pskl (open_bskl_wrt_bskl Q (bskl_var_f α)))).
    { simpl. rewrite bskl_to_pskl_open. apply Hrp1.
      clear - Fr. fsetdec. }
    destruct (HcIH F (add α Δ1) Δ2 ((α ~ abind_tvar) ++ Θ0)
                (open_pskl_wrt_pskl P0b (pskl_var_f α))
                (pskl_tophole PPt) ρ
                ((α ~ abind_tvar) ++ Θ) Ψ
                (open_bskl_wrt_bskl Q (bskl_var_f α))
                eq_refl Hwf0' HwfP0α HwfPα Hrig' Hnfd0' Hfaf' Hinc'
                Hwfth' Hnfdth' HΨ Hjα Hrsα Hrpα)
      as [P1 [Θ1' [Hc Hopt']]].
    destruct (proj2 (proj2 a_assign_unify_consis_tvar_prefix) _ _ _ _
                _ _ _ _ Hc ((α, abind_tvar) :: nil) Θ0 eq_refl
                (tvar_prefix_cons tvar_prefix_nil)) as [Θ1 HeqΘ1'].
    simpl in HeqΘ1'. subst Θ1'.
    (* assemble the cofinite node by renaming the α-instance (L9) *)
    assert (Huq0 : uniq ((α ~ abind_tvar) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf0').
    assert (HαΔ1 : α `notin` Δ1) by (clear - Fr; fsetdec).
    assert (HαΔ2 : α `notin` Δ2) by (clear - Fr; fsetdec).
    exists (pskl_all_syn (close_pskl_wrt_pskl α P1)), Θ1.
    split.
    { apply a_consis__univ_ghost1 with
        (L := L `union` dom Θ0 `union` dom Θ1 `union` dom Θ
              `union` singleton α `union` F `union` Δ1 `union` Δ2
              `union` ftvar_in_pskl P0b `union` ftvar_in_pskl PPt
              `union` ftvar_in_pskl P1).
      intros X HX.
      assert (HXα : X <> α) by (clear - HX; fsetdec).
      assert (HXΘ0 : X `notin` dom Θ0) by (clear - HX; fsetdec).
      assert (HXΘ1 : X `notin` dom Θ1) by (clear - HX; fsetdec).
      assert (HXΔ1 : X `notin` Δ1) by (clear - HX; fsetdec).
      assert (HXΔ2 : X `notin` Δ2) by (clear - HX; fsetdec).
      assert (HXP0b : X `notin` ftvar_in_pskl P0b)
        by (clear - HX; fsetdec).
      assert (HXPPt : X `notin` ftvar_in_pskl PPt)
        by (clear - HX; fsetdec).
      assert (HXP1 : X `notin` ftvar_in_pskl P1)
        by (clear - HX; fsetdec).
      destruct (proj2 (proj2 (a_assign_unify_consis_rename_tvar α X))
                  _ _ _ _ _ _ _ _ Hc nil Θ0 eq_refl tvar_prefix_nil
                  Huq0
                  ltac:(simpl; clear - HXΘ0 HXα; fsetdec)
                  ltac:(simpl; clear - HXΘ1 HXα; fsetdec)
                  ltac:(pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          P0b (pskl_var_f α)) as Hup;
                        simpl in Hup;
                        clear - HXα HXP0b Hup; fsetdec)
                  ltac:(simpl; clear - HXα HXPPt; fsetdec)
                  ltac:(clear - HXP1; fsetdec)
                  ltac:(clear - HXα HXΔ1; fsetdec)
                  ltac:(clear - HXα HXΔ2; fsetdec))
        as [Θt [HeqΘt Hren]].
      simpl in HeqΘt. inversion HeqΘt. subst Θt.
      assert (Ho0 : open_pskl_wrt_pskl P0b (pskl_var_f X)
                  = subst_pskl_in_pskl (pskl_var_f X) α
                      (open_pskl_wrt_pskl P0b (pskl_var_f α)))
        by (apply subst_pskl_in_pskl_intro; clear - Fr; fsetdec).
      assert (Ht0 : subst_pskl_in_pskl (pskl_var_f X) α
                      (pskl_tophole PPt) = pskl_tophole PPt)
        by (apply subst_pskl_in_pskl_fresh_eq; simpl;
            clear - Fr; fsetdec).
      rewrite <- Ho0 in Hren. rewrite Ht0 in Hren.
      rewrite (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α) in Hren.
      eapply (proj2 (proj2 a_assign_unify_consis_compat));
        [ exact Hren
        | intros γ Hγ; left; exact Hγ
        | apply rn_set_add_same; exact HαΔ1
        | apply rn_set_notin; exact HαΔ2 ].
    }
    (* optimality *)
    intros ρ1 Hid Hinc1.
    assert (Hinc1' : ((α ~ abind_tvar) ++ Θ0) ≤[ ρ1 ]
                       ((α ~ abind_tvar) ++ Θ1)).
    { apply (a_inc__tvar (Ξ:=nil) α Hinc1).
      apply a_decls_suffix. apply a_decls__nil. }
    destruct (Hopt' ρ1 Hid Hinc1') as [ζ [Hζ [Hie Hprec]]].
    exists ζ.
    assert (Hζ' : Θ1 ≤[ ζ ] Θ).
    { destruct (a_inc_tvar_inv Hζ) as [Ξs [Θ2 [HeqT [Hsuf Hinc2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hinc2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    assert (Hie' : a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ).
    { destruct (a_inc_equiv_tvar_inv Hie) as [Ξs [Θ2 [HeqT [Hsuf Hie2]]]].
      destruct Ξs as [ | [y b] Ξs' ]; simpl in HeqT.
      - inversion HeqT; subst. exact Hie2.
      - injection HeqT. intros HeqΘtail Heqb Heqy. exfalso.
        rewrite HeqΘtail in HαΘ.
        repeat rewrite dom_app in HαΘ. simpl dom in HαΘ.
        clear - HαΘ. fsetdec. }
    split; [ exact Hζ' | ]. split; [ exact Hie' | ].
    assert (Hlcζ : msubst_lc ζ) by (eapply a_inc_msubst_lc; exact Hζ').
    assert (Huq1' : uniq ((α ~ abind_tvar) ++ Θ1))
      by (destruct (auc_uniq_consis Hc Huq0) as [Hu1 _]; exact Hu1).
    assert (HαΘ1 : α `notin` dom Θ1) by solve_uniq.
    assert (Hαζ : α `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HαΘ1; fsetdec. }
    assert (Himg : forall γ τ, In (γ, τ) ζ -> α `notin` ftvar_in_ptyp τ).
    { intros γ τ Hin.
      pose proof (a_inc_images_ftv_dom Hζ' _ _ Hin) as Hsc.
      clear - Hsc HαΘ. fsetdec. }
    unfold ad_precise_f in Hprec |- *.
    rewrite bskl_to_pskl_msubst_bskl in Hprec |- *.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec |- *.
    change (ad_refine_syn_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
      (bskl_all_inh (pskl_to_bskl_inh
         (msubst_pskl ζ (close_pskl_wrt_pskl α P1))))
      (bskl_all_inh (pskl_to_bskl_inh (bskl_to_pskl Q)))).
    apply ad_refine_syn_f__all with
      (L := singleton α `union` dom Θ `union` dom Θ1
            `union` Δ1 `union` Δ2
            `union` ftvar_in_bskl Q `union` ftvar_in_pskl P1).
    intros X HX.
    assert (HXζ : X `notin` dom ζ).
    { intro Hin.
      destruct (a_inc_dom_flex Hζ' Hin) as [Hb | [τ Hb]];
        apply binds_In in Hb; clear - Hb HX; fsetdec. }
    rewrite <- !pskl_to_bskl_inh_open.
    rewrite <- (msubst_pskl_open_lc (close_pskl_wrt_pskl α P1) Hlcζ HXζ).
    rewrite <- (subst_pskl_in_pskl_spec P1 (pskl_var_f X) α).
    rewrite <- bskl_to_pskl_open.
    pose proof (ad_refine_syn_f_ctx_to_delta Hprec nil Θ eq_refl
                  ltac:(clear; fsetdec)
                  (a_wf_aenv_uniq Hwfth')) as Hp1.
    simpl in Hp1.
    assert (HαF : α `in` (add α Δ1 `union` Δ2))
      by (clear; fsetdec).
    assert (Hdefsθ : forall β τ,
              binds β (abind_flex_mono_def τ) Θ ->
              α `notin` ftvar_in_ptyp τ).
    { intros β τ Hb.
      assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
        by (eapply a_wf_aenv_def_ftv_dom; eassumption).
      clear - Hsc HαΘ. fsetdec. }
    pose proof (ad_refine_syn_f_rename X Hp1 HαF HαΘ Hdefsθ) as Hp2.
    rewrite !pskl_to_bskl_inh_subst_var in Hp2.
    rewrite (msubst_pskl_subst_var ζ P1 Hαζ HXζ Himg) in Hp2.
    rewrite bskl_to_pskl_subst_var in Hp2.
    assert (HoQ : open_bskl_wrt_bskl Q (bskl_var_f X)
                = subst_bskl_in_bskl (bskl_var_f X) α
                    (open_bskl_wrt_bskl Q (bskl_var_f α)))
      by (apply subst_bskl_in_bskl_intro; clear - Fr; fsetdec).
    rewrite <- HoQ in Hp2.
    eapply ad_refine_syn_f_fmono;
      [ | eapply ad_refine_syn_f_delta_mono; [ exact Hp2 | ] ].
    { clear - HαΔ1 HαΔ2. fsetdec. }
    { clear - HαΔ1 HαΔ2 HX. fsetdec. }
  (* ----------------------------------------------------- tophole_drop *)
  - (* C-UnivGhost2 (paper :3072-3164): the subject strips its ⊤◇; the
       guarded subject body makes the join target Q guarded, which drives
       BOTH sub-cases: input ⊤◇P0t (strip on all three, [univ_ghost]) or
       input guarded (subject-only strip, [univ_ghost2]). *)
    match goal with
    | Hpm : _ ⨟ _ ⊨ₛᵃ _ ≈ _ |- _ => rename Hpm into Hj
    end.
    (* SUBJECT: PP = ⊤◇PPt. *)
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    { (* var δ : rigid, its image is δ itself *)
      exfalso.
      assert (Hbtδ : binds δ abind_tvar Θ0).
      { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
        destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
          [ exfalso; clear - HΔ; fsetdec
          | exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            apply a_flex__var; exact Hb
          | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
            eapply a_flex__var_def; exact Hb ]. }
      assert (Hδρ : δ `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
      simpl in HeqS. discriminate. }
    inversion HeqS; subst R. clear HeqS.
    assert (HgPPt : guarded_pskl PPt) by (inversion HwfP; assumption).
    assert (HwfPPt : Θ0 ⨟ empty ⊢ₚₛᵃ PPt) by (inversion HwfP; assumption).
    assert (HgρP : guarded_pskl (msubst_pskl ρ PPt))
      by (eapply guarded_pskl_msubst_inc; eauto).
    assert (HlcQ : lc_bskl Q) by (eapply ad_refine_syn_f_lc_r; exact Hrs).
    assert (HgQ : guarded_bskl Q).
    { eapply ad_pat_consis_guarded_r;
        [ exact Hj | exact Hwfth | reflexivity | exact HgρP | exact HlcQ ]. }
    (* the subject-side refinement drops its ⊤◇ against the guarded Q *)
    change (ad_refine_pskl_f Δ2 Θ Δ2
              (pskl_tophole (msubst_pskl ρ PPt)) (bskl_to_pskl Q)) in Hrp.
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl ρ PPt) (bskl_to_pskl Q)).
    { eapply ad_refine_pskl_f_tophole_guarded_inv;
        [ exact Hwfth | exact Hrp | ].
      apply guarded_bskl_to_pskl. exact HgQ. }
    (* INPUT: split on whether PP0 is a ⊤◇. *)
    assert (Hthdec : (exists P0t, PP0 = pskl_tophole P0t) \/
                     (forall P0t, PP0 <> pskl_tophole P0t)).
    { destruct PP0; try (right; intros ? Hc0; discriminate).
      left; eexists; reflexivity. }
    destruct Hthdec as [[P0t ->] | Hnth0].
    + (* PP0 = ⊤◇P0t : paper :3098-3132; both inputs strip, [univ_ghost]. *)
      assert (Hg0t : guarded_pskl P0t) by (inversion HwfP0; assumption).
      assert (HwfP0t : Θ0 ⨟ empty ⊢ₚₛᵃ P0t) by (inversion HwfP0; assumption).
      change (ad_refine_syn_f Δ1 Θ Δ1
                (bskl_tophole (pskl_to_bskl_inh (msubst_pskl ρ P0t))) Q)
        in Hrs.
      assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
                (pskl_to_bskl_inh (msubst_pskl ρ P0t)) Q)
        by (eapply ad_refine_syn_f_tophole_guarded_inv; eauto).
      assert (Hlt : mu_lt (mu_consis Θ ρ P0t PPt Θ0)
                          (mu_consis Θ ρ (pskl_tophole P0t)
                                         (pskl_tophole PPt) Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
        pose proof (Vpskl_tophole_lt Θ ρ P0t).
        pose proof (Vpskl_tophole_lt Θ ρ PPt). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH F Δ1 Δ2 Θ0 P0t PPt ρ Θ Ψ Q eq_refl Hwf0 HwfP0t HwfPPt
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs' Hrp')
        as [P1 [Θ1 [Hc Hopt']]].
      exists (pskl_tophole P1), Θ1. split.
      { apply a_consis__univ_ghost. exact Hc. }
      intros ρ1 Hid Hinc1.
      destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      unfold ad_precise_f in *. simpl.
      apply ad_refine_syn_f__tophole_remove. exact Hprec.
    + (* PP0 guarded : paper :3134-3163; subject-only strip, [univ_ghost2]. *)
      assert (Hg0 : guarded_pskl PP0).
      { destruct PP0 as [ | n0 | δ0 | Pa0 Pb0 | Pb0 | | Pt0 ].
        - apply guarded_pskl__unit.
        - inversion HwfP0.
        - apply guarded_pskl__var.
        - pose proof (ad_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption.
        - (* ∀ : an inherited quantifier never refines to the guarded Q *)
          exfalso. simpl in Hrs.
          eapply ad_refine_syn_f_all_inh_guarded_absurd;
            [ exact Hwfth | exact Hrs | exact HgQ ].
        - exfalso; apply HneP0hole; reflexivity.
        - exfalso; eapply Hnth0; reflexivity. }
      assert (Hlt : mu_lt (mu_consis Θ ρ PP0 PPt Θ0)
                          (mu_consis Θ ρ PP0 (pskl_tophole PPt) Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left. unfold V_consis.
        pose proof (Vpskl_tophole_lt Θ ρ PPt). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH F Δ1 Δ2 Θ0 PP0 PPt ρ Θ Ψ Q eq_refl Hwf0 HwfP0 HwfPPt
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hj Hrs Hrp')
        as [P1 [Θ1 [Hc Hopt']]].
      exists P1, Θ1. split.
      { apply a_consis__univ_ghost2;
          [ exact Hg0 | exact HnfP0 | exact Hc ]. }
      exact Hopt'.
  (* ----------------------------------------------- flex_l (impossible) *)
  - (* The subject is non-flex, so a variable subject is RIGID in Θ0 and
       stays rigid in Θ — it cannot be the defined flexible the join's
       left lookup unfolds. *)
    exfalso.
    destruct PP as [ | n | δ | PPa PPb | PPb | | PPt ];
      simpl in HeqS; try discriminate.
    assert (Hbtδ : binds δ abind_tvar Θ0).
    { inversion HwfP as [ | Θw Δw δw Hbt | | | | ]; subst.
      destruct Hbt as [HΔ | [Hb | [Hb | [τ0 Hb]]]];
        [ exfalso; clear - HΔ; fsetdec
        | exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          apply a_flex__var; exact Hb
        | exfalso; destruct HnfP as [_ Hnfl]; apply Hnfl;
          eapply a_flex__var_def; exact Hb ]. }
    assert (Hδρ : δ `notin` dom ρ)
      by (eapply a_inc_tvar_notin_dom; eauto).
    rewrite (msubst_lookup_notin ρ Hδρ) in HeqS.
    simpl in HeqS. inversion HeqS; subst α.
    assert (HbtΘ : binds δ abind_tvar Θ)
      by (eapply a_inc_binds_tvar; eauto).
    pose proof (binds_unique _ _ _ _ _ HbtΘ H (a_wf_aenv_uniq Hwfth))
      as Hcon; discriminate.
  (* ----------------------------------------------------------- flex_r *)
  - (* Target-side definition unfold [Qb = α̂ ≔ τ]: the join shrinks while
       the measure stands still — this is exactly why the core INDUCTS on
       the join.  Transport Hrs/Hrp through the unfold
       ([ad_refine_syn_f_flex_target_unfold] and its uncoloured twin, fed
       by the [no_flex_dep] invariant), recurse on the premise via [IHHj],
       and re-attach the [α̂]-target to the resulting precision by
       [ad_refine_syn__flex_r]. *)
    match goal with
    | Hb : binds _ (abind_flex_mono_def _) _ |- _ => rename Hb into Hbα
    end.
    assert (Hmτ : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hdisj : AtomSetImpl.inter (Δ1 `union` Δ2) (ftvar_in_ptyp τ)
                      [=] empty)
      by (apply (Hnfdth _ _ Hbα)).
    assert (HΔbt : forall X, X `in` (Δ1 `union` Δ2) ->
                             binds X abind_tvar Θ).
    { intros X HX. eapply a_inc_binds_tvar; [ exact Hinc | ].
      apply Hrig. exact HX. }
    (* transport the two refinement witnesses through the unfold *)
    assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
              (pskl_to_bskl_inh (msubst_pskl ρ PP0)) (ptyp_to_bskl_syn τ)).
    { eapply ad_refine_syn_f_flex_target_unfold;
        [ exact Hwfth | exact Hbα
        | intros X HX; apply HΔbt; clear - HX; fsetdec
        | clear - Hdisj; fsetdec
        | exact Hrs ]. }
    assert (Hrp' : ad_refine_pskl_f Δ2 Θ Δ2
              (msubst_pskl ρ PP) (bskl_to_pskl (ptyp_to_bskl_syn τ))).
    { unfold ptyp_to_bskl_syn.
      rewrite bskl_to_pskl_pskl_to_bskl_syn.
      eapply ad_refine_pskl_f_flex_target_unfold;
        [ exact Hwfth | exact Hbα
        | intros X HX; apply HΔbt; clear - HX; fsetdec
        | clear - Hdisj; fsetdec
        | exact Hrp ]. }
    (* recurse on the premise at the SAME measure *)
    destruct (IHHj F Δ1 Δ2 Θ0 PP0 PP ρ IH Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf
                   Hinc Hwfth Hnfdth HΨ HeqS HnfP HnfP0 HneP0hole Hnthg
                   Hrs' Hrp')
      as [P1 [Θ1 [Hc Hopt']]].
    exists P1, Θ1. split; [ exact Hc | ].
    intros ρ1 Hid Hinc1.
    destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    (* re-attach the flexible target to the precision *)
    unfold ad_precise_f in *. simpl.
    eapply ad_refine_syn_f__flex_r; [ exact Hbα | ].
    unfold ptyp_to_bskl_syn in Hprec.
    rewrite bskl_to_pskl_pskl_to_bskl_syn in Hprec.
    rewrite (mono_inh_eq_syn Hmτ) in Hprec.
    exact Hprec.
Qed.

Lemma consis_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  consis_complete_at m.
Proof.
  intros m IH. unfold consis_complete_at.
  intros F Δ1 Δ2 Θ0 P0 P ρ Θ Ψ Qb Hm Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf
    Hinc Hwfth Hnfdth HΨ Hjoin Hrs Hrp.
  subst m.
  (* ---- Layer 0a: flexible SUBJECT — parts 2/3 (t breaks the tie) ---- *)
  destruct (a_flex_shape_dec HwfP) as [[β [-> Hfβ]] | HnfP].
  { destruct (a_flex_shape_dec HwfP0) as [[δ0 [-> Hfδ0]] | HnfP0].
    - (* C-Flex : both hatted — part 2 (unification). *)
      assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
                (pskl_to_uskl (msubst_pskl ρ (pskl_var_f β))) ≈ Qb)
        by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
      assert (Hjoin'' : empty ⨟ Θ ⊨ₛᵃ
                (ptyp_to_uskl_syn (msubst_lookup ρ β)) ≈ Qb).
      { replace (msubst_pskl ρ (pskl_var_f β))
          with (ptyp_to_pskl (msubst_lookup ρ β)) in Hjoin' by reflexivity.
        rewrite pskl_to_uskl_ptyp in Hjoin'. exact Hjoin'. }
      assert (Hmβ : mono_ptyp (msubst_lookup ρ β))
        by (eapply a_inc_lookup_mono; exact Hinc).
      assert (Hmδ0 : mono_ptyp (msubst_lookup ρ δ0))
        by (eapply a_inc_lookup_mono; exact Hinc).
      apply ad_refine_syn_f_forget in Hrs.
      replace (msubst_pskl ρ (pskl_var_f δ0))
        with (ptyp_to_pskl (msubst_lookup ρ δ0)) in Hrs by reflexivity.
      rewrite (ptyp_to_bskl_inh_syn_eq Hmδ0) in Hrs.
      destruct (refine_mono_join Hrs Hwfth (B := msubst_lookup ρ δ0)
                  eq_refl Hmδ0) as [C [HmC [HeqQb HeqδC]]].
      subst Qb.
      destruct (consis_mono_join Hjoin'' Hwfth (A := msubst_lookup ρ β)
                  eq_refl Hmβ) as [C' [HmC' [HeqQb' HeqβC']]].
      assert (HCC : C = C')
        by (apply ptyp_to_bskl_syn_inj; auto).
      subst C'.
      assert (Heqβδ : Θ ⊢ (msubst_lookup ρ β) ≡ᵗ (msubst_lookup ρ δ0)).
      { eapply a_tyequiv__trans; [ exact HeqβC' | ].
        apply a_tyequiv__sym; exact HeqδC. }
      assert (Hlt : mu_lt (mu_unify Θ ρ β δ0 Θ0)
                          (mu_consis Θ ρ (pskl_var_f δ0) (pskl_var_f β) Θ0)).
      { unfold mu_unify, mu_consis. apply mu_lt_intro. right.
        split; [ symmetry; apply V_flex | ].
        right. split; [ reflexivity | left; lia ]. }
      destruct (IH _ Hlt) as [_ [HuIH _]].
      destruct (HuIH F Θ0 β δ0 ρ Θ eq_refl Hwf0 Hfβ Hfδ0 Hinc Hwfth Heqβδ)
        as [Θ1 [Hu Hopt']].
      exists (pskl_var_f β), Θ1. split.
      { apply a_consis__flex. exact Hu. }
      intros ρ1 Hid Hinc1.
      destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ Hie]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      (* precision recovery for the hatted output (prop_precise_recover) *)
      assert (Hbtβ0 : a_binds_tvar β Θ0) by (right; exact Hfβ).
      assert (Hwfvβ : a_wf_ptyp Θ1 (msubst_lookup ρ1 β))
        by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtβ0 ]).
      rewrite (msubst_lookup_id β Hid) in Hwfvβ.
      assert (HbtβΘ1 : a_binds_tvar β Θ1) by (inversion Hwfvβ; assumption).
      destruct (a_unify_sound Hu Hwf0) as [_ [Hwf1 _]].
      try unfold ad_precise_f.
      apply ad_refine_syn_f_of_plain_no_hole;
        [ | apply pskl_to_bskl_inh_no_hole, bskl_to_pskl_no_hole,
            msubst_bskl_no_hole; simpl; exact I ].
      eapply consis_precise_via_join with (Θ0 := Θ0) (θ1 := ρ1);
        [ exact Hwfth | exact Hfβ | exact Hinc | exact HbtβΘ1
        | exact Hζ | exact Hwf1 | exact Hie
        | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfβ ]
        | apply (msubst_lookup_id β Hid)
        | exact Hjoin' ].
    - (* C-FlexL : hatted subject, non-flex input — part 3 (assignment).
         The callee's join is built from the competing solution by the
         refine→join mono bridge [refine_inh_mono_consis] (design doc §9.1)
         plus the Q-side mono transport [tyequiv_mono_consis_transport_q];
         precision recovers by [consis_precise_via_join]. *)
      assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
                (pskl_to_uskl (msubst_pskl ρ (pskl_var_f β))) ≈ Qb)
        by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
      assert (Hjoin'' : empty ⨟ Θ ⊨ₛᵃ
                (ptyp_to_uskl_syn (msubst_lookup ρ β)) ≈ Qb).
      { replace (msubst_pskl ρ (pskl_var_f β))
          with (ptyp_to_pskl (msubst_lookup ρ β)) in Hjoin' by reflexivity.
        rewrite pskl_to_uskl_ptyp in Hjoin'. exact Hjoin'. }
      assert (Hmβ : mono_ptyp (msubst_lookup ρ β))
        by (eapply a_inc_lookup_mono; exact Hinc).
      (* the join target is a monotype painting: Qb = syn C, θβ̂ ≡ᵗ C *)
      destruct (consis_mono_join Hjoin'' Hwfth (A := msubst_lookup ρ β)
                  eq_refl Hmβ) as [C [HmC [HeqQb HeqβC]]].
      subst Qb.
      (* refine→join bridge on the Δ1-refinement *)
      apply ad_refine_syn_f_forget in Hrs.
      assert (Hbr : empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P0))
                      ≈ (ptyp_to_bskl_syn C)).
      { eapply refine_inh_mono_consis;
          [ exact Hrs | exact Hwfth
          | apply mono_ptyp_to_bskl_syn; exact HmC
          | reflexivity
          | intros X HX; left; eapply a_inc_binds_tvar;
              [ exact Hinc | apply Hrig; clear - HX; fsetdec ] ]. }
      (* transport the join target from C to θβ̂ along the equivalence *)
      assert (Hvβ : forall X, X `in` ftvar_in_ptyp (msubst_lookup ρ β) ->
                              a_binds_tvar X Θ).
      { intros X HX. eapply a_wf_ptyp_ftv_tvarish; [ | exact HX ].
        eapply a_inc_lookup_wf;
          [ exact Hinc | exact Hwf0 | right; exact Hfβ ]. }
      destruct (tyequiv_mono_consis_transport_q HeqβC Hwfth Hmβ Hvβ)
        as [Htq _].
      assert (Hjoin3 : empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P0))
                        ≈ (ptyp_to_bskl_syn (msubst_lookup ρ β)))
        by (apply Htq; exact Hbr).
      (* the measure: V constant (pairing), n constant, t breaks the tie *)
      assert (Hlt : mu_lt (mu_assign Θ ρ β P0 nil Θ0)
                          (mu_consis Θ ρ P0 (pskl_var_f β) Θ0)).
      { unfold mu_assign, mu_consis. apply mu_lt_intro. right.
        split; [ symmetry; apply V_flexL | ].
        right. split; [ reflexivity | left; lia ]. }
      assert (Hdom : dom (nil : aenv) [<=] ftvar_in_pskl P0)
        by (simpl; clear; fsetdec).
      destruct (IH _ Hlt) as [_ [_ HaIH]].
      destruct (HaIH F Θ0 nil β P0 ρ Θ eq_refl a_decls__nil Hwf0 Hfβ
                     HwfP0 HnfP0 Hdom Hinc Hwfth Hjoin3)
        as [Θ1 [Ha Hopt']].
      exists (pskl_var_f β), Θ1. split.
      { apply a_consis__flex_l; [ exact HnfP0 | exact Ha ]. }
      intros ρ1 Hid Hinc1.
      destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ Hie]].
      exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
      (* precision recovery for the hatted output (prop_precise_recover) *)
      assert (Hbtβ0 : a_binds_tvar β Θ0) by (right; exact Hfβ).
      assert (Hwfvβ : a_wf_ptyp Θ1 (msubst_lookup ρ1 β))
        by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtβ0 ]).
      rewrite (msubst_lookup_id β Hid) in Hwfvβ.
      assert (HbtβΘ1 : a_binds_tvar β Θ1) by (inversion Hwfvβ; assumption).
      assert (Hwf1 : a_wf_aenv Θ1)
        by (eapply a_assign_preserves_wf;
              [ exact Ha | apply a_decls__nil | exact Hwf0 | exact HwfP0 ]).
      try unfold ad_precise_f.
      apply ad_refine_syn_f_of_plain_no_hole;
        [ | apply pskl_to_bskl_inh_no_hole, bskl_to_pskl_no_hole,
            msubst_bskl_no_hole; simpl; exact I ].
      eapply consis_precise_via_join with (Θ0 := Θ0) (θ1 := ρ1);
        [ exact Hwfth | exact Hfβ | exact Hinc | exact HbtβΘ1
        | exact Hζ | exact Hwf1 | exact Hie
        | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfβ ]
        | apply (msubst_lookup_id β Hid)
        | exact Hjoin' ]. }
  (* ---- Layer 0b: flexible INPUT, non-flex subject : C-FlexR --------- *)
  destruct (a_flex_shape_dec HwfP0) as [[δ0 [-> Hfδ0]] | HnfP0].
  { (* part 3 (assignment δ̂0 ≔ P): the input δ̂0's image is a monotype, so
       [refine_mono_join] reads Qb = syn C off the Δ1-refinement and the
       join's TARGET transports from C to θδ̂0 along the equivalence
       ([tyequiv_mono_consis_transport_q] — general subject); precision by
       [consis_precise_via_refine]. *)
    assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ
              (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb)
      by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
    assert (Hmδ0 : mono_ptyp (msubst_lookup ρ δ0))
      by (eapply a_inc_lookup_mono; exact Hinc).
    (* the Δ1-refinement's source is a monotype painting: Qb = syn C *)
    pose proof Hrs as Hrs2.
    apply ad_refine_syn_f_forget in Hrs2.
    replace (msubst_pskl ρ (pskl_var_f δ0))
      with (ptyp_to_pskl (msubst_lookup ρ δ0)) in Hrs2 by reflexivity.
    rewrite (ptyp_to_bskl_inh_syn_eq Hmδ0) in Hrs2.
    destruct (refine_mono_join Hrs2 Hwfth (B := msubst_lookup ρ δ0)
                eq_refl Hmδ0) as [C [HmC [HeqQb HeqδC]]].
    (* transport the join target from C to θδ̂0 along the equivalence *)
    assert (Hvδ : forall X, X `in` ftvar_in_ptyp (msubst_lookup ρ δ0) ->
                            a_binds_tvar X Θ).
    { intros X HX. eapply a_wf_ptyp_ftv_tvarish; [ | exact HX ].
      eapply a_inc_lookup_wf;
        [ exact Hinc | exact Hwf0 | right; exact Hfδ0 ]. }
    destruct (tyequiv_mono_consis_transport_q HeqδC Hwfth Hmδ0 Hvδ)
      as [Htq _].
    assert (Hjoin3 : empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P))
                      ≈ (ptyp_to_bskl_syn (msubst_lookup ρ δ0))).
    { apply Htq. rewrite <- HeqQb. exact Hjoin'. }
    (* the measure: V constant (pairing), n constant, t breaks the tie *)
    assert (Hlt : mu_lt (mu_assign Θ ρ δ0 P nil Θ0)
                        (mu_consis Θ ρ (pskl_var_f δ0) P Θ0)).
    { unfold mu_assign, mu_consis. apply mu_lt_intro. right.
      split; [ symmetry; apply V_flexR | ].
      right. split; [ reflexivity | left; lia ]. }
    assert (Hdom : dom (nil : aenv) [<=] ftvar_in_pskl P)
      by (simpl; clear; fsetdec).
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH F Θ0 nil δ0 P ρ Θ eq_refl a_decls__nil Hwf0 Hfδ0
                   HwfP HnfP Hdom Hinc Hwfth Hjoin3)
      as [Θ1 [Ha Hopt']].
    exists (pskl_var_f δ0), Θ1. split.
    { apply a_consis__flex_r; [ exact HnfP | exact Ha ]. }
    intros ρ1 Hid Hinc1.
    destruct (Hopt' ρ1 Hid Hinc1) as [ζ [Hζ Hie]].
    exists ζ. split; [ exact Hζ | ]. split; [ exact Hie | ].
    (* precision recovery for the hatted output, off the Δ1-refinement *)
    assert (Hbtδ00 : a_binds_tvar δ0 Θ0) by (right; exact Hfδ0).
    assert (Hwfvδ : a_wf_ptyp Θ1 (msubst_lookup ρ1 δ0))
      by (eapply a_inc_lookup_wf; [ exact Hinc1 | exact Hwf0 | exact Hbtδ00 ]).
    rewrite (msubst_lookup_id δ0 Hid) in Hwfvδ.
    assert (HbtδΘ1 : a_binds_tvar δ0 Θ1) by (inversion Hwfvδ; assumption).
    assert (Hwf1 : a_wf_aenv Θ1)
      by (eapply a_assign_preserves_wf;
            [ exact Ha | apply a_decls__nil | exact Hwf0 | exact HwfP ]).
    try unfold ad_precise_f.
    apply ad_refine_syn_f_of_plain_no_hole;
      [ | apply pskl_to_bskl_inh_no_hole, bskl_to_pskl_no_hole,
          msubst_bskl_no_hole; simpl; exact I ].
    eapply consis_precise_via_refine with (Θ0 := Θ0) (θ1 := ρ1);
      [ exact Hwfth | exact Hfδ0 | exact Hinc | exact HbtδΘ1
      | exact Hζ | exact Hwf1 | exact Hie
      | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfδ0 ]
      | apply (msubst_lookup_id δ0 Hid)
      | exact Hrs ]. }
  (* ---- Layer 0c: P0 = ◇ : C-GhostR ---------------------------------- *)
  destruct (pskl_eq_dec P0 pskl_hole) as [-> | HneP0hole].
  { (* axiom node [a_consis__ghost_r].  The side condition
       [Δ1 ∩ ftv(P) = ∅] is the mirror rigid-ftv chase, through the JOIN
       ([ad_pat_consis_rigid_ftv_rev]) against the Δ1-hygiene of the hole
       fill in Hrs; precision re-inherits the Δ2-refinement through the
       join by [refine_join_reinherit]. *)
    assert (Hjoin' : empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb)
      by (eapply consis_psi_cong_local; [ exact Hjoin | exact HΨ ]).
    change (ad_refine_syn_f Δ1 Θ Δ1 bskl_hole Qb) in Hrs.
    (* Qb is a syn-painting fixed point (its refinement source is ◇) *)
    assert (HQb : pskl_to_bskl_syn (bskl_to_pskl Qb) = Qb).
    { inversion Hrs; subst.
      - rewrite bskl_to_pskl_pskl_to_bskl_syn. reflexivity.
      - simpl. reflexivity. }
    (* the ftv chase for the GhostR side condition *)
    assert (Hside : forall X, X `in` Δ1 -> X `notin` ftvar_in_pskl P).
    { intros X HinΔ1 HinP.
      assert (HbX0 : binds X abind_tvar Θ0)
        by (apply Hrig; clear - HinΔ1; fsetdec).
      assert (HbX : binds X abind_tvar Θ)
        by (eapply a_inc_binds_tvar; eauto).
      assert (HXnd : X `notin` dom ρ)
        by (eapply a_inc_tvar_notin_dom; eauto).
      assert (Hdefs : forall β τ, binds β (abind_flex_mono_def τ) Θ ->
                                  X `notin` ftvar_in_ptyp τ).
      { intros β τ Hb. pose proof (Hnfdth _ _ Hb) as Hd.
        clear - Hd HinΔ1. fsetdec. }
      assert (HninQb : X `notin` ftvar_in_bskl Qb).
      { inversion Hrs; subst.
        - (* hole : the Δ1-hygiene of the fill *)
          match goal with
          | Hint : AtomSetImpl.inter Δ1 (ftvar_in_pskl ?Pf) [=] empty |- _ =>
              pose proof (ftvar_in_bskl_syn Pf) as Hfe;
              clear - Hint HinΔ1 Hfe; fsetdec
          end.
        - (* flex_r : Qb is a defined flexible, never the rigid X *)
          simpl.
          match goal with
          | Hbr : binds ?α0 (abind_flex_mono_def _) Θ |- _ =>
              assert (Hne : X <> α0)
                by (intro Heq; subst;
                    pose proof (binds_unique _ _ _ _ _ HbX Hbr
                                  (a_wf_aenv_uniq Hwfth)) as Hcon;
                    discriminate)
          end.
          clear - Hne; fsetdec. }
      assert (HinθP : X `in` ftvar_in_pskl (msubst_pskl ρ P))
        by (apply msubst_pskl_ftv_keep; assumption).
      assert (HninS : X `notin`
                ftvar_in_uskl (pskl_to_uskl (msubst_pskl ρ P))).
      { eapply ad_pat_consis_rigid_ftv_rev;
          [ exact Hwfth | exact HbX | exact Hdefs | exact Hjoin'
          | exact HninQb ]. }
      pose proof (ftvar_in_uskl_pskl (msubst_pskl ρ P)) as Hfe2.
      clear - HninS HinθP Hfe2. fsetdec. }
    exists P, Θ0. split.
    { apply a_consis__ghost_r.
      apply inter_empty_pointwise. exact Hside. }
    intros ρ1 Hid Hinc1. exists ρ.
    destruct (opt_axiom_factor Hwf0 Hid Hinc1 Hinc) as [Hout Hfact].
    split; [ exact Hout | ]. split; [ exact Hfact | ].
    (* precision by the re-inherit bridge (subset goal second, AFTER the
       bridge instantiates the Δ) *)
    assert (HwfθP : Θ ⨟ Δ2 ⊢ₚₛᵃ (msubst_pskl ρ P)).
    { eapply ad_wf_pskl_delta_mono;
        [ eapply ad_wf_pskl_msubst_inc;
            [ exact Hinc | exact Hwf0 | exact HwfP
            | intros X HX; exfalso; clear - HX; fsetdec ]
        | clear; fsetdec ]. }
    unfold ad_precise_f.
    rewrite bskl_to_pskl_msubst_bskl.
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    eapply ad_refine_syn_f_delta_mono with (Δ0 := Δ2);
      [ | clear; fsetdec ].
    eapply ad_refine_syn_f_fextend_ftv;
      [ eapply refine_join_reinherit with (Θj := Θ);
          [ exact Hrp | exact Hwfth | exact Hwfth
          | intros x b Hb; exact Hb
          | exact HwfθP
          | rewrite HQb; exact Hjoin' ]
      | ].
    intros γ Hγ.
    destruct (AtomSetProperties.In_dec γ Δ2) as [HγΔ2 | HγΔ2];
      [ left; exact HγΔ2 | right ].
    assert (HγΔ1 : γ `in` Δ1) by (clear - Hγ HγΔ2; fsetdec).
    assert (Hbγ : binds γ abind_tvar Θ)
      by (eapply a_inc_binds_tvar; [ exact Hinc | ];
          apply Hrig; clear - HγΔ1; fsetdec).
    split.
    + assert (Hnq : γ `notin` ftvar_in_bskl Qb)
        by (eapply ad_refine_syn_f_hole_src_target_ftv;
            [ exact Hrs | exact Hwfth
            | clear - HγΔ1; fsetdec | exact Hbγ ]).
      pose proof (ftvar_in_bskl_inh (bskl_to_pskl Qb)) as Hfe.
      pose proof (ftvar_in_pskl_bskl_to_pskl Qb) as Hfe2.
      clear - Hnq Hfe Hfe2. fsetdec.
    + intros β τ Hb.
      pose proof (Hnfdth β τ Hb) as Hi.
      clear - Hi HγΔ1. fsetdec. }
  (* ---- Layer 0d: P0 = ⊤◇.P0', P guarded : C-UnivGhostR -------------- *)
  assert (Hthdec : (exists P0', P0 = pskl_tophole P0') \/
                   (forall P0', P0 <> pskl_tophole P0')).
  { destruct P0; try (right; intros ? Hc; discriminate).
    left. eexists. reflexivity. }
  destruct Hthdec as [[P0' ->] | Hnth].
  { pose proof (ad_wf_pskl_lc HwfP) as HlcP.
    assert (Hgdec : guarded_pskl P \/ ~ guarded_pskl P).
    { destruct P; try (right; intro Hg; inversion Hg; fail).
      - left; apply guarded_pskl__unit.
      - left; apply guarded_pskl__var.
      - left; inversion HlcP; apply guarded_pskl__arrow; assumption. }
    destruct Hgdec as [HgP | HngP].
    - (* C-UnivGhostR : strip the input's ⊤◇, V drops on the input side. *)
      assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0') by (inversion HwfP0; assumption).
      assert (Hgρ : guarded_pskl (msubst_pskl ρ P))
        by (eapply guarded_pskl_msubst_inc; eauto).
      assert (HlcQb : lc_bskl Qb) by (eapply ad_refine_syn_f_lc_r; eauto).
      assert (HgQb : guarded_bskl Qb)
        by (eapply ad_pat_consis_guarded_r; eauto).
      change (ad_refine_syn_f Δ1 Θ Δ1
                (bskl_tophole (pskl_to_bskl_inh (msubst_pskl ρ P0'))) Qb)
        in Hrs.
      assert (Hrs' : ad_refine_syn_f Δ1 Θ Δ1
                (pskl_to_bskl_inh (msubst_pskl ρ P0')) Qb)
        by (eapply ad_refine_syn_f_tophole_guarded_inv; eauto).
      assert (Hlt : mu_lt (mu_consis Θ ρ P0' P Θ0)
                          (mu_consis Θ ρ (pskl_tophole P0') P Θ0)).
      { unfold mu_consis. apply mu_lt_intro. left.
        unfold V_consis.
        pose proof (Vpskl_tophole_lt Θ ρ P0'). lia. }
      destruct (IH _ Hlt) as [HcIH _].
      destruct (HcIH F Δ1 Δ2 Θ0 P0' P ρ Θ Ψ Qb eq_refl Hwf0 HwfP0' HwfP
                     Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ Hjoin Hrs' Hrp)
        as [P1 [Θ1 [Hc Hopt']]].
      exists P1, Θ1. split.
      { apply a_consis__univ_ghost_r;
          [ exact HgP | exact HnfP | exact Hc ]. }
      exact Hopt'.
    - (* P unguarded: fall through to the main dispatch. *)
      eapply (consis_complete_core Hjoin);
        try eassumption; try reflexivity.
      intros P0'' Heq0 Hg. inversion Heq0; subst P0''. exact (HngP Hg). }
  (* ---- Layer 1: the main dispatch ----------------------------------- *)
  eapply (consis_complete_core Hjoin);
    try eassumption; try reflexivity.
  intros P0'' Heq0 Hg. exact (Hnth P0'' Heq0).
Qed.

(* ===================================================================== *)
(*  §4  The bundle, by well-founded induction on μ                        *)
(* ===================================================================== *)

Theorem complete_mu : forall m, complete_at m.
Proof.
  intro m; induction (mu_lt_wf m) as [m _ IH].
  repeat split;
    [ apply consis_complete_step
    | apply unify_complete_step
    | apply assign_complete_step ]; exact IH.
Qed.

(* ===================================================================== *)
(*  §5  Corollaries                                                       *)
(* ===================================================================== *)

(** The join-shaped statement the earlier scaffold stated directly (kept
    verbatim for downstream compatibility); now an instance of the bundle. *)
Lemma consis_complete : forall Ψ Θ S Qb,
  Ψ ⨟ Θ ⊨ₛᵃ S ≈ Qb ->
  forall F Δ1 Δ2 Θ0 P0 P ρ,
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    (forall X, X `in` (Δ1 `union` Δ2) -> binds X abind_tvar Θ0) ->
    no_flex_dep (Δ1 `union` Δ2) Θ0 ->
    flex_above_free (Δ1 `union` Δ2) Θ0 ->
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    no_flex_dep (Δ1 `union` Δ2) Θ ->
    Ψ [=] empty ->
    S = pskl_to_uskl (msubst_pskl ρ P) ->
    ad_refine_syn_f Δ1 Θ Δ1 (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f Δ2 Θ Δ2 (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis F Δ1 Δ2 Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           ad_precise_f (Δ1 `union` Δ2) Θ (Δ1 `union` Δ2)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb)).
Proof.
  intros Ψ Θ S Qb Hj F Δ1 Δ2 Θ0 P0 P ρ
    Hwf0 HwfP0 HwfP Hrig Hnfd0 Hfaf Hinc Hwfth Hnfdth HΨ HeqS Hrs Hrp.
  subst S.
  destruct (complete_mu (mu_consis Θ ρ P0 P Θ0)) as [Hc _].
  eapply Hc; try eassumption; reflexivity.
Qed.

(* ===================================================================== *)
(*  Top-level completeness of consistency, DERIVED from the bundle by     *)
(*  instantiating the augmentation to Δ1 = Δ2 = ∅, Ψ = ∅.  The paper's    *)
(*  unaugmented statement (this is the [TODO] the old bundle left open).  *)
(* ===================================================================== *)
Lemma a_consis_complete_thm : forall F Θ0 P0 P,
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  forall ρ Θ Qb,
    Θ0 ≤[ ρ ] Θ ->
    a_wf_aenv Θ ->
    empty ⨟ Θ ⊨ₛᵃ (pskl_to_uskl (msubst_pskl ρ P)) ≈ Qb ->
    ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh (msubst_pskl ρ P0)) Qb ->
    ad_refine_pskl_f empty Θ empty (msubst_pskl ρ P) (bskl_to_pskl Qb) ->
    exists P1 Θ1,
      a_consis F empty empty Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           Θ ⨟ empty ⊢ₚᵣᵃ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb)).
Proof.
  intros F Θ0 P0 P Hwf0 HwfP0 HwfP ρ Θ Qb Hinc Hwfth Hjoin Hrs Hrp.
  (* [Δ1 ∪ Δ2 = ∅], so rigid / no_flex_dep / flex_above_free are vacuous. *)
  assert (Hcc : exists P1 Θ1,
      a_consis F empty empty Θ0 P0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> Θ0 ≤[ ρ1 ] Θ1 ->
         exists ζ,
           Θ1 ≤[ ζ ] Θ /\
           a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
           ad_precise_f (empty `union` empty) Θ (empty `union` empty)
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) (bskl_to_pskl Qb))).
  { eapply consis_complete with (Δ1 := empty) (Δ2 := empty).
    all: try (first [ eassumption | reflexivity ]).
    all: try (intros X HX; exfalso; clear - HX; fsetdec).  (* rigid: X ∈ ∅ *)
    all: repeat intro; fsetdec. }     (* no_flex_dep / flex_above_free / Ψ *)
  destruct Hcc as [P1 [Θ1 [Hc Hopt]]].
  exists P1, Θ1. split; [ exact Hc | ].
  intros ρ1 Hid Hinc1.
  destruct (Hopt ρ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
  exists ζ. repeat split; try assumption.
  (* forget the hygiene, then shrink [∅ ∪ ∅ ⊆ ∅]. *)
  apply ad_precise_f_forget in Hprec.
  eapply ad_refine_syn_delta_mono; [ exact Hprec | clear; fsetdec ].
Qed.
