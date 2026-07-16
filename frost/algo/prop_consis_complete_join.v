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
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
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
           Θ ⨟ (Δ1 `union` Δ2) ⊢ₚᵣᵃ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb)).

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
  - (* head [γ ~ tvar] RIGID.  Two sub-paths, neither yet closed:
       γ ∈ ftv(P) — NO RULE fires; the STUCK-CHECK (design doc §9.2,
         [paper-gap]: the paper never proves the walk cannot reach this
         head) must refute the solution: a_inc peels γ before reaching α̂,
         so θα̂ is wf BELOW γ, while γ ∈ ftv(θP) (rigid_survives_solution)
         and the join against the monotype θα̂ forces γ ∈ ftv(θα̂) —
         contradiction.  Ingredient (ii) — "rigid ftv survives the join
         into a def-free-below-γ target" — is not yet built.
       γ ∉ ftv(P) — Assign-SkipRigid; the walk truncates the solution
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
           Θ ⨟ (Δ1 `union` Δ2) ⊢ₚᵣᵃ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb)).
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
    cbn [pskl_to_bskl_syn msubst_bskl].
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    rewrite (msubst_lookup_notin ρ Hδρ).
    apply consis_precise_mono_join with (A := ptyp_var_f δ)
                                        (Qb := bskl_var_f δ);
      [ exact Hwfth | apply mono_ptyp__var
      | intros X HX; simpl in HX;
        assert (HXδ : X = δ) by (clear - HX; fsetdec); subst X;
        left; exact HbtΘ
      | apply ad_pat_consis__var; [ clear; fsetdec | left; exact HbtΘ ] ].
  (* ------------------------------------------------------------ arrow *)
  - (* C-Arrow (paper :2691-2775): two structural sub-nodes at strictly
       smaller V; the second runs at the first's output context via the
       first's factoring ζ1 (from its optimality at the soundness
       id-witness), and the two factorings compose by [a_inc_equiv_glue].
       TRUE; not yet mechanized. *)
    admit.
  (* ------------------------------------------- forall_inh (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* --------------------------------------------- forall_inh_untagged *)
  - (* C-ForallInh (paper :2777-2851): open with a fresh rigid α added to
       Θ0, Δ1, Δ2; V unchanged by the opening ([Vpskl_open]) but strictly
       smaller by the binder strip; needs the head-preservation (L8) and
       renaming (L9) enablers to reassemble the cofinite [a_consis__
       forall_inh] node from the single fresh instance.  TRUE; not yet
       mechanized. *)
    admit.
  (* ------------------------------------------- forall_syn (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* ------------------------------------------------------ forall_syn *)
  - (* C-ForallSyn (paper :2853-2926): as C-ForallInh with the opened α
       added to Δ2 only and the input ⊤◇.P0' carried unchanged.  TRUE;
       not yet mechanized. *)
    admit.
  (* ---------------------------------------------- ghostg (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* -------------------------------------------- topholeg (impossible) *)
  - destruct (msubst_pskl ρ PP); simpl in HeqS; discriminate.
  (* ------------------------------------------------------------- hole *)
  - (* C-Ghost (paper :2583-2613): subject ◇, axiom node [a_consis__ghost].
       The side condition [Δ2 ∩ ftv(P0) = ∅] needs the rigid-ftv-survival
       of the competing Δ1-refinement (Hrs) against the Δ2-hygiene of the
       hole fill in the competing join — the [no_flex_dep]-guarded ftv
       chase.  Precision transplants the CLOSED OPT C-Ghost case
       ([consis_hole_target_inh] + Hrs).  TRUE; not yet mechanized. *)
    admit.
  (* ---------------------------------------------------------- tophole *)
  - (* C-UnivGhost / C-UnivGhostG (paper :2928-2993) with the C-UnivGhost2
       tophole-input sub-case (:3096-3132): both sides strip one ⊤◇, V
       drops by 2 (or 1), recurse.  TRUE; not yet mechanized. *)
    admit.
  (* ------------------------------------------------------ tophole_inh *)
  - (* C-UnivGhost1 (paper :2995-3070): the input's ∀ opens with a fresh
       rigid α added to Θ0 and Δ1; the subject ⊤◇.P' is carried unchanged.
       Needs the same L8/L9 enablers as the ∀-cases.  TRUE; not yet
       mechanized. *)
    admit.
  (* ----------------------------------------------------- tophole_drop *)
  - (* C-UnivGhost2, guarded-input sub-case (paper :3134-3163): the subject
       strips its ⊤◇ ([a_consis__univ_ghost2]), the input is unchanged; V
       drops by 1 on the subject side.  TRUE; not yet mechanized. *)
    admit.
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
       the join.  Transport Hrs/Hrp through the unfold (their flex_r-target
       inversions), recurse on the premise, and re-attach the [α̂]-target
       to the resulting precision by [ad_refine_syn__flex_r].  TRUE; the
       two target-unfold inversion helpers are not yet mechanized. *)
    admit.
Admitted.

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
      eapply consis_precise_via_join with (Θ0 := Θ0) (θ1 := ρ1);
        [ exact Hwfth | exact Hfβ | exact Hinc | exact HbtβΘ1
        | exact Hζ | exact Hwf1 | exact Hie
        | eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | exact Hfβ ]
        | apply (msubst_lookup_id β Hid)
        | exact Hjoin' ].
    - (* C-FlexL : hatted subject, non-flex input — part 3 (assignment).
         Constructing the callee's solution needs the refine→join mono
         bridge (the [paper-gap] of design doc §9.1: [inh θP0 ⊳ syn C] with
         [C] mono implies [⌊θP0⌋ ≈ syn C]); precision then recovers by
         [consis_precise_via_join].  TRUE; the bridge is not yet
         mechanized. *)
      admit. }
  (* ---- Layer 0b: flexible INPUT, non-flex subject : C-FlexR --------- *)
  destruct (a_flex_shape_dec HwfP0) as [[δ0 [-> Hfδ0]] | HnfP0].
  { (* part 3 with the join's TARGET transported along [refine_mono_join]
       (the input α̂'s image is a monotype, so Qb is its syn painting up to
       ≡ᵗ); precision by [consis_precise_via_refine].  TRUE; the target
       transport for a GENERAL subject is not yet mechanized. *)
    admit. }
  (* ---- Layer 0c: P0 = ◇ : C-GhostR ---------------------------------- *)
  destruct (pskl_eq_dec P0 pskl_hole) as [-> | HneP0hole].
  { (* axiom node [a_consis__ghost_r]; the side condition
       [Δ1 ∩ ftv(P) = ∅] needs the rigid-ftv survival of the subject
       through the competing join against the Δ1-hygiene of the hole fill
       in Hrs; precision collapses to Hrs as in the CLOSED OPT C-Ghost.
       TRUE; the ftv-survival lemma is not yet mechanized. *)
    admit. }
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
Admitted.

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
           Θ ⨟ (Δ1 `union` Δ2) ⊢ₚᵣᵃ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb)).
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
           Θ ⨟ (empty `union` empty) ⊢ₚᵣᵃ
             (msubst_bskl ζ (pskl_to_bskl_syn P1)) ⊑ (bskl_to_pskl Qb))).
  { eapply consis_complete with (Δ1 := empty) (Δ2 := empty).
    all: try (first [ eassumption | reflexivity ]).
    all: try (intros X HX; exfalso; clear - HX; fsetdec).  (* rigid: X ∈ ∅ *)
    all: repeat intro; fsetdec. }     (* no_flex_dep / flex_above_free / Ψ *)
  destruct Hcc as [P1 [Θ1 [Hc Hopt]]].
  exists P1, Θ1. split; [ exact Hc | ].
  intros ρ1 Hid Hinc1.
  destruct (Hopt ρ1 Hid Hinc1) as [ζ [Hζ [Hie Hprec]]].
  exists ζ. repeat split; try assumption.
  (* [∅ ∪ ∅ ⊆ ∅]: shrink the precision judgment's Δ. *)
  eapply ad_refine_syn_delta_mono; [ exact Hprec | clear; fsetdec ].
Qed.
