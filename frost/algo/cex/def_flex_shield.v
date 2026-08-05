(** ⭕⭕ [flex_shield] — P6-Sv's RETIRED REPAIR PREMISE, kept for the record.

    MOVED HERE 2026-08-05 from frost/algo/prop_look_complete_sub_var.v, where
    it had had no consumer since 2026-08-03: every use in P6-Sv's induction
    was a relay, and the leaf lemma fed only a regression test.  Under the
    authors' repaired [SolE-FlexR] the counterexample it was invented against
    (cex_p6sv_forall_flex.v) is retracted outright, so nothing in the PROOFS
    refers to it at all.

    It survives because the cex/ files that record this campaign's history
    state their conclusions against it — [cex_p7_shield_realizable.v],
    [cex_p7_shield_double_occ.v], [regr_p7_shield_arrow.v],
    [cex_p7_sub_monoish.v], [cex_p7_shield_forall_flex.v].  Keeping the
    definition next to them, rather than in a live proof file, is the point
    of the move: a reader of P6-Sv should not have to page past 490 lines of
    a premise P6-Sv does not take.

    ⚠️ NOT a counterexample itself — this file holds DEFINITIONS.  It lives
    under cex/ because that is who its users are. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_look_complete.

Set Implicit Arguments.

(* ===================================================================== *)
(*  [flex_shield Θ0 Ψ' Δρ P0 ψa]  — THE REPAIR PREMISE                    *)
(* ===================================================================== *)

(** Positionally: every raw-Θ0-flexible position of [P0] faces a part of
    [ψa] that is both Δρ-clean and Ψ'-tag-free.

    - [fsh_clean] is the only rule for a NON-ALIGNED pair, and it demands
      BOTH conditions — this is what refutes counterexample (1) (P0 = α̂
      faces a Ψ'-tagged ∀^ε) and (2) (the pair (arrow, ∀) is non-aligned
      and ψa is tagged).
    - [fsh_flexfree] is the other base case: nothing to protect.  It is
      what makes the ForallL descent maintainable — at a TAGGED ψa the
      clean rule is impossible, so a surviving derivation is flex-free or
      structural.
    - [fsh_all_r] BAKES IN the ρ-growth [add α Δρ]: the tagged quantifier
      that Sub-ForallL instantiates is exactly the one whose binder joins
      Δρ, so the descent is an instantiation rather than an argument.
    - [ψa] is [is_tskl], whose shapes are unit / var / arrow / ∀^ε / ◈ /
      ∀◈ — hence no plain-[tophole] row on the right. *)
Inductive flex_shield (Θ0 : aenv) (Ψ' : atoms) : atoms -> pskl -> uskl -> Prop :=
| fsh_clean : forall Δρ P0 ψa,
    (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
    (ftag_in_uskl ψa) ∩ Ψ' [=] empty ->
    flex_shield Θ0 Ψ' Δρ P0 ψa
| fsh_flexfree : forall Δρ P0 ψa,
    pskl_flex_free Θ0 P0 ->
    flex_shield Θ0 Ψ' Δρ P0 ψa
| fsh_arrow : forall Δρ P1 P2 ψ1 ψ2,
    flex_shield Θ0 Ψ' Δρ P1 ψ1 ->
    flex_shield Θ0 Ψ' Δρ P2 ψ2 ->
    flex_shield Θ0 Ψ' Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2)
| fsh_all_l : forall L Δρ P0 ψa,           (* Sub-ForallR descends P0 only *)
    (forall α, α `notin` L ->
       flex_shield Θ0 Ψ' Δρ (open_pskl_wrt_pskl P0 (pskl_var_f α)) ψa) ->
    flex_shield Θ0 Ψ' Δρ (pskl_all_syn P0) ψa
| fsh_all_r : forall L Δρ ε P0 ψ,          (* Sub-ForallL descends ψa only *)
    (forall α, α `notin` L ->
       flex_shield Θ0 Ψ' (add α Δρ) P0 (open_uskl_wrt_uskl ψ (uskl_var_f α))) ->
    flex_shield Θ0 Ψ' Δρ P0 (uskl_all_etag ε ψ)
| fsh_tophole_l : forall Δρ P0 ψa,
    flex_shield Θ0 Ψ' Δρ P0 ψa ->
    flex_shield Θ0 Ψ' Δρ (pskl_tophole P0) ψa
| fsh_topholeg_r : forall Δρ P0 ψ,
    flex_shield Θ0 Ψ' Δρ P0 ψ ->
    flex_shield Θ0 Ψ' Δρ P0 (uskl_topholeg ψ)
(* A ρ-REPLACED RIGID VARIABLE is safe opposite ANY payload, flexible or
   not — this is P6-Cv's leaf: the precision premise forces [Pi] to be that
   very variable ([ad_ppre_delta_var_inv] + [msubst_pskl_var_inv]), SolS-Var
   / SolE-Var keep it, and the conclusion's precision is the var rule.  So
   no dirt reaches the payload however dirty the position is.
   WITHOUT this rule the premise is TOO STRONG: it would reject
   [ψa = ∀^ε β.β] against [P0 = α̂] with [Pi = ∀β.β] — where the algorithm
   SUCCEEDS (SolS-ForallL then SolS-Var gives [Pa = ∀β.β], whose precision
   against [∀^ε β.β] holds).  Contrast the counterexample, whose body is
   [β→β]: a compound body sends the solve to SolE-FlexR instead, which is
   what destroys the information. *)
| fsh_rho_var : forall Δρ P0 α,
    α `in` Δρ ->
    flex_shield Θ0 Ψ' Δρ P0 (uskl_var_f α).

(* ===================================================================== *)
(*  Basic kit                                                             *)
(* ===================================================================== *)

(** Δρ is a "dirty set" the clean rule bounds and the ρ-var rule inhabits,
    so the relation is congruent — but NOT antitone — in it. *)
Lemma flex_shield_delta_cong : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall Δρ', Δρ' [=] Δρ ->
  flex_shield Θ0 Ψ' Δρ' P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros Δρ' Heq.
  - apply fsh_clean; [ clear - H Heq; fsetdec | exact H0 ].
  - apply fsh_flexfree; exact H.
  - apply fsh_arrow; [ apply IHflex_shield1 | apply IHflex_shield2 ]; exact Heq.
  - apply fsh_all_l with (L := L); intros α Hα; apply H0; assumption.
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα.
    apply H0; [ exact Hα | clear - Heq; fsetdec ].
  - apply fsh_tophole_l; apply IHflex_shield; exact Heq.
  - apply fsh_topholeg_r; apply IHflex_shield; exact Heq.
  - apply fsh_rho_var; clear - H Heq; fsetdec.
Qed.

(** The tag index is a "to be solved" upper bound read only by the clean
    row, so shrinking it only weakens the requirement — which is what the
    Arrow case needs, since each branch carries its OWN tag set. *)
Lemma flex_shield_psi_anti : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall Ψ'', Ψ'' [<=] Ψ' ->
  flex_shield Θ0 Ψ'' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros Ψ'' Hsub.
  - apply fsh_clean; [ exact H | clear - H0 Hsub; fsetdec ].
  - apply fsh_flexfree; exact H.
  - apply fsh_arrow; [ apply IHflex_shield1 | apply IHflex_shield2 ]; exact Hsub.
  - apply fsh_all_l with (L := L); intros α Hα; apply H0; assumption.
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα; apply H0; assumption.
  - apply fsh_tophole_l; apply IHflex_shield; exact Hsub.
  - apply fsh_topholeg_r; apply IHflex_shield; exact Hsub.
  - apply fsh_rho_var; exact H.
Qed.

(** Weakening by a rigid binder (the ForallR descent runs at [Θ0, γ]). *)
Lemma flex_shield_weaken_tvar : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall γ,
  flex_shield ((γ ~ abind_tvar) ++ Θ0) Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros γ.
  - apply fsh_clean; assumption.
  - apply fsh_flexfree; apply pskl_flex_free_weaken_tvar; exact H.
  - apply fsh_arrow; [ apply IHflex_shield1 | apply IHflex_shield2 ].
  - apply fsh_all_l with (L := L); intros α Hα; apply H0; exact Hα.
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα; apply H0; exact Hα.
  - apply fsh_tophole_l; apply IHflex_shield.
  - apply fsh_topholeg_r; apply IHflex_shield.
  - apply fsh_rho_var; exact H.
Qed.

(** Weakening by a FLEXIBLE prefix (P6-Ss's Sub-Arrow runs its right branch
    at [Ξc1,Θ0], where Ξc1 holds the flexibles the left branch collected).

    This one needs a side condition, and [flex_shield_weaken_tvar] does
    not: [fsh_flexfree] is ANTI-monotone in the context — it asserts that no
    variable of P0 is a Θ0-FLEXIBLE, and a prefix of flexibles could make one
    so.  Requiring the prefix to avoid [ftv P0] is exactly enough, and it is
    what the call site has (Ξc1's names are fresh for Θ0, while P0 is
    Θ0-scoped).  The [fsh_all_l] descent opens a binder, so its cofinite set
    grows by [dom Ξ] to keep the condition. *)
Lemma flex_shield_weaken_flex_prefix : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall Ξ, (ftvar_in_pskl P0) ∩ (dom Ξ) [=] empty ->
  flex_shield (Ξ ++ Θ0) Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros Ξ Hfr.
  - apply fsh_clean; assumption.
  - (* flexfree: a P0-variable is outside dom Ξ, so its binding is Θ0's *)
    apply fsh_flexfree. intros α Hα Hflex.
    assert (HαΞ : α `notin` dom Ξ) by (clear - Hfr Hα; fsetdec).
    apply (H α Hα).
    destruct Hflex as [Hb | [τ Hb]];
      [ left | right; exists τ ];
      (destruct (binds_app_1 _ _ _ _ _ Hb) as [Hb' | Hb'];
        [ exfalso; apply HαΞ; eapply binds_In; exact Hb' | exact Hb' ]).
  - simpl in Hfr. apply fsh_arrow;
      [ apply IHflex_shield1 | apply IHflex_shield2 ];
      clear - Hfr; fsetdec.
  - (* the opened binder must miss dom Ξ too *)
    apply fsh_all_l with (L := L `union` dom Ξ); intros α Hα.
    apply H0; [ clear - Hα; solve_notin | ].
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f α)) as Hup.
    simpl in Hup, Hfr. clear - Hup Hfr Hα; fsetdec.
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα; apply H0; assumption.
  - simpl in Hfr. apply fsh_tophole_l; apply IHflex_shield; exact Hfr.
  - apply fsh_topholeg_r; apply IHflex_shield; exact Hfr.
  - apply fsh_rho_var; exact H.
Qed.

(** Rigid renaming.  Needed by both binder descents: the derivation's
    cofinite set is existential, so the binder the INDUCTION picks is not
    the one the rule's family offers.  Renaming on the [P0] side leaves
    [ψa] and [Δρ] untouched; on the [ψa] side it moves the Δρ-element too.

    [paper-gap: none — pure mech bookkeeping.] *)
Lemma flex_shield_rename_l : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ P0 ψa ->
  forall α1 α2,
  ~ a_flex_tvar Θ0 α2 ->
  flex_shield Θ0 Ψ' Δρ (subst_pskl_in_pskl (pskl_var_f α2) α1 P0) ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H; induction H; intros α1 α2 H2.
  - apply fsh_clean; assumption.
  - apply fsh_flexfree; apply pskl_flex_free_subst; assumption.
  - simpl; apply fsh_arrow;
      [ apply IHflex_shield1 | apply IHflex_shield2 ]; exact H2.
  - simpl. apply fsh_all_l with (L := L `union` singleton α1); intros α Hα.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα; fsetdec | apply lc_pskl_var_f ].
    apply H0; [ clear - Hα; fsetdec | exact H2 ].
  - apply fsh_all_r with (L := L) (ε := ε); intros α Hα.
    apply H0; [ exact Hα | exact H2 ].
  - simpl; apply fsh_tophole_l; apply IHflex_shield; exact H2.
  - apply fsh_topholeg_r; apply IHflex_shield; exact H2.
  - apply fsh_rho_var; exact H.
Qed.

(** On the target side the renamed variable is a Δρ ELEMENT — the binder
    that [fsh_all_r] added — so it moves in [Δρ] as well as in [ψa]. *)
Lemma flex_shield_rename_r_gen : forall Θ0 Ψ' Δρ' P0 ψa,
  flex_shield Θ0 Ψ' Δρ' P0 ψa ->
  forall Δρ α1 α2,
  Δρ' [=] add α1 Δρ ->
  α1 `notin` Δρ -> α2 `notin` Δρ -> α2 `notin` ftvar_in_uskl ψa ->
  flex_shield Θ0 Ψ' (add α2 Δρ) P0
    (subst_bskl_in_uskl (uskl_var_f α2) α1 ψa).
Proof.
  intros Θ0 Ψ' Δρ' P0 ψa H; induction H;
    intros Δρ0 α1 α2 Heq Hα1 Hα2 Hα2ψ.
  - (* clean: α1 is not free in ψa (it is in the dirty set), so the
       renaming is the identity *)
    assert (Hfr : α1 `notin` ftvar_in_uskl ψa)
      by (clear - H Heq; fsetdec).
    rewrite (@subst_bskl_in_uskl_fresh_eq ψa (uskl_var_f α2) α1 Hfr).
    apply fsh_clean; [ clear - H Heq Hα2ψ; fsetdec | exact H0 ].
  - apply fsh_flexfree; exact H.
  - simpl in Hα2ψ |- *. apply fsh_arrow;
      [ apply IHflex_shield1 | apply IHflex_shield2 ];
      solve [ exact Heq | exact Hα1 | exact Hα2 | clear - Hα2ψ; fsetdec ].
  - apply fsh_all_l with (L := L); intros α Hα.
    apply H0; solve [ exact Hα | exact Heq | exact Hα1 | exact Hα2
                    | exact Hα2ψ ].
  - (* all_r: the rule's binder joins the dirty set, so the equation is
       re-associated under it *)
    simpl in Hα2ψ |- *.
    apply fsh_all_r with (L := L `union` singleton α1 `union` singleton α2
                            `union` Δρ0) (ε := ε);
      intros α Hα.
    (* extract the pieces of the pick-fresh union ONCE: a [fsetdec] that
       still sees the 4-way union is the known quadratic pattern *)
    assert (HαL : α `notin` L) by (clear - Hα; solve_notin).
    assert (HαΔ : α `notin` Δρ0) by (clear - Hα; solve_notin).
    assert (Hα1' : α <> α1)
      by (apply notin_singleton_1; clear - Hα; solve_notin).
    assert (Hα2' : α <> α2)
      by (apply notin_singleton_1; clear - Hα; solve_notin).
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | apply not_eq_sym; exact Hα1' | apply lc_uskl_var_f ].
    eapply flex_shield_delta_cong;
      [ eapply (H0 α HαL (add α Δρ0) α1 α2);
          [ clear - Heq; fsetdec
          | clear - Hα1 Hα1'; fsetdec
          | clear - Hα2 Hα2'; fsetdec
          | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                          (uskl_var_f α)) as Hup;
            simpl in Hup; clear - Hup Hα2ψ Hα2'; fsetdec ]
      | clear; fsetdec ].
  - simpl; apply fsh_tophole_l; apply IHflex_shield;
      solve [ exact Heq | exact Hα1 | exact Hα2 | exact Hα2ψ ].
  - simpl in Hα2ψ |- *. apply fsh_topholeg_r; apply IHflex_shield;
      solve [ exact Heq | exact Hα1 | exact Hα2 | exact Hα2ψ ].
  - (* rho_var: the renamed variable may BE the ρ-replaced one *)
    simpl.
    match goal with |- context [if ?c then _ else _] => destruct c as [-> | Hne] end.
    + apply fsh_rho_var; clear; fsetdec.
    + apply fsh_rho_var. clear - H Heq Hne; fsetdec.
Qed.

Lemma flex_shield_rename_r : forall Θ0 Ψ' Δρ P0 ψa α1 α2,
  flex_shield Θ0 Ψ' (add α1 Δρ) P0 ψa ->
  α1 `notin` Δρ -> α2 `notin` Δρ -> α2 `notin` ftvar_in_uskl ψa ->
  flex_shield Θ0 Ψ' (add α2 Δρ) P0
    (subst_bskl_in_uskl (uskl_var_f α2) α1 ψa).
Proof.
  intros Θ0 Ψ' Δρ P0 ψa α1 α2 H Hα1 Hα2 Hα2ψ.
  eapply flex_shield_rename_r_gen;
    [ exact H | clear; fsetdec | exact Hα1 | exact Hα2 | exact Hα2ψ ].
Qed.

(* ===================================================================== *)
(*  THE DESCENT LEMMAS — one per descent of the P6-Sv induction           *)
(* ===================================================================== *)

(** Sub-Arrow: both sides decompose. *)
Lemma flex_shield_arrow_inv : forall Θ0 Ψ' Δρ P1 P2 ψ1 ψ2,
  flex_shield Θ0 Ψ' Δρ (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2) ->
  flex_shield Θ0 Ψ' Δρ P1 ψ1 /\ flex_shield Θ0 Ψ' Δρ P2 ψ2.
Proof.
  intros Θ0 Ψ' Δρ P1 P2 ψ1 ψ2 H.
  remember (pskl_arrow P1 P2) as P0 eqn:HeqP.
  remember (uskl_arrow ψ1 ψ2) as ψa eqn:Heqψ.
  revert P1 P2 ψ1 ψ2 HeqP Heqψ.
  induction H; intros P1' P2' ψ1' ψ2' HeqP Heqψ;
    try discriminate HeqP; try discriminate Heqψ.
  - (* clean: both components inherit both conditions *)
    subst; simpl in H, H0.
    split; apply fsh_clean; clear - H H0; fsetdec.
  - (* flexfree *)
    subst.
    destruct (pskl_flex_free_arrow_inv H) as [Hf1 Hf2].
    split; apply fsh_flexfree; assumption.
  - (* arrow *)
    inversion HeqP; inversion Heqψ; subst; split; assumption.
Qed.

(** Sub-UnivGhostLG: the target loses a dotted ghost, [P0] is kept. *)
Lemma flex_shield_topholeg_r_inv : forall Θ0 Ψ' Δρ P0 ψ,
  flex_shield Θ0 Ψ' Δρ P0 (uskl_topholeg ψ) ->
  flex_shield Θ0 Ψ' Δρ P0 ψ.
Proof.
  intros Θ0 Ψ' Δρ P0 ψ H.
  remember (uskl_topholeg ψ) as ψa eqn:Heqψ.
  revert ψ Heqψ; induction H; intros ψ' Heqψ; try discriminate Heqψ.
  - subst; simpl in H, H0. apply fsh_clean; clear - H H0; fsetdec.
  - apply fsh_flexfree; exact H.
  - (* all_l : push the descent under the P0-binder by the IH *)
    apply fsh_all_l with (L := L); intros α Hα; apply H0; [ exact Hα | exact Heqψ ].
  - (* tophole_l *) apply fsh_tophole_l; apply IHflex_shield; exact Heqψ.
  - (* topholeg_r *) inversion Heqψ; subst; assumption.
Qed.

(** The [P0]-side ∀◇ strip (SolS-UnivGhostL / SolE-GhostGuarded keep the
    target and strip the payload's ghost). *)
Lemma flex_shield_tophole_l_inv : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ (pskl_tophole P0) ψa ->
  flex_shield Θ0 Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H.
  remember (pskl_tophole P0) as P eqn:HeqP.
  revert P0 HeqP; induction H; intros P0' HeqP; try discriminate HeqP.
  - apply fsh_clean; assumption.
  - subst; apply fsh_flexfree; apply pskl_flex_free_tophole_inv; exact H.
  - (* all_r : push under the ψa-binder by the IH *)
    apply fsh_all_r with (L := L) (ε := ε); intros α Hα;
      apply H0; [ exact Hα | exact HeqP ].
  - (* tophole_l *) inversion HeqP; subst; assumption.
  - (* topholeg_r *) apply fsh_topholeg_r; apply IHflex_shield; exact HeqP.
  - (* rho_var: the target is untouched by stripping the payload's ghost *)
    apply fsh_rho_var; exact H.
Qed.

(** **Sub-ForallR**: [P0 = ∀.P0₀] descends, the target is kept, and the
    context gains the rigid binder.  The [fsh_all_r] case is where the two
    one-sided rules would fail to commute — they do not, because the
    induction hypothesis re-derives the opposite-sided rule. *)
Lemma flex_shield_descend_l : forall Θ0 Ψ' Δρ P0 ψa,
  flex_shield Θ0 Ψ' Δρ (pskl_all_syn P0) ψa ->
  forall γ, γ `notin` dom Θ0 ->
  flex_shield ((γ ~ abind_tvar) ++ Θ0) Ψ' Δρ
    (open_pskl_wrt_pskl P0 (pskl_var_f γ)) ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H.
  remember (pskl_all_syn P0) as P eqn:HeqP.
  revert P0 HeqP; induction H; intros P0' HeqP γ Hγ;
    try discriminate HeqP.
  - (* clean: the target is untouched *)
    apply fsh_clean; assumption.
  - (* flexfree *)
    subst; apply fsh_flexfree; apply pskl_flex_free_open_tvar; assumption.
  - (* all_l: rename the family's binder to γ, then weaken the context *)
    inversion HeqP; subst.
    apply flex_shield_weaken_tvar.
    pick fresh α for (L `union` ftvar_in_pskl P0' `union` singleton γ).
    rewrite (subst_pskl_in_pskl_intro α P0' (pskl_var_f γ));
      [ | clear - Fr; fsetdec ].
    eapply flex_shield_rename_l;
      [ apply (H α ltac:(clear - Fr; fsetdec))
      | intros Hflex;
        (* γ is fresh for Θ0, hence not one of its flexibles *)
        destruct Hflex as [Hb | [τ Hb]];
        apply Hγ; eapply binds_In; eassumption ].
  - (* all_r: rebuild the ψa-side rule from the IH *)
    apply fsh_all_r with (L := L) (ε := ε); intros α Hα.
    apply H0; [ exact Hα | exact HeqP | exact Hγ ].
  - (* topholeg_r *)
    apply fsh_topholeg_r; apply IHflex_shield; [ exact HeqP | exact Hγ ].
  - (* rho_var: the target is untouched by the ForallR descent *)
    apply fsh_rho_var; exact H.
Qed.

(** **Sub-ForallL**: the target's TAGGED quantifier is instantiated, so its
    binder joins Δρ.  The clean rule is IMPOSSIBLE here — [ε ∈ Ψ'] and
    [ε ∈ ftag(∀^ε.ψ)] — which is exactly why the premise excludes the two
    counterexamples, and why a surviving derivation is flex-free or
    structural and therefore pushes down. *)
Lemma flex_shield_descend_r : forall Θ0 Ψ' Δρ ε P0 ψ,
  flex_shield Θ0 Ψ' Δρ P0 (uskl_all_etag ε ψ) ->
  ε `in` Ψ' ->
  forall β, β `notin` Δρ -> β `notin` ftvar_in_uskl ψ ->
  flex_shield Θ0 Ψ' (add β Δρ) P0 (open_uskl_wrt_uskl ψ (uskl_var_f β)).
Proof.
  intros Θ0 Ψ' Δρ ε P0 ψ H.
  remember (uskl_all_etag ε ψ) as ψa eqn:Heqψ.
  revert ε ψ Heqψ; induction H; intros ε' ψ' Heqψ Hε β HβΔ Hβ;
    try discriminate Heqψ.
  - (* clean: IMPOSSIBLE — the instantiated tag is in Ψ' *)
    exfalso; subst; simpl in H0. clear - H0 Hε; fsetdec.
  - (* flexfree: nothing to protect, at any Δρ *)
    apply fsh_flexfree; exact H.
  - (* all_l: rebuild the P0-side rule from the IH *)
    apply fsh_all_l with (L := L); intros α Hα.
    eapply H0; [ exact Hα | exact Heqψ | exact Hε | exact HβΔ | exact Hβ ].
  - (* all_r: rename the family's binder to β *)
    inversion Heqψ; subst.
    pick fresh α for (L `union` ftvar_in_uskl ψ' `union` singleton β
                        `union` Δρ).
    rewrite (subst_bskl_in_uskl_intro α ψ' (uskl_var_f β));
      [ | clear - Fr; fsetdec ].
    assert (HαL : α `notin` L) by (clear - Fr; solve_notin).
    assert (HαΔ : α `notin` Δρ) by (clear - Fr; solve_notin).
    assert (Hαψ : α `notin` ftvar_in_uskl ψ') by (clear - Fr; solve_notin).
    eapply flex_shield_rename_r;
      [ apply (H α HαL)
      | exact HαΔ
      | exact HβΔ
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ'
                      (uskl_var_f α)) as Hup;
        simpl in Hup;
        assert (Hαβ : α <> β)
          by (apply notin_singleton_1; clear - Fr; solve_notin);
        clear - Hup Hβ Hαβ; fsetdec ].
  - (* tophole_l *)
    apply fsh_tophole_l;
      eapply IHflex_shield; [ exact Heqψ | exact Hε | exact HβΔ | exact Hβ ].
Qed.

(** The TWO-SIDED descent — consistency's ForallInh opens BOTH sides at the
    same binder — is just the two one-sided descents composed.  So the
    two-sided row is not a separate obligation: the guess's binder joins Δρ
    (it IS ρ-replaced from the subtyping side's point of view) and the
    payload's binder is a fresh rigid of the context, which is exactly what
    the two descents already deliver. *)
Lemma flex_shield_descend_both : forall Θ0 Ψ' Δρ ε P0 ψ,
  flex_shield Θ0 Ψ' Δρ (pskl_all_syn P0) (uskl_all_etag ε ψ) ->
  ε `in` Ψ' ->
  forall α, α `notin` Δρ -> α `notin` ftvar_in_uskl ψ -> α `notin` dom Θ0 ->
  flex_shield ((α ~ abind_tvar) ++ Θ0) Ψ' (add α Δρ)
    (open_pskl_wrt_pskl P0 (pskl_var_f α))
    (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros Θ0 Ψ' Δρ ε P0 ψ H Hε α HαΔ Hαψ HαΘ.
  apply flex_shield_descend_l;
    [ eapply flex_shield_descend_r; [ exact H | exact Hε | exact HαΔ | exact Hαψ ]
    | exact HαΘ ].
Qed.

(* ===================================================================== *)
(*  Leaf use, and the regression test for the counterexample               *)
(* ===================================================================== *)

(** What the flexible-payload rows of the induction consume.  At a target
    that is neither a tagged ∀ nor a dotted ghost (the shapes with their
    own cases), only [fsh_clean] can justify a flexible [P0] — the
    structural rows need a compound payload and [fsh_flexfree] contradicts
    flexibility — so both conditions come out. *)
Lemma flex_shield_flex_leaf : forall Θ0 Ψ' Δρ α ψa,
  flex_shield Θ0 Ψ' Δρ (pskl_var_f α) ψa ->
  a_flex_tvar Θ0 α ->
  (forall ε ψ, ψa <> uskl_all_etag ε ψ) ->
  (forall ψ, ψa <> uskl_topholeg ψ) ->
  ((ftvar_in_uskl ψa) ∩ Δρ [=] empty /\ (ftag_in_uskl ψa) ∩ Ψ' [=] empty)
  \/ (exists α0, ψa = uskl_var_f α0 /\ α0 `in` Δρ).
Proof.
  intros Θ0 Ψ' Δρ α ψa H.
  remember (pskl_var_f α) as P eqn:HeqP.
  revert α HeqP; induction H; intros α' HeqP Hflex Hnall Hntg;
    try discriminate HeqP.
  - (* clean *) left; split; assumption.
  - (* flexfree: contradicts the flexibility of α *)
    exfalso; subst. apply (H α'); [ simpl; clear; fsetdec | exact Hflex ].
  - (* all_r: excluded by the shape side condition *)
    exfalso; eapply Hnall; reflexivity.
  - (* topholeg_r: likewise *)
    exfalso; eapply Hntg; reflexivity.
  - (* rho_var: the DIRTY-but-safe row — P6-Cv's leaf closes it *)
    right; eexists; split; [ reflexivity | exact H ].
Qed.

(** REGRESSION TEST for the repair — kept (like the [cex/] files) because it
    is what ties the mech-only premise to the machine-checked counterexample;
    the main theorem itself does not use it.

    The premise EXCLUDES the configuration
    of [cex_p6sv_forall_flex.v] — a raw-flexible payload facing a
    Ψ'-tagged quantifier whose binder is USED in the body.  (When the
    binder is UNUSED the configuration is harmless and correctly allowed:
    ρ replaces nothing, so no dirt reaches the flexible.) *)
Theorem flex_shield_excludes_cex : forall Θ0 Ψ' Δρ α ε ψ,
  a_flex_tvar Θ0 α ->
  ε `in` Ψ' ->
  (forall β, β `notin` ftvar_in_uskl ψ ->
     open_uskl_wrt_uskl ψ (uskl_var_f β)
     = uskl_arrow (uskl_var_f β) (uskl_var_f β)) ->
  ~ flex_shield Θ0 Ψ' Δρ (pskl_var_f α) (uskl_all_etag ε ψ).
Proof.
  intros Θ0 Ψ' Δρ α ε ψ Hflex Hε Hbody H.
  pick fresh β for (Δρ `union` ftvar_in_uskl ψ).
  pose proof (flex_shield_descend_r H Hε (β := β)
                ltac:(clear - Fr; fsetdec) ltac:(clear - Fr; fsetdec)) as Hd.
  rewrite (Hbody β ltac:(clear - Fr; fsetdec)) in Hd.
  destruct (flex_shield_flex_leaf Hd Hflex
              ltac:(intros ε0 ψ0 Hc; discriminate Hc)
              ltac:(intros ψ0 Hc; discriminate Hc))
    as [[Hclean _] | (α0 & Hc & _)]; [ | discriminate Hc ].
  cbn [ftvar_in_uskl] in Hclean.
  assert (Hin : β `in` empty) by (rewrite <- Hclean; clear; fsetdec).
  clear - Hin; fsetdec.
Qed.
