Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.consistency.prop_consis.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

Local Ltac ghost_close :=
  repeat split;
  first [ assumption | reflexivity | (simpl in *; fsetdec) ].

Lemma e_consis_inv_ghost_subject : forall Δ1 Δ2 S0 Θ0 P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_ghost ∼ Q ⊣ Θ1 }}e ->
  (forall β, P0 <> pskl_var_f β) ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = P0 /\ Δ2 ∩ ftvar_in_pskl P0 [=] empty.
Proof.
  intros * Hd Hnv. inversion Hd; subst;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | match goal with
                | H : guarded_pskl pskl_ghost |- _ => inversion H
                end ].
  all: ghost_close.
Qed.

Lemma e_consis_inv_ghost_pattern : forall Δ1 Δ2 S0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_ghost ] P ∼ Q ⊣ Θ1 }}e ->
  (forall β, P <> pskl_var_f β) ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = P /\ Δ1 ∩ ftvar_in_pskl P [=] empty.
Proof.
  intros * Hd Hnv. inversion Hd; subst;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | match goal with
                | H : guarded_pskl pskl_ghost |- _ => inversion H
                end ].
  all: ghost_close.
Qed.

Lemma e_consis_inv_ghost_flex_pattern : forall Δ1 Δ2 S0 Θ0 β Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ] pskl_ghost ∼ Q ⊣ Θ1 }}e ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = pskl_var_f β
    /\ Δ2 ∩ ftvar_in_pskl (pskl_var_f β) [=] empty.
Proof.
  intros * Hd. inversion Hd; subst;
    try solve [ congruence
              | match goal with
                | H : guarded_pskl pskl_ghost |- _ => inversion H
                end ].
  ghost_close.
Qed.

Lemma e_consis_inv_flex_subject_ghost : forall Δ1 Δ2 S0 Θ0 α Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_ghost ] (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  S1 = S0 /\ Θ1 = Θ0 /\ Q = pskl_var_f α
    /\ Δ1 ∩ ftvar_in_pskl (pskl_var_f α) [=] empty.
Proof.
  intros * Hd. inversion Hd; subst;
    try solve [ congruence
              | match goal with
                | H : guarded_pskl pskl_ghost |- _ => inversion H
                end ].
  ghost_close.
Qed.

Lemma swaps_dodge_nil : forall (S : atoms) a b,
  In (a, b) (@nil (atom * atom)) -> a `notin` S /\ b `notin` S.
Proof. intros S a b []. Qed.

Lemma e_consis_swaps : forall ps Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  forall Δ1' Δ2' S0',
  Δ1' [=] swaps_atoms ps Δ1 -> Δ2' [=] swaps_atoms ps Δ2 ->
  S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0)
       ⊢[ Δ1' | Δ2' | (swaps_pskl ps P0) ]
       (swaps_pskl ps P) ∼ (swaps_pskl ps Q) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ];
    intros * Hd Δ1' Δ2' S0' HD1 HD2 HS; simpl in *.
  - destruct (e_consis_supply_respect Hd HS) as [S1' [HS1 Hd']].
    exists S1'. split; [ exact HS1 | ].
    eapply e_consis_delta_respect; eassumption.
  - assert (H1 : swap_atoms a b Δ1 [=] swap_atoms a b Δ1) by reflexivity.
    assert (H2 : swap_atoms a b Δ2 [=] swap_atoms a b Δ2) by reflexivity.
    assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_consis_swap Hd H1 H2 Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ Hda _ _ _ HD1 HD2 HS)
      as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_guess_mono_swaps : forall ps S0 P S1 Ξ τ,
  e_guess_mono S0 P S1 Ξ τ ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    e_guess_mono S0' (swaps_pskl ps P) S1' (swaps_aenv ps Ξ)
      (swaps_ptyp ps τ).
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_guess_mono_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_guess_mono_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_guess_mono_rel : forall S0 P S1 Ξ A S1' Ξ' A',
  e_guess_mono S0 P S1 Ξ A ->
  e_guess_mono S0 P S1' Ξ' A' ->
  ftvar_in_pskl P [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_ptyp ps A = A'.
Proof.
  intros S0 P S1 Ξ A S1' Ξ' A' Hd Hd'.
  revert S1 Ξ A Hd.
  induction Hd' as
    [S0 α' Hα'
    |S0 S1' P Ξ' A' Dp' IH
    |S0 α
    |S0
    |S0 Sa' S1' P1 P2 Xa' Xb' Aa' Ab' D1' IH1 D2' IH2
    |S0 S1' P Ξ' Aa' β' Hβ' Dp' IH];
    intros S1 Ξ A Hd Hcov.
  -
    destruct (e_guess_mono_inv_ghost Hd) as [α [Hα [-> [-> ->]]]].
    exists ((α, α') :: nil). repeat apply conj.
    + intros ? ? [Heqp | []]. inversion Heqp; subst. split; assumption.
    + symmetry. exact (swap_atoms_fresh_add _ _ _ Hα Hα').
    + rewrite swaps_aenv_app_dist, swaps_aenv_one_flex, swaps_aenv_nil.
      cbn [swaps_atom]. rewrite swap_atom_l. reflexivity.
    + rewrite swaps_ptyp_var_f. cbn [swaps_atom]. rewrite swap_atom_l.
      reflexivity.
  -
    pose proof (e_guess_mono_inv_univ_ghost Hd) as Dp.
    simpl in Hcov.
    exact (IH S1 Ξ A Dp Hcov).
  -
    destruct (e_guess_mono_inv_var Hd) as [-> [-> ->]].
    exists nil. repeat apply conj; simpl; try reflexivity. intros ? ? [].
  -
    destruct (e_guess_mono_inv_unit Hd) as [-> [-> ->]].
    exists nil. repeat apply conj; simpl; try reflexivity. intros ? ? [].
  -
    destruct (e_guess_mono_inv_arrow Hd)
      as [Sa [Xa [Xb [Aa [Ab [-> [-> [D1 D2]]]]]]]].
    simpl in Hcov.
    destruct (IH1 Sa Xa Aa D1 ltac:(clear - Hcov; fsetdec))
      as [ps1 [Hav1 [HS1 [HX1 HA1]]]].
    assert (HP2 : swaps_pskl ps1 P2 = P2)
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    pose proof HS1 as HS1r. symmetry in HS1r.
    destruct (e_guess_mono_swaps ps1 D2 HS1r) as [S2t [HS2t D2t]].
    rewrite HP2 in D2t.
    pose proof (e_guess_mono_supply_grows D1') as Hgr1'.
    destruct (IH2 S2t (swaps_aenv ps1 Xb) (swaps_ptyp ps1 Ab)
                  D2t ltac:(clear - Hcov Hgr1'; fsetdec))
      as [ps2 [Hav2 [HS2 [HX2 HA2]]]].

    pose proof (e_guess_mono_generated_in_supply D1') as Hdom1'.
    pose proof (e_guess_mono_generated_ftvar D1') as Hftv1'.
    pose proof (e_guess_mono_ftv D1') as HftA1'.
    assert (HX1' : swaps_aenv ps2 Xa' = Xa')
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hdom1' Hftv1'; fsetdec).
    assert (HA1' : swaps_ptyp ps2 Aa' = Aa')
      by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hdom1' HftA1' Hcov Hgr1'; fsetdec).
    exists (ps1 ++ ps2). repeat apply conj.
    + apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1'; fsetdec.
    + exact (swaps_atoms_app_transport HS2t HS2).
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_ptyp_app, !swaps_ptyp_arrow, HA1, HA2, HA1'.
      reflexivity.
  -
    destruct (e_guess_mono_inv_all_syn Hd) as [β [Aa [Hβ [-> Dp]]]].
    simpl in Hcov.
    destruct (e_guess_mono_swap Dp (swap_atoms_fresh_add _ _ _ Hβ Hβ'))
      as [S1t [HS1t Dpt]].
    rewrite swap_pskl_open_var, swap_atom_l, (swap_pskl_fresh_id β β' P)
      in Dpt by (clear - Hcov Hβ Hβ'; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β'))
      as Hup.
    destruct (IH S1t (swap_aenv β β' Ξ) (swap_ptyp β β' Aa)
                 Dpt ltac:(clear - Hup Hcov; simpl in *; fsetdec))
      as [ps' [Hav' [HS' [HX' HA']]]].
    exists ((β, β') :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_ptyp swap_ptyp]. rewrite swap_ptyp_close.
      rewrite swap_atom_l.
      rewrite swaps_ptyp_all, swaps_ptyp_close, HA'.
      f_equal. f_equal. apply (swaps_atom_dodge_in Hav'). fsetdec.
Qed.

Local Ltac kill_unguarded :=
  repeat match goal with
         | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
         | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
         | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
         end.

Lemma e_consis_inv_arrow : forall Δ1 Δ2 S0 Θ0 P0a P0b P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
     (pskl_arrow P1 P2) ∼ Q ⊣ Θ1 }}e ->
  exists Sm Θm Q1 Q2,
    Q = pskl_arrow Q1 Q2 /\
    {{ S0 ↝ Sm ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θm }}e /\
    {{ Sm ↝ S1 ⊨ Θm ⊢[ Δ1 | Δ2 | P0b ] P2 ∼ Q2 ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_unit : forall Δ1 Δ2 S0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] pskl_unit ∼ Q ⊣ Θ1 }}e ->
  Q = pskl_unit /\ S1 = S0 /\ Θ1 = Θ0.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_forall_inh : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
     (pskl_all_syn P) ∼ Q ⊣ Θ1 }}e ->
  exists α Qb,
    α `notin` S0 /\ Q = pskl_all_syn (close_pskl_wrt_pskl α Qb) /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | (add α Δ2)
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Qb
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_forall_syn : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     (pskl_all_syn P) ∼ Q ⊣ Θ1 }}e ->
  exists α Qb,
    α `notin` S0 /\ Q = pskl_all_syn (close_pskl_wrt_pskl α Qb) /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ Δ1 | (add α Δ2) | (pskl_univ_ghost P0) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Qb
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_univ_ghost : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}e ->
  exists Qb,
    Q = pskl_univ_ghost Qb /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Qb ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto. Qed.

Lemma e_consis_inv_univ_ghost1 : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
     (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}e ->
  exists α Qb,
    α `notin` S0 /\ Q = pskl_all_syn (close_pskl_wrt_pskl α Qb) /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | Δ2
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (pskl_univ_ghost P) ∼ Qb ⊣ ((α ~ abind_tvar) ++ Θ1) }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; eauto 10. Qed.

Lemma e_consis_inv_univ_ghost2_unit : forall Δ1 Δ2 S0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ]
     (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] P ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_univ_ghost2_arrow : forall Δ1 Δ2 S0 Θ0 P0a P0b P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
     (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ] P ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_univ_ghost_r_unit : forall Δ1 Δ2 S0 Θ0 P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     pskl_unit ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_unit ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_univ_ghost_r_arrow : forall Δ1 Δ2 S0 Θ0 P0 P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     (pskl_arrow P1 P2) ∼ Q ⊣ Θ1 }}e ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_arrow P1 P2) ∼ Q ⊣ Θ1 }}e.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded; auto. Qed.

Lemma e_consis_inv_flex_r : forall Δ1 Δ2 S0 Θ0 α P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ] P ∼ Q ⊣ Θ1 }}e ->
  (forall β, P <> pskl_var_f β) -> P <> pskl_ghost ->
  (forall Pb, P <> pskl_univ_ghost Pb) ->
  Q = pskl_var_f α /\ a_non_flex Θ0 P /\
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 }}e.
Proof.
  intros * Hd Hnv Hnh Hnt. inversion Hd; subst; kill_unguarded;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | exfalso; eapply Hnt; reflexivity ].
  all: (split; [ reflexivity | split; assumption ]).
Qed.

Lemma e_consis_inv_flex_l : forall Δ1 Δ2 S0 Θ0 α P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  (forall β, P0 <> pskl_var_f β) -> P0 <> pskl_ghost ->
  (forall Pb, P0 <> pskl_univ_ghost Pb) ->
  Q = pskl_var_f α /\ a_non_flex Θ0 P0 /\
  {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P0 ⊣ Θ1 }}e.
Proof.
  intros * Hd Hnv Hnh Hnt. inversion Hd; subst; kill_unguarded;
    try solve [ congruence
              | exfalso; eapply Hnv; reflexivity
              | exfalso; eapply Hnt; reflexivity ].
  all: (split; [ reflexivity | split; assumption ]).
Qed.

Lemma e_consis_inv_var_univ_ghost : forall Δ1 Δ2 S0 Θ0 β P1 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ]
     (pskl_univ_ghost P1) ∼ Q ⊣ Θ1 }}e ->
  (a_flex_tvar Θ0 β /\ Q = pskl_var_f β /\
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] β ≔ (pskl_univ_ghost P1) ⊣ Θ1 }}e)
  \/ (a_non_flex Θ0 (pskl_var_f β) /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ] P1 ∼ Q ⊣ Θ1 }}e).
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded.
  - right; auto.
  - left; repeat split; auto. eapply e_assign_target_flex; eassumption.
Qed.

Lemma e_consis_inv_univ_ghost_var : forall Δ1 Δ2 S0 Θ0 α P0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
     (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
  (a_flex_tvar Θ0 α /\ Q = pskl_var_f α /\
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ (pskl_univ_ghost P0) ⊣ Θ1 }}e)
  \/ (a_non_flex Θ0 (pskl_var_f α) /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_var_f α) ∼ Q ⊣ Θ1 }}e).
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded.
  - left; repeat split; auto. eapply e_assign_target_flex; eassumption.
  - right; auto.
Qed.

Lemma e_consis_inv_var_var : forall Δ1 Δ2 S0 Θ0 α β Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ]
     (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->

  (α = β /\ binds α abind_tvar Θ0 /\ Q = pskl_var_f α /\
     S1 = S0 /\ Θ1 = Θ0)

  \/ (Q = pskl_var_f α /\ {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e)

  \/ (a_non_flex Θ0 (pskl_var_f β) /\ Q = pskl_var_f α /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ (pskl_var_f β) ⊣ Θ1 }}e)

  \/ (a_non_flex Θ0 (pskl_var_f α) /\ Q = pskl_var_f β /\
      {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] β ≔ (pskl_var_f α) ⊣ Θ1 }}e).
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded.
  - left; repeat split; auto.
  - right; left; auto.
  - right; right; left; auto.
  - right; right; right; auto.
Qed.

Local Ltac kill_skip_other :=
  match goal with
  | H : _ = abind_tvar \/ (exists _, _ = abind_var_typ _) \/
        (exists _, _ = abind_var_skl _) |- _ =>
      solve [ destruct H as [Hb | [[? Hb] | [? Hb]]]; discriminate ]
  end.

Lemma e_assign_inv_nil : forall S0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ nil ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

Lemma e_assign_inv_flex_self : forall S0 Θ0 Ξ α P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  (Ξ = nil /\ P = pskl_univ_ghost (pskl_var_f α) /\ S1 = S0 /\
     Θ1 = (α ~ abind_flex_mono) ++ Θ0)
  \/ (α `notin` ftvar_in_pskl P /\
      exists βs τ, e_guess_mono S0 P S1 βs τ /\ mono_ptyp τ /\
        Θ1 = (α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0).
Proof.
  intros * Hd. inversion Hd; subst; try congruence.
  - left; split; [ reflexivity
                 | split; [ reflexivity | split; reflexivity ] ].
  - right; split; [ assumption | eauto 10 ].
Qed.

Lemma e_assign_inv_flex_other : forall S0 Θ0 Ξ α β P S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  (β `in` ftvar_in_pskl P /\
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ (Ξ ++ (β ~ abind_flex_mono)) ] α ≔ P ⊣ Θ1 }}e)
  \/ (β `notin` ftvar_in_pskl P /\ exists Θ1',
        Θ1 = (β ~ abind_flex_mono) ++ Θ1' /\
        {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e).
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence.
  - left; split; assumption.
  - right; split; [ assumption | eauto ].
Qed.

Lemma e_assign_inv_def : forall S0 Θ0 Ξ α β τ P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α /\
  exists Θ1' Q, Θ1 = (β ~ abind_flex_mono_def τ) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ (Ξ ++ Θ0) ⊢[ empty | empty
         | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ]
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ∼ Q
       ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. split; [ assumption | eauto ]. Qed.

Lemma e_assign_inv_tvar : forall S0 Θ0 Ξ α β P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  β `notin` ftvar_in_pskl P /\ exists Θ1',
    Θ1 = (β ~ abind_tvar) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. split; [ assumption | eauto ]. Qed.

Lemma e_assign_inv_var_typ : forall S0 Θ0 Ξ α x A P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((x ~ abind_var_typ A) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (x ~ abind_var_typ A) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_assign_inv_var_skl : forall S0 Θ0 Ξ α x Q P S1 Θ1,
  {{ S0 ↝ S1 ⊨ ((x ~ abind_var_skl Q) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (x ~ abind_var_skl Q) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_unify_inv_nil : forall S0 α β S1 Θ1,
  {{ S0 ↝ S1 ⊨ nil ⊲ α ≈ᵘ β ⊣ Θ1 }}e -> False.
Proof.
  intros * Hd. inversion Hd; subst.
  destruct H as [Hb | [τ Hb]]; inversion Hb.
Qed.

Lemma e_unify_inv_flex_l : forall S0 Θ0 α β S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar Θ0 β /\ S1 = S0 /\
  Θ1 = (α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0.
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence; try kill_skip_other.
  split; [ assumption | split; reflexivity ].
Qed.

Lemma e_unify_inv_flex_r : forall S0 Θ0 α β S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar Θ0 α /\ S1 = S0 /\
  Θ1 = (β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0.
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence; try kill_skip_other.
  split; [ assumption | split; reflexivity ].
Qed.

Lemma e_unify_inv_flex_skip : forall S0 Θ0 γ α β S1 Θ1,
  α <> β -> γ <> α -> γ <> β ->
  {{ S0 ↝ S1 ⊨ ((γ ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (γ ~ abind_flex_mono) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1' }}e.
Proof.
  intros * Hne H1 H2 Hd.
  inversion Hd; subst; try congruence; try kill_skip_other. eauto.
Qed.

Lemma e_unify_inv_def : forall S0 Θ0 γ τ α β S1 Θ1,
  α <> β ->
  {{ S0 ↝ S1 ⊨ ((γ ~ abind_flex_mono_def τ) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  a_flex_tvar ((γ ~ abind_flex_mono_def τ) ++ Θ0) α /\
  a_flex_tvar ((γ ~ abind_flex_mono_def τ) ++ Θ0) β /\
  exists Θ1' Q, Θ1 = (γ ~ abind_flex_mono_def τ) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty
         | (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f β))) ]
       (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f α))) ∼ Q
       ⊣ Θ1' }}e.
Proof.
  intros * Hne Hd.
  inversion Hd; subst; try congruence; try kill_skip_other.
  split; [ assumption | split; [ assumption | eauto ] ].
Qed.

Lemma e_unify_inv_other : forall S0 Θ0 c b α β S1 Θ1,
  α <> β ->
  (b = abind_tvar \/ (exists A, b = abind_var_typ A) \/
   (exists Q, b = abind_var_skl Q)) ->
  {{ S0 ↝ S1 ⊨ ((c ~ b) ++ Θ0) ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
  exists Θ1', Θ1 = (c ~ b) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1' }}e.
Proof.
  intros * Hne Hb Hd.
  destruct Hb as [-> | [[A ->] | [Q ->]]];
    inversion Hd; subst; try congruence; eauto.
Qed.

Lemma e_unify_consis_refl_mono :
  (forall S0 Θ0 Ξ α P S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e -> True) /\
  (forall S0 Θ0 α β S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
     α = β -> aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0) /\
  (forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
     P0 = P -> (exists A, P = ptyp_to_pskl A /\ mono_ptyp A) ->
     aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0).
Proof.
  apply e_assign_unify_consis_mutind.

  1-8: intros; exact I.

  -  intros S Θ0 α Hf Heq HD. split; reflexivity.
  -
    intros S Θ0 α β Hne Hf Heq HD. contradiction.
  -
    intros S Θ0 α β Hne Hf Heq HD. contradiction.
  -
    intros S0 S1 Θ0 Θ1 α1 τ α β Q Hfa Hfb Hd IH Heq HD. subst.
    destruct (aenv_defs_mono_cons_inv HD) as [Hmτ HD0].
    destruct IH as [-> ->];
      [ reflexivity
      | eexists; split;
        [ reflexivity
        | apply mono_ptyp_subst; [ apply mono_ptyp__var | exact Hmτ ] ]
      | exact HD0
      | ].
    split; reflexivity.
  -
    intros S0 S1 Θ0 Θ1 α1 α β Hne1 Hne2 Hd IH Heq HD. subst.
    destruct (aenv_defs_mono_cons_inv HD) as [_ HD0].
    destruct IH as [-> ->]; [ reflexivity | exact HD0 | ].
    split; reflexivity.
  -
    intros S0 S1 Θ0 Θ1 c b α β Hb Hd IH Heq HD. subst.
    destruct (aenv_defs_mono_cons_inv HD) as [_ HD0].
    destruct IH as [-> ->]; [ reflexivity | exact HD0 | ].
    split; reflexivity.

  -
    intros Δ1 Δ2 S Θ0 P0 Hdis Heq Hsh HD. split; reflexivity.
  -  intros Δ1 Δ2 S Θ0 Heq Hsh HD. split; reflexivity.
  -  intros Δ1 Δ2 S Θ0 α Hb Heq Hsh HD. split; reflexivity.
  -
    intros Δ1 Δ2 S0 S1 S2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2
           Hd1 IH1 Hd2 IH2 Heq Hsh HD.
    destruct Hsh as [Ash [He Hmo]]; destruct Ash; simpl in He;
      try discriminate.
    inversion He; subst. inversion Heq; subst. inversion Hmo; subst.
    destruct IH1 as [-> ->];
      [ reflexivity
      | eexists; split; [ reflexivity | assumption ] | exact HD | ].
    destruct IH2 as [-> ->];
      [ reflexivity
      | eexists; split; [ reflexivity | assumption ] | exact HD | ].
    split; reflexivity.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hα Hd IH Heq Hsh HD.
    destruct Hsh as [Ash [He Hmo]]; destruct Ash; simpl in He;
      try discriminate; inversion Hmo.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hα Hd IH Heq Hsh HD. discriminate.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hd IH Heq Hsh HD.
    exfalso. destruct Hsh as [Ash [He Hmo]]; destruct Ash; discriminate.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α Hα Hd IH Heq Hsh HD. discriminate.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hg Hnf Hd IH Heq Hsh HD.
    exfalso. destruct Hsh as [Ash [He Hmo]]; destruct Ash; discriminate.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α β Hd IH Heq Hsh HD.
    inversion Heq; subst.
    destruct IH as [-> ->]; [ reflexivity | exact HD | ].
    split; reflexivity.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P0 Hnf Hnhole Hd IH Heq Hsh HD.
    exfalso. subst. destruct Hnf as [_ Hf]. apply Hf.
    apply a_flex_var_iff_tvar. eapply e_assign_target_flex; eassumption.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 α P Hnf Hnhole Hd IH Heq Hsh HD.
    exfalso. subst. destruct Hnf as [_ Hf]. apply Hf.
    apply a_flex_var_iff_tvar. eapply e_assign_target_flex; eassumption.
  -
    intros Δ1 Δ2 S Θ0 P Hdis Heq Hsh HD. split; reflexivity.
  -
    intros Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q Hg Hnf Hd IH Heq Hsh HD.
    exfalso. subst.
    destruct Hsh as [Ash [He Hmo]]; destruct Ash; discriminate.
Qed.

Corollary e_unify_refl : forall S0 Θ0 α S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ α ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros. eapply (proj1 (proj2 e_unify_consis_refl_mono));
    [ eassumption | reflexivity | assumption ].
Qed.

Definition consis_call_answer {S0 : supply} {Θ : aenv} {c : consis_call}
    (o : option (sig (consis_call_spec S0 Θ c))) : option consis_result :=
  match o with None => None | Some r => Some (proj1_sig r) end.

Definition consis_call_run (S0 : supply) (Θ : aenv) (c : consis_call)
    (Sd : supply) (Θd : aenv) (Qd : pskl) : Prop :=
  match c with
  | consis_call_assign Ξ α P => {{ S0 ↝ Sd ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θd }}e
  | consis_call_unify α β    => {{ S0 ↝ Sd ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θd }}e
  | consis_call_consis Δ1 Δ2 P0 P =>
      {{ S0 ↝ Sd ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Qd ⊣ Θd }}e
  end.

Definition consis_call_out_rel (c : consis_call) (Qd Qr : pskl) : Prop :=
  match c with
  | consis_call_consis _ _ _ _ => Qd = Qr
  | _                          => True
  end.

Definition consis_call_uniq (Θ : aenv) (c : consis_call) : Prop :=
  match c with
  | consis_call_assign Ξ _ _ => uniq (Ξ ++ Θ)
  | _                        => uniq Θ
  end.

Definition consis_call_cover (Θ : aenv) (c : consis_call) : atoms :=
  match c with
  | consis_call_assign Ξ _ P => ftvar_in_aenv (Ξ ++ Θ) ∪ ftvar_in_pskl P
  | consis_call_unify _ _    => ftvar_in_aenv Θ
  | consis_call_consis Δ1 Δ2 P0 P =>
      ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P ∪ Δ1 ∪ Δ2
  end.

Definition consis_call_complete (S0 : supply) (Θ : aenv) (c : consis_call)
    : Prop :=
  forall (Hlc : consis_call_lc c) (HD : consis_call_defs_mono Θ c)
         (H : e_consis_call_order S0 Θ c),
    consis_call_uniq Θ c ->
    consis_call_cover Θ c [<=] S0 ->
    forall Sd Θd Qd, consis_call_run S0 Θ c Sd Θd Qd ->
    exists r ps,
      consis_call_answer (e_consis_call_impl c S0 Θ Hlc HD H) = Some r
      /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
      /\ swaps_atoms ps Sd [=] cs_supply r
      /\ swaps_aenv ps Θd = cs_ctx r
      /\ consis_call_out_rel c (swaps_pskl ps Qd) (cs_out r).

Local Ltac kill_ccall Hmot Hu Hcov Hder q r Hr ps Hav HS HT HQ :=
  match goal with
  | |- context [ e_consis_call_impl ?c ?S ?T ?hl ?hd ?h ] =>
      let Hx := fresh "Hx" in
      let Hcl := fresh "Hcl" in
      let rr := fresh "rr" in
      destruct (Hmot hl hd h Hu Hcov _ _ q Hder)
        as [r [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_consis_call_impl c S T hl hd h) as [ [rr Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx; cbn [consis_call_answer] in Hx;
      [ inversion Hx; subst; clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

Ltac head_fresh Hav Hcov :=
  apply swaps_aenv_fresh_id; intros a0 b0 Hin;
  let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
  destruct (Hav a0 b0 Hin) as [Ha0 Hb0]; split;
  clear - Ha0 Hb0 Hcov; repeat rewrite ftvar_in_aenv_app in Hcov;
  simpl in *; fsetdec.

Local Ltac out_var_id Hav Hcov :=
  cbn [cs_out proj1_sig]; rewrite swaps_pskl_var_f; f_equal;
  apply swaps_atom_notin; intros a0 b0 Hin;
  let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
  let Heq := fresh "Heq" in
  destruct (Hav a0 b0 Hin) as [Ha0 Hb0];
  split; intro Heq; subst; clear - Ha0 Hb0 Hcov; simpl in *; fsetdec.

Local Ltac flex_test_true Hft :=
  let Hfb := fresh "Hfb" in
  lazymatch goal with
  | |- context [ sumbool_of_bool (flex_bound_ck ?T ?a) ] =>
      destruct (sumbool_of_bool (flex_bound_ck T a)) as [Hfb | Hfb];
      [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
          [ exact Hfb | exact Hft ] ]
  end.

Local Ltac do_solve_m Hocc Hg Hmt Hcov rg Hgs ps Hav HSg HXg HAg :=
  match goal with
  | |- context [ sumbool_of_bool (mem ?a (ftvar_in_pskl ?p)) ] =>
      let Hmem := fresh "Hmem" in
      destruct (sumbool_of_bool (mem a (ftvar_in_pskl p))) as [Hmem | Hmem];
      [ exfalso; apply mem_true_in in Hmem; contradiction | ]
  end;
  cbv beta iota;
  match goal with
  | |- context [ e_guess_mono_impl ?s ?p ?h ] =>
      destruct (e_guess_mono_impl s p h) as [rg Hgs];
      unfold guess_spec in Hgs
  end;
  cbv beta iota;
  destruct (e_guess_mono_rel Hg Hgs
              ltac:(clear - Hcov; repeat rewrite ftvar_in_aenv_app in Hcov;
                    simpl in *; fsetdec))
    as [ps [Hav [HSg [HXg HAg]]]];
  match goal with
  | |- context [ sumbool_of_bool (mono_ck (gr_type ?r)) ] =>
      let Hmc := fresh "Hmc" in
      destruct (sumbool_of_bool (mono_ck (gr_type r))) as [Hmc | Hmc];
      [ | exfalso; rewrite <- HAg in Hmc;
          contradict Hmc; apply Bool.not_false_iff_true;
          apply mono_ck_complete; apply mono_ptyp_swaps; exact Hmt ]
  end;
  cbv beta iota;
  let Hain := fresh "Hain" in
  assert (Hain : True) by exact I;
  eexists; exists ps;
  split; [ reflexivity | ];
  repeat apply conj;
  [ exact Hav
  | cbn [cs_supply proj1_sig]; exact HSg
  | cbn [cs_ctx proj1_sig];
    rewrite swaps_aenv_app_dist; rewrite swaps_aenv_app_dist;
    rewrite swaps_aenv_one_def, HXg, HAg;
    rewrite (swaps_atom_notin ps)
      by (intros a0 b0 Hin;
          let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
          let Heq := fresh "Heq" in
          destruct (Hav a0 b0 Hin) as [Ha0 Hb0];
          split; intro Heq; subst;
          clear - Ha0 Hb0 Hcov;
          repeat rewrite ftvar_in_aenv_app in Hcov; simpl in *; fsetdec);
    rewrite (swaps_aenv_fresh_id ps)
      by (intros a0 b0 Hin;
          let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
          destruct (Hav a0 b0 Hin) as [Ha0 Hb0]; split;
          clear - Ha0 Hb0 Hcov;
          repeat rewrite ftvar_in_aenv_app in *; simpl in *; fsetdec);
    reflexivity
  | exact I ].

Local Ltac do_flex_id HD Hd :=
  let Hs := fresh "Hs" in let Ht := fresh "Ht" in
  destruct (e_unify_refl Hd HD) as [Hs Ht]; subst;
  match goal with
  | |- context [ sumbool_of_bool (flex_bound_ck ?T ?a) ] =>
      let Hfb := fresh "Hfb" in
      destruct (sumbool_of_bool (flex_bound_ck T a)) as [Hfb | Hfb];
      [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
          [ exact Hfb | exact (proj1 (e_unify_target_flex Hd)) ] ]
  end;
  cbv beta iota;
  eexists; exists (@nil (atom * atom));
  split; [ reflexivity | ];
  repeat apply conj; [ intros ? ? [] | cbn [swaps_atoms cs_supply proj1_sig]; reflexivity
          | cbn [swaps_aenv cs_ctx proj1_sig]; reflexivity | exact I ].

Local Ltac split_eqdec Hl Hr :=
  lazymatch goal with
  | |- context [ @eq_dec ?T ?E ?x ?y ] =>
      destruct (@eq_dec T E x y) as [ Hl | Hr ]
  end.

Local Ltac do_flex_l Hmot Hd Hu Hcov :=
  let Hnf := fresh "Hnf" in let Da := fresh "Da" in
  let Hft := fresh "Hft" in let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in
  let ps := fresh "ps" in let Hav := fresh "Hav" in
  let HS := fresh "HS" in let HT := fresh "HT" in let HQ := fresh "HQ" in
  destruct (e_consis_inv_flex_l Hd ltac:(intros; discriminate)
              ltac:(discriminate) ltac:(intros; discriminate))
    as [-> [Hnf Da]];
  pose proof (e_assign_target_flex Da) as Hft;
  flex_test_true Hft; cbv beta iota;
  lazymatch goal with
  | |- context [ e_consis_call_impl (consis_call_assign nil ?a ?p)
                   ?s ?t ?x ?y ?zz ] =>
      assert (Hcov0 : ftvar_in_aenv (nil ++ t) ∪ ftvar_in_pskl p [<=] s)
        by (clear - Hcov; simpl in *; fsetdec)
  end;
  kill_ccall Hmot Hu Hcov0 Da pskl_unit r Hr ps Hav HS HT HQ;
  eexists; exists ps;
  split; [ reflexivity | ];
  repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
          | cbn [cs_ctx proj1_sig]; exact HT | ];
  out_var_id Hav Hcov.

Local Ltac do_ghost_cell Hdis :=
  match goal with
  | |- context [ sumbool_of_bool (is_empty ?S) ] =>
      let He := fresh "He" in
      destruct (sumbool_of_bool (is_empty S)) as [He | He];
      [ cbv beta iota
      | exfalso; rewrite AtomSetImpl.is_empty_1 in He;
        [ discriminate | clear - Hdis; simpl in *; fsetdec ] ]
  end;
  eexists; exists (@nil (atom * atom));
  split; [ reflexivity | ];
  repeat apply conj; [ intros ? ? []
          | cbn [swaps_atoms cs_supply proj1_sig]; reflexivity
          | cbn [swaps_aenv cs_ctx proj1_sig]; reflexivity
          | cbn [swaps_pskl cs_out proj1_sig]; reflexivity ].

Local Ltac do_pass Hmot Hd Hu Hcov Qd :=
  let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in
  let ps := fresh "ps" in let Hav := fresh "Hav" in
  let HS := fresh "HS" in let HT := fresh "HT" in let HQ := fresh "HQ" in
  lazymatch goal with
  | |- context [ e_consis_call_impl ?c ?s ?t ?x ?y ?zz ] =>
      assert (Hcov0 : consis_call_cover t c [<=] s)
        by (clear - Hcov;
            cbn [consis_call_cover ftvar_in_pskl] in *; fsetdec)
  end;
  kill_ccall Hmot Hu Hcov0 Hd Qd r Hr ps Hav HS HT HQ;
  exists r, ps;
  split; [ reflexivity | ];
  repeat apply conj; [ exact Hav | exact HS | exact HT | exact HQ ].

Local Ltac do_flex_r Hmot Hd Hu Hcov :=
  let Hnf := fresh "Hnf" in let Da := fresh "Da" in
  let Hft := fresh "Hft" in let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in
  let ps := fresh "ps" in let Hav := fresh "Hav" in
  let HS := fresh "HS" in let HT := fresh "HT" in let HQ := fresh "HQ" in
  destruct (e_consis_inv_flex_r Hd ltac:(intros; discriminate)
              ltac:(discriminate) ltac:(intros; discriminate))
    as [-> [Hnf Da]];
  pose proof (e_assign_target_flex Da) as Hft;
  flex_test_true Hft; cbv beta iota;
  lazymatch goal with
  | |- context [ e_consis_call_impl (consis_call_assign nil ?a ?p)
                   ?s ?t ?x ?y ?zz ] =>
      assert (Hcov0 : ftvar_in_aenv (nil ++ t) ∪ ftvar_in_pskl p [<=] s)
        by (clear - Hcov; simpl in *; fsetdec)
  end;
  kill_ccall Hmot Hu Hcov0 Da pskl_unit r Hr ps Hav HS HT HQ;
  eexists; exists ps;
  split; [ reflexivity | ];
  repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
          | cbn [cs_ctx proj1_sig]; exact HT | ];
  cbn [cs_out proj1_sig]; out_var_id Hav Hcov.

Lemma consis_swaps_close : forall S Sd St Θ Q α β ps r,
  α `notin` S -> β `notin` S ->
  (forall a b, In (a, b) ps -> a `notin` add β S /\ b `notin` add β S) ->
  St [=] swap_atoms α β Sd -> swaps_atoms ps St [=] cs_supply r ->
  swaps_aenv ps ((β ~ abind_tvar) ++ swap_aenv α β Θ) = cs_ctx r ->
  swaps_pskl ps (swap_pskl α β Q) = cs_out r ->
  cs_ctx r = (β ~ abind_tvar) ++ swaps_aenv ps (swap_aenv α β Θ) /\
  (forall a b, In (a, b) ((α, β) :: ps) -> a `notin` S /\ b `notin` S) /\
  swaps_atoms ((α, β) :: ps) Sd [=] cs_supply r /\
  swaps_pskl ((α, β) :: ps) (pskl_all_syn (close_pskl_wrt_pskl α Q)) =
    pskl_all_syn (close_pskl_wrt_pskl β (cs_out r)).
Proof.
  intros * Hα Hβ Hav HSt HS HT HQ.
  assert (Hfix : swaps_atom ps β = β)
    by (apply (swaps_atom_dodge_in Hav); fsetdec).
  split.
  - rewrite <- HT, swaps_aenv_cons_tvar, Hfix. reflexivity.
  - split.
    + eapply swaps_fresh_cons; eassumption.
    + split.
      * eapply swaps_atoms_cons_transport; eassumption.
      * eapply swaps_pskl_close_binder; eassumption.
Qed.

Arguments consis_swaps_close {S Sd St Θ Q α β ps r} _ _ _ _ _ _ _.

Lemma e_consis_call_impl_complete : forall S0 Θ c
    (H0 : e_consis_call_order S0 Θ c), consis_call_complete S0 Θ c.
Proof.
  intros S0 Θ c H0.
  induction H0 as
    [S1 Θ' Ξ α P hg has Has hdep Hdep hskip Hskip hrg Hrg htv Htv hts Hts
    |S1 Θ' α β has Has hsk Hsk hrg Hrg htv Htv hts Hts
    |S1 Θ' Δ1 Δ2 P0 P qhead IHhead qtail IHtail
      q2 Q2 q3 Q3 q4 Q4 q5 Q5 q6 Q6 q7 Q7 q8 Q8 q9 Q9 q10 Q10];
    unfold consis_call_complete;
    intros Hlc HD Hord Hu Hcov Sd Θd Qd Hd;
    cbn [consis_call_lc consis_call_uniq consis_call_cover
         consis_call_run consis_call_out_rel consis_call_defs_mono] in *.
  -
    destruct Θ' as [ | [β0 b] Θ0 ];
      [ destruct (e_assign_inv_nil Hd) | ].
    destruct b as [ | A | Q | | τ ].
    +
      rewrite e_consis_call_impl_equation_2. cbv beta iota.
      destruct (e_assign_inv_tvar Hd) as [Hnf [Θd' [-> Dt]]].
      destruct (sumbool_of_bool (mem β0 (ftvar_in_pskl P))) as [Hm | Hm];
        [ exfalso; apply mem_true_in in Hm; contradiction | ].
      cbv beta iota.
      assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
        by (clear - Hcov; rewrite ftvar_in_aenv_app in *; simpl in *;
            fsetdec).
      kill_ccall (Hrg β0 Θ0 eq_refl) Hu0 Hcov0 Dt pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((β0 ~ abind_tvar) ++ cs_ctx r) pskl_unit), ps.
      refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    +
      rewrite e_consis_call_impl_equation_3. cbv beta iota.
      destruct (e_assign_inv_var_typ Hd) as [Θd' [-> Dt]].
      assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
        by (clear - Hcov; rewrite ftvar_in_aenv_app in *; simpl in *;
            fsetdec).
      kill_ccall (Htv β0 A Θ0 eq_refl) Hu0 Hcov0 Dt pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((β0 ~ abind_var_typ A) ++ cs_ctx r) pskl_unit), ps.
      refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    +
      rewrite e_consis_call_impl_equation_4. cbv beta iota.
      destruct (e_assign_inv_var_skl Hd) as [Θd' [-> Dt]].
      assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
        by (clear - Hcov; rewrite ftvar_in_aenv_app in *; simpl in *;
            fsetdec).
      kill_ccall (Hts β0 Q Θ0 eq_refl) Hu0 Hcov0 Dt pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((β0 ~ abind_var_skl Q) ++ cs_ctx r) pskl_unit), ps.
      refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    +
      rewrite e_consis_call_impl_equation_5. cbv beta iota.
      destruct (β0 == α) as [-> | Hne].
      *
        destruct (e_assign_inv_flex_self Hd)
          as [[HΞ [HP [HSd HΘd]]] | [Hocc [bs [tau [Hg [Hmt HΘd]]]]]].
        --
           subst Ξ. subst P. subst Sd. subst Θd. cbv beta iota.
           split_eqdec Hca1 Hca2; [ | congruence ].
           cbv beta iota.
           exists (mk_consis_result S1 ((α ~ abind_flex_mono) ++ Θ0)
                     pskl_unit), (@nil (atom * atom)).
           repeat apply conj.
           ++ reflexivity.
           ++ apply swaps_dodge_nil.
           ++ reflexivity.
           ++ reflexivity.
           ++ exact I.
        --
           subst Θd.
           destruct Ξ as [ | e Ξ' ];
             [ destruct P as [ | n | γ | Pa Pb | Pb | | Pb ];
               [ | | | | | | destruct Pb as [ | n' | γ | Pa' Pb' | Pb' | | Pb' ] ]
             | ];
             cbv beta iota;
             try (destruct (γ == α) as [-> | Hnγ];
                  [ exfalso; apply Hocc; simpl; fsetdec | ]);
             cbv beta iota;
             do_solve_m Hocc Hg Hmt Hcov rg Hgs psg Havg HSg HXg HAg.
      *
        destruct (e_assign_inv_flex_other (not_eq_sym Hne) Hd)
          as [[Hin Dd] | [Hni [Θd' [-> Ds]]]].
        -- destruct (sumbool_of_bool (mem β0 (ftvar_in_pskl P)))
             as [Hm | Hm];
             [ | exfalso; apply mem_false_notin in Hm; contradiction ].
           cbv beta iota.
           assert (Hu0 : uniq ((Ξ ++ (β0 ~ abind_flex_mono)) ++ Θ0))
             by (clear - Hu; solve_uniq).
           assert (Hcov0 : ftvar_in_aenv ((Ξ ++ (β0 ~ abind_flex_mono))
                             ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
             by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
                 simpl in *; fsetdec).
           kill_ccall (Hdep β0 Θ0 eq_refl) Hu0 Hcov0 Dd pskl_unit
             r Hr ps Hav HS HT HQ.
           exists r, ps.
           exact (conj eq_refl (conj Hav (conj HS (conj HT I)))).
        -- destruct (sumbool_of_bool (mem β0 (ftvar_in_pskl P)))
             as [Hm | Hm];
             [ exfalso; apply mem_true_in in Hm; contradiction | ].
           cbv beta iota.
           assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
           assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P [<=] S1)
             by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
                 simpl in *; fsetdec).
           kill_ccall (Hskip β0 Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
             r Hr ps Hav HS HT HQ.
           exists (mk_consis_result (cs_supply r)
                     ((β0 ~ abind_flex_mono) ++ cs_ctx r) pskl_unit), ps.
           refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
           cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
           head_fresh Hav Hcov.
    +
      rewrite e_consis_call_impl_equation_6. cbv beta iota.
      destruct (e_assign_inv_def Hd) as [Hft [Θd' [Qm [-> Dc]]]].
      destruct (sumbool_of_bool
                  (flex_bound_ck ((β0, abind_flex_mono_def τ) :: Θ0) α))
        as [Hfb | Hfb];
        [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
            [ exact Hfb | exact Hft ] ].
      cbv beta iota.
      assert (Hu0 : uniq (Ξ ++ Θ0)) by (clear - Hu; solve_uniq).
      pose proof (a_flex_tvar_in_dom Hft) as Hαdom.
      pose proof (dom_subset_ftvar_in_aenv
                    ((β0, abind_flex_mono_def τ) :: Θ0)) as Hdm.
      assert (HΘ : ftvar_in_aenv ((β0, abind_flex_mono_def τ) :: Θ0)
                [<=] S1)
        by (clear - Hcov; rewrite ftvar_in_aenv_app in Hcov; fsetdec).
      assert (HαS : α `in` S1) by (clear - HΘ Hαdom Hdm; fsetdec).
      assert (Hcov0 : consis_call_cover (Ξ ++ Θ0)
                (consis_call_consis empty empty
                   (subst_pskl_in_pskl (ptyp_to_pskl τ) β0 P)
                   (subst_pskl_in_pskl (ptyp_to_pskl τ) β0 (pskl_var_f α)))
                [<=] S1)
        by (cbn [consis_call_cover]; repeat rewrite (empty_union_2 (s := empty)) by (unfold Empty; clear; fsetdec);
            apply subst_pskl_preserves_cover; rewrite ftvar_ptyp_to_pskl;
            clear - Hcov HαS; repeat rewrite ftvar_in_aenv_app in *;
            simpl in *; fsetdec).
      kill_ccall (Has β0 τ Θ0 eq_refl) Hu0 Hcov0 Dc Qm
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((β0 ~ abind_flex_mono_def τ) ++ cs_ctx r) pskl_unit), ps.
      refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
  -
    destruct Θ' as [ | [γ b] Θ0 ];
      [ destruct (e_unify_inv_nil Hd) | ].
    destruct b as [ | A | Q | | τ ].
    +
      rewrite e_consis_call_impl_equation_8. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      destruct (e_unify_inv_other Hne ltac:(left; reflexivity) Hd)
        as [Θd' [-> Ds]].
      assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv Θ0 [<=] S1)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_ccall (Hrg γ Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((γ ~ abind_tvar) ++ cs_ctx r) pskl_unit), ps.
      refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    +
      rewrite e_consis_call_impl_equation_9. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      destruct (e_unify_inv_other Hne
                  ltac:(right; left; exists A; reflexivity) Hd)
        as [Θd' [-> Ds]].
      assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv Θ0 [<=] S1)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_ccall (Htv γ A Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((γ ~ abind_var_typ A) ++ cs_ctx r) pskl_unit), ps.
      refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    +
      rewrite e_consis_call_impl_equation_10. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      destruct (e_unify_inv_other Hne
                  ltac:(right; right; exists Q; reflexivity) Hd)
        as [Θd' [-> Ds]].
      assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv Θ0 [<=] S1)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_ccall (Hts γ Q Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((γ ~ abind_var_skl Q) ++ cs_ctx r) pskl_unit), ps.
      refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    +
      rewrite e_consis_call_impl_equation_11. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      split_eqdec Heq2 Hne2.
      *
        subst. cbv beta iota.
        destruct (e_unify_inv_flex_l Hne Hd) as [Hfβ [-> ->]].
        destruct (sumbool_of_bool (flex_bound_ck Θ0 β)) as [Hfb | Hfb];
          [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
              [ exact Hfb | exact Hfβ ] ].
        cbv beta iota.
        eexists; exists (@nil (atom * atom)).
        repeat apply conj.
        -- reflexivity.
        -- apply swaps_dodge_nil.
        -- reflexivity.
        -- reflexivity.
        -- exact I.
      * cbv beta iota. split_eqdec Heq3 Hne3.
        --
           subst. cbv beta iota.
           destruct (e_unify_inv_flex_r Hne Hd) as [Hfα [-> ->]].
           destruct (sumbool_of_bool (flex_bound_ck Θ0 α)) as [Hfb | Hfb];
             [ | exfalso; eapply flex_bound_ck_not_flex_tvar;
                 [ exact Hfb | exact Hfα ] ].
           cbv beta iota.
           eexists; exists (@nil (atom * atom)).
           repeat apply conj.
           ++ reflexivity.
           ++ apply swaps_dodge_nil.
           ++ reflexivity.
           ++ reflexivity.
           ++ exact I.
        --
           cbv beta iota.
           destruct (e_unify_inv_flex_skip Hne Hne2 Hne3 Hd)
             as [Θd' [-> Ds]].
           assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
           assert (Hcov0 : ftvar_in_aenv Θ0 [<=] S1)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_ccall (Hsk γ Θ0 eq_refl) Hu0 Hcov0 Ds pskl_unit
             r Hr ps Hav HS HT HQ.
           exists (mk_consis_result (cs_supply r)
                     ((γ ~ abind_flex_mono) ++ cs_ctx r) pskl_unit), ps.
           refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
           cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
           head_fresh Hav Hcov.
    +
      rewrite e_consis_call_impl_equation_12. cbv beta iota.
      split_eqdec Heq Hne; [ subst; cbv beta iota; do_flex_id HD Hd | ].
      cbv beta iota.
      destruct (e_unify_inv_def Hne Hd) as [Hfa [Hfb [Θd' [Qm [-> Dc]]]]].
      destruct (sumbool_of_bool
                  (flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) α
                   && flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) β))
        as [Hbb | Hbb];
        [ | exfalso; apply andb_false_iff in Hbb;
            destruct Hbb as [Hbb | Hbb];
            eapply flex_bound_ck_not_flex_tvar; eassumption ].
      cbv beta iota.
      assert (Hu0 : uniq Θ0) by (clear - Hu; solve_uniq).
      pose proof (a_flex_tvar_in_dom Hfa) as Hαdom.
      pose proof (a_flex_tvar_in_dom Hfb) as Hβdom.
      pose proof (dom_subset_ftvar_in_aenv
                    ((γ, abind_flex_mono_def τ) :: Θ0)) as Hdm.
      assert (HβS : β `in` S1) by (clear - Hcov Hβdom Hdm; fsetdec).
      assert (HαS : α `in` S1) by (clear - Hcov Hαdom Hdm; fsetdec).
      assert (Hcov0 : consis_call_cover Θ0
                (consis_call_consis empty empty
                   (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f β)))
                   (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f α))))
                [<=] S1)
        by (cbn [consis_call_cover]; repeat rewrite (empty_union_2 (s := empty)) by (unfold Empty; clear; fsetdec);
            repeat rewrite ptyp_to_pskl_subst; apply subst_pskl_preserves_cover;
            repeat rewrite ftvar_ptyp_to_pskl; clear - Hcov HαS HβS;
            simpl in *; fsetdec).
      kill_ccall (Has γ τ Θ0 eq_refl) Hu0 Hcov0 Dc Qm
        r Hr ps Hav HS HT HQ.
      exists (mk_consis_result (cs_supply r)
                ((γ ~ abind_flex_mono_def τ) ++ cs_ctx r) pskl_unit), ps.
      refine (conj eq_refl (conj Hav (conj HS (conj _ I)))).
      cbn [cs_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
  -
    destruct Hlc as [Hlc0 Hlc1].
    rewrite e_consis_call_impl_equation_13.
    destruct P0 as [ | n0 | β0 | P0a P0b | P0' | | P0' ]; cbv beta iota.
    +
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      *
        destruct (e_consis_inv_unit Hd) as [-> [-> ->]].
        exists (mk_consis_result S1 Θ' pskl_unit), (@nil (atom * atom)).
        repeat apply conj.
        -- reflexivity.
        -- apply swaps_dodge_nil.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
      *  inversion Hlc1.
      *
        destruct (e_consis_inv_flex_l Hd ltac:(intros; discriminate)
                    ltac:(discriminate) ltac:(intros; discriminate))
          as [-> [Hnf Da]].
        pose proof (e_assign_target_flex Da) as Hft.
        flex_test_true Hft. cbv beta iota.
        assert (Hcov0 : ftvar_in_aenv (nil ++ Θ') ∪ ftvar_in_pskl pskl_unit
                          [<=] S1) by (clear - Hcov; simpl in *; fsetdec).
        kill_ccall (Q9 α0 eq_refl) Hu Hcov0 Da pskl_unit
          r Hr ps Hav HS HT HQ.
        exists (mk_consis_result (cs_supply r) (cs_ctx r) (pskl_var_f α0)),
               ps.
        split; [ reflexivity | ].
        repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                | cbn [cs_ctx proj1_sig]; exact HT | ].
        cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
      *  inversion Hd.
      *  inversion Hd.
      *
        destruct (e_consis_inv_ghost_subject Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      *
        pose proof (e_consis_inv_univ_ghost2_unit Hd) as Dc.
        assert (Hcov0 : consis_call_cover Θ'
                  (consis_call_consis Δ1 Δ2 pskl_unit Pb) [<=] S1)
          by (clear - Hcov;
              cbn [consis_call_cover ftvar_in_pskl] in *; fsetdec).
        kill_ccall (Q6 Pb eq_refl) Hu Hcov0 Dc Qd r Hr ps Hav HS HT HQ.
        exists r, ps.
        exact (conj eq_refl (conj Hav (conj HS (conj HT HQ)))).
    +  inversion Hlc0.
    +
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      *  do_flex_r (Q10 β0 eq_refl) Hd Hu Hcov.
      * inversion Hlc1.
      *
        split_eqdec Heqab Hneab.
        --
           subst β0. cbv beta iota.
           destruct (sumbool_of_bool (rigid_bound_ck Θ' α0)) as [Hrb | Hrb];
             cbv beta iota.
           ++
              destruct (e_consis_inv_var_var Hd)
                as [ [_ [_ [-> [-> ->]]]]
                   | [ [-> Du]
                     | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
              ** exists (mk_consis_result S1 Θ' (pskl_var_f α0)),
                        (@nil (atom * atom)).
                 repeat apply conj.
                 --- reflexivity.
                 --- apply swaps_dodge_nil.
                 --- reflexivity.
                 --- reflexivity.
                 --- reflexivity.
              **
                 destruct (e_unify_refl Du HD) as [-> ->].
                 exists (mk_consis_result S1 Θ' (pskl_var_f α0)),
                        (@nil (atom * atom)).
                 repeat apply conj.
                 --- reflexivity.
                 --- apply swaps_dodge_nil.
                 --- reflexivity.
                 --- reflexivity.
                 --- reflexivity.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. eapply e_assign_target_flex;
                   eassumption.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. eapply e_assign_target_flex;
                   eassumption.
           ++
              destruct (e_consis_inv_var_var Hd)
                as [ [_ [Hbt _]]
                   | [ [-> Du]
                     | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
              ** exfalso.
                 assert (Hct : rigid_bound_ck Θ' α0 = true)
                   by (apply rigid_bound_ck_complete; exact Hbt).
                 rewrite Hct in Hrb. discriminate.
              ** assert (Hcov0 : ftvar_in_aenv Θ' [<=] S1)
                   by (clear - Hcov; simpl in *; fsetdec).
                 kill_ccall (Q8 α0 α0 eq_refl eq_refl) Hu Hcov0 Du
                   pskl_unit r Hr ps Hav HS HT HQ.
                 exists (mk_consis_result (cs_supply r) (cs_ctx r)
                           (pskl_var_f α0)), ps.
                 split; [ reflexivity | ].
                 repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                         | cbn [cs_ctx proj1_sig]; exact HT | ].
                 cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. eapply e_assign_target_flex;
                   eassumption.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. eapply e_assign_target_flex;
                   eassumption.
        --
           cbv beta iota.
           destruct (sumbool_of_bool
                       (flex_bound_ck Θ' α0 && flex_bound_ck Θ' β0))
             as [Hbb | Hbb]; cbv beta iota.
           ++
              pose proof (andb_prop _ _ Hbb) as [Hba Hbβ].
              destruct (e_consis_inv_var_var Hd)
                as [ [Heq _]
                   | [ [-> Du]
                     | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
              ** congruence.
              ** assert (Hcov0 : ftvar_in_aenv Θ' [<=] S1)
                   by (clear - Hcov; simpl in *; fsetdec).
                 kill_ccall (Q8 α0 β0 eq_refl eq_refl) Hu Hcov0 Du
                   pskl_unit r Hr ps Hav HS HT HQ.
                 exists (mk_consis_result (cs_supply r) (cs_ctx r)
                           (pskl_var_f α0)), ps.
                 split; [ reflexivity | ].
                 repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                         | cbn [cs_ctx proj1_sig]; exact HT | ].
                 cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. apply flex_bound_ck_flex_tvar.
                 exact Hbβ.
              ** exfalso. destruct Hnf as [_ Hf]. apply Hf.
                 apply a_flex_var_iff_tvar. apply flex_bound_ck_flex_tvar.
                 exact Hba.
           ++ destruct (sumbool_of_bool (flex_bound_ck Θ' β0))
                as [Hbβ | Hbβ]; cbv beta iota.
              **
                 destruct (e_consis_inv_var_var Hd)
                   as [ [Heq _]
                      | [ [-> Du]
                        | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
                 --- congruence.
                 --- exfalso.
                     destruct (e_unify_target_flex Du) as [Hfa Hfb2].
                     assert (Hca : flex_bound_ck Θ' α0 = true)
                       by (apply flex_tvar_flex_bound_ck; exact Hfa).
                     assert (Hcb : flex_bound_ck Θ' β0 = true)
                       by (apply flex_tvar_flex_bound_ck; exact Hfb2).
                     rewrite Hca, Hcb in Hbb. discriminate.
                 --- exfalso. destruct Hnf as [_ Hf]. apply Hf.
                     apply a_flex_var_iff_tvar. apply flex_bound_ck_flex_tvar.
                     exact Hbβ.
                 --- assert (Hcov0 : ftvar_in_aenv (nil ++ Θ')
                               ∪ ftvar_in_pskl (pskl_var_f α0) [<=] S1)
                       by (clear - Hcov; simpl in *; fsetdec).
                     kill_ccall (Q10 β0 eq_refl) Hu Hcov0 Da pskl_unit
                       r Hr ps Hav HS HT HQ.
                     exists (mk_consis_result (cs_supply r) (cs_ctx r)
                               (pskl_var_f β0)), ps.
                     split; [ reflexivity | ].
                     repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                             | cbn [cs_ctx proj1_sig]; exact HT | ].
                     cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
              ** destruct (sumbool_of_bool (flex_bound_ck Θ' α0))
                   as [Hba | Hba]; cbv beta iota.
                 ---
                     destruct (e_consis_inv_var_var Hd)
                       as [ [Heq _]
                          | [ [-> Du]
                            | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
                     +++ congruence.
                     +++ exfalso.
                         destruct (e_unify_target_flex Du) as [Hfa Hfb2].
                         assert (Hcb : flex_bound_ck Θ' β0 = true)
                           by (apply flex_tvar_flex_bound_ck; exact Hfb2).
                         rewrite Hcb in Hbβ. discriminate.
                     +++ assert (Hcov0 : ftvar_in_aenv (nil ++ Θ')
                                   ∪ ftvar_in_pskl (pskl_var_f β0) [<=] S1)
                           by (clear - Hcov; simpl in *; fsetdec).
                         kill_ccall (Q9 α0 eq_refl) Hu Hcov0 Da
                           pskl_unit r Hr ps Hav HS HT HQ.
                         exists (mk_consis_result (cs_supply r) (cs_ctx r)
                                   (pskl_var_f α0)), ps.
                         split; [ reflexivity | ].
                         repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                                 | cbn [cs_ctx proj1_sig]; exact HT | ].
                         cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
                     +++ exfalso. destruct Hnf as [_ Hf]. apply Hf.
                         apply a_flex_var_iff_tvar. apply flex_bound_ck_flex_tvar.
                         exact Hba.
                 ---
                     exfalso.
                     destruct (e_consis_inv_var_var Hd)
                       as [ [Heq _]
                          | [ [-> Du]
                            | [ [Hnf [-> Da]] | [Hnf [-> Da]] ] ] ].
                     +++ congruence.
                     +++ destruct (e_unify_target_flex Du) as [Hfa _].
                         assert (Hca : flex_bound_ck Θ' α0 = true)
                           by (apply flex_tvar_flex_bound_ck; exact Hfa).
                         rewrite Hca in Hba. discriminate.
                     +++ assert (Hca : flex_bound_ck Θ' α0 = true)
                           by (apply flex_tvar_flex_bound_ck;
                               eapply e_assign_target_flex; eassumption).
                         rewrite Hca in Hba. discriminate.
                     +++ assert (Hcb : flex_bound_ck Θ' β0 = true)
                           by (apply flex_tvar_flex_bound_ck;
                               eapply e_assign_target_flex; eassumption).
                         rewrite Hcb in Hbβ. discriminate.
      *  do_flex_r (Q10 β0 eq_refl) Hd Hu Hcov.
      *  do_flex_r (Q10 β0 eq_refl) Hd Hu Hcov.
      *
        destruct (e_consis_inv_ghost_flex_pattern Hd) as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      *
        destruct (e_consis_inv_var_univ_ghost Hd)
          as [ [Hft [-> Da]] | [Hnf Dc] ].
        -- flex_test_true Hft. cbv beta iota.
           assert (Hcov0 : ftvar_in_aenv (nil ++ Θ')
                     ∪ ftvar_in_pskl (pskl_univ_ghost Pb) [<=] S1)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_ccall (Q10 β0 eq_refl) Hu Hcov0 Da pskl_unit
             r Hr ps Hav HS HT HQ.
           exists (mk_consis_result (cs_supply r) (cs_ctx r)
                     (pskl_var_f β0)), ps.
           split; [ reflexivity | ].
           repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                   | cbn [cs_ctx proj1_sig]; exact HT | ].
           cbn [cs_out proj1_sig]. out_var_id Hav Hcov.
        -- destruct (sumbool_of_bool (flex_bound_ck Θ' β0)) as [Hfb | Hfb];
             [ exfalso; destruct Hnf as [_ Hf]; apply Hf;
               apply a_flex_var_iff_tvar; apply flex_bound_ck_flex_tvar;
               exact Hfb | ].
           cbv beta iota.
           assert (Hcov0 : consis_call_cover Θ'
                     (consis_call_consis Δ1 Δ2 (pskl_var_f β0) Pb) [<=] S1)
             by (clear - Hcov;
                 cbn [consis_call_cover ftvar_in_pskl] in *; fsetdec).
           kill_ccall (Q6 Pb eq_refl) Hu Hcov0 Dc Qd r Hr ps Hav HS HT HQ.
           exists r, ps.
           exact (conj eq_refl (conj Hav (conj HS (conj HT HQ)))).
    +
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      *  inversion Hd.
      * inversion Hlc1.
      *  do_flex_l (Q9 α0 eq_refl) Hd Hu Hcov.
      *
        pose proof (IHhead P0a P0b Pa Pb eq_refl eq_refl) as IH1.
        cbn [ftvar_in_pskl] in Hcov.
        destruct (e_consis_inv_arrow Hd)
          as [Sm [Θm [Qd1 [Qd2 [-> [D1 D2]]]]]].
        assert (Hcov1 : consis_call_cover Θ'
                  (consis_call_consis Δ1 Δ2 P0a Pa) [<=] S1)
          by (cbn [consis_call_cover] in *; clear - Hcov; fsetdec).
        kill_ccall IH1 Hu Hcov1 D1 Qd1 r1 Hr1 ps1 Hav1 HS1 HT1 HQ1.
        cbn [consis_call_spec consis_spec] in Hr1.
        pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                      _ _ _ _ _ _ _ _ _ Hr1 Hu
                      ltac:(cbn [consis_call_cover] in *; clear - Hcov;
                            fsetdec))
          as [Da1 [Hu1' Hcov1']].
        pose proof (e_consis_supply_grows Hr1) as Hgr1.
        pose proof ((proj2 (proj2 e_assign_unify_consis_out_ftvar))
                      _ _ _ _ _ _ _ _ _ Hr1 Hu
                      ltac:(cbn [consis_call_cover] in *; clear - Hcov;
                            fsetdec)) as Hout1.
        assert (HDl : Δ1 [=] swaps_atoms ps1 Δ1)
          by (symmetry; apply swaps_atoms_notin, (swaps_dodge_sub Hav1);
              clear - Hcov; fsetdec).
        assert (HDr : Δ2 [=] swaps_atoms ps1 Δ2)
          by (symmetry; apply swaps_atoms_notin, (swaps_dodge_sub Hav1);
              clear - Hcov; fsetdec).
        pose proof HS1 as HS1r. symmetry in HS1r.
        destruct (e_consis_swaps ps1 D2 HDl HDr HS1r)
          as [S2t [HS2t D2t]].
        rewrite HT1, (swaps_pskl_fresh_id ps1 P0b),
          (swaps_pskl_fresh_id ps1 Pb) in D2t
          by (apply (swaps_dodge_sub Hav1); clear - Hcov; fsetdec).
        pose proof (IHtail P0a P0b Pa Pb _ _ _ eq_refl eq_refl Hr1) as IH2.
        assert (Hcov2 : consis_call_cover (cs_ctx r1)
                  (consis_call_consis Δ1 Δ2 P0b Pb) [<=] cs_supply r1)
          by (cbn [consis_call_cover] in *;
              clear - Hcov Hcov1' Hgr1; fsetdec).
        kill_ccall IH2 Hu1' Hcov2 D2t (swaps_pskl ps1 Qd2)
          r2 Hr2 ps2 Hav2 HS2 HT2 HQ2.
        exists (mk_consis_result (cs_supply r2) (cs_ctx r2)
                  (pskl_arrow (cs_out r1) (cs_out r2))), (ps1 ++ ps2).
        split; [ reflexivity | ].
        repeat apply conj.
        -- apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1; fsetdec.
        -- exact (swaps_atoms_app_transport HS2t HS2).
        -- cbn [cs_ctx]. rewrite swaps_aenv_app. exact HT2.
        -- cbn [cs_out]. rewrite swaps_pskl_app, !swaps_pskl_arrow.
           rewrite HQ1 in *. f_equal; [ | exact HQ2 ].
           apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav2).
           clear - Hout1; fsetdec.
      *  inversion Hd.
      *
        destruct (e_consis_inv_ghost_subject Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      *
        pose proof (e_consis_inv_univ_ghost2_arrow Hd) as Dc.
        do_pass (Q6 Pb eq_refl) Dc Hu Hcov Qd.
    +
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      *  inversion Hd.
      * inversion Hlc1.
      *  do_flex_l (Q9 α0 eq_refl) Hd Hu Hcov.
      *  inversion Hd.
      *
        destruct (e_consis_inv_forall_inh Hd) as [α [Qb [Hα [-> Dp]]]].
        pose proof (supply_fresh_notin S1) as Hz.
        simpl ftvar_in_pskl in Hcov.
        assert (HD1 : add (supply_fresh S1) Δ1
                  [=] swap_atoms α (supply_fresh S1) (add α Δ1))
          by (apply swap_atoms_fresh_add; clear - Hα Hz Hcov; fsetdec).
        assert (HD2 : add (supply_fresh S1) Δ2
                  [=] swap_atoms α (supply_fresh S1) (add α Δ2))
          by (apply swap_atoms_fresh_add; clear - Hα Hz Hcov; fsetdec).
        pose proof (swap_atoms_fresh_add _ _ _ Hα Hz) as HSq.
        destruct (e_consis_swap Dp HD1 HD2 HSq) as [S1t [HS1t Dpt]].
        rewrite !swap_aenv_app, !swap_aenv_one_tvar, !swap_pskl_open_var,
          swap_atom_l in Dpt.
        rewrite (swap_aenv_fresh_id α (supply_fresh S1) Θ'),
          (swap_pskl_fresh_id α (supply_fresh S1) P0'),
          (swap_pskl_fresh_id α (supply_fresh S1) Pb) in Dpt
          by (clear - Hα Hz Hcov; simpl in *; fsetdec).
        pose proof (dom_subset_ftvar_in_aenv Θ') as Hdm.
        assert (Hu' : uniq ((supply_fresh S1 ~ abind_tvar) ++ Θ'))
          by (apply uniq_push;
              [ exact Hu | clear - Hz Hcov Hdm; fsetdec ]).
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0'
                      (pskl_var_f (supply_fresh S1))) as Hup1.
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Pb
                      (pskl_var_f (supply_fresh S1))) as Hup2.
        assert (Hcov' : consis_call_cover
                  ((supply_fresh S1 ~ abind_tvar) ++ Θ')
                  (consis_call_consis
                     (add (supply_fresh S1) Δ1) (add (supply_fresh S1) Δ2)
                     (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S1)))
                     (open_pskl_wrt_pskl Pb (pskl_var_f (supply_fresh S1))))
                  [<=] add (supply_fresh S1) S1).
        { cbn [consis_call_cover]. simpl ftvar_in_aenv.
          clear - Hcov Hup1 Hup2. simpl in *. fsetdec. }
        kill_ccall (Q2 P0' Pb eq_refl eq_refl) Hu' Hcov' Dpt
          (swap_pskl α (supply_fresh S1) Qb) r Hr ps Hav HS HT HQ.
        destruct (consis_swaps_close Hα Hz Hav HS1t HS HT HQ)
          as (HTz & HavAll & HSAll & HQAll).
        destruct (@split_tvar_head_hit_eq _ _ _ HTz) as [pf Hsp].
        rewrite Hsp. cbv beta iota.
        exists (mk_consis_result (cs_supply r)
                  (swaps_aenv ps (swap_aenv α (supply_fresh S1) Θd))
                  (pskl_all_syn (close_pskl_wrt_pskl (supply_fresh S1) (cs_out r)))),
               ((α, supply_fresh S1) :: ps).
        exact (conj eq_refl (conj HavAll (conj HSAll (conj eq_refl HQAll)))).
      *
        destruct (e_consis_inv_ghost_subject Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      *
        destruct (e_consis_inv_univ_ghost1 Hd) as [α [Qb [Hα [-> Dp]]]].
        pose proof (supply_fresh_notin S1) as Hz.
        simpl ftvar_in_pskl in Hcov.
        assert (HD1 : add (supply_fresh S1) Δ1
                  [=] swap_atoms α (supply_fresh S1) (add α Δ1))
          by (apply swap_atoms_fresh_add; clear - Hα Hz Hcov; fsetdec).
        assert (HD2 : Δ2 [=] swap_atoms α (supply_fresh S1) Δ2)
          by (symmetry; apply swap_atoms_notin;
              clear - Hα Hz Hcov; fsetdec).
        pose proof (swap_atoms_fresh_add _ _ _ Hα Hz) as HSq.
        destruct (e_consis_swap Dp HD1 HD2 HSq) as [S1t [HS1t Dpt]].
        rewrite !swap_aenv_app, !swap_aenv_one_tvar, !swap_pskl_open_var,
          swap_atom_l in Dpt.
        rewrite (swap_aenv_fresh_id α (supply_fresh S1) Θ'),
          (swap_pskl_fresh_id α (supply_fresh S1) P0'),
          (swap_pskl_fresh_id α (supply_fresh S1) (pskl_univ_ghost Pb)) in Dpt
          by (clear - Hα Hz Hcov; simpl in *; fsetdec).
        pose proof (dom_subset_ftvar_in_aenv Θ') as Hdm.
        assert (Hu' : uniq ((supply_fresh S1 ~ abind_tvar) ++ Θ'))
          by (apply uniq_push;
              [ exact Hu | clear - Hz Hcov Hdm; fsetdec ]).
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0'
                      (pskl_var_f (supply_fresh S1))) as Hup1.
        assert (Hcov' : consis_call_cover
                  ((supply_fresh S1 ~ abind_tvar) ++ Θ')
                  (consis_call_consis (add (supply_fresh S1) Δ1) Δ2
                     (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S1)))
                     (pskl_univ_ghost Pb))
                  [<=] add (supply_fresh S1) S1).
        { cbn [consis_call_cover]. simpl ftvar_in_aenv.
          clear - Hcov Hup1. simpl in *. fsetdec. }
        kill_ccall (Q5 P0' Pb eq_refl eq_refl) Hu' Hcov' Dpt
          (swap_pskl α (supply_fresh S1) Qb) r Hr ps Hav HS HT HQ.
        destruct (consis_swaps_close Hα Hz Hav HS1t HS HT HQ)
          as (HTz & HavAll & HSAll & HQAll).
        destruct (@split_tvar_head_hit_eq _ _ _ HTz) as [pf Hsp].
        rewrite Hsp. cbv beta iota.
        exists (mk_consis_result (cs_supply r)
                  (swaps_aenv ps (swap_aenv α (supply_fresh S1) Θd))
                  (pskl_all_syn (close_pskl_wrt_pskl (supply_fresh S1) (cs_out r)))),
               ((α, supply_fresh S1) :: ps).
        exact (conj eq_refl (conj HavAll (conj HSAll (conj eq_refl HQAll)))).
    +
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      * destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * inversion Hlc1.
      *
        destruct (e_consis_inv_flex_subject_ghost Hd) as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      *
        destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      * destruct (e_consis_inv_ghost_pattern Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
    +
      destruct P as [ | n | α0 | Pa Pb | Pb | | Pb ]; cbv beta iota.
      *
        pose proof (e_consis_inv_univ_ghost_r_unit Hd) as Dc.
        do_pass (Q7 P0' eq_refl) Dc Hu Hcov Qd.
      * inversion Hlc1.
      *
        destruct (e_consis_inv_univ_ghost_var Hd)
          as [ [Hft [-> Da]] | [Hnf Dc] ].
        -- flex_test_true Hft. cbv beta iota.
           assert (Hcov0 : ftvar_in_aenv (nil ++ Θ')
                     ∪ ftvar_in_pskl (pskl_univ_ghost P0') [<=] S1)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_ccall (Q9 α0 eq_refl) Hu Hcov0 Da pskl_unit
             r Hr ps Hav HS HT HQ.
           eexists; exists ps.
           split; [ reflexivity | ].
           repeat apply conj; [ exact Hav | cbn [cs_supply proj1_sig]; exact HS
                   | cbn [cs_ctx proj1_sig]; exact HT | ].
           out_var_id Hav Hcov.
        -- destruct (sumbool_of_bool (flex_bound_ck Θ' α0)) as [Hfb | Hfb];
             [ exfalso; destruct Hnf as [_ Hf]; apply Hf;
               apply a_flex_var_iff_tvar; apply flex_bound_ck_flex_tvar;
               exact Hfb | ].
           cbv beta iota. do_pass (Q7 P0' eq_refl) Dc Hu Hcov Qd.
      *
        pose proof (e_consis_inv_univ_ghost_r_arrow Hd) as Dc.
        do_pass (Q7 P0' eq_refl) Dc Hu Hcov Qd.
      *
        destruct (e_consis_inv_forall_syn Hd) as [α [Qb [Hα [-> Dp]]]].
        pose proof (supply_fresh_notin S1) as Hz.
        simpl ftvar_in_pskl in Hcov.
        assert (HD1 : Δ1 [=] swap_atoms α (supply_fresh S1) Δ1)
          by (symmetry; apply swap_atoms_notin;
              clear - Hα Hz Hcov; fsetdec).
        assert (HD2 : add (supply_fresh S1) Δ2
                  [=] swap_atoms α (supply_fresh S1) (add α Δ2))
          by (apply swap_atoms_fresh_add; clear - Hα Hz Hcov; fsetdec).
        pose proof (swap_atoms_fresh_add _ _ _ Hα Hz) as HSq.
        destruct (e_consis_swap Dp HD1 HD2 HSq) as [S1t [HS1t Dpt]].
        rewrite !swap_aenv_app, !swap_aenv_one_tvar, !swap_pskl_open_var,
          swap_atom_l in Dpt.
        rewrite (swap_aenv_fresh_id α (supply_fresh S1) Θ'),
          (swap_pskl_fresh_id α (supply_fresh S1) (pskl_univ_ghost P0')),
          (swap_pskl_fresh_id α (supply_fresh S1) Pb) in Dpt
          by (clear - Hα Hz Hcov; simpl in *; fsetdec).
        pose proof (dom_subset_ftvar_in_aenv Θ') as Hdm.
        assert (Hu' : uniq ((supply_fresh S1 ~ abind_tvar) ++ Θ'))
          by (apply uniq_push;
              [ exact Hu | clear - Hz Hcov Hdm; fsetdec ]).
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Pb
                      (pskl_var_f (supply_fresh S1))) as Hup2.
        assert (Hcov' : consis_call_cover
                  ((supply_fresh S1 ~ abind_tvar) ++ Θ')
                  (consis_call_consis Δ1 (add (supply_fresh S1) Δ2)
                     (pskl_univ_ghost P0')
                     (open_pskl_wrt_pskl Pb (pskl_var_f (supply_fresh S1))))
                  [<=] add (supply_fresh S1) S1).
        { cbn [consis_call_cover]. simpl ftvar_in_aenv.
          clear - Hcov Hup2. simpl in *. fsetdec. }
        kill_ccall (Q3 P0' Pb eq_refl eq_refl) Hu' Hcov' Dpt
          (swap_pskl α (supply_fresh S1) Qb) r Hr ps Hav HS HT HQ.
        destruct (consis_swaps_close Hα Hz Hav HS1t HS HT HQ)
          as (HTz & HavAll & HSAll & HQAll).
        destruct (@split_tvar_head_hit_eq _ _ _ HTz) as [pf Hsp].
        rewrite Hsp. cbv beta iota.
        exists (mk_consis_result (cs_supply r)
                  (swaps_aenv ps (swap_aenv α (supply_fresh S1) Θd))
                  (pskl_all_syn (close_pskl_wrt_pskl (supply_fresh S1) (cs_out r)))),
               ((α, supply_fresh S1) :: ps).
        exact (conj eq_refl (conj HavAll (conj HSAll (conj eq_refl HQAll)))).
      *
        destruct (e_consis_inv_ghost_subject Hd
                    ltac:(intros ? Habs; discriminate Habs))
          as [-> [-> [-> Hdis]]].
        do_ghost_cell Hdis.
      *
        destruct (e_consis_inv_univ_ghost Hd) as [Qb [-> Dc]].
        assert (Hcov0 : consis_call_cover Θ'
                  (consis_call_consis Δ1 Δ2 P0' Pb) [<=] S1)
          by (clear - Hcov;
              cbn [consis_call_cover ftvar_in_pskl] in *; fsetdec).
        kill_ccall (Q4 P0' Pb eq_refl eq_refl) Hu Hcov0 Dc Qb
          r Hr ps Hav HS HT HQ.
        exists (mk_consis_result (cs_supply r) (cs_ctx r)
                  (pskl_univ_ghost (cs_out r))), ps.
        split; [ reflexivity | ].
        repeat apply conj; [ exact Hav | cbn [cs_supply]; exact HS
                | cbn [cs_ctx]; exact HT | ].
        cbn [cs_out]. rewrite swaps_pskl_univ_ghost. f_equal. exact HQ.

Qed.

Corollary e_consis_impl_complete : forall Δ1 Δ2 S0 Θ P0 P
    (HP0 : lc_pskl P0) (HP : lc_pskl P) (HD : aenv_defs_mono Θ)
    (H : e_consis_order Δ1 Δ2 S0 Θ P0 P) Sd Θd Qd,
  {{ S0 ↝ Sd ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Qd ⊣ Θd }}e ->
  uniq Θ ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P ∪ Δ1 ∪ Δ2 [<=] S0 ->
  exists r ps,
    e_consis_impl Δ1 Δ2 S0 Θ P0 P HP0 HP HD H = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] cs_supply (proj1_sig r)
    /\ swaps_aenv ps Θd = cs_ctx (proj1_sig r)
    /\ swaps_pskl ps Qd = cs_out (proj1_sig r).
Proof.
  intros * Hd Hu Hcov.
  set (Ho := e_consis_order_to_call _ _ _ _ _ _ H).
  destruct (e_consis_call_impl_complete Ho (conj HP0 HP) HD Ho Hu Hcov
              Sd Θd Qd Hd) as [r0 [ps [Heq [Hav [HS [HT HQ]]]]]].
  unfold e_consis_impl. fold Ho.
  destruct (e_consis_call_impl (consis_call_consis Δ1 Δ2 P0 P) S0 Θ
              (conj HP0 HP) HD Ho) as [ [rr Hrr] | ] eqn:Hcl;
    try rewrite Hcl in Heq; cbn [consis_call_answer proj1_sig] in Heq;
    [ inversion Heq; subst | discriminate ].
  eexists; exists ps.
  exact (conj eq_refl (conj Hav (conj HS (conj HT HQ)))).
Qed.
