Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.

Set Implicit Arguments.

Lemma e_guess_mono_supply_grows : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> S0 [<=] S1.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    fsetdec.
Qed.

Lemma e_guess_mono_generated_in_supply : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> dom Ξ [<=] S1.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    simpl; try fsetdec.

  pose proof (e_guess_mono_supply_grows H2) as Hgrow.
  rewrite dom_app. clear - IH1 IH2 Hgrow. fsetdec.
Qed.

Lemma e_guess_mono_generated_fresh : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  forall α, α `in` dom Ξ -> α `notin` S0.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    intros α0 Hα0; simpl in *.
  -  assert (α0 = α) by (clear - Hα0; fsetdec). subst. assumption.
  -  auto.
  -  clear - Hα0; fsetdec.
  -  clear - Hα0; fsetdec.
  -
    rewrite dom_app in Hα0. destruct (union_1 Hα0) as [Hin | Hin]; auto.
    pose proof (e_guess_mono_supply_grows H1) as Hgrow.
    pose proof (IH2 _ Hin) as Hout. clear - Hgrow Hout. fsetdec.
  -
    specialize (IH _ Hα0). clear - IH. fsetdec.
Qed.

Corollary e_guess_mono_block_fresh : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> dom Ξ ∩ S0 [=] empty.
Proof.
  intros * H. intros γ. split; intros Hγ; [ | clear - Hγ; fsetdec ].
  assert (Hin : γ `in` dom Ξ) by (clear - Hγ; fsetdec).
  pose proof (e_guess_mono_generated_fresh H Hin) as Hout.
  clear - Hγ Hout. fsetdec.
Qed.

Lemma e_guess_mono_generated_ftvar : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    simpl; try fsetdec.
  rewrite ftvar_in_aenv_app, dom_app. fsetdec.
Qed.

Lemma e_guess_mono_uniq : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> uniq Ξ.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    try solve [ solve_uniq ].

  apply uniq_app_4; auto.
  unfold disjoint. intros y Hy.
  assert (Hy1 : y `in` dom Ξ1) by (clear - Hy; fsetdec).
  assert (Hy2 : y `in` dom Ξ2) by (clear - Hy; fsetdec).
  pose proof (e_guess_mono_generated_in_supply H1 Hy1) as Hin.
  pose proof (e_guess_mono_generated_fresh H2 Hy2) as Hout.
  contradiction.
Qed.

Lemma e_guess_mono_ftv : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  ftvar_in_ptyp A [<=] ftvar_in_pskl P ∪ dom Ξ.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    simpl; repeat rewrite dom_app; try solve [ fsetdec ].

  { assert (Hcl : ftvar_in_ptyp (close_ptyp_wrt_ptyp β A)
                    [=] AtomSetImpl.remove β (ftvar_in_ptyp A))
      by (apply ftvar_in_ptyp_close_ptyp_wrt_ptyp).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
    simpl in Hup. clear - IH Hcl Hup. fsetdec. }
Qed.

Lemma e_guess_supply_grows : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> S0 [<=] S1.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ fsetdec | exact (e_guess_mono_supply_grows Hg) ].
Qed.

Lemma e_guess_block_in_supply : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> dom Ξ [<=] S1.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ simpl; fsetdec | exact (e_guess_mono_generated_in_supply Hg) ].
Qed.

Lemma e_guess_block_fresh : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> dom Ξ ∩ S0 [=] empty.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ simpl; fsetdec | exact (e_guess_mono_block_fresh Hg) ].
Qed.

Lemma e_guess_uniq : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> uniq Ξ.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ apply uniq_nil | exact (e_guess_mono_uniq Hg) ].
Qed.

Lemma e_guess_block_ftvar : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ];
    [ simpl; fsetdec | exact (e_guess_mono_generated_ftvar Hg) ].
Qed.

Lemma e_guess_ftv : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> ftvar_in_pskl Q' [<=] ftvar_in_pskl Q ∪ dom Ξ.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ]; [ simpl; fsetdec | ].

  rewrite ftvar_ptyp_to_pskl. exact (e_guess_mono_ftv Hg).
Qed.

Corollary e_guess_mono_uniq_app : forall S0 P S1 Ξ A Θ,
  e_guess_mono S0 P S1 Ξ A ->
  ftvar_in_aenv Θ [<=] S0 ->
  uniq Θ ->
  uniq (Ξ ++ Θ).
Proof.
  intros * Hg HΘ Hu.
  apply uniq_app_4; [ eapply e_guess_mono_uniq; eassumption | assumption | ].
  unfold disjoint. intros y Hy.
  assert (Hy1 : y `in` dom Ξ) by (clear - Hy; fsetdec).
  assert (Hy2 : y `in` dom Θ) by (clear - Hy; fsetdec).
  pose proof (e_guess_mono_generated_fresh Hg Hy1) as Hout.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hdom.
  assert (Hin : y `in` S0) by (clear - Hy2 Hdom HΘ; fsetdec).
  contradiction.
Qed.

Lemma e_guess_mono_sound : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  forall Θ,
  ftvar_in_aenv Θ [<=] S0 ->
  ftvar_in_pskl P [<=] S0 ->
  a_guess_mono Θ P Ξ A.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    intros Θ HΘ HP; simpl in HP.
  -
    apply a_guess_mono__ghost. clear - Hα HΘ. fsetdec.
  -  apply a_guess_mono__univ_ghost. auto.
  -  apply a_guess_mono__var.
  -  apply a_guess_mono__unit.
  -
    pose proof (e_guess_mono_supply_grows H1) as Hgrow.
    apply a_guess_mono__arrow.
    + apply IH1; [ assumption | clear - HP; fsetdec ].
    + apply IH2; [ clear - HΘ Hgrow; fsetdec | clear - HP Hgrow; fsetdec ].
  -
    apply a_guess_mono__forall with (β := β).
    + clear - Hβ HΘ HP. fsetdec.
    + apply IH.
      * rewrite ftvar_in_aenv_cons_tvar. clear - HΘ. fsetdec.
      * pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β))
          as Hup.
        simpl in Hup. clear - Hup HP. fsetdec.
Qed.

Example a_guess_mono_admits_repeated_block : forall α,
  a_guess_mono nil (pskl_arrow pskl_ghost pskl_ghost)
    ((α ~ abind_flex_mono) ++ (α ~ abind_flex_mono))
    (ptyp_arrow (ptyp_var_f α) (ptyp_var_f α)).
Proof.
  intros α.
  apply a_guess_mono__arrow with
    (Ξ1 := (α ~ abind_flex_mono) ++ nil) (Ξ2 := (α ~ abind_flex_mono) ++ nil);
    apply a_guess_mono__ghost; simpl; solve_notin_auto.
Qed.

Example e_guess_mono_refuses_repeated_block : forall α S0 S1,
  ~ e_guess_mono S0 (pskl_arrow pskl_ghost pskl_ghost) S1
      ((α ~ abind_flex_mono) ++ (α ~ abind_flex_mono))
      (ptyp_arrow (ptyp_var_f α) (ptyp_var_f α)).
Proof.
  intros α S0 S1 H.
  pose proof (e_guess_mono_uniq H) as Hu.
  inversion Hu as [ | β bd Ξ Hu' Hβ Heq ]; subst.
  simpl in Hβ. clear - Hβ. fsetdec.
Qed.

Lemma e_guess_sound : forall S0 NM Q S1 Ξ Q' Θ,
  e_guess S0 NM Q S1 Ξ Q' ->
  ftvar_in_aenv Θ [<=] S0 ->
  ftvar_in_pskl Q [<=] S0 ->
  a_guess Θ NM Q Ξ Q'.
Proof.
  intros * H HΘ HQ; destruct H as [ S Q0 | S0 S1 Q0 Ξ A Hg ].
  - apply a_guess__sk.
  - apply a_guess__ty. eapply e_guess_mono_sound; eassumption.
Qed.

Lemma e_guess_mono_swap : forall a b S0 P S1 Ξ τ,
  e_guess_mono S0 P S1 Ξ τ ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    e_guess_mono S0' (swap_pskl a b P) S1' (swap_aenv a b Ξ)
      (swap_ptyp a b τ).
Proof.
  intros a b S0 P S1 Ξ τ H. induction H; intros S0' Heq; simpl.
  -
    exists (add (swap_atom a b α) S0'). split;
      [ apply eq_swap_atoms_add; exact Heq | ].
    apply e_guess_mono__ghost. eapply swap_notin_eq; eassumption.
  -
    destruct (IHe_guess_mono _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_guess_mono__univ_ghost; exact Hd ].
  -  exists S0'. split; [ exact Heq | apply e_guess_mono__var ].
  -  exists S0'. split; [ exact Heq | apply e_guess_mono__unit ].
  -
    destruct (IHe_guess_mono1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IHe_guess_mono2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app. eapply e_guess_mono__arrow; eassumption.
  -
    destruct (IHe_guess_mono (add (swap_atom a b β) S0'))
      as [S1' [HS1 Hd]]; [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    rewrite swap_ptyp_close.
    apply e_guess_mono__forall with (β := swap_atom a b β).
    + eapply swap_notin_eq; eassumption.
    + rewrite swap_pskl_open_var in Hd. exact Hd.
Qed.

Lemma e_guess_swap : forall a b S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    e_guess S0' NM (swap_pskl a b Q) S1' (swap_aenv a b Ξ)
      (swap_pskl a b Q').
Proof.
  intros a b S0 NM Q S1 Ξ Q' H.
  destruct H as [ S Q0 | S0' S1' Q0 Ξ0 A Hg ]; intros S0'' Heq.
  - exists S0''. split; [ exact Heq | simpl; apply e_guess__sk ].
  - destruct (e_guess_mono_swap Hg Heq) as [S1'' [HS1 Hg']].
    exists S1''. split; [ exact HS1 | ].
    rewrite swap_pskl_ptyp_to_pskl. apply e_guess__ty. exact Hg'.
Qed.

Lemma e_guess_mono_supply_respect : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ e_guess_mono S0' P S1' Ξ A.
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_guess_mono_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_ptyp_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  exact Hswap.
Qed.

Lemma e_guess_supply_respect : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ e_guess S0' NM Q S1' Ξ Q'.
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_guess_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  exact Hswap.
Qed.

Lemma e_guess_mono_inv_ghost : forall S0 S1 Ξ A,
  e_guess_mono S0 pskl_ghost S1 Ξ A ->
  exists α, α `notin` S0 /\ S1 = add α S0 /\
    Ξ = (α ~ abind_flex_mono) ++ nil /\ A = ptyp_var_f α.
Proof. intros * Hd. inversion Hd; subst; eauto 10. Qed.

Lemma e_guess_mono_inv_unit : forall S0 S1 Ξ A,
  e_guess_mono S0 pskl_unit S1 Ξ A -> S1 = S0 /\ Ξ = nil /\ A = ptyp_unit.
Proof. intros * Hd. inversion Hd; subst; auto. Qed.

Lemma e_guess_mono_inv_var : forall S0 α S1 Ξ A,
  e_guess_mono S0 (pskl_var_f α) S1 Ξ A ->
  S1 = S0 /\ Ξ = nil /\ A = ptyp_var_f α.
Proof. intros * Hd. inversion Hd; subst; auto. Qed.

Lemma e_guess_mono_inv_arrow : forall S0 P Q S2 Ξ A,
  e_guess_mono S0 (pskl_arrow P Q) S2 Ξ A ->
  exists S1 Ξ1 Ξ2 A1 A2,
    Ξ = Ξ1 ++ Ξ2 /\ A = ptyp_arrow A1 A2 /\
    e_guess_mono S0 P S1 Ξ1 A1 /\ e_guess_mono S1 Q S2 Ξ2 A2.
Proof. intros * Hd. inversion Hd; subst; eauto 10. Qed.

Lemma e_guess_mono_inv_all_syn : forall S0 P S1 Ξ A,
  e_guess_mono S0 (pskl_all_syn P) S1 Ξ A ->
  exists β A0, β `notin` S0 /\ A = ptyp_all (close_ptyp_wrt_ptyp β A0) /\
    e_guess_mono (add β S0) (open_pskl_wrt_pskl P (pskl_var_f β)) S1 Ξ A0.
Proof. intros * Hd. inversion Hd; subst; eauto 10. Qed.

Lemma e_guess_mono_inv_univ_ghost : forall S0 P S1 Ξ A,
  e_guess_mono S0 (pskl_univ_ghost P) S1 Ξ A -> e_guess_mono S0 P S1 Ξ A.
Proof. intros * Hd. inversion Hd; subst; auto. Qed.
