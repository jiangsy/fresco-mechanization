Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.subtyping.def_look.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Lemma e_looksub_lookeq_supply_grows :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> S0 [<=] S1) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> S0 [<=] S1).
Proof.
  apply e_looksub_lookeq_mutind;
    intros; fsetdec.
Qed.

Corollary e_looksub_supply_grows : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> S0 [<=] S1.
Proof. apply e_looksub_lookeq_supply_grows. Qed.

Corollary e_lookeq_supply_grows : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> S0 [<=] S1.
Proof. apply e_looksub_lookeq_supply_grows. Qed.

#[local] Ltac look_grow_facts :=
  repeat match goal with
  | H : e_looksub ?S0 _ _ _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_looksub_supply_grows H)
      end
  | H : e_lookeq ?S0 _ _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_lookeq_supply_grows H)
      end
  end.

Lemma e_looksub_lookeq_block :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
     /\ ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
     /\ ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply e_looksub_lookeq_mutind;
    intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    look_grow_facts;
    repeat (rewrite dom_app in * || rewrite ftvar_in_aenv_app in * );
    simpl in *;
    repeat match goal with |- _ /\ _ => split end;
    try solve [ match goal with
                | H : ?X ∩ _ [=] empty |- ?X ∩ _ [=] empty => clear - H; fsetdec
                end ];
    try solve [ fsetdec ];
    try solve [ solve_uniq ];
    try solve [ apply uniq_app_4;
                [ assumption | assumption | unfold disjoint; fsetdec ] ].
Qed.

Corollary e_looksub_generated_in_supply : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> dom Ξ [<=] S1.
Proof. intros * H. apply (proj1 e_looksub_lookeq_block) in H. tauto. Qed.

Corollary e_lookeq_generated_in_supply : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> dom Ξ [<=] S1.
Proof. intros * H. apply (proj2 e_looksub_lookeq_block) in H. tauto. Qed.

Corollary e_looksub_block_ftvar : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros * H. apply (proj1 e_looksub_lookeq_block) in H. tauto. Qed.

Corollary e_lookeq_block_ftvar : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros * H. apply (proj2 e_looksub_lookeq_block) in H. tauto. Qed.

#[local] Ltac open_upper_facts :=
  repeat match goal with
  | H : context [ ftvar_in_pskl (open_pskl_wrt_pskl ?X (pskl_var_f ?b)) ] |- _ =>
      lazymatch goal with
      | _ : ftvar_in_pskl (open_pskl_wrt_pskl X (pskl_var_f b)) [<=] _ |- _ =>
          fail
      | _ => pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper X (pskl_var_f b))
      end
  end.

Lemma e_looksub_lookeq_cstr_ftvar :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     ftvar_in_a_cstrs C [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     ftvar_in_a_cstrs C [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P').
Proof.
  apply e_looksub_lookeq_mutind;
    intros; look_grow_facts; open_upper_facts;
    repeat rewrite ftvar_in_a_cstrs_app in *;
    simpl in *; fsetdec.
Qed.

Corollary e_looksub_cstr_ftvar : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0 ->
  ftvar_in_a_cstrs C [<=] S1.
Proof.
  intros * H Hcov. pose proof (e_looksub_supply_grows H) as Hgrow.
  apply (proj1 e_looksub_lookeq_cstr_ftvar) in H. clear - H Hcov Hgrow. fsetdec.
Qed.

Lemma e_looksub_lookeq_cstr_old :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     ftvar_in_a_cstrs C ∩ S0 [<=] ftvar_in_pskl P ∪ ftvar_in_pskl P') /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     ftvar_in_a_cstrs C ∩ S0 [<=] ftvar_in_pskl P ∪ ftvar_in_pskl P').
Proof.
  apply e_looksub_lookeq_mutind;
    intros; look_grow_facts; open_upper_facts;
    repeat rewrite ftvar_in_a_cstrs_app in *;
    simpl in *; fsetdec.
Qed.

Lemma e_look_cross_half_guard :
  forall S0 S1 Θ α P1 P1' Ξ1 C1 (Ξ2 : aenv) (C2 : a_cstrs),
  {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
  ftvar_in_pskl P1 ∪ ftvar_in_pskl P1' [<=] S0 ->
  dom Ξ2 ∩ S1 [=] empty ->
  ftvar_in_a_cstrs C2 ∩ S1 [<=] S0 ->
  ftvar_in_a_cstrs C1 ∩ dom Ξ2 [=] empty
  /\ ftvar_in_a_cstrs C2 ∩ dom Ξ1 [=] empty.
Proof.
  intros * He HcovA Hd2 Hold2.
  pose proof (e_lookeq_supply_grows He) as Hgrow.
  assert (Hc1 : ftvar_in_a_cstrs C1 [<=] S1).
  { pose proof ((proj2 e_looksub_lookeq_cstr_ftvar) _ _ _ _ _ _ _ _ He) as H1.
    clear - H1 HcovA Hgrow. fsetdec. }
  assert (Hb1in : dom Ξ1 [<=] S1)
    by (exact (e_lookeq_generated_in_supply He)).
  assert (Hb1fr : dom Ξ1 ∩ S0 [=] empty).
  { pose proof He as He'.
    apply (proj2 e_looksub_lookeq_block) in He'. tauto. }
  split; [ clear - Hc1 Hd2; fsetdec | ].
  assert (Hx : ftvar_in_a_cstrs C2 ∩ dom Ξ1 [<=] ftvar_in_a_cstrs C2 ∩ S1)
    by (clear - Hb1in; fsetdec).
  clear - Hx Hold2 Hb1fr. fsetdec.
Qed.

Lemma e_looksub_lookeq_absent_pins :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     α `notin` ftvar_in_pskl P ->
     Ξ = nil /\ C = nil /\ S1 [=] S0) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     α `notin` ftvar_in_pskl P ->
     Ξ = nil /\ C = nil /\ S1 [=] S0).
Proof.
  apply e_looksub_lookeq_mutind.

  -
    intros S Θ α m P Habs. exfalso. simpl in Habs. clear - Habs. fsetdec.
  -
    intros S Θ α m P P' Hn Habs.
    split; [ reflexivity | ]. split; [ reflexivity | reflexivity ].
  -
    intros S Θ α m P Hne Habs.
    split; [ reflexivity | ]. split; [ reflexivity | reflexivity ].
  -
    intros S0 S1 Θ α A B Ξ C Hgf Hne Hg1 Hg2 He IH Habs. exact (IH Habs).
  -
    intros S0 S1 Θ α A B Ξ C β Hgf Hβ Hocc Hnv He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  -
    intros S0 S1 S2 Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He IH1 Hs IH2 Habs.
    simpl in Habs.
    destruct (IH1 ltac:(clear - Habs; fsetdec)) as [-> [-> HS1]].
    destruct (IH2 ltac:(clear - Habs; fsetdec)) as [-> [-> HS2]].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    clear - HS1 HS2. fsetdec.
  -
    intros S0 S1 Θ α m P P' Ξ C β Hβ Hocc Hnh Hfr He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  -
    intros S0 S1 Θ α m P P' Ξ C Hnh Hfr He IH Habs.
    apply IH. simpl in Habs. exact Habs.

  -
    intros S Θ α P Habs. exfalso. simpl in Habs. clear - Habs. fsetdec.
  -
    intros S Θ α P P' Hn Habs.
    split; [ reflexivity | ]. split; [ reflexivity | reflexivity ].
  -
    intros S Θ α P Hne Habs.
    split; [ reflexivity | ]. split; [ reflexivity | reflexivity ].
  -
    intros S Θ α P β α1 Hα1 Hflx Hne Hin Habs.
    exfalso. clear - Hin Habs. fsetdec.
  -
    intros S0 S1 S2 Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He1 IH1 He2 IH2 Habs.
    simpl in Habs.
    destruct (IH1 ltac:(clear - Habs; fsetdec)) as [-> [-> HS1]].
    destruct (IH2 ltac:(clear - Habs; fsetdec)) as [-> [-> HS2]].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    clear - HS1 HS2. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C He IH Habs.
    apply IH. simpl in Habs. exact Habs.
  -
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Habs.
    exfalso. clear - Hocc Habs. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C Hg Hfx He IH Habs.
    apply IH. simpl in Habs. exact Habs.
  -
    intros S0 S1 Θ α P P' Ξ C Hne Hg He IH Habs. exact (IH Habs).
Qed.

Corollary e_looksub_absent_pins : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil /\ S1 [=] S0.
Proof. intros. eapply (proj1 e_looksub_lookeq_absent_pins); eassumption. Qed.

Corollary e_lookeq_absent_pins : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  α `notin` ftvar_in_pskl P ->
  Ξ = nil /\ C = nil /\ S1 [=] S0.
Proof. intros. eapply (proj2 e_looksub_lookeq_absent_pins); eassumption. Qed.

Lemma e_looksub_lookeq_sound :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
     {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
     {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a).
Proof.
  apply e_looksub_lookeq_mutind.

  -  intros. apply a_looksub__var.
  -  intros. apply a_looksub__absent; assumption.
  -  intros. apply a_looksub__vacuous. assumption.
  -
    intros S0 S1 Θ α A B Ξ C Hgf Hne Hg1 Hg2 Hl IH Hcov.
    apply a_looksub__check; auto.
  -
    intros S0 S1 Θ α A B Ξ C β Hgf Hβ Hocc Hnv Hl IH Hcov.
    apply a_looksub__forall_r with (β := β).
    + assumption.
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + exact Hnv.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β)) as Hup.
      simpl in Hup, Hcov |- *.
      clear - Hup Hcov. fsetdec.
  -
    intros S0 S1 S2 Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He IH1 Hs IH2 Hcov.
    simpl in Hcov.
    pose proof (e_lookeq_supply_grows He) as Hgrow.
    assert (HcovA : ftvar_in_pskl P1 ∪ ftvar_in_pskl P1' [<=] S0)
      by (clear - Hcov; fsetdec).
    assert (HcovB : ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0)
      by (clear - Hcov; fsetdec).
    assert (Hd2 : dom Ξ2 ∩ S1 [=] empty).
    { pose proof Hs as Hs'.
      apply (proj1 e_looksub_lookeq_block) in Hs'. tauto. }
    assert (Hold2 : ftvar_in_a_cstrs C2 ∩ S1 [<=] S0)
      by (pose proof (proj1 e_looksub_lookeq_cstr_old _ _ _ _ _ _ _ _ _ Hs) as Ho;
          clear - Ho HcovB; fsetdec).
    destruct (e_look_cross_half_guard Ξ2 C2 He HcovA Hd2 Hold2)
      as [Hg1 Hg2].
    apply a_looksub__arrow; [ exact Hg1 | exact Hg2 | | ].
    + apply IH1. clear - Hcov. fsetdec.
    + apply IH2. clear - Hcov Hgrow. fsetdec.
  -
    intros S0 S1 Θ α m P P' Ξ C β Hβ Hocc Hnh Hfr Hl IH Hcov.
    apply a_looksub__forall_l with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + exact Hnh.
    + exact Hfr.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
      simpl in Hup, Hcov |- *.
      clear - Hup Hcov. fsetdec.
  -
    intros S0 S1 Θ α m P P' Ξ C Hnh Hfr Hl IH Hcov.
    apply a_looksub__univ_ghost_l; [ exact Hnh | exact Hfr | ].
    apply IH. simpl in Hcov.
    clear - Hcov. fsetdec.

  -  intros. apply a_lookeq__var.
  -  intros. apply a_lookeq__absent; assumption.
  -  intros. apply a_lookeq__vacuous. assumption.
  -
    intros S Θ α P β α1 Hα1 Hflx Hne Hin Hcov.
    apply a_lookeq__flex_r; auto.
    simpl in Hcov. clear - Hα1 Hcov. fsetdec.
  -
    intros S0 S1 S2 Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He1 IH1 He2 IH2 Hcov.
    simpl in Hcov.
    pose proof (e_lookeq_supply_grows He1) as Hgrow.
    assert (HcovA : ftvar_in_pskl P1 ∪ ftvar_in_pskl P1' [<=] S0)
      by (clear - Hcov; fsetdec).
    assert (HcovB : ftvar_in_pskl P2 ∪ ftvar_in_pskl P2' [<=] S0)
      by (clear - Hcov; fsetdec).
    assert (Hd2 : dom Ξ2 ∩ S1 [=] empty).
    { pose proof He2 as He2'.
      apply (proj2 e_looksub_lookeq_block) in He2'. tauto. }
    assert (Hold2 : ftvar_in_a_cstrs C2 ∩ S1 [<=] S0)
      by (pose proof (proj2 e_looksub_lookeq_cstr_old _ _ _ _ _ _ _ _ He2) as Ho;
          clear - Ho HcovB; fsetdec).
    destruct (e_look_cross_half_guard Ξ2 C2 He1 HcovA Hd2 Hold2)
      as [Hg1 Hg2].
    apply a_lookeq__arrow; [ exact Hg1 | exact Hg2 | | ].
    + apply IH1. clear - Hcov. fsetdec.
    + apply IH2. clear - Hcov Hgrow. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Hcov.
    apply a_lookeq__forall_inh with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f β)) as H2.
      simpl in H1, H2, Hcov |- *.
      clear - H1 H2 Hcov. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Hcov.
    apply a_lookeq__forall_syn with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      simpl in H1, Hcov |- *.
      clear - H1 Hcov. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C He IH Hcov.
    apply a_lookeq__univ_ghost. apply IH. simpl in Hcov. clear - Hcov. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH Hcov.
    apply a_lookeq__univ_ghost1 with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + exact Hocc.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P' (pskl_var_f β)) as H2.
      simpl in H2, Hcov |- *.
      clear - H2 Hcov. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C Hg Hfx He IH Hcov.
    apply a_lookeq__univ_ghost2; [ assumption | assumption | ].
    apply IH. simpl in Hcov. clear - Hcov. fsetdec.
  -
    intros S0 S1 Θ α P P' Ξ C Hne Hg He IH Hcov.
    apply a_lookeq__univ_ghost_r; [ assumption | assumption | ].
    apply IH. simpl in Hcov. clear - Hcov. fsetdec.
Qed.

Corollary e_looksub_sound : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a.
Proof. intros. eapply (proj1 e_looksub_lookeq_sound); eassumption. Qed.

Lemma e_looksub_lookeq_swap : forall a b,
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
          ≼[ (swap_atom a b α) , m ] (swap_pskl a b P')
          ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
          ∼[ (swap_atom a b α) ] (swap_pskl a b P')
          ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e).
Proof.
  intros a b.
  apply e_looksub_lookeq_mutind.

  -
    intros S Θ α m P S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_looksub__var ].
  -
    intros S Θ α m P P' Hni S0' Heq. simpl.
    exists S0'. split; [ exact Heq | ].
    apply e_looksub__absent. auto using swap_pskl_ftv_notin.
  -
    intros S Θ α m P Hne S0' Heq. simpl.
    exists S0'. split;
      [ exact Heq | apply e_looksub__vacuous; apply swap_pskl_neq_var; exact Hne ].
  -
    intros S0 S1 Θ α A B Ξ C Hgf Hne Hg1 Hg2 Hl IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_looksub__check;
      auto using swap_pskl_neq_var, guarded_pskl_swap, pskl_ghost_free_swap.
  -
    intros S0 S1 Θ α A B Ξ C β Hgf Hβ Hocc Hnv Hl IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_looksub__forall_r with (β := swap_atom a b β);
      [ apply pskl_ghost_free_swap; exact Hgf
      | eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc
      | apply swap_pskl_neq_var; exact Hnv | ].
    rewrite swap_pskl_open_var in Hd. exact Hd.
  -
    intros S0 S1 S2 Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He IH1 Hs IH2 S0' Heq.
    simpl.
    destruct (IH1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IH2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app, swap_cstrs_app.
    eapply e_looksub__arrow; eassumption.
  -
    intros S0 S1 Θ α m P P' Ξ C β Hβ Hocc Hnh Hfr Hl IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_looksub__forall_l with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc
      | apply swap_pskl_not_ghost; exact Hnh
      | apply forall_r_off_swap; exact Hfr | ].
    rewrite swap_pskl_open_var in Hd. exact Hd.
  -
    intros S0 S1 Θ α m P P' Ξ C Hnh Hfr Hl IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split;
      [ exact HS1
      | apply e_looksub__univ_ghost_l;
          [ apply swap_pskl_not_ghost; exact Hnh
          | apply forall_r_off_swap; exact Hfr | exact Hd ] ].

  -
    intros S Θ α P S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_lookeq__var ].
  -
    intros S Θ α P P' Hni S0' Heq. simpl.
    exists S0'. split; [ exact Heq | ].
    apply e_lookeq__absent. auto using swap_pskl_ftv_notin.
  -
    intros S Θ α P Hne S0' Heq. simpl.
    exists S0'. split;
      [ exact Heq | apply e_lookeq__vacuous; apply swap_pskl_neq_var; exact Hne ].
  -
    intros S Θ α P β α1 Hα1 Hflx Hne Hin S0' Heq. simpl.
    exists (add (swap_atom a b α1) S0'). split;
      [ apply eq_swap_atoms_add; exact Heq | ].
    apply e_lookeq__flex_r;
      [ eapply swap_notin_eq; eassumption
      | auto using a_flex_tvar_swap
      | auto using swap_pskl_neq_var
      | auto using swap_pskl_ftv_in ].
  -
    intros S0 S1 S2 Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 He1 IH1 He2 IH2 S0' Heq.
    simpl.
    destruct (IH1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IH2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app, swap_cstrs_app.
    eapply e_lookeq__arrow; eassumption.
  -
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__forall_inh with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc | ].
    rewrite !swap_pskl_open_var in Hd. exact Hd.
  -
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__forall_syn with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc | ].
    rewrite swap_pskl_open_var in Hd. exact Hd.
  -
    intros S0 S1 Θ α P P' Ξ C He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_lookeq__univ_ghost; exact Hd ].
  -
    intros S0 S1 Θ α P P' Ξ C β Hβ Hocc He IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__univ_ghost1 with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption
      | apply swap_pskl_ftv_in; exact Hocc | ].
    rewrite swap_pskl_open_var in Hd. exact Hd.
  -
    intros S0 S1 Θ α P P' Ξ C Hg Hfx He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__univ_ghost2;
      auto using guarded_pskl_swap, flex_r_off_swap.
  -
    intros S0 S1 Θ α P P' Ξ C Hne Hg He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_lookeq__univ_ghost_r;
      auto using swap_pskl_neq_var, guarded_pskl_swap.
Qed.

Lemma e_looksub_lookeq_supply_respect :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e).
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_looksub_lookeq_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_cstrs_same in Hswap.
  setoid_rewrite swap_atom_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  exact Hswap.
Qed.

Corollary e_looksub_swap : forall a b S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
       ≼[ (swap_atom a b α) , m ] (swap_pskl a b P')
       ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e.
Proof. intros a b. apply e_looksub_lookeq_swap. Qed.

Corollary e_lookeq_swap : forall a b S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ (swap_pskl a b P)
       ∼[ (swap_atom a b α) ] (swap_pskl a b P')
       ⤳ (swap_aenv a b Ξ) ⨾ (swap_cstrs a b C) }}e.
Proof. intros a b. apply e_looksub_lookeq_swap. Qed.
