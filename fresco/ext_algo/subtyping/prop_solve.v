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
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Lemma e_solve_sub_eq_supply_grows :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e -> S0 [<=] S1) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> S0 [<=] S1).
Proof.
  apply e_solve_sub_eq_mutind;
    intros;
    try (match goal with
         | Hg : e_guess_mono _ _ _ _ _ |- _ =>
             exact (e_guess_mono_supply_grows Hg)
         end);
    fsetdec.
Qed.

Corollary e_solve_sub_supply_grows : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e -> S0 [<=] S1.
Proof. apply e_solve_sub_eq_supply_grows. Qed.

Corollary e_solve_eq_supply_grows : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> S0 [<=] S1.
Proof. apply e_solve_sub_eq_supply_grows. Qed.

Lemma e_solve_cstr_supply_grows : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e -> S0 [<=] S1.
Proof.
  intros * H; induction H;
    try (match goal with
         | Hs : e_solve_sub _ _ _ _ _ _ _ _ |- _ =>
             pose proof (e_solve_sub_supply_grows Hs)
         end);
    try (match goal with
         | He : e_solve_eq _ _ _ _ _ _ _ |- _ =>
             pose proof (e_solve_eq_supply_grows He)
         end);
    fsetdec.
Qed.

#[local] Ltac solve_grow_facts :=
  repeat match goal with
  | H : e_solve_sub ?S0 _ _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_solve_sub_supply_grows H)
      end
  | H : e_solve_eq ?S0 _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_solve_eq_supply_grows H)
      end
  | H : e_solve_cstr ?S0 _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_solve_cstr_supply_grows H)
      end
  | H : e_guess_mono ?S0 _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_guess_mono_supply_grows H)
      end
  end.

#[local] Ltac guess_block_facts :=
  repeat match goal with
  | H : e_guess_mono _ _ _ ?X _ |- _ =>
      lazymatch goal with
      | _ : dom X [<=] _ |- _ => fail
      | _ => pose proof (e_guess_mono_generated_in_supply H);
             pose proof (e_guess_mono_block_fresh H);
             pose proof (e_guess_mono_uniq H);
             pose proof (e_guess_mono_generated_ftvar H)
      end
  end.

Lemma e_solve_sub_eq_block :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
     /\ ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
     /\ ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply e_solve_sub_eq_mutind;
    intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    solve_grow_facts; guess_block_facts;
    repeat (rewrite dom_app in * || rewrite ftvar_in_aenv_app in * );
    simpl in *;
    repeat split;
    try solve [ fsetdec ];
    try solve [ solve_uniq ];
    try solve [ apply uniq_app_4;
                [ assumption | assumption | unfold disjoint; fsetdec ] ].
Qed.

Corollary e_solve_eq_block_in_supply : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> dom Ξ [<=] S1.
Proof. intros * H. apply (proj2 e_solve_sub_eq_block) in H. tauto. Qed.

Corollary e_solve_eq_block_ftvar : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros * H. apply (proj2 e_solve_sub_eq_block) in H. tauto. Qed.

Corollary e_solve_eq_uniq : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> uniq Ξ.
Proof. intros * H. apply (proj2 e_solve_sub_eq_block) in H. tauto. Qed.

Lemma e_solve_ctx_cov : forall (Ξ Θ : aenv) (S0 S1 : supply),
  ftvar_in_aenv Θ [<=] S0 ->
  S0 [<=] S1 ->
  dom Ξ [<=] S1 ->
  ftvar_in_aenv Ξ [<=] dom Ξ ->
  ftvar_in_aenv (Ξ ++ Θ) [<=] S1.
Proof. intros * H1 H2 H3 H4. rewrite ftvar_in_aenv_app. fsetdec. Qed.

#[local] Ltac binder_facts :=
  repeat match goal with
  | H : context [ ftvar_in_pskl (open_pskl_wrt_pskl ?X (pskl_var_f ?b)) ] |- _ =>
      lazymatch goal with
      | _ : ftvar_in_pskl (open_pskl_wrt_pskl X (pskl_var_f b)) [<=] _ |- _ =>
          fail
      | _ => pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper X (pskl_var_f b))
      end
  end;
  repeat match goal with
  | |- context [ ftvar_in_pskl (close_pskl_wrt_pskl ?b ?X) ] =>
      lazymatch goal with
      | _ : ftvar_in_pskl (close_pskl_wrt_pskl b X) [=] _ |- _ => fail
      | _ => pose proof (ftvar_in_pskl_close_pskl_wrt_pskl X b)
      end
  end.

Lemma e_solve_sub_eq_out_ftvar :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     ftvar_in_pskl P' [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     ftvar_in_pskl P' [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q).
Proof.
  apply e_solve_sub_eq_mutind;
    intros; solve_grow_facts;

    repeat match goal with
    | H : e_guess_mono _ _ _ _ _ |- _ =>
        lazymatch goal with
        | _ : ftvar_in_ptyp _ [<=] _ |- _ => fail
        | _ => pose proof (e_guess_mono_ftv H);
               pose proof (e_guess_mono_generated_in_supply H)
        end
    end;
    simpl in *; binder_facts;
    simpl in *;
    try fsetdec.
  all: rewrite ftvar_ptyp_to_pskl; fsetdec.
Qed.

Corollary e_solve_eq_out_ftvar : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  ftvar_in_pskl P' [<=] S1.
Proof.
  intros * H Hcov. pose proof (e_solve_eq_supply_grows H) as Hgrow.
  apply (proj2 e_solve_sub_eq_out_ftvar) in H. clear - H Hcov Hgrow. fsetdec.
Qed.

Lemma e_solve_sub_eq_sound :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
     {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
     {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a).
Proof.
  apply e_solve_sub_eq_mutind.

  -  intros. apply a_solve_sub__var.
  -
    intros S0 S1 Θ m P Q Ξ P' β Hβ Hs IH Hcov.
    apply a_solve_sub__forall_l with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      simpl in H1, Hcov |- *. clear - H1 Hcov. fsetdec.
  -
    intros S0 S1 Θ m P Q Ξ P' Hs IH Hcov.
    apply a_solve_sub__univ_ghost_l. apply IH. simpl in Hcov.
    clear - Hcov. fsetdec.
  -  intros. apply a_solve_sub__vacuous. assumption.
  -
    intros S0 S1 Θ P Q Ξ P' Hgf Hg1 Hg2 He IH Hcov.
    apply a_solve_sub__check; auto.
  -
    intros S0 S1 Θ P B Ξ P' β Hgf Hoff Hβ Hs IH Hcov.
    apply a_solve_sub__forall_r with (β := β);
      [ assumption | assumption | | ].
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β)) as H1.
      simpl in H1, Hcov |- *. clear - H1 Hcov. fsetdec.
  -
    intros S0 S1 S2 Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' He IH1 Hs IH2 Hcov.
    simpl in Hcov.
    pose proof (e_solve_eq_supply_grows He) as Hgrow.
    pose proof (e_solve_eq_block_in_supply He) as Hbin.
    pose proof (e_solve_eq_block_ftvar He) as Hbftv.
    apply a_solve_sub__arrow.
    + apply IH1. clear - Hcov. fsetdec.
    + apply IH2.
      assert (Hctx : ftvar_in_aenv (Ξ1 ++ Θ) [<=] S1)
        by (apply e_solve_ctx_cov with (S0 := S0);
            solve [ clear - Hcov; fsetdec | assumption ]).
      clear - Hctx Hcov Hgrow. fsetdec.
  -
    intros S0 S1 S2 Θ m Q1 Q2 Ξ1 Ξ2 P1' P2' He IH1 Hs IH2 Hcov.
    simpl in Hcov.
    pose proof (e_solve_eq_supply_grows He) as Hgrow.
    pose proof (e_solve_eq_block_in_supply He) as Hbin.
    pose proof (e_solve_eq_block_ftvar He) as Hbftv.
    apply a_solve_sub__ghost_l_fn.
    + apply IH1. simpl. clear - Hcov. fsetdec.
    + apply IH2.
      assert (Hctx : ftvar_in_aenv (Ξ1 ++ Θ) [<=] S1)
        by (apply e_solve_ctx_cov with (S0 := S0);
            solve [ clear - Hcov; fsetdec | assumption ]).
      simpl. clear - Hctx Hcov Hgrow. fsetdec.
  -  intros. apply a_solve_sub__ghost_l; assumption.

  -  intros. apply a_solve_eq__unit.
  -  intros. apply a_solve_eq__var.
  -
    intros S0 S1 Θ α P Ξ A Hf Hnf Hng Hg Hcov.
    apply a_solve_eq__flex_r; try assumption.
    eapply e_guess_mono_sound;
      [ exact Hg | clear - Hcov; fsetdec | clear - Hcov; fsetdec ].
  -  intros. apply a_solve_eq__ghost_l.
  -  intros. apply a_solve_eq__ghost_r.
  -
    intros S0 S1 S2 Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' He1 IH1 He2 IH2 Hcov.
    simpl in Hcov.
    pose proof (e_solve_eq_supply_grows He1) as Hgrow.
    pose proof (e_solve_eq_block_in_supply He1) as Hbin.
    pose proof (e_solve_eq_block_ftvar He1) as Hbftv.
    apply a_solve_eq__arrow.
    + apply IH1. clear - Hcov. fsetdec.
    + apply IH2.
      assert (Hctx : ftvar_in_aenv (Ξ1 ++ Θ) [<=] S1)
        by (apply e_solve_ctx_cov with (S0 := S0);
            solve [ clear - Hcov; fsetdec | assumption ]).
      clear - Hctx Hcov Hgrow. fsetdec.
  -
    intros S0 S1 Θ P Q Ξ P' β Hβ He IH Hcov.
    apply a_solve_eq__forall with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f β)) as H2.
      simpl in H1, H2, Hcov |- *. clear - H1 H2 Hcov. fsetdec.
  -
    intros S0 S1 Θ P Q Ξ P' He IH Hcov.
    apply a_solve_eq__univ_ghost_both. apply IH. simpl in Hcov.
    clear - Hcov. fsetdec.
  -
    intros S0 S1 Θ P Q Ξ P' β Hβ He IH Hcov.
    apply a_solve_eq__univ_ghost_l_all with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f β)) as H2.
      simpl in H2, Hcov |- *. clear - H2 Hcov. fsetdec.
  -
    intros S0 S1 Θ P Q Ξ P' Hg He IH Hcov.
    apply a_solve_eq__univ_ghost_l_guarded; [ assumption | ].
    apply IH. simpl in Hcov. clear - Hcov. fsetdec.
  -
    intros S0 S1 Θ P Q Ξ P' β Hβ He IH Hcov.
    apply a_solve_eq__all_l_univ_ghost with (β := β).
    + simpl in Hcov. clear - Hβ Hcov. fsetdec.
    + apply IH.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as H1.
      simpl in H1, Hcov |- *. clear - H1 Hcov. fsetdec.
  -
    intros S0 S1 Θ P Q Ξ P' Hg He IH Hcov.
    apply a_solve_eq__univ_ghost_r_guarded; [ assumption | ].
    apply IH. simpl in Hcov. clear - Hcov. fsetdec.
Qed.

Corollary e_solve_sub_sound : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a.
Proof. intros. eapply (proj1 e_solve_sub_eq_sound); eassumption. Qed.

Corollary e_solve_eq_sound : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a.
Proof. intros. eapply (proj2 e_solve_sub_eq_sound); eassumption. Qed.

Lemma e_solve_cstr_block : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  dom Ξ [<=] S1 /\ dom Ξ ∩ S0 [=] empty /\ uniq Ξ
  /\ ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros * H; induction H as
    [ S Θ P | S0 S1 Θ m Q P Ξ P' Hs | S0 S1 S2 Θ Q C P Ξ1 Ξ2 P' P'' He Hc IH ].
  - simpl. repeat split; try apply uniq_nil; fsetdec.
  -
    exact ((proj1 e_solve_sub_eq_block) _ _ _ _ _ _ _ _ Hs).
  - destruct IH as [Hin2 [Hfr2 [Hu2 Hft2]]].
    pose proof (e_solve_eq_block_in_supply He) as Hin1.
    pose proof (e_solve_eq_block_ftvar He) as Hft1.
    pose proof (e_solve_eq_uniq He) as Hu1.
    pose proof ((proj2 e_solve_sub_eq_block) _ _ _ _ _ _ _ He) as Hall.
    destruct Hall as [_ [Hfr1 _]].
    pose proof (e_solve_eq_supply_grows He) as Hg1.
    pose proof (e_solve_cstr_supply_grows Hc) as Hg2.
    repeat rewrite dom_app in *; repeat rewrite ftvar_in_aenv_app in *.
    repeat split; try solve [ fsetdec ].
    apply uniq_app_4; [ assumption | assumption | unfold disjoint; fsetdec ].
Qed.

Lemma e_solve_cstr_out_ftvar : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  ftvar_in_pskl Q [<=] S1 ∪ ftvar_in_pskl P ∪ ftvar_in_a_cstrs C.
Proof.
  intros * H; induction H as
    [ S Θ P | S0 S1 Θ m Q P Ξ P' Hs | S0 S1 S2 Θ Q C P Ξ1 Ξ2 P' P'' He Hc IH ];
    simpl in *.
  - fsetdec.
  - pose proof ((proj1 e_solve_sub_eq_out_ftvar) _ _ _ _ _ _ _ _ Hs).
    fsetdec.
  - pose proof ((proj2 e_solve_sub_eq_out_ftvar) _ _ _ _ _ _ _ He).
    pose proof (e_solve_cstr_supply_grows Hc) as Hg2.
    fsetdec.
Qed.

Lemma e_solve_cstr_sound : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_a_cstrs C ∪ ftvar_in_pskl P [<=] S0 ->
  {{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}a.
Proof.
  intros * H; induction H as
    [ S Θ P | S0 S1 Θ m Q P Ξ P' Hs | S0 S1 S2 Θ Q C P Ξ1 Ξ2 P' P'' He Hc IH ];
    intros Hcov; simpl in Hcov.
  - apply a_solve_cstr__empty.
  - apply a_solve_cstr__sub. eapply e_solve_sub_sound;
      [ exact Hs | clear - Hcov; fsetdec ].
  -
    pose proof (e_solve_eq_supply_grows He) as Hg1.
    pose proof (e_solve_eq_block_in_supply He) as Hbin.
    pose proof (e_solve_eq_block_ftvar He) as Hbftv.
    pose proof (e_solve_eq_out_ftvar He ltac:(clear - Hcov; fsetdec)) as Hout.
    apply a_solve_cstr__eq with (P'' := P'').
    + eapply e_solve_eq_sound; [ exact He | clear - Hcov; fsetdec ].
    + apply IH.
      assert (Hctx : ftvar_in_aenv (Ξ1 ++ Θ) [<=] S1)
        by (apply e_solve_ctx_cov with (S0 := S0);
            solve [ clear - Hcov; fsetdec | assumption ]).
      clear - Hctx Hout Hcov Hg1. fsetdec.
Qed.

Lemma e_solve_sub_eq_swap : forall a b,
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ₛ (swap_pskl a b P) ≼[ m ]
          (swap_pskl a b Q) ⤳ (swap_aenv a b Ξ) ⨾ (swap_pskl a b P') }}e) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ₑ (swap_pskl a b P) ∼
          (swap_pskl a b Q) ⤳ (swap_aenv a b Ξ) ⨾ (swap_pskl a b P') }}e).
Proof.
  intros a b.
  apply e_solve_sub_eq_mutind.

  -
    intros S Θ m α Q S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_solve_sub__var ].
  -
    intros S0 S1 Θ m P Q Ξ P' β Hβ Hs IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    rewrite swap_pskl_close.
    apply e_solve_sub__forall_l with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption | ].
    rewrite swap_pskl_open_var in Hd.    exact Hd.
  -
    intros S0 S1 Θ m P Q Ξ P' Hs IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_solve_sub__univ_ghost_l; exact Hd ].
  -
    intros S Θ m P Hoff S0' Heq. simpl.
    exists S0'. split;
      [ exact Heq | apply e_solve_sub__vacuous; apply peel_l_off_swap; exact Hoff ].
  -
    intros S0 S1 Θ P Q Ξ P' Hgf Hg1 Hg2 He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_solve_sub__check;
      auto using guarded_pskl_swap, pskl_ghost_free_swap.
  -
    intros S0 S1 Θ P B Ξ P' β Hgf Hoff Hβ Hs IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_solve_sub__forall_r with (β := swap_atom a b β);
      [ apply pskl_ghost_free_swap; exact Hgf
      | apply solve_l_off_swap; exact Hoff
      | eapply swap_notin_eq; eassumption | ].
    rewrite swap_pskl_open_var in Hd.    exact Hd.
  -
    intros S0 S1 S2 Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' He IH1 Hs IH2 S0' Heq. simpl.
    destruct (IH1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IH2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app.
    eapply e_solve_sub__arrow; [ exact Hd1 | ].
    rewrite <- swap_aenv_app. exact Hd2.
  -
    intros S0 S1 S2 Θ m Q1 Q2 Ξ1 Ξ2 P1' P2' He IH1 Hs IH2 S0' Heq. simpl.
    destruct (IH1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IH2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app.
    eapply e_solve_sub__ghost_l_fn; [ exact Hd1 | ].
    rewrite <- swap_aenv_app. exact Hd2.
  -
    intros S Θ B Hgf Hg S0' Heq. simpl.
    exists S0'. split; [ exact Heq | ].
    apply e_solve_sub__ghost_l;
      auto using guarded_pskl_swap, pskl_ghost_free_swap.

  -
    intros S Θ S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_solve_eq__unit ].
  -
    intros S Θ α Q S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_solve_eq__var ].
  -
    intros S0 S1 Θ α P Ξ A Hft Hnf Hng Hg S0' Heq. simpl.
    destruct (e_guess_mono_swap Hg Heq) as [S1' [HS1 Hg']].
    exists S1'. split; [ exact HS1 | ].
    rewrite swap_pskl_ptyp_to_pskl.
    apply e_solve_eq__flex_r;
      auto using a_flex_tvar_swap, a_non_flex_swap, nonghost_pskl_swap.
  -
    intros S Θ Q S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_solve_eq__ghost_l ].
  -
    intros S Θ P S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_solve_eq__ghost_r ].
  -
    intros S0 S1 S2 Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' He1 IH1 He2 IH2 S0' Heq. simpl.
    destruct (IH1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IH2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app.
    eapply e_solve_eq__arrow; [ exact Hd1 | ].
    rewrite <- swap_aenv_app. exact Hd2.
  -
    intros S0 S1 Θ P Q Ξ P' β Hβ He IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    rewrite swap_pskl_close.
    apply e_solve_eq__forall with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption | ].
    rewrite !swap_pskl_open_var in Hd.    exact Hd.
  -
    intros S0 S1 Θ P Q Ξ P' He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_solve_eq__univ_ghost_both; exact Hd ].
  -
    intros S0 S1 Θ P Q Ξ P' β Hβ He IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    rewrite swap_pskl_close.
    apply e_solve_eq__univ_ghost_l_all with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption | ].
    rewrite swap_pskl_open_var in Hd.    exact Hd.
  -
    intros S0 S1 Θ P Q Ξ P' Hg He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_solve_eq__univ_ghost_l_guarded; auto using guarded_pskl_swap.
  -
    intros S0 S1 Θ P Q Ξ P' β Hβ He IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    rewrite swap_pskl_close.
    apply e_solve_eq__all_l_univ_ghost with (β := swap_atom a b β);
      [ eapply swap_notin_eq; eassumption | ].
    rewrite swap_pskl_open_var in Hd.    exact Hd.
  -
    intros S0 S1 Θ P Q Ξ P' Hg He IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_solve_eq__univ_ghost_r_guarded; auto using guarded_pskl_swap.
Qed.

Corollary e_solve_sub_swap : forall a b S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ₛ (swap_pskl a b P) ≼[ m ]
       (swap_pskl a b Q) ⤳ (swap_aenv a b Ξ) ⨾ (swap_pskl a b P') }}e.
Proof. intros a b. apply e_solve_sub_eq_swap. Qed.

Corollary e_solve_eq_swap : forall a b S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊢ₑ (swap_pskl a b P) ∼
       (swap_pskl a b Q) ⤳ (swap_aenv a b Ξ) ⨾ (swap_pskl a b P') }}e.
Proof. intros a b. apply e_solve_sub_eq_swap. Qed.

Lemma e_solve_cstr_swap : forall a b S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ) ⊩ (swap_cstrs a b C) ⨾ (swap_pskl a b P)
       ⤳ (swap_aenv a b Ξ) ⨾ (swap_pskl a b Q) }}e.
Proof.
  intros a b S0 Θ C P S1 Ξ Q H; induction H as
    [ S Θ P | S0 S1 Θ m Q P Ξ P' Hs
    | S0 S1 S2 Θ Q C P Ξ1 Ξ2 P' P'' He Hc IH ];
    intros S0' Heq; simpl.
  - exists S0'. split; [ exact Heq | apply e_solve_cstr__empty ].
  - destruct (e_solve_sub_swap Hs Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_solve_cstr__sub; exact Hd ].
  - destruct (e_solve_eq_swap He Heq) as [S1' [HS1 Hd1]].
    destruct (IH _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | ].
    rewrite swap_aenv_app.
    eapply e_solve_cstr__eq;
      [ exact Hd1 | rewrite <- swap_aenv_app; exact Hd2 ].
Qed.

Lemma e_solve_sub_eq_supply_respect :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e).
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_solve_sub_eq_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  exact Hswap.
Qed.

Corollary e_solve_sub_supply_respect : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ {{ S0' ↝ S1' ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e.
Proof. apply e_solve_sub_eq_supply_respect. Qed.

Corollary e_solve_eq_supply_respect : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ {{ S0' ↝ S1' ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e.
Proof. apply e_solve_sub_eq_supply_respect. Qed.

Lemma e_solve_cstr_supply_respect : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ {{ S0' ↝ S1' ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e.
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_solve_cstr_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_cstrs_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  exact Hswap.
Qed.
