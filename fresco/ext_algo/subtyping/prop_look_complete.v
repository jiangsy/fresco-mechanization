(** Completeness of the supply-threaded collection runners.  Head-result
    determinism aligns each arrow tail, and swaps align fresh binders. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.
Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_ln.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.prop_dec.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.subtyping.prop_extract_det.

Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.prop_look.
Require Import src.fresco.ext_algo.subtyping.def_look_impl.

Set Implicit Arguments.
Open Scope fresco_e_scope.

Local Ltac case_test :=
  match goal with
  | |- context [ sumbool_of_bool ?b ] =>
      let Hm := fresh "Htest" in
      destruct (sumbool_of_bool b) as [Hm | Hm]
  end.

(* Runner flexibility tests agree with the derivation's FlexR side conditions. *)
Local Ltac flex_test_absurd :=
  solve [ match goal with
          | Hm : flex_bound_ck ?T ?b = false, Hf : a_flex_tvar ?T ?b |- _ =>
              exfalso; rewrite (flex_tvar_flex_bound_ck _ _ Hf) in Hm;
              discriminate
          end
        | match goal with
          | Hm : flex_bound_ck ?T ?b = true,
            Hg : flex_r_off ?T (pskl_var_f ?b) |- _ =>
              exfalso; exact (Hg b eq_refl (flex_bound_ck_flex_tvar _ _ Hm))
          end ].

(** Close an impossible inversion case: the branch's decision tests
    contradict the rule's own side conditions. *)
Local Ltac look_absurd :=
  solve [ discriminate
        | match goal with
          | Hm : mem ?a ?s = true, Hn : ?a `notin` ?s |- _ =>
              exfalso; apply Hn; apply mem_true_in; exact Hm
          end
        | match goal with
          | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
          | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
          | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
          | Hg : nonghost_pskl (pskl_univ_ghost _) |- _ => inversion Hg
          | Hg : nonghost_pskl pskl_ghost |- _ => inversion Hg
          end
        | match goal with
          | Hck : ghost_free_ck ?P = false, Hg : pskl_ghost_free ?P |- _ =>
              apply ghost_free_ck_complete in Hg; congruence
          end
        | match goal with
          | Hck : guarded_shape_ck ?P && ghost_free_ck ?P = false,
            Hg : guarded_pskl ?P, Hgf : pskl_ghost_free ?P |- _ =>
              apply guarded_shape_ck_complete in Hg;
              apply ghost_free_ck_complete in Hgf;
              rewrite Hg, Hgf in Hck; discriminate
          end
        | match goal with
          | Hlc : lc_pskl (pskl_var_b _) |- _ => inversion Hlc
          end ].

#[local] Hint Extern 2 (_ [<=] _) =>
  match goal with Hcov : _ [<=] _ |- ?G =>
    tryif has_evar G then fail else (clear - Hcov; simpl in *; fsetdec)
  end : look_complete.

Local Ltac finish_look_eq_call :=
  match goal with
  | D : e_lookeq ?S ?T ?a ?p ?q _ _ _
    |- context [e_lookeq_impl ?S ?T ?a ?p ?q ?hp ?hq ?h] =>
      let Hne := fresh "Hne" in
      let r := fresh "r" in let Hr := fresh "Hr" in
      assert (Hne : e_lookeq_impl S T a p q hp hq h <> None)
        by (eauto 8 with look_complete);
      destruct (e_lookeq_impl S T a p q hp hq h) as [[r Hr]|];
      [cbv beta iota; discriminate | exact (False_ind _ (Hne eq_refl))]
  end.

Lemma e_lookeq_impl_complete : forall S0 Θ α P Q HP HQ H S1 Ξ C,
  e_lookeq S0 Θ α P Q S1 Ξ C ->
  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q) [<=] S0 ->
  e_lookeq_impl S0 Θ α P Q HP HQ H <> None.
Proof.
  intros S0 Θ α P Q HP HQ H. generalize H. revert HP HQ.
  induction H as [S0 Θ α P Q p1 IHhead p1t IHtail
    p2 q2 p3 q3 p4 q4 p5 q5 p6 q6 p7 q7].
  intros HP HQ H S1 Ξ C Hd Hcov.
  destruct P as [ | n | β | P1 P2 | P1 | | P1 ];
    destruct Q as [ | n' | β' | Q1 Q2 | Q1 | | Q1 ];
    simp e_lookeq_impl; repeat case_test;
    try solve [discriminate | destruct (α == β); discriminate];
    inversion Hd; subst; try look_absurd; try flex_test_absurd.
  all: try solve [finish_look_eq_call].
  { (* The head's renaming transports the given tail to the runner's supply. *)
    match goal with
    | D1 : e_lookeq S0 Θ α P1 Q1 ?Sm _ _,
      D2 : e_lookeq ?Sm Θ α P2 Q2 _ _ _ |- _ =>
        rename D1 into Hhead; rename D2 into Htail
    end.
    assert (Hcov1 : add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P1
        ∪ ftvar_in_pskl Q1) [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    match goal with
    | |- context [e_lookeq_impl S0 Θ α P1 Q1 ?hp ?hq ?h] =>
        assert (Hne : e_lookeq_impl S0 Θ α P1 Q1 hp hq h <> None)
          by (eauto 8);
        destruct (e_lookeq_impl S0 Θ α P1 Q1 hp hq h) as [[r Hr]|];
        [cbv beta iota; clear Hne | exact (False_ind _ (Hne eq_refl))]
    end.
    unfold lookeq_spec in Hr.
    destruct (e_lookeq_rel Hhead Hr Hcov1) as (ps & Hav & HS & HX & HC).
    pose proof HS as HSr. symmetry in HSr.
    destruct (e_lookeq_swaps ps Htail HSr) as (Sf & _ & Htail').
    rewrite (swaps_atom_dodge_in Hav) in Htail' by (clear - Hcov; fsetdec).
    rewrite (swaps_aenv_fresh_id ps Θ), (swaps_pskl_fresh_id ps P2),
      (swaps_pskl_fresh_id ps Q2) in Htail'
      by (apply (swaps_dodge_sub Hav); clear - Hcov; simpl in *; fsetdec).
    pose proof (e_lookeq_supply_grows Hr) as Hgrow.
    assert (Hcov2 : add α (ftvar_in_aenv Θ
        ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2) [<=] lk_supply r)
      by (clear - Hcov Hgrow; simpl in *; fsetdec).
    finish_look_eq_call. }
  (* The three binder rules differ only in the inputs they open. *)
  all: pose proof (supply_fresh_notin S0) as Hfresh.
  all: lazymatch goal with
    | Hb : ?b `notin` ?S,
      D : e_lookeq (add ?b ?S) ((?b ~ abind_tvar) ++ ?T) ?a _ _ _ _ _ |- _ =>
        destruct (e_lookeq_swap D (swap_atoms_fresh_add _ _ _ Hb Hfresh))
          as (Sf & _ & Hbody);
        rewrite swap_aenv_app, swap_aenv_one_tvar in Hbody;
        rewrite (swap_aenv_fresh_id b (supply_fresh S) T) in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec);
        rewrite !swap_pskl_open_var, !swap_atom_l in Hbody;
        rewrite (swap_atom_other b (supply_fresh S) a) in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec);
        repeat rewrite swap_pskl_fresh_id in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec)
    end.
  all: pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
    (pskl_var_f (supply_fresh S0))) as Hup1.
  all: pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q1
    (pskl_var_f (supply_fresh S0))) as Hup2.
  all: match goal with
    | |- context [e_lookeq_impl ?S ?T ?a ?p ?q _ _ _] =>
        assert (Hcov' : add a (ftvar_in_aenv T ∪ ftvar_in_pskl p
            ∪ ftvar_in_pskl q) [<=] S)
          by (clear - Hcov Hup1 Hup2; simpl in *; fsetdec)
    end.
  all: finish_look_eq_call.
Qed.

#[local] Hint Resolve e_lookeq_impl_complete : look_complete.

Local Ltac finish_look_sub_call :=
  match goal with
  | D : e_looksub ?S ?T ?a ?m ?p ?q _ _ _
    |- context [e_looksub_impl ?S ?T ?a ?m ?p ?q ?hp ?hq ?h] =>
      let Hne := fresh "Hne" in
      let r := fresh "r" in let Hr := fresh "Hr" in
      assert (Hne : e_looksub_impl S T a m p q hp hq h <> None)
        by (eauto 8 with look_complete);
      destruct (e_looksub_impl S T a m p q hp hq h) as [[r Hr]|];
      [cbv beta iota; discriminate | exact (False_ind _ (Hne eq_refl))]
  end.

Lemma e_looksub_impl_complete : forall S0 Θ α m P Q HP HQ H S1 Ξ C,
  e_looksub S0 Θ α m P Q S1 Ξ C ->
  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q) [<=] S0 ->
  e_looksub_impl S0 Θ α m P Q HP HQ H <> None.
Proof.
  intros S0 Θ α m P Q HP HQ H. generalize H. revert HP HQ.
  induction H as [S0 Θ α m P Q pck pfr qfr par part qar pfl qfl pug qug].
  intros HP HQ H S1 Ξ C Hd Hcov.
  destruct P as [ | n | β | P1 P2 | P1 | | P1 ];
    destruct Q as [ | n' | β' | Q1 Q2 | Q1 | | Q1 ];
    destruct m as [ | | m ];
    simp e_looksub_impl; repeat case_test;
    try solve [discriminate | destruct (α == β); discriminate];
    inversion Hd; subst; try look_absurd; try flex_test_absurd.
  all: try solve [
    match goal with
    | H : forall_r_off mode_tc (pskl_all_syn ?B),
      Hck : ghost_free_ck (pskl_all_syn ?B) = true |- _ =>
        exfalso; apply (H B eq_refl eq_refl);
        apply ghost_free_ck_sound; exact Hck
    end].
  all: try solve [finish_look_eq_call | finish_look_sub_call].
  { (* The head's renaming transports the given tail to the runner's supply. *)
    match goal with
    | D1 : e_lookeq S0 Θ α P1 Q1 ?Sm _ _,
      D2 : e_looksub ?Sm Θ α _ P2 Q2 _ _ _ |- _ =>
        rename D1 into Hhead; rename D2 into Htail
    end.
    assert (Hcov1 : add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P1
        ∪ ftvar_in_pskl Q1) [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    match goal with
    | |- context [e_lookeq_impl S0 Θ α P1 Q1 ?hp ?hq ?h] =>
        assert (Hne : e_lookeq_impl S0 Θ α P1 Q1 hp hq h <> None)
          by (eapply e_lookeq_impl_complete; eassumption);
        destruct (e_lookeq_impl S0 Θ α P1 Q1 hp hq h) as [[r Hr]|];
        [cbv beta iota; clear Hne | exact (False_ind _ (Hne eq_refl))]
    end.
    unfold lookeq_spec in Hr.
    destruct (e_lookeq_rel Hhead Hr Hcov1) as (ps & Hav & HS & HX & HC).
    pose proof HS as HSr. symmetry in HSr.
    destruct (e_looksub_swaps ps Htail HSr) as (Sf & _ & Htail').
    rewrite (swaps_atom_dodge_in Hav) in Htail' by (clear - Hcov; fsetdec).
    rewrite (swaps_aenv_fresh_id ps Θ), (swaps_pskl_fresh_id ps P2),
      (swaps_pskl_fresh_id ps Q2) in Htail'
      by (apply (swaps_dodge_sub Hav); clear - Hcov; simpl in *; fsetdec).
    pose proof (e_lookeq_supply_grows Hr) as Hgrow.
    assert (Hcov2 : add α (ftvar_in_aenv Θ
        ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2) [<=] lk_supply r)
      by (clear - Hcov Hgrow; simpl in *; fsetdec).
    finish_look_sub_call. }
  (* Both binder rules use the same fresh-atom transport. *)
  all: pose proof (supply_fresh_notin S0) as Hfresh.
  all: lazymatch goal with
    | Hb : ?b `notin` ?S,
      D : e_looksub (add ?b ?S) ((?b ~ abind_tvar) ++ ?T) ?a _ _ _ _ _ _ |- _ =>
        destruct (e_looksub_swap D (swap_atoms_fresh_add _ _ _ Hb Hfresh))
          as (Sf & _ & Hbody);
        rewrite swap_aenv_app, swap_aenv_one_tvar in Hbody;
        rewrite (swap_aenv_fresh_id b (supply_fresh S) T) in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec);
        rewrite !swap_pskl_open_var, !swap_atom_l in Hbody;
        rewrite (swap_atom_other b (supply_fresh S) a) in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec);
        repeat rewrite swap_pskl_fresh_id in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec)
    end.
  all: lazymatch goal with
    | |- context [e_looksub_impl ?S ?T ?a _ ?p ?q _ _ _] =>
        assert (Hcov' : add a (ftvar_in_aenv T ∪ ftvar_in_pskl p
            ∪ ftvar_in_pskl q) [<=] S)
          by (clear - Hcov;
              match goal with
              | |- context [open_pskl_wrt_pskl ?B ?V] =>
                  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B V) as Hopen
              end;
              simpl in *; fsetdec)
    end.
  all: finish_look_sub_call.
Qed.
