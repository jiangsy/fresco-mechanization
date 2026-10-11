(** Completeness of the supply-threaded solvers, proved directly against
    their runners.  Determinism aligns the tail of an arrow with the
    runner's head; no auxiliary context of rigid supply atoms is needed. *)

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
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.prop_solve.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_ln.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.prop_dec.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.subtyping.def_solve_impl.
Require Import src.fresco.ext_algo.subtyping.prop_extract_det.

Set Implicit Arguments.
Open Scope fresco_e_scope.

Local Ltac solver_tests :=
  repeat match goal with
  | |- context [sumbool_of_bool ?b] => destruct (sumbool_of_bool b)
  end.

Local Ltac solver_absurd :=
  solve [discriminate
  | match goal with
    | H : peel_l_off (pskl_all_syn ?P) |- _ =>
        exfalso; exact ((proj1 H) P eq_refl)
    | H : peel_l_off (pskl_univ_ghost ?P) |- _ =>
        exfalso; exact ((proj2 H) P eq_refl)
    | H : solve_l_off (pskl_all_syn ?P) |- _ =>
        exfalso; exact ((proj1 (proj2 H)) P eq_refl)
    | H : solve_l_off (pskl_univ_ghost ?P) |- _ =>
        exfalso; exact ((proj2 (proj2 H)) P eq_refl)
    | H : lc_pskl (pskl_var_b _) |- _ => inversion H
    | H : guarded_pskl (pskl_all_syn _) |- _ => inversion H
    | H : guarded_pskl (pskl_univ_ghost _) |- _ => inversion H
    | H : guarded_pskl pskl_ghost |- _ => inversion H
    | H : nonghost_pskl pskl_ghost |- _ => inversion H
    | H : nonghost_pskl (pskl_univ_ghost _) |- _ => inversion H
    | Hf : a_flex_tvar ?T ?a,
      Hck : context [flex_bound_ck ?T ?a] |- _ =>
        rewrite (flex_tvar_flex_bound_ck _ _ Hf) in Hck;
        simpl in Hck; discriminate

    end
  | repeat match goal with
    | Hg : pskl_ghost_free ?P, Hck : context [ghost_free_ck ?P] |- _ =>
        rewrite (ghost_free_ck_complete _ Hg) in Hck
    | Hg : guarded_pskl ?P, Hck : context [guarded_shape_ck ?P] |- _ =>
        rewrite (guarded_shape_ck_complete _ Hg) in Hck
    end; discriminate].

#[local] Hint Extern 2 (_ [<=] _) =>
  match goal with Hcov : _ [<=] _ |- ?G =>
    tryif has_evar G then fail else (clear - Hcov; simpl in *; fsetdec)
  end : solver_complete.

Local Ltac finish_eq_call :=
  match goal with
  | D : e_solve_eq ?S ?T ?p ?q _ _ _
    |- context [e_solve_eq_impl ?S ?T ?p ?q ?hp ?hq ?h] =>
      let Hne := fresh "Hne" in
      let r := fresh "r" in let Hr := fresh "Hr" in
      assert (Hne : e_solve_eq_impl S T p q hp hq h <> None)
        by (eauto 8 with solver_complete);
      destruct (e_solve_eq_impl S T p q hp hq h) as [[r Hr]|];
      [cbv beta iota; discriminate | exact (False_ind _ (Hne eq_refl))]
  end.

Lemma e_solve_eq_impl_complete : forall S0 Θ P Q HP HQ H S1 Ξ Y,
  e_solve_eq S0 Θ P Q S1 Ξ Y ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  e_solve_eq_impl S0 Θ P Q HP HQ H <> None.
Proof.
  intros S0 Θ P Q HP HQ H. generalize H. revert HP HQ.
  induction H as [S0 Θ P Q p1 p2 IHhead p2t IHtail
    p3 q3 p4 q4 p5 q5 p6 q6 p7 q7 p8 q8].
  intros HP HQ H S1 Ξ Y Hd Hcov.
  destruct P as [ | n | α | P1 P2 | P1 | | P1 ];
    destruct Q as [ | n' | β | Q1 Q2 | Q1 | | Q1 ];
    simp e_solve_eq_impl; solver_tests;
    try discriminate; inversion Hd; subst; try solver_absurd.
  all: try solve [
    match goal with
    | |- context [e_guess_mono_impl ?s ?p ?hp] =>
        destruct (e_guess_mono_impl s p hp); discriminate
    end].
  all: try solve [finish_eq_call].
  { (* Align the recursive tail with the head result chosen by the runner. *)
    match goal with
    | D1 : e_solve_eq S0 Θ P1 Q1 ?Sm ?X ?Y1,
      D2 : e_solve_eq ?Sm (?X ++ Θ) P2 Q2 _ _ _ |- _ =>
        rename D1 into Hhead; rename D2 into Htail
    end.
    assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P1
        ∪ ftvar_in_pskl Q1 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    match goal with
    | |- context [e_solve_eq_impl S0 Θ P1 Q1 ?hp ?hq ?h] =>
        assert (Hne : e_solve_eq_impl S0 Θ P1 Q1 hp hq h <> None)
          by (eauto 8);
        destruct (e_solve_eq_impl S0 Θ P1 Q1 hp hq h) as [[r Hr]|];
        [cbv beta iota; clear Hne | exact (False_ind _ (Hne eq_refl))]
    end.
    unfold solve_eq_spec in Hr.
    destruct (e_solve_eq_rel Hhead Hr Hcov1) as (ps & Hav & HS & HX & HY).
    assert (HΘ : swaps_aenv ps Θ = Θ).
    { apply swaps_aenv_fresh_id. intros a b Hin.
      destruct (Hav a b Hin) as [Ha Hb]. split; clear - Ha Hb Hcov; fsetdec. }
    assert (HP2 : swaps_pskl ps P2 = P2).
    { apply swaps_pskl_fresh_id. intros a b Hin.
      destruct (Hav a b Hin) as [Ha Hb]. split;
        clear - Ha Hb Hcov; simpl in *; fsetdec. }
    assert (HQ2 : swaps_pskl ps Q2 = Q2).
    { apply swaps_pskl_fresh_id. intros a b Hin.
      destruct (Hav a b Hin) as [Ha Hb]. split;
        clear - Ha Hb Hcov; simpl in *; fsetdec. }
    symmetry in HS.
    destruct (e_solve_eq_swaps ps Htail HS) as (Sf & _ & Htail').
    rewrite swaps_aenv_app_dist, HX, HΘ, HP2, HQ2 in Htail'.
    pose proof (e_solve_eq_supply_grows Hr) as Hgrow.
    pose proof (e_solve_eq_block_ftvar Hr) as Hblock.
    pose proof (e_solve_eq_block_in_supply Hr) as Hdom.
    assert (Hcov2 : ftvar_in_aenv (sv_block r ++ Θ)
        ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2 [<=] sv_supply r).
    { rewrite ftvar_in_aenv_app. clear - Hcov Hgrow Hblock Hdom.
      simpl in *; fsetdec. }
    finish_eq_call. }
  (* The three binder rules share the same fresh-opener transport. *)
  all: pose proof (supply_fresh_notin S0) as Hfresh.
  all: lazymatch goal with
    | Hb : ?b `notin` ?S,
      D : e_solve_eq (add ?b ?S) ((?b ~ abind_tvar) ++ ?T) _ _ _ _ _ |- _ =>
        assert (HS : add (supply_fresh S) S
            [=] swap_atoms b (supply_fresh S) (add b S))
          by (rewrite swap_atoms_add, swap_atom_l, swap_atoms_notin;
              [reflexivity | exact Hb | exact Hfresh]);
        destruct (e_solve_eq_swap D HS) as (Sf & _ & Hbody);
        rewrite swap_aenv_app, swap_aenv_one_tvar in Hbody;
        rewrite (swap_aenv_fresh_id b (supply_fresh S) T) in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec);
        rewrite !swap_pskl_open_var, !swap_atom_l in Hbody;
        repeat rewrite swap_pskl_fresh_id in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec)
    end.
  all: pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
    (pskl_var_f (supply_fresh S0))) as Hup1.
  all: pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q1
    (pskl_var_f (supply_fresh S0))) as Hup2.
  all: match goal with
    | |- context [e_solve_eq_impl ?S ?T ?p ?q _ _ _] =>
        assert (Hcov' : ftvar_in_aenv T ∪ ftvar_in_pskl p
            ∪ ftvar_in_pskl q [<=] S)
          by (clear - Hcov Hup1 Hup2; simpl in *; fsetdec)
    end.
  all: finish_eq_call.
Qed.

#[local] Hint Resolve e_solve_eq_impl_complete : solver_complete.

Local Ltac finish_sub_call :=
  match goal with
  | D : e_solve_sub ?S ?T ?m ?p ?q _ _ _
    |- context [e_solve_sub_impl ?S ?T ?m ?p ?q ?hp ?hq ?h] =>
      let Hne := fresh "Hne" in
      let r := fresh "r" in let Hr := fresh "Hr" in
      assert (Hne : e_solve_sub_impl S T m p q hp hq h <> None)
        by (eauto 8 with solver_complete);
      destruct (e_solve_sub_impl S T m p q hp hq h) as [[r Hr]|];
      [cbv beta iota; discriminate | exact (False_ind _ (Hne eq_refl))]
  end.

Lemma e_solve_sub_impl_complete : forall S0 Θ m P Q HP HQ H S1 Ξ Y,
  e_solve_sub S0 Θ m P Q S1 Ξ Y ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  e_solve_sub_impl S0 Θ m P Q HP HQ H <> None.
Proof.
  intros S0 Θ m P Q HP HQ H. generalize H. revert HP HQ.
  induction H as [S0 Θ m P Q p1 q1 p2 q2 p3 p4 q4 p5 p5t q5 p6 p6t q6].
  intros HP HQ H S1 Ξ Y Hd Hcov.
  destruct P as [ | n | α | P1 P2 | P1 | | P1 ];
    destruct Q as [ | n' | β | Q1 Q2 | Q1 | | Q1 ];
    destruct m as [ | | m ];
    simp e_solve_sub_impl; solver_tests;
    try discriminate; inversion Hd; subst; try solver_absurd.
  all: try solve [finish_eq_call | finish_sub_call].
  all: try solve [
    match goal with
    | D1 : e_solve_eq ?S ?T ?p ?q ?Sm ?X ?Y1,
      D2 : e_solve_sub ?Sm (?X ++ ?T) ?m ?p2 ?q2 _ _ _
      |- context [e_solve_eq_impl ?S ?T ?p ?q ?hp ?hq ?h] =>
        assert (Hcov1 : ftvar_in_aenv T ∪ ftvar_in_pskl p
            ∪ ftvar_in_pskl q [<=] S)
          by (clear - Hcov; simpl in *; fsetdec);
        assert (Hne : e_solve_eq_impl S T p q hp hq h <> None)
          by (eapply e_solve_eq_impl_complete; eassumption);
        destruct (e_solve_eq_impl S T p q hp hq h) as [[r Hr]|];
        [cbv beta iota; clear Hne | exact (False_ind _ (Hne eq_refl))];
        unfold solve_eq_spec in Hr;
        destruct (e_solve_eq_rel D1 Hr Hcov1) as (ps & Hav & HS & HX & HY);
        assert (HΘ : swaps_aenv ps T = T)
          by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav);
              clear - Hcov; fsetdec);
        assert (HP2 : swaps_pskl ps p2 = p2)
          by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav);
              clear - Hcov; simpl in *; fsetdec);
        assert (HQ2 : swaps_pskl ps q2 = q2)
          by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav);
              clear - Hcov; simpl in *; fsetdec);
        symmetry in HS;
        destruct (e_solve_sub_swaps ps D2 HS) as (Sf & _ & Htail');
        rewrite swaps_aenv_app_dist, HX, HΘ, HP2, HQ2 in Htail';
        pose proof (e_solve_eq_supply_grows Hr) as Hgrow;
        pose proof (e_solve_eq_block_ftvar Hr) as Hblock;
        pose proof (e_solve_eq_block_in_supply Hr) as Hdom;
        assert (Hcov2 : ftvar_in_aenv (sv_block r ++ T)
            ∪ ftvar_in_pskl p2 ∪ ftvar_in_pskl q2 [<=] sv_supply r)
          by (rewrite ftvar_in_aenv_app; clear - Hcov Hgrow Hblock Hdom;
              simpl in *; fsetdec);
        finish_sub_call
    end].
  (* ForallL and ForallR differ only in which input is opened. *)
  all: pose proof (supply_fresh_notin S0) as Hfresh.
  all: lazymatch goal with
    | Hb : ?b `notin` ?S,
      D : e_solve_sub (add ?b ?S) ((?b ~ abind_tvar) ++ ?T) _ _ _ _ _ _ |- _ =>
        assert (HS : add (supply_fresh S) S
            [=] swap_atoms b (supply_fresh S) (add b S))
          by (rewrite swap_atoms_add, swap_atom_l, swap_atoms_notin;
              [reflexivity | exact Hb | exact Hfresh]);
        destruct (e_solve_sub_swap D HS) as (Sf & _ & Hbody);
        rewrite swap_aenv_app, swap_aenv_one_tvar in Hbody;
        rewrite (swap_aenv_fresh_id b (supply_fresh S) T) in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec);
        rewrite !swap_pskl_open_var, !swap_atom_l in Hbody;
        repeat rewrite swap_pskl_fresh_id in Hbody
          by (clear - Hb Hfresh Hcov; simpl in *; fsetdec)
    end.
  all: lazymatch goal with
    | |- context [e_solve_sub_impl ?S ?T _ ?p ?q _ _ _] =>
        assert (Hcov' : ftvar_in_aenv T ∪ ftvar_in_pskl p
            ∪ ftvar_in_pskl q [<=] S) by (
              clear - Hcov;
              match goal with
              | |- context [open_pskl_wrt_pskl ?B ?V] =>
                  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B V) as Hopen
              end;
              simpl in *; fsetdec)
    end.
  all: finish_sub_call.
Qed.
