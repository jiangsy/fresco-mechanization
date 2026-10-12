Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.prop_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.prop_solve.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.def_look_impl.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.def_extract_impl.
Require Import src.fresco.ext_algo.subtyping.prop_look_complete.
Require Import src.fresco.ext_algo.subtyping.prop_solve_complete.
Require Import src.fresco.ext_algo.subtyping.prop_extract_det.
Require Import src.fresco.ext_algo.subtyping.def_solve_impl.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

Lemma e_solve_cstr_impl_complete : forall S0 Θ C P HP HC H S1 Ξ Y,
  e_solve_cstr S0 Θ C P S1 Ξ Y ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_a_cstrs C [<=] S0 ->
  e_solve_cstr_impl S0 Θ C P HP HC H <> None.
Proof.
  intros S0 Θ C. revert S0 Θ.
  induction C as [|c C IH]; intros S0 Θ P HP HC H S1 Ξ Y Hd Hcov.
  - simp e_solve_cstr_impl. discriminate.
  - destruct c as [m Q | Q].
    + destruct (e_solve_cstr_inv_sub Hd) as [-> Hsub].
      simp e_solve_cstr_impl.
      match goal with
      | |- context [e_solve_sub_impl ?S ?T ?M ?p ?q ?hp ?hq ?h] =>
          pose proof (e_solve_sub_impl_complete hp hq h Hsub
            ltac:(clear - Hcov; simpl in *; fsetdec)) as Hne;
          destruct (e_solve_sub_impl S T M p q hp hq h) as [[r Hr]|];
          [cbv beta iota; discriminate | exact (False_ind _ (Hne eq_refl))]
      end.
    + destruct (e_solve_cstr_inv_eq Hd) as (Sm & Ξ1 & Ξ2 & Y0 & _ & Heq & Htail).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      simp e_solve_cstr_impl.
      match goal with
      | |- context [e_solve_eq_impl ?S ?T ?p ?q ?hp ?hq ?h] =>
          pose proof (e_solve_eq_impl_complete hp hq h Heq Hcov1) as Hne;
          destruct (e_solve_eq_impl S T p q hp hq h) as [[r Hr]|];
          [cbv beta iota; clear Hne | exact (False_ind _ (Hne eq_refl))]
      end.
      unfold solve_eq_spec in Hr.
      destruct (e_solve_eq_rel Heq Hr Hcov1) as (ps & Hav & HS & HX & HY).
      pose proof HS as HSr. symmetry in HSr.
      destruct (e_solve_cstr_swaps ps Htail HSr)
        as (Sf & _ & Htail').
      rewrite swaps_aenv_app_dist, HX, HY, (swaps_aenv_fresh_id ps Θ),
        (swaps_cstrs_fresh_id ps C) in Htail'
        by (apply (swaps_dodge_sub Hav); clear - Hcov; simpl in *; fsetdec).
      pose proof (e_solve_eq_supply_grows Hr) as Hgr.
      pose proof (e_solve_eq_block_in_supply Hr) as Hdom.
      pose proof (e_solve_eq_block_ftvar Hr) as Hft.
      pose proof (e_solve_eq_out_ftvar Hr ltac:(clear - Hcov1; fsetdec)) as Hout.
      assert (Hcov2 : ftvar_in_aenv (sv_block r ++ Θ)
          ∪ ftvar_in_pskl (sv_out r) ∪ ftvar_in_a_cstrs C [<=] sv_supply r).
      { rewrite ftvar_in_aenv_app. clear - Hgr Hdom Hft Hout Hcov.
        simpl in *; fsetdec. }
      match goal with
      | |- context [e_solve_cstr_impl ?S ?T ?c ?p ?hp ?hc ?h] =>
          pose proof (IH S T p hp hc h _ _ _ Htail' Hcov2) as Hne;
          destruct (e_solve_cstr_impl S T c p hp hc h) as [[r2 Hr2]|];
          [cbv beta iota; discriminate | exact (False_ind _ (Hne eq_refl))]
      end.
Qed.

Lemma e_extract_impl_complete : forall S0 Θ0 NM α m P P'
    (HP : lc_pskl P) (HP' : lc_pskl P')
    (H : e_extract_order S0 Θ0 NM α m P P') S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  e_extract_impl S0 Θ0 NM α m P P' HP HP' H <> None.
Proof.
  intros * Hd Hcov.
  destruct (e_extract_inv Hd)
    as (Sa1 & Sa2 & Ξl & Ξs & Ξg & C & Qs & _ & Hlook & Hfold & _).
  simp e_extract_impl.
  match goal with
  | |- context [ e_looksub_impl ?S ?T ?a ?mm ?p ?q ?hp ?hq ?h ] =>
      let Hne := fresh "Hne" in
      assert (Hne : e_looksub_impl S T a mm p q hp hq h <> None)
        by (exact (e_looksub_impl_complete hp hq h Hlook Hcov));
      destruct (e_looksub_impl S T a mm p q hp hq h) as [[r Hr] | ];
      [ cbv beta iota | exact (False_ind _ (Hne eq_refl)) ]
  end.
  unfold looksub_spec in Hr.
  destruct (e_looksub_rel Hlook Hr Hcov) as (ps & Hav & HS & HX & HC).
  pose proof HS as HSr. symmetry in HSr.
  destruct (e_solve_cstr_swaps ps Hfold HSr) as (Sf & _ & Hfold').
  rewrite swaps_aenv_app_dist, HX, HC, swaps_pskl_ghost,
    (swaps_aenv_fresh_id ps Θ0) in Hfold'
    by (apply (swaps_dodge_sub Hav); clear - Hcov; fsetdec).
  pose proof (e_looksub_supply_grows Hr) as Hgr.
  pose proof (e_looksub_generated_in_supply Hr) as Hdom.
  pose proof (e_looksub_block_ftvar Hr) as Hft.
  pose proof (e_looksub_cstr_ftvar Hr ltac:(clear - Hcov; fsetdec)) as Hcs.
  assert (Hcovf : ftvar_in_aenv (lk_block r ++ Θ0)
            ∪ ftvar_in_pskl pskl_ghost ∪ ftvar_in_a_cstrs (lk_cstrs r)
            [<=] lk_supply r).
  { rewrite ftvar_in_aenv_app. simpl. clear - Hgr Hdom Hft Hcs Hcov. fsetdec. }
  match goal with
  | |- context [ e_solve_cstr_impl ?S ?T ?c ?p ?hp ?hc ?h ] =>
      let Hne := fresh "Hne" in
      assert (Hne : e_solve_cstr_impl S T c p hp hc h <> None)
        by (exact (e_solve_cstr_impl_complete hp hc h Hfold' Hcovf));
      destruct (e_solve_cstr_impl S T c p hp hc h) as [[r2 Hr2] | ];
      [ cbv beta iota | exact (False_ind _ (Hne eq_refl)) ]
  end.
  discriminate.
Qed.
