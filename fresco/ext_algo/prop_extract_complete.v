(** Completeness of the extraction runner.  Collection determinism moves
    the given fold onto the runner's collection.  Solver completeness then
    supplies the second stage; guessing is total. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.prop_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.prop_solve.
Require Import src.fresco.ext_algo.prop_solve_det.
Require Import src.fresco.ext_algo.def_order.
Require Import src.fresco.ext_algo.prop_termination.
Require Import src.fresco.ext_algo.def_look_impl.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.def_extract_impl.
Require Import src.fresco.ext_algo.prop_run_complete.
Require Import src.fresco.ext_algo.prop_extract_det.
Require Import src.fresco.ext_algo.def_solve_impl.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

Definition rigids (S : atoms) : aenv :=
  List.map (fun x => (x, abind_tvar)) (AtomSetImpl.elements S).

Lemma rigids_binds_tvar : forall S x bd,
  binds x bd (rigids S) -> bd = abind_tvar.
Proof.
  intros S. unfold rigids.
  induction (AtomSetImpl.elements S) as [ | a l IH ]; intros x bd Hb.
  - inversion Hb.
  - unfold binds in Hb. simpl in Hb.
    destruct Hb as [ E | Hb ]; [ inversion E; reflexivity | ].
    apply (IH x). exact Hb.
Qed.

Lemma rigids_dom : forall S, dom (rigids S) [=] S.
Proof.
  intros S. unfold rigids.
  intros x. split.
  - intros Hx.
    assert (Hin : In x (AtomSetImpl.elements S)).
    { induction (AtomSetImpl.elements S) as [ | a l IH ]; simpl in *.
      - exfalso. clear - Hx. fsetdec.
      - destruct (x == a) as [ -> | Hne ]; [ auto | ].
        right. apply IH. clear - Hx Hne. fsetdec. }
    apply AtomSetImpl.elements_2.
    apply CoqListFacts.InA_iff_In. exact Hin.
  - intros Hx.
    apply AtomSetImpl.elements_1 in Hx.
    apply CoqListFacts.InA_iff_In in Hx.
    induction (AtomSetImpl.elements S) as [ | a l IH ]; simpl in *.
    + inversion Hx.
    + destruct Hx as [ -> | Hx ]; [ fsetdec | ].
      pose proof (IH Hx). fsetdec.
Qed.

Lemma map_tvar_ftvar_dom : forall (l : list atom),
  ftvar_in_aenv (List.map (fun x => (x, abind_tvar)) l)
  [=] dom (List.map (fun x => (x, abind_tvar)) l).
Proof.
  induction l as [ | a l IH ]; simpl.
  - clear. fsetdec.
  - rewrite IH. clear. fsetdec.
Qed.

Lemma rigids_ftvar : forall S, ftvar_in_aenv (rigids S) [=] S.
Proof.
  intros S. unfold rigids.
  rewrite map_tvar_ftvar_dom.
  exact (rigids_dom S).
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
  pose proof ((proj1 e_looksub_lookeq_sound) _ _ _ _ _ _ _ _ _ Hlook
                ltac:(clear - Hcov; fsetdec)) as Hlookraw.
  match goal with
  | |- context [ e_looksub_impl ?S ?T ?a ?mm ?p ?q ?hp ?hq ?h ] =>
      let Hne := fresh "Hne" in
      assert (Hne : e_looksub_impl S T a mm p q hp hq h <> None)
        by (exact (e_looksub_impl_complete hp hq h Hlookraw
                     ltac:(clear - Hcov; fsetdec)));
      destruct (e_looksub_impl S T a mm p q hp hq h) as [[r Hr] | ];
      [ cbv beta iota | exact (False_ind _ (Hne eq_refl)) ]
  end.
  unfold looksub_spec in Hr.
  destruct (e_looksub_rel Hlook Hr Hcov) as (ps & Hav & HS & HX & HC).
  assert (HΘ : swaps_aenv ps Θ0 = Θ0).
  { apply swaps_aenv_fresh_id. intros a b Hin.
    destruct (Hav a b Hin) as [Ha Hb]. split; clear - Ha Hb Hcov; fsetdec. }
  destruct (e_solve_cstr_swaps ps Hfold
              (S0' := lk_supply r) ltac:(symmetry; exact HS)) as (Sf & _ & Hfold').
  rewrite swaps_aenv_app_dist, HX, HΘ, HC, swaps_pskl_ghost in Hfold'.
  pose proof (e_looksub_supply_grows Hr) as Hgr.
  pose proof (e_looksub_generated_in_supply Hr) as Hdom.
  pose proof (e_looksub_block_ftvar Hr) as Hft.
  pose proof (e_looksub_cstr_ftvar Hr ltac:(clear - Hcov; fsetdec)) as Hcs.
  assert (Hcovf : ftvar_in_aenv (lk_block r ++ Θ0)
            ∪ ftvar_in_pskl pskl_ghost ∪ ftvar_in_a_cstrs (lk_cstrs r)
            [<=] lk_supply r).
  { rewrite ftvar_in_aenv_app. simpl. clear - Hgr Hdom Hft Hcs Hcov. fsetdec. }
  (* Leaked collection openers belong to the supply, so make them visible
     to the solver transport without changing any flexibility tests. *)
  set (Θf := rigids (lk_supply r) ++ lk_block r ++ Θ0).
  assert (Hrig : forall x bd, binds x bd (rigids (lk_supply r)) -> bd = abind_tvar)
    by (intros; eapply rigids_binds_tvar; eassumption).
  assert (Hcovr : ftvar_in_aenv Θf ∪ ftvar_in_a_cstrs (lk_cstrs r)
            ∪ ftvar_in_pskl pskl_ghost [<=] lk_supply r).
  { unfold Θf. rewrite ftvar_in_aenv_app, rigids_ftvar.
    clear - Hcovf. fsetdec. }
  assert (Hfolda : {{ Θf ⊩ (lk_cstrs r) ⨾ pskl_ghost
                     ⤳ (swaps_aenv ps Ξs) ⨾ (swaps_pskl ps Qs) }}a).
  { eapply e_solve_cstr_sound; [ | exact Hcovr ].
    apply e_solve_cstr_weaken_rigid; [ exact Hfold' | exact Hrig ]. }
  pose proof (e_solve_cstr_block Hfold') as (_ & _ & Hu & _).
  assert (Hagr : flex_agree
      (ftvar_in_pskl pskl_ghost ∪ ftvar_in_a_cstrs (lk_cstrs r))
      Θf (lk_block r ++ Θ0)).
  { intros x _. unfold Θf. apply a_flex_tvar_rigid_prefix_iff. exact Hrig. }
  assert (Hscp : ftvar_in_pskl pskl_ghost ∪ ftvar_in_a_cstrs (lk_cstrs r)
            [<=] ftvar_in_aenv Θf).
  { unfold Θf. rewrite ftvar_in_aenv_app, rigids_ftvar.
    clear - Hcovf. fsetdec. }
  match goal with
  | |- context [ e_solve_cstr_impl ?S ?T ?c ?p ?hp ?hc ?h ] =>
      let Hne := fresh "Hne" in
      assert (Hne : e_solve_cstr_impl S T c p hp hc h <> None)
        by (exact (e_solve_cstr_impl_complete hp hc h Hfolda Hu Hagr Hscp Hcovf));
      destruct (e_solve_cstr_impl S T c p hp hc h) as [[r2 Hr2] | ];
      [ cbv beta iota | exact (False_ind _ (Hne eq_refl)) ]
  end.
  discriminate.
Qed.

Lemma e_extract_run_complete : forall S0 Θ0 NM α m P P' HP HP' S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  e_extract_run S0 Θ0 NM α m P P' HP HP' <> None.
Proof.
  intros * Hd Hcov. unfold e_extract_run.
  pose proof (e_extract_impl_complete HP HP'
    (@e_extract_order_total S0 Θ0 NM α m P P' HP HP') Hd Hcov) as Hne.
  revert Hne.
  destruct (e_extract_impl S0 Θ0 NM α m P P' HP HP'
    (@e_extract_order_total S0 Θ0 NM α m P P' HP HP')) as [[r Hr] | ];
    intros Hne; [ discriminate | exact (False_ind _ (Hne eq_refl)) ].
Qed.

