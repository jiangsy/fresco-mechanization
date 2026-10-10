(** Completeness of the extraction pipeline.  The constraint fold uses
    threaded solver determinism and list induction; collection determinism
    then moves the extraction derivation onto the runner's collection. *)

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

(* Expose supply atoms as rigid bindings when invoking the existing
   solver completeness lemmas.  This preserves all flexibility tests. *)
Lemma e_solve_eq_impl_complete_threaded : forall S0 Θ P Q HP HQ H S1 Ξ Y,
  e_solve_eq S0 Θ P Q S1 Ξ Y ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  e_solve_eq_impl S0 Θ P Q HP HQ H <> None.
Proof.
  intros * Hd Hcov.
  assert (Hrig : forall x bd, binds x bd (rigids S0) -> bd = abind_tvar)
    by (intros; eapply rigids_binds_tvar; eassumption).
  assert (Hflex : forall x, a_flex_tvar (rigids S0 ++ Θ) x <-> a_flex_tvar Θ x)
    by (intros; apply a_flex_tvar_rigid_prefix_iff; exact Hrig).
  assert (Hcovr : ftvar_in_aenv (rigids S0 ++ Θ)
      ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0)
    by (rewrite ftvar_in_aenv_app, rigids_ftvar; clear - Hcov; fsetdec).
  pose proof ((proj2 e_solve_sub_eq_ctx_equiv) _ _ _ _ _ _ _ Hd
      (rigids S0 ++ Θ) ltac:(intros x; symmetry; apply Hflex)) as Hr.
  eapply e_solve_eq_impl_complete; [ exact (e_solve_eq_sound Hr Hcovr)
    | intros x _; apply Hflex
    | rewrite ftvar_in_aenv_app, rigids_ftvar; clear - Hcov; fsetdec
    | exact Hcov ].
Qed.

Lemma e_solve_sub_impl_complete_threaded : forall S0 Θ m P Q HP HQ H S1 Ξ Y,
  e_solve_sub S0 Θ m P Q S1 Ξ Y ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  e_solve_sub_impl S0 Θ m P Q HP HQ H <> None.
Proof.
  intros * Hd Hcov.
  assert (Hrig : forall x bd, binds x bd (rigids S0) -> bd = abind_tvar)
    by (intros; eapply rigids_binds_tvar; eassumption).
  assert (Hflex : forall x, a_flex_tvar (rigids S0 ++ Θ) x <-> a_flex_tvar Θ x)
    by (intros; apply a_flex_tvar_rigid_prefix_iff; exact Hrig).
  assert (Hcovr : ftvar_in_aenv (rigids S0 ++ Θ)
      ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0)
    by (rewrite ftvar_in_aenv_app, rigids_ftvar; clear - Hcov; fsetdec).
  pose proof ((proj1 e_solve_sub_eq_ctx_equiv) _ _ _ _ _ _ _ _ Hd
      (rigids S0 ++ Θ) ltac:(intros x; symmetry; apply Hflex)) as Hr.
  eapply e_solve_sub_impl_complete; [ exact (e_solve_sub_sound Hr Hcovr)
    | intros x _; apply Hflex
    | rewrite ftvar_in_aenv_app, rigids_ftvar; clear - Hcov; fsetdec
    | exact Hcov ].
Qed.

(* Align the given tail with the runner by the head solver's swaps. *)
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
          pose proof (e_solve_sub_impl_complete_threaded hp hq h Hsub
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
          pose proof (e_solve_eq_impl_complete_threaded hp hq h Heq Hcov1) as Hne;
          destruct (e_solve_eq_impl S T p q hp hq h) as [[r Hr]|];
          [cbv beta iota; clear Hne | exact (False_ind _ (Hne eq_refl))]
      end.
      unfold solve_eq_spec in Hr.
      destruct (e_solve_eq_rel Heq Hr Hcov1) as (ps & Hav & HS & HX & HY).
      assert (HΘ : swaps_aenv ps Θ = Θ).
      { apply swaps_aenv_fresh_id. intros a b Hin.
        destruct (Hav a b Hin) as [Ha Hb]. split; clear - Ha Hb Hcov; fsetdec. }
      assert (HCfix : swaps_cstrs ps C = C).
      { apply swaps_cstrs_fresh_id. intros a b Hin.
        destruct (Hav a b Hin) as [Ha Hb]. split; clear - Ha Hb Hcov;
          simpl in *; fsetdec. }
      destruct (e_solve_cstr_swaps ps Htail
        (S0' := sv_supply r) ltac:(symmetry; exact HS)) as (Sf & _ & Htail').
      rewrite swaps_aenv_app_dist, HX, HΘ, HCfix, HY in Htail'.
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

