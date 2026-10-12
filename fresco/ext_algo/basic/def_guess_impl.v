Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_uip.
Require Import src.fresco.ext_algo.basic.def_guess.

Record guess_result : Type := mk_guess_result {
  gr_supply : supply;
  gr_block  : aenv;
  gr_type   : ptyp
}.

Definition guess_spec (S0 : supply) (P : pskl) (r : guess_result) : Prop :=
  e_guess_mono S0 P (gr_supply r) (gr_block r) (gr_type r).

Notation guess_res S0 P := (sig (guess_spec S0 P)).

Inductive e_guess_mono_order : supply -> pskl -> Prop :=
| ego_ghost : forall S,
    e_guess_mono_order S pskl_ghost
| ego_univ_ghost : forall S P,
    e_guess_mono_order S P ->
    e_guess_mono_order S (pskl_univ_ghost P)
| ego_var : forall S α,
    e_guess_mono_order S (pskl_var_f α)
| ego_unit : forall S,
    e_guess_mono_order S pskl_unit
| ego_arrow : forall S P Q,
    e_guess_mono_order S P ->
    (forall S1 Ξ1 A, e_guess_mono S P S1 Ξ1 A -> e_guess_mono_order S1 Q) ->
    e_guess_mono_order S (pskl_arrow P Q)
| ego_forall : forall S P,
    e_guess_mono_order (add (supply_fresh S) S)
      (open_pskl_wrt_pskl P (pskl_var_f (supply_fresh S))) ->
    e_guess_mono_order S (pskl_all_syn P).

Lemma e_guess_mono_order_var_b_absurd : forall S n,
  e_guess_mono_order S (pskl_var_b n) -> False.
Proof. intros * H; inversion H. Qed.

#[local] Ltac guess_impl_tac :=
  intros;
  try (match goal with H : e_guess_mono_order _ _ |- _ =>
         inversion H; subst end);
  unfold guess_spec in *; simpl in *;
  eauto using e_guess_mono, supply_fresh_notin.

#[tactic="guess_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_guess_mono_impl (S0 : supply) (P : pskl)
    (H : e_guess_mono_order S0 P) : guess_res S0 P
  by struct H :=
| S0, pskl_ghost, H =>
    exist _ (mk_guess_result (add (supply_fresh S0) S0)
               ((supply_fresh S0 ~ abind_flex_mono) ++ nil)
               (ptyp_var_f (supply_fresh S0))) _
| S0, pskl_var_f α, H => exist _ (mk_guess_result S0 nil (ptyp_var_f α)) _
| S0, pskl_unit, H => exist _ (mk_guess_result S0 nil ptyp_unit) _
| S0, pskl_univ_ghost P, H =>
    let (r, Hr) := e_guess_mono_impl S0 P _ in
    exist _ r _
| S0, pskl_arrow P Q, H =>
    let (r1, H1) := e_guess_mono_impl S0 P _ in
    let (r2, H2) := e_guess_mono_impl (gr_supply r1) Q _ in
    exist _ (mk_guess_result (gr_supply r2)
               (gr_block r1 ++ gr_block r2)
               (ptyp_arrow (gr_type r1) (gr_type r2))) _
| S0, pskl_all_syn P, H =>
    let (r, Hr) := e_guess_mono_impl (add (supply_fresh S0) S0)
                     (open_pskl_wrt_pskl P (pskl_var_f (supply_fresh S0))) _ in
    exist _ (mk_guess_result (gr_supply r) (gr_block r)
               (ptyp_all (close_ptyp_wrt_ptyp (supply_fresh S0) (gr_type r)))) _
| S0, pskl_var_b n, H =>
    False_rect _ (e_guess_mono_order_var_b_absurd S0 n H).

Lemma e_guess_mono_order_total : forall P,
  lc_pskl P ->
  forall S0, e_guess_mono_order S0 P.
Proof.
  intros P Hlc;
    induction Hlc as [ | α | P1 P2 Hlc1 IH1 Hlc2 IH2 | P1 Hlc IH
                     | | P1 Hlc IH ];
    intros S0.
  - apply ego_unit.
  - apply ego_var.
  - apply ego_arrow; [ apply IH1 | intros; apply IH2 ].
  - apply ego_forall. apply IH.
  - apply ego_ghost.
  - apply ego_univ_ghost. apply IH.
Qed.

Definition e_guess_mono_run (S0 : supply) (P : pskl) (H : lc_pskl P)
  : guess_result :=
  proj1_sig (e_guess_mono_impl S0 P (e_guess_mono_order_total P H S0)).

Lemma e_guess_mono_run_sound : forall S0 P (H : lc_pskl P),
  e_guess_mono S0 P
    (gr_supply (e_guess_mono_run S0 P H))
    (gr_block  (e_guess_mono_run S0 P H))
    (gr_type   (e_guess_mono_run S0 P H)).
Proof.
  intros S0 P H. unfold e_guess_mono_run.
  exact (proj2_sig (e_guess_mono_impl S0 P (e_guess_mono_order_total P H S0))).
Qed.

Record guess_sk_result : Type := mk_guess_sk_result {
  gs_supply : supply;
  gs_block  : aenv;
  gs_skel   : pskl
}.

Definition e_guess_run (S0 : supply) (NM : a_sub_mode) (Q : pskl)
    (H : lc_pskl Q) : guess_sk_result :=
  match NM with
  | a_sub_mode_sk => mk_guess_sk_result S0 nil Q
  | a_sub_mode_ty =>
      let r := e_guess_mono_run S0 Q H in
      mk_guess_sk_result (gr_supply r) (gr_block r) (ptyp_to_pskl (gr_type r))
  end.

Lemma e_guess_run_sound : forall S0 NM Q (H : lc_pskl Q),
  e_guess S0 NM Q
    (gs_supply (e_guess_run S0 NM Q H))
    (gs_block  (e_guess_run S0 NM Q H))
    (gs_skel   (e_guess_run S0 NM Q H)).
Proof.
  intros S0 NM Q H; destruct NM; simpl.
  - apply e_guess__ty. apply e_guess_mono_run_sound.
  - apply e_guess__sk.
Qed.
