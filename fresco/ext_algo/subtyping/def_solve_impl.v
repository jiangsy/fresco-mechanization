Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_uip.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.basic.prop_termination.

Set Equations With UIP.

Open Scope fresco_e_scope.

Record solve_result : Type := mk_solve_result {
  sv_supply : supply;
  sv_block  : aenv;
  sv_out    : pskl
}.

Definition solve_eq_spec (S0 : supply) (Θ : aenv) (P Q : pskl)
    (r : solve_result) : Prop :=
  {{ S0 ↝ (sv_supply r) ⊨ Θ ⊢ₑ P ∼ Q ⤳ (sv_block r) ⨾ (sv_out r) }}e.

Definition solve_sub_spec (S0 : supply) (Θ : aenv) (m : mode) (P Q : pskl)
    (r : solve_result) : Prop :=
  {{ S0 ↝ (sv_supply r) ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ (sv_block r) ⨾ (sv_out r) }}e.

Definition solve_cstr_spec (S0 : supply) (Θ : aenv) (C : a_cstrs) (P : pskl)
    (r : solve_result) : Prop :=
  {{ S0 ↝ (sv_supply r) ⊨ Θ ⊩ C ⨾ P ⤳ (sv_block r) ⨾ (sv_out r) }}e.

#[local] Hint Resolve supply_fresh_notin guarded_shape_ck_sound
  ghost_free_ck_sound non_flex_ck_sound nonghost_ck_sound
  flex_bound_ck_flex_tvar lc_pskl_all_syn_inv
  e_solve_eq_lc e_solve_sub_lc : solvedec.
#[local] Hint Constructors e_solve_eq e_solve_sub e_solve_cstr
  lc_pskl : solvedec.
#[local] Hint Resolve peel_l_off_unit peel_l_off_var_b peel_l_off_var
  peel_l_off_arrow peel_l_off_ghost solve_l_off_unit solve_l_off_var_b
  solve_l_off_arrow solve_l_off_ghost : solvedec.

#[local] Ltac solve_impl_tac :=
  intros;
  try match goal with
      | H : e_solve_eq_order _ _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | H : e_solve_sub_order _ _ _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | H : e_solve_cstr_order _ _ _ _ |- _ => inversion H; subst
      end;
  repeat match goal with
         | HF : Forall _ (_ :: _) |- _ => inversion HF; subst; clear HF
         end;
  unfold solve_eq_spec, solve_sub_spec, solve_cstr_spec, guess_spec,
    lc_a_cstr in *;
  repeat match goal with
         | Hb : _ && _ = true |- _ => apply andb_prop in Hb; destruct Hb
         end;
  select_shape_premises; saturate_lc; simpl in *;
  try congruence;
  eauto 6 with solvedec.

#[tactic="solve_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_solve_eq_impl (S0 : supply) (Θ : aenv) (P Q : pskl)
    (HP : lc_pskl P) (HQ : lc_pskl Q)
    (H : e_solve_eq_order S0 Θ P Q)
    : option (sig (solve_eq_spec S0 Θ P Q)) by struct H :=

| S0, Θ, pskl_var_f α, Q, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil (pskl_var_f α)) _)
| S0, Θ, pskl_ghost, Q, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil Q) _)

| S0, Θ, pskl_unit, pskl_unit, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil pskl_unit) _)
| S0, Θ, pskl_unit, pskl_ghost, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil pskl_unit) _)
| S0, Θ, pskl_unit, pskl_var_f β, HP, HQ, H =>
    match sumbool_of_bool (flex_bound_ck Θ β && nonghost_ck pskl_unit
                           && non_flex_ck Θ pskl_unit) with
    | right _ => None
    | left _ =>
        let (r, Hr) := e_guess_mono_impl S0 pskl_unit _ in
        Some (exist _ (mk_solve_result (gr_supply r) (gr_block r)
                (ptyp_to_pskl (gr_type r))) _)
    end
| S0, Θ, pskl_unit, pskl_univ_ghost Q1, HP, HQ, H =>
    match e_solve_eq_impl S0 Θ pskl_unit Q1 _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_unit, Q, HP, HQ, H => None

| S0, Θ, pskl_arrow P1 P2, pskl_arrow Q1 Q2, HP, HQ, H =>
    match e_solve_eq_impl S0 Θ P1 Q1 _ _ _ with
    | None => None
    | Some (exist _ r1 Hr1) =>
        match e_solve_eq_impl (sv_supply r1) (sv_block r1 ++ Θ) P2 Q2
                _ _ _ with
        | None => None
        | Some (exist _ r2 Hr2) =>
            Some (exist _ (mk_solve_result (sv_supply r2)
                    (sv_block r2 ++ sv_block r1)
                    (pskl_arrow (sv_out r1) (sv_out r2))) _)
        end
    end
| S0, Θ, pskl_arrow P1 P2, pskl_ghost, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil (pskl_arrow P1 P2)) _)
| S0, Θ, pskl_arrow P1 P2, pskl_var_f β, HP, HQ, H =>
    match sumbool_of_bool (flex_bound_ck Θ β
                           && nonghost_ck (pskl_arrow P1 P2)
                           && non_flex_ck Θ (pskl_arrow P1 P2)) with
    | right _ => None
    | left _ =>
        let (r, Hr) := e_guess_mono_impl S0 (pskl_arrow P1 P2) _ in
        Some (exist _ (mk_solve_result (gr_supply r) (gr_block r)
                (ptyp_to_pskl (gr_type r))) _)
    end
| S0, Θ, pskl_arrow P1 P2, pskl_univ_ghost Q1, HP, HQ, H =>
    match e_solve_eq_impl S0 Θ (pskl_arrow P1 P2) Q1 _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_arrow P1 P2, Q, HP, HQ, H => None

| S0, Θ, pskl_all_syn P1, pskl_all_syn Q1, HP, HQ, H =>
    match e_solve_eq_impl (add (supply_fresh S0) S0)
            ((supply_fresh S0 ~ abind_tvar) ++ Θ)
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
            (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))
            _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_solve_result (sv_supply r) (sv_block r)
                (pskl_all_syn
                   (close_pskl_wrt_pskl (supply_fresh S0) (sv_out r)))) _)
    end
| S0, Θ, pskl_all_syn P1, pskl_ghost, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil (pskl_all_syn P1)) _)
| S0, Θ, pskl_all_syn P1, pskl_var_f β, HP, HQ, H =>
    match sumbool_of_bool (flex_bound_ck Θ β
                           && nonghost_ck (pskl_all_syn P1)
                           && non_flex_ck Θ (pskl_all_syn P1)) with
    | right _ => None
    | left _ =>
        let (r, Hr) := e_guess_mono_impl S0 (pskl_all_syn P1) _ in
        Some (exist _ (mk_solve_result (gr_supply r) (gr_block r)
                (ptyp_to_pskl (gr_type r))) _)
    end
| S0, Θ, pskl_all_syn P1, pskl_univ_ghost Q1, HP, HQ, H =>
    match e_solve_eq_impl (add (supply_fresh S0) S0)
            ((supply_fresh S0 ~ abind_tvar) ++ Θ)
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
            (pskl_univ_ghost Q1) _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_solve_result (sv_supply r) (sv_block r)
                (pskl_all_syn
                   (close_pskl_wrt_pskl (supply_fresh S0) (sv_out r)))) _)
    end
| S0, Θ, pskl_all_syn P1, Q, HP, HQ, H => None

| S0, Θ, pskl_univ_ghost P1, pskl_univ_ghost Q1, HP, HQ, H =>
    match e_solve_eq_impl S0 Θ P1 Q1 _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_solve_result (sv_supply r) (sv_block r)
                (pskl_univ_ghost (sv_out r))) _)
    end
| S0, Θ, pskl_univ_ghost P1, pskl_ghost, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil (pskl_univ_ghost P1)) _)
| S0, Θ, pskl_univ_ghost P1, pskl_all_syn Q1, HP, HQ, H =>
    match e_solve_eq_impl (add (supply_fresh S0) S0)
            ((supply_fresh S0 ~ abind_tvar) ++ Θ)
            (pskl_univ_ghost P1)
            (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))
            _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_solve_result (sv_supply r) (sv_block r)
                (pskl_all_syn
                   (close_pskl_wrt_pskl (supply_fresh S0) (sv_out r)))) _)
    end
| S0, Θ, pskl_univ_ghost P1, pskl_unit, HP, HQ, H =>
    match e_solve_eq_impl S0 Θ P1 pskl_unit _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_univ_ghost P1, pskl_var_f β, HP, HQ, H =>
    match e_solve_eq_impl S0 Θ P1 (pskl_var_f β) _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_univ_ghost P1, pskl_arrow Q1 Q2, HP, HQ, H =>
    match e_solve_eq_impl S0 Θ P1 (pskl_arrow Q1 Q2) _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_univ_ghost P1, pskl_var_b n, HP, HQ, H => None

| S0, Θ, pskl_var_b n, pskl_ghost, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil (pskl_var_b n)) _)
| S0, Θ, pskl_var_b n, Q, HP, HQ, H => None.

#[tactic="solve_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_solve_sub_impl (S0 : supply) (Θ : aenv) (m : mode) (P Q : pskl)
    (HP : lc_pskl P) (HQ : lc_pskl Q)
    (H : e_solve_sub_order S0 Θ m P Q)
    : option (sig (solve_sub_spec S0 Θ m P Q)) by struct H :=

| S0, Θ, m, pskl_var_f α, Q, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil (pskl_var_f α)) _)
| S0, Θ, m, pskl_all_syn P1, Q, HP, HQ, H =>
    match e_solve_sub_impl (add (supply_fresh S0) S0)
            ((supply_fresh S0 ~ abind_tvar) ++ Θ) m
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
            Q _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_solve_result (sv_supply r) (sv_block r)
                (pskl_all_syn
                   (close_pskl_wrt_pskl (supply_fresh S0) (sv_out r)))) _)
    end
| S0, Θ, m, pskl_univ_ghost P1, Q, HP, HQ, H =>
    match e_solve_sub_impl S0 Θ m P1 Q _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_solve_result (sv_supply r) (sv_block r)
                (pskl_univ_ghost (sv_out r))) _)
    end
| S0, Θ, m, P, pskl_ghost, HP, HQ, H =>
    Some (exist _ (mk_solve_result S0 nil P) _)
| S0, Θ, mode_tc, P, pskl_all_syn B, HP, HQ, H =>
    match sumbool_of_bool (ghost_free_ck (pskl_all_syn B)) with
    | right _ => None
    | left _ =>
        match e_solve_sub_impl (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_tvar) ++ Θ) mode_tc P
                (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
                _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, mode_tc, pskl_ghost, Q, HP, HQ, H =>
    match sumbool_of_bool (guarded_shape_ck Q && ghost_free_ck Q) with
    | right _ => None
    | left _ => Some (exist _ (mk_solve_result S0 nil (pskl_univ_ghost Q)) _)
    end
| S0, Θ, mode_tc, P, Q, HP, HQ, H =>
    match sumbool_of_bool (guarded_shape_ck P && guarded_shape_ck Q
                           && ghost_free_ck Q) with
    | right _ => None
    | left _ =>
        match e_solve_eq_impl S0 Θ P Q _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, mode_fn m', pskl_arrow P1 P2, pskl_arrow Q1 Q2, HP, HQ, H =>

    match e_solve_eq_impl S0 Θ P1 Q1 _ _ _ with
    | None => None
    | Some (exist _ r1 Hr1) =>
        match e_solve_sub_impl (sv_supply r1) (sv_block r1 ++ Θ) m' P2 Q2
                _ _ _ with
        | None => None
        | Some (exist _ r2 Hr2) =>
            Some (exist _ (mk_solve_result (sv_supply r2)
                    (sv_block r2 ++ sv_block r1)
                    (pskl_arrow (sv_out r1) (sv_out r2))) _)
        end
    end
| S0, Θ, mode_fn m', pskl_ghost, pskl_arrow Q1 Q2, HP, HQ, H =>

    match e_solve_eq_impl S0 Θ pskl_ghost Q1 _ _ _ with
    | None => None
    | Some (exist _ r1 Hr1) =>
        match e_solve_sub_impl (sv_supply r1) (sv_block r1 ++ Θ) m'
                pskl_ghost Q2 _ _ _ with
        | None => None
        | Some (exist _ r2 Hr2) =>
            Some (exist _ (mk_solve_result (sv_supply r2)
                    (sv_block r2 ++ sv_block r1)
                    (pskl_univ_ghost
                       (pskl_arrow (sv_out r1) (sv_out r2)))) _)
        end
    end
| S0, Θ, m, P, Q, HP, HQ, H => None.

Next Obligation.
  unfold solve_sub_spec; simpl.
  apply e_solve_sub__vacuous; auto with fresco.
Qed.
Next Obligation.
  unfold solve_sub_spec; simpl.
  apply e_solve_sub__vacuous; auto with fresco.
Qed.

#[tactic="solve_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_solve_cstr_impl (S0 : supply) (Θ : aenv) (C : a_cstrs) (P : pskl)
    (HP : lc_pskl P) (HC : Forall lc_a_cstr C)
    (H : e_solve_cstr_order S0 Θ C P)
    : option (sig (solve_cstr_spec S0 Θ C P)) by struct H :=

| S0, Θ, nil, P, HP, HC, H =>
    Some (exist _ (mk_solve_result S0 nil P) _)
| S0, Θ, (a_cstr_sub m Q0 :: nil), P, HP, HC, H =>
    match e_solve_sub_impl S0 Θ m P Q0 _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, (a_cstr_sub m Q0 :: c :: C'), P, HP, HC, H => None
| S0, Θ, (a_cstr_eq Q0 :: C'), P, HP, HC, H =>
    match e_solve_eq_impl S0 Θ P Q0 _ _ _ with
    | None => None
    | Some (exist _ r1 Hr1) =>
        match e_solve_cstr_impl (sv_supply r1) (sv_block r1 ++ Θ) C'
                (sv_out r1) _ _ _ with
        | None => None
        | Some (exist _ r2 Hr2) =>
            Some (exist _ (mk_solve_result (sv_supply r2)
                    (sv_block r2 ++ sv_block r1) (sv_out r2)) _)
        end
    end.

Definition e_solve_eq_run (S0 : supply) (Θ : aenv) (P Q : pskl)
    (HP : lc_pskl P) (HQ : lc_pskl Q) : option solve_result :=
  match e_solve_eq_impl S0 Θ P Q HP HQ
          (@e_solve_eq_order_total S0 Θ P Q HP) with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_solve_eq_run_sound : forall S0 Θ P Q HP HQ r,
  e_solve_eq_run S0 Θ P Q HP HQ = Some r ->
  {{ S0 ↝ (sv_supply r) ⊨ Θ ⊢ₑ P ∼ Q ⤳ (sv_block r) ⨾ (sv_out r) }}e.
Proof.
  intros *. unfold e_solve_eq_run.
  destruct (e_solve_eq_impl S0 Θ P Q HP HQ
              (@e_solve_eq_order_total S0 Θ P Q HP)) as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.

Definition e_solve_sub_run (S0 : supply) (Θ : aenv) (m : mode) (P Q : pskl)
    (HP : lc_pskl P) (HQ : lc_pskl Q) : option solve_result :=
  match e_solve_sub_impl S0 Θ m P Q HP HQ
          (@e_solve_sub_order_total S0 Θ m P Q HP) with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_solve_sub_run_sound : forall S0 Θ m P Q HP HQ r,
  e_solve_sub_run S0 Θ m P Q HP HQ = Some r ->
  {{ S0 ↝ (sv_supply r) ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ (sv_block r) ⨾ (sv_out r) }}e.
Proof.
  intros *. unfold e_solve_sub_run.
  destruct (e_solve_sub_impl S0 Θ m P Q HP HQ
              (@e_solve_sub_order_total S0 Θ m P Q HP)) as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.

Definition e_solve_cstr_run (S0 : supply) (Θ : aenv) (C : a_cstrs) (P : pskl)
    (HP : lc_pskl P) (HC : Forall lc_a_cstr C) : option solve_result :=
  match e_solve_cstr_impl S0 Θ C P HP HC
          (@e_solve_cstr_order_total C S0 Θ P HP HC) with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_solve_cstr_run_sound : forall S0 Θ C P HP HC r,
  e_solve_cstr_run S0 Θ C P HP HC = Some r ->
  {{ S0 ↝ (sv_supply r) ⊨ Θ ⊩ C ⨾ P ⤳ (sv_block r) ⨾ (sv_out r) }}e.
Proof.
  intros *. unfold e_solve_cstr_run.
  destruct (e_solve_cstr_impl S0 Θ C P HP HC
              (@e_solve_cstr_order_total C S0 Θ P HP HC)) as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.
