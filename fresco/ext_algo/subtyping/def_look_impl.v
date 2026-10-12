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
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.basic.prop_termination.

Set Equations With UIP.

Open Scope fresco_e_scope.

Record look_result : Type := mk_look_result {
  lk_supply : supply;
  lk_block  : aenv;
  lk_cstrs  : a_cstrs
}.

Definition lookeq_spec (S0 : supply) (Θ : aenv) (α : atom) (P P' : pskl)
    (r : look_result) : Prop :=
  {{ S0 ↝ (lk_supply r) ⊨ Θ ⊢ P ∼[ α ] P' ⤳ (lk_block r) ⨾ (lk_cstrs r) }}e.

Definition looksub_spec (S0 : supply) (Θ : aenv) (α : atom) (m : mode)
    (P P' : pskl) (r : look_result) : Prop :=
  {{ S0 ↝ (lk_supply r) ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ (lk_block r)
     ⨾ (lk_cstrs r) }}e.

#[local] Hint Resolve supply_fresh_notin mem_true_in mem_false_notin
  guarded_shape_ck_sound ghost_free_ck_sound lc_pskl_all_syn_inv : lookdec.
#[local] Hint Constructors e_lookeq e_looksub lc_pskl : lookdec.
#[local] Hint Extern 4 (_ <> _) => congruence : lookdec.
#[local] Hint Extern 1 (flex_r_off _ _) =>
  (solve [ apply flex_r_off_nonvar; intros ?; discriminate
         | apply flex_r_off_rigid; apply flex_bound_ck_not_flex_tvar;
           assumption ]) : lookdec.
#[local] Hint Extern 1 (a_flex_tvar _ _) =>
  (apply flex_bound_ck_flex_tvar; assumption) : lookdec.
#[local] Hint Extern 4 (_ `notin` _) =>
  solve [ apply mem_false_notin; assumption | simpl in *; fsetdec ] : lookdec.
#[local] Hint Extern 4 (_ `in` _) =>
  solve [ apply mem_true_in; assumption | simpl in *; fsetdec ] : lookdec.
#[local] Hint Extern 4 (forall_r_off _ _) =>
  solve [ apply forall_r_off_nontc; discriminate
        | apply forall_r_off_nonall; intros ?; discriminate
        | apply forall_r_off_ck; assumption ] : lookdec.

#[local] Ltac forall_r_off_tac :=
  match goal with
  | |- forall_r_off _ _ =>
      solve [ apply forall_r_off_nontc; discriminate
            | apply forall_r_off_nonall; intros ?; discriminate
            | apply forall_r_off_ck; assumption ]
  end.

#[local] Ltac look_impl_tac :=
  try forall_r_off_tac;
  intros;
  try match goal with
      | H : e_lookeq_order _ _ _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | H : e_looksub_order _ _ _ _ _ _ |- _ => inversion H; subst
      end;
  unfold lookeq_spec, looksub_spec in *;
  repeat match goal with
         | Hb : _ && _ = true |- _ => apply andb_prop in Hb; destruct Hb
         end;
  select_shape_premises; saturate_lc; simpl in *;
  try congruence;
  eauto 6 with lookdec.

#[tactic="look_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_lookeq_impl (S0 : supply) (Θ : aenv) (α : atom) (P P' : pskl)
    (HP : lc_pskl P) (HP' : lc_pskl P')
    (H : e_lookeq_order S0 Θ α P P')
    : option (sig (lookeq_spec S0 Θ α P P')) by struct H :=

| S0, Θ, α, pskl_var_f β, P', HP, HP', H =>
    match α == β with
    | left _ =>
        Some (exist _ (mk_look_result S0 nil (a_cstr_eq P' :: nil)) _)
    | right _ =>
        Some (exist _ (mk_look_result S0 nil nil) _)
    end

| S0, Θ, α, pskl_unit, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, pskl_var_b n, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, pskl_ghost, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)

| S0, Θ, α, pskl_arrow P1 P2, pskl_ghost, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, pskl_arrow P1 P2, pskl_var_f β, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match sumbool_of_bool (flex_bound_ck Θ β) with
        | right _ => None
        | left _ =>
            Some (exist _ (mk_look_result (add (supply_fresh S0) S0)
                    ((supply_fresh S0 ~ abind_flex_mono) ++ nil)
                    (a_cstr_eq (pskl_var_f (supply_fresh S0)) :: nil)) _)
        end
    end
| S0, Θ, α, pskl_arrow P1 P2, pskl_arrow P1' P2', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_lookeq_impl S0 Θ α P1 P1' _ _ _ with
        | None => None
        | Some (exist _ r1 Hr1) =>
            match e_lookeq_impl (lk_supply r1) Θ α P2 P2' _ _ _ with
            | None => None
            | Some (exist _ r2 Hr2) =>
                Some (exist _ (mk_look_result (lk_supply r2)
                        (lk_block r1 ++ lk_block r2)
                        (lk_cstrs r1 ++ lk_cstrs r2)) _)
            end
        end
    end
| S0, Θ, α, pskl_arrow P1 P2, pskl_univ_ghost Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_lookeq_impl S0 Θ α (pskl_arrow P1 P2) Q' _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_arrow P1 P2, P', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ => None
    end

| S0, Θ, α, pskl_all_syn Q, pskl_ghost, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, pskl_all_syn Q, pskl_var_f β, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>

        match sumbool_of_bool (flex_bound_ck Θ β) with
        | right _ => None
        | left _ =>
            Some (exist _ (mk_look_result (add (supply_fresh S0) S0)
                    ((supply_fresh S0 ~ abind_flex_mono) ++ nil)
                    (a_cstr_eq (pskl_var_f (supply_fresh S0)) :: nil)) _)
        end
    end
| S0, Θ, α, pskl_all_syn Q, pskl_all_syn Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_lookeq_impl (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
                (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))
                _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_all_syn Q, pskl_univ_ghost Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_lookeq_impl (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
                (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                (pskl_univ_ghost Q') _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_all_syn Q, P', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ => None
    end

| S0, Θ, α, pskl_univ_ghost Q, pskl_ghost, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, pskl_univ_ghost Q, pskl_var_f β, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_univ_ghost Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match sumbool_of_bool (flex_bound_ck Θ β) with
        | left _ =>
            Some (exist _ (mk_look_result (add (supply_fresh S0) S0)
                    ((supply_fresh S0 ~ abind_flex_mono) ++ nil)
                    (a_cstr_eq (pskl_var_f (supply_fresh S0)) :: nil)) _)
        | right _ =>
            match e_lookeq_impl S0 Θ α Q (pskl_var_f β) _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        end
    end
| S0, Θ, α, pskl_univ_ghost Q, pskl_univ_ghost Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_univ_ghost Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_lookeq_impl S0 Θ α Q Q' _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_univ_ghost Q, pskl_all_syn Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_univ_ghost Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_lookeq_impl (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
                (pskl_univ_ghost Q)
                (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))
                _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_univ_ghost Q, pskl_unit, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_univ_ghost Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_lookeq_impl S0 Θ α Q pskl_unit _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_univ_ghost Q, pskl_arrow P1' P2', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_univ_ghost Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_lookeq_impl S0 Θ α Q (pskl_arrow P1' P2') _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_univ_ghost Q, pskl_var_b n, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_univ_ghost Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ => None
    end.

#[tactic="look_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_looksub_impl (S0 : supply) (Θ : aenv) (α : atom) (m : mode)
    (P P' : pskl) (HP : lc_pskl P) (HP' : lc_pskl P')
    (H : e_looksub_order S0 Θ α m P P')
    : option (sig (looksub_spec S0 Θ α m P P')) by struct H :=

| S0, Θ, α, m, pskl_var_f β, P', HP, HP', H =>
    match α == β with
    | left _ =>
        Some (exist _ (mk_look_result S0 nil (a_cstr_sub m P' :: nil)) _)
    | right _ =>
        Some (exist _ (mk_look_result S0 nil nil) _)
    end
| S0, Θ, α, m, pskl_unit, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, m, pskl_var_b n, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, m, pskl_ghost, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)

| S0, Θ, α, m, pskl_arrow P1 P2, pskl_ghost, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, mode_tc, pskl_arrow P1 P2, pskl_all_syn B, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match sumbool_of_bool (ghost_free_ck (pskl_all_syn B)) with
        | right _ => None
        | left _ =>
            match e_looksub_impl (add (supply_fresh S0) S0)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc
                    (pskl_arrow P1 P2)
                    (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
                    _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        end
    end
| S0, Θ, α, mode_fn m', pskl_arrow P1 P2, pskl_arrow P1' P2', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_lookeq_impl S0 Θ α P1 P1' _ _ _ with
        | None => None
        | Some (exist _ r1 Hr1) =>
            match e_looksub_impl (lk_supply r1) Θ α m' P2 P2' _ _ _ with
            | None => None
            | Some (exist _ r2 Hr2) =>
                Some (exist _ (mk_look_result (lk_supply r2)
                        (lk_block r1 ++ lk_block r2)
                        (lk_cstrs r1 ++ lk_cstrs r2)) _)
            end
        end
    end
| S0, Θ, α, mode_tc, pskl_arrow P1 P2, P', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match sumbool_of_bool (guarded_shape_ck P' && ghost_free_ck P') with
        | right _ => None
        | left _ =>
            match e_lookeq_impl S0 Θ α (pskl_arrow P1 P2) P' _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        end
    end
| S0, Θ, α, m, pskl_arrow P1 P2, P', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ => None
    end

| S0, Θ, α, m, pskl_all_syn Q, pskl_ghost, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, mode_tc, pskl_all_syn Q, pskl_all_syn B, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match sumbool_of_bool (ghost_free_ck (pskl_all_syn B)) with
        | left _ =>
            match e_looksub_impl (add (supply_fresh S0) S0)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc
                    (pskl_all_syn Q)
                    (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
                    _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>
            match e_looksub_impl (add (supply_fresh S0) S0)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc
                    (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                    (pskl_all_syn B) _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        end
    end
| S0, Θ, α, m, pskl_all_syn Q, P', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_looksub_impl (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_tvar) ++ Θ) α m
                (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                P' _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end

| S0, Θ, α, m, pskl_univ_ghost Q, pskl_ghost, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, mode_tc, pskl_univ_ghost Q, pskl_all_syn B, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_univ_ghost Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match sumbool_of_bool (ghost_free_ck (pskl_all_syn B)) with
        | left _ =>
            match e_looksub_impl (add (supply_fresh S0) S0)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc
                    (pskl_univ_ghost Q)
                    (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
                    _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>
            match e_looksub_impl S0 Θ α mode_tc Q (pskl_all_syn B) _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        end
    end
| S0, Θ, α, m, pskl_univ_ghost Q, P', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_univ_ghost Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match e_looksub_impl S0 Θ α m Q P' _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end.

Definition e_lookeq_run (S0 : supply) (Θ : aenv) (α : atom) (P P' : pskl)
    (HP : lc_pskl P) (HP' : lc_pskl P') : option look_result :=
  match e_lookeq_impl S0 Θ α P P' HP HP'
          (e_lookeq_order_total S0 Θ α P P') with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_lookeq_run_sound : forall S0 Θ α P P' HP HP' r,
  e_lookeq_run S0 Θ α P P' HP HP' = Some r ->
  {{ S0 ↝ (lk_supply r) ⊨ Θ ⊢ P ∼[ α ] P' ⤳ (lk_block r) ⨾ (lk_cstrs r) }}e.
Proof.
  intros *. unfold e_lookeq_run.
  destruct (e_lookeq_impl S0 Θ α P P' HP HP'
              (e_lookeq_order_total S0 Θ α P P')) as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.

Definition e_looksub_run (S0 : supply) (Θ : aenv) (α : atom) (m : mode)
    (P P' : pskl) (HP : lc_pskl P) (HP' : lc_pskl P') : option look_result :=
  match e_looksub_impl S0 Θ α m P P' HP HP'
          (e_looksub_order_total S0 Θ α m P P') with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_looksub_run_sound : forall S0 Θ α m P P' HP HP' r,
  e_looksub_run S0 Θ α m P P' HP HP' = Some r ->
  {{ S0 ↝ (lk_supply r) ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ (lk_block r)
     ⨾ (lk_cstrs r) }}e.
Proof.
  intros *. unfold e_looksub_run.
  destruct (e_looksub_impl S0 Θ α m P P' HP HP'
              (e_looksub_order_total S0 Θ α m P P')) as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.
