(** ext_algo — the CONSTRAINT-SOLVING layer as EXECUTABLE FUNCTIONS, by
    Bove–Capretta.  Phase 4 step 3: runners for [e_solve_eq], [e_solve_sub]
    and the fold [e_solve_cstr] on the orders of def_order.v §3, total at an
    lc subject (prop_termination.v §11).

    Result shape, dispatch discipline and obligation-tactic recipe are
    def_look_impl.v's (read its header): [option (sig (spec …))],
    soundness-only, the reference implementation's match order —
    [solve_eq] (type.ml:399-464) and [solve_sub] (:489-533) — and one
    inversion of the order hypothesis per branch.

    ⚙ THE LAYERING REPEATS: [e_solve_eq] never calls [e_solve_sub], so the
    eq runner is closed first; the sub runner and the fold consume it as an
    ordinary function.  [SE-FlexR] consumes M1.7's [e_guess_mono_impl] — the
    first time a phase-4 runner composes with the spike's.

    ⚙ TWO DISPATCH NOTES AGAINST type.ml, both because rigid/flex is
    CONTEXTUAL here where the OCaml is syntactic:
    - a variable subject takes [SolE-Var]/[SolS-Var] immediately (type.ml
      :404/:491 for [TVar]); for a flexible variable type.ml reaches its
      separate [SolE-FlexL]/[SolS-Flex] rows (:458/:529) — in the mech both
      are the SAME rule ([e_solve_eq__var]/[e_solve_sub__var]) and the
      results agree, so the early dispatch is the faithful collapse.
    - [SolS-ForallR] here fires at a ghost subject too: type.ml:510 guards
      with [is_type a], a premise [e_solve_sub__forall_r] does not have,
      and the runner follows the rule.

    ⚙ In the SOLVING layer the subject's ∀ is peeled BEFORE the checked
    type's ([SolS-ForallL] :494 precedes [SolS-ForallR] :510) — the
    OPPOSITE of the subtyping walk's commitment (§8b.1, type.ml:910/958).
    Both are the reference's own orders; they differ per function. *)

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
Require Import src.fresco.algo.sub.prop_solve_sub.   (* lc_pskl_*_inv *)
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_uip.
Require Import src.fresco.ext_algo.def_dec.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_guess_impl.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.def_order.
Require Import src.fresco.ext_algo.prop_termination.

(* ⚠️ NO [Set Implicit Arguments] in an implementation file — see
   def_guess_impl.v's header. *)

(* ⭐ §8c.4 — the unfolding equations, derived against def_uip.v's
   Hedberg UIP so no axiom is incurred.  ⚠️ per-FILE flag. *)
Set Equations With UIP.

Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  The result                                                        *)
(* ===================================================================== *)

Record solve_result : Type := mk_solve_result {
  sv_supply : supply;
  sv_block  : aenv;      (* Ξ — the generated flexibles *)
  sv_out    : pskl       (* P' — the solved pattern *)
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

(* ===================================================================== *)
(*  §2  The obligation tactic — def_look_impl.v's §2 recipe               *)
(* ===================================================================== *)

#[local] Hint Resolve supply_fresh_notin guarded_shape_ck_sound
  ghost_free_ck_sound non_flex_ck_sound nonghost_ck_sound
  flex_bound_ck_flex_tvar lc_pskl_all_syn_inv
  e_solve_eq_lc e_solve_sub_lc : solvedec.
#[local] Hint Constructors e_solve_eq e_solve_sub e_solve_cstr
  lc_pskl : solvedec.
(* ⭐ THE SOLVE-DISPATCH GUARD (2026-08-18).  [SS-Vacuous] and [SS-ForallR]
   now demand that the earlier, SUBJECT-dispatching clauses do not apply —
   which is exactly the information Equations' own splitting leaves in the
   goal, since by the time control reaches those clauses the subject has
   been split away from [var_f] / [all_syn] / [univ_ghost]. *)
#[local] Hint Resolve peel_l_off_unit peel_l_off_var_b peel_l_off_var
  peel_l_off_arrow peel_l_off_ghost solve_l_off_unit solve_l_off_var_b
  solve_l_off_arrow solve_l_off_ghost : solvedec.

#[local] Ltac select_shape_premises :=
  repeat match goal with
         | Hp : forall _ _ _ _ _, _ = _ -> _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ _ eq_refl eq_refl eq_refl)
                   | clear Hp ]
         | Hp : forall _ _ _, _ = _ -> _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ eq_refl eq_refl eq_refl)
                   | clear Hp ]
         | Hp : forall _ _ _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _ _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl) | clear Hp ]
         | Hp : _ = _ -> _ |- _ =>
             first [ specialize (Hp eq_refl) | clear Hp ]
         | Hp : _ /\ _ |- _ => destruct Hp
         end.

#[local] Ltac saturate_lc :=
  repeat match goal with
         | Hlc : lc_pskl (pskl_arrow ?a ?b) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a, _ : lc_pskl b |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_arrow_inv in Hx;
                    destruct Hx
             end
         | Hlc : lc_pskl (pskl_univ_ghost ?a) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_univ_ghost_inv in Hx
             end
         end.

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

(* ===================================================================== *)
(*  §3  [e_solve_eq_impl]  (≈ solve_eq, type.ml:399)                      *)
(* ===================================================================== *)

#[tactic="solve_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_solve_eq_impl (S0 : supply) (Θ : aenv) (P Q : pskl)
    (HP : lc_pskl P) (HQ : lc_pskl Q)
    (H : e_solve_eq_order S0 Θ P Q)
    : option (sig (solve_eq_spec S0 Θ P Q)) by struct H :=

| S0, Θ, pskl_var_f α, Q, HP, HQ, H =>                    (* SE-Var/FlexL *)
    Some (exist _ (mk_solve_result S0 nil (pskl_var_f α)) _)
| S0, Θ, pskl_ghost, Q, HP, HQ, H =>                       (* SE-GhostL *)
    Some (exist _ (mk_solve_result S0 nil Q) _)

(* ---- unit subject ---- *)
| S0, Θ, pskl_unit, pskl_unit, HP, HQ, H =>               (* SE-Unit *)
    Some (exist _ (mk_solve_result S0 nil pskl_unit) _)
| S0, Θ, pskl_unit, pskl_ghost, HP, HQ, H =>               (* SE-VacuousR *)
    Some (exist _ (mk_solve_result S0 nil pskl_unit) _)
| S0, Θ, pskl_unit, pskl_var_f β, HP, HQ, H =>            (* SE-FlexR *)
    match sumbool_of_bool (flex_bound_ck Θ β && nonghost_ck pskl_unit
                           && non_flex_ck Θ pskl_unit) with
    | right _ => None
    | left _ =>
        let (r, Hr) := e_guess_mono_impl S0 pskl_unit _ in
        Some (exist _ (mk_solve_result (gr_supply r) (gr_block r)
                (ptyp_to_pskl (gr_type r))) _)
    end
| S0, Θ, pskl_unit, pskl_univ_ghost Q1, HP, HQ, H =>         (* SE-GuardedGhost *)
    match e_solve_eq_impl S0 Θ pskl_unit Q1 _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_unit, Q, HP, HQ, H => None

(* ---- arrow subject ---- *)
| S0, Θ, pskl_arrow P1 P2, pskl_arrow Q1 Q2, HP, HQ, H => (* SE-Arrow *)
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
| S0, Θ, pskl_arrow P1 P2, pskl_ghost, HP, HQ, H =>        (* SE-VacuousR *)
    Some (exist _ (mk_solve_result S0 nil (pskl_arrow P1 P2)) _)
| S0, Θ, pskl_arrow P1 P2, pskl_var_f β, HP, HQ, H =>     (* SE-FlexR *)
    match sumbool_of_bool (flex_bound_ck Θ β
                           && nonghost_ck (pskl_arrow P1 P2)
                           && non_flex_ck Θ (pskl_arrow P1 P2)) with
    | right _ => None
    | left _ =>
        let (r, Hr) := e_guess_mono_impl S0 (pskl_arrow P1 P2) _ in
        Some (exist _ (mk_solve_result (gr_supply r) (gr_block r)
                (ptyp_to_pskl (gr_type r))) _)
    end
| S0, Θ, pskl_arrow P1 P2, pskl_univ_ghost Q1, HP, HQ, H =>  (* SE-GuardedGhost *)
    match e_solve_eq_impl S0 Θ (pskl_arrow P1 P2) Q1 _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_arrow P1 P2, Q, HP, HQ, H => None

(* ---- ∀ subject ---- *)
| S0, Θ, pskl_all_syn P1, pskl_all_syn Q1, HP, HQ, H =>   (* SE-Forall *)
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
| S0, Θ, pskl_all_syn P1, pskl_ghost, HP, HQ, H =>         (* SE-VacuousR *)
    Some (exist _ (mk_solve_result S0 nil (pskl_all_syn P1)) _)
| S0, Θ, pskl_all_syn P1, pskl_var_f β, HP, HQ, H =>      (* SE-FlexR *)
    match sumbool_of_bool (flex_bound_ck Θ β
                           && nonghost_ck (pskl_all_syn P1)
                           && non_flex_ck Θ (pskl_all_syn P1)) with
    | right _ => None
    | left _ =>
        let (r, Hr) := e_guess_mono_impl S0 (pskl_all_syn P1) _ in
        Some (exist _ (mk_solve_result (gr_supply r) (gr_block r)
                (ptyp_to_pskl (gr_type r))) _)
    end
| S0, Θ, pskl_all_syn P1, pskl_univ_ghost Q1, HP, HQ, H =>   (* SE-ForallGhost *)
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

(* ---- ⫯ subject ---- *)
| S0, Θ, pskl_univ_ghost P1, pskl_univ_ghost Q1, HP, HQ, H =>   (* SE-UnivGhost *)
    match e_solve_eq_impl S0 Θ P1 Q1 _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_solve_result (sv_supply r) (sv_block r)
                (pskl_univ_ghost (sv_out r))) _)
    end
| S0, Θ, pskl_univ_ghost P1, pskl_ghost, HP, HQ, H =>         (* SE-VacuousR *)
    Some (exist _ (mk_solve_result S0 nil (pskl_univ_ghost P1)) _)
| S0, Θ, pskl_univ_ghost P1, pskl_all_syn Q1, HP, HQ, H =>   (* SE-GhostForall *)
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
| S0, Θ, pskl_univ_ghost P1, pskl_unit, HP, HQ, H =>         (* SE-GhostGuarded *)
    match e_solve_eq_impl S0 Θ P1 pskl_unit _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_univ_ghost P1, pskl_var_f β, HP, HQ, H =>      (* SE-GhostGuarded *)
    match e_solve_eq_impl S0 Θ P1 (pskl_var_f β) _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_univ_ghost P1, pskl_arrow Q1 Q2, HP, HQ, H =>  (* SE-GhostGuarded *)
    match e_solve_eq_impl S0 Θ P1 (pskl_arrow Q1 Q2) _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| S0, Θ, pskl_univ_ghost P1, pskl_var_b n, HP, HQ, H => None

(* ---- dangling index subject ---- *)
| S0, Θ, pskl_var_b n, pskl_ghost, HP, HQ, H =>            (* SE-VacuousR *)
    Some (exist _ (mk_solve_result S0 nil (pskl_var_b n)) _)
| S0, Θ, pskl_var_b n, Q, HP, HQ, H => None.

(* ===================================================================== *)
(*  §4  [e_solve_sub_impl]  (≈ solve_sub, type.ml:489)                    *)
(* ===================================================================== *)

#[tactic="solve_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_solve_sub_impl (S0 : supply) (Θ : aenv) (m : mode) (P Q : pskl)
    (HP : lc_pskl P) (HQ : lc_pskl Q)
    (H : e_solve_sub_order S0 Θ m P Q)
    : option (sig (solve_sub_spec S0 Θ m P Q)) by struct H :=

| S0, Θ, m, pskl_var_f α, Q, HP, HQ, H =>                 (* SS-Var/Flex *)
    Some (exist _ (mk_solve_result S0 nil (pskl_var_f α)) _)
| S0, Θ, m, pskl_all_syn P1, Q, HP, HQ, H =>              (* SS-ForallL *)
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
| S0, Θ, m, pskl_univ_ghost P1, Q, HP, HQ, H =>              (* SS-UnivGhostL *)
    match e_solve_sub_impl S0 Θ m P1 Q _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_solve_result (sv_supply r) (sv_block r)
                (pskl_univ_ghost (sv_out r))) _)
    end
| S0, Θ, m, P, pskl_ghost, HP, HQ, H =>                    (* SS-Vacuous *)
    Some (exist _ (mk_solve_result S0 nil P) _)
| S0, Θ, mode_tc, P, pskl_all_syn B, HP, HQ, H =>         (* SS-ForallR *)
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
| S0, Θ, mode_tc, pskl_ghost, Q, HP, HQ, H =>              (* SS-GhostL *)
    match sumbool_of_bool (guarded_shape_ck Q && ghost_free_ck Q) with
    | right _ => None
    | left _ => Some (exist _ (mk_solve_result S0 nil (pskl_univ_ghost Q)) _)
    end
| S0, Θ, mode_tc, P, Q, HP, HQ, H =>                      (* SS-Check *)
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
    (* SS-Arrow *)
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
    (* SS-GhostLF *)
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

(** ⭐ THE SS-Vacuous OBLIGATIONS, SPELLED OUT (2026-08-18).  Under the
    SOLVE-DISPATCH guard the row carries [peel_l_off P], and at the two
    leaves Equations reaches it with a NON-atomic subject ([var_b] and
    [arrow]) the obligation tactic does not close it — so they are
    discharged here.  ⚙ Both are one line: by the time control reaches the
    [SS-Vacuous] clause the subject has already been split away from
    [var_f] / [∀] / [⫯], which is exactly what the guard asks. *)
Next Obligation.
  unfold solve_sub_spec; simpl.
  apply e_solve_sub__vacuous; auto with fresco.
Qed.
Next Obligation.
  unfold solve_sub_spec; simpl.
  apply e_solve_sub__vacuous; auto with fresco.
Qed.

(* ===================================================================== *)
(*  §5  [e_solve_cstr_impl] — the fold  (≈ constr_solve, type.ml:537)     *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(*  §6  Totality-backed argument-free runners, and their soundness        *)
(* ===================================================================== *)

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
