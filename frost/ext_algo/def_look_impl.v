(** ext_algo — the CONSTRAINT-COLLECTION cluster as EXECUTABLE FUNCTIONS,
    by Bove–Capretta.  Phase 4 step 2 of the termination campaign
    (docs/HANDOFF-extractable-algo-encoding.md §8b): runners for [e_lookeq]
    and [e_looksub] on the orders of def_order.v §2, whose totality is
    UNCONDITIONAL (prop_termination.v §11).

    ⭐ THE RESULT SHAPE FOR PARTIAL JUDGEMENTS, decided here for the whole of
    phase 4: [option (sig (spec …))].  [None] means "no rule applied" and is
    justified by nothing — the contract is SOUNDNESS-ONLY ([Some r] is a real
    run), and "rejection is justified" (completeness of the runner) is
    deferred to a later determinism pass.  [sig] erases at extraction, so the
    OCaml type is a plain ['a option] — §8's bar — where [type.ml] raises
    [UnifyError] instead ([constr_collect_eq], type.ml:626).

    ⭐ DISPATCH ORDER IS THE REFERENCE IMPLEMENTATION'S.  [e_lookeq_impl]
    follows [constr_collect_eq] (type.ml:542-626): Var, Absent, Vacuous,
    FlexR, then the shape pairs, with the ghost-strips last; [e_looksub_impl]
    follows [constr_collect_sub] (type.ml:649-701): Absent/Var first,
    Vacuous, ForallR BEFORE Arrow/ForallL/UnivGhostL, Check LAST.  Rows the
    mech does not have (Con, Mod) are skipped.  ⚙ One deliberate divergence:
    [type.ml]'s LS-Arrow collects the CODOMAIN first (:676) because its
    [constr] accumulator builds back-to-front; the mech rule [e_looksub__arrow]
    threads the supply domain-first, and the runner follows the rule.

    ⚙ THE TWO JUDGEMENTS LAYER instead of going mutual: [e_lookeq] never
    calls [e_looksub] (def_order.v §2), so [e_lookeq_impl] is closed first
    and [e_looksub_impl] consumes it as an ordinary function.

    ⚙ THE lc HYPOTHESES are the honest preconditions of every runner since
    M1.7 ([e_guess_mono_run]'s [lc_pskl]): [guarded_pskl]'s arrow row embeds
    local closure, so the branches that build a guarded-evidence rule
    instance ([LE-UnivGhost2]/[LE-UnivGhostR]/[LS-Check]) need it.  Both are
    erased at extraction. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.sub.prop_solve_sub.   (* lc_pskl_*_inv *)
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_uip.
Require Import src.frost.ext_algo.def_dec.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_guess_impl.
Require Import src.frost.ext_algo.def_order.
Require Import src.frost.ext_algo.prop_termination.

(* ⚠️ NO [Set Implicit Arguments] in an implementation file — see
   def_guess_impl.v's header. *)

(* ⭐ §8c.4 — the unfolding equations, derived against def_uip.v's
   Hedberg UIP so no axiom is incurred.  ⚠️ per-FILE flag. *)
Set Equations With UIP.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The result                                                        *)
(* ===================================================================== *)

(** One record for both judgements — they return the same three things
    (final supply, generated block, collected constraints). *)
Record look_result : Type := mk_look_result {
  lk_supply : supply;
  lk_block  : aenv;      (* Ξ — the generated flexibles *)
  lk_cstrs  : a_cstrs    (* C — the collected constraints *)
}.

Definition lookeq_spec (S0 : supply) (Θ : aenv) (α : atom) (P P' : pskl)
    (r : look_result) : Prop :=
  {{ S0 ↝ (lk_supply r) ⊨ Θ ⊢ P ∼[ α ] P' ⤳ (lk_block r) ⨾ (lk_cstrs r) }}e.

Definition looksub_spec (S0 : supply) (Θ : aenv) (α : atom) (m : mode)
    (P P' : pskl) (r : look_result) : Prop :=
  {{ S0 ↝ (lk_supply r) ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ (lk_block r)
     ⨾ (lk_cstrs r) }}e.

(* ===================================================================== *)
(*  §2  The obligation tactic                                             *)
(*                                                                        *)
(*  Two goal kinds, one tactic (the guess_impl_tac recipe, scaled to the   *)
(*  one-constructor orders): invert the ONE order hypothesis, SELECT the   *)
(*  premises whose shape equations this branch satisfies ([eq_refl]        *)
(*  application; non-matching premises are cleared — in a branch with      *)
(*  concrete shapes they belong to other rules), saturate the lc           *)
(*  inversions, then [eauto] builds both the recursive calls' order        *)
(*  arguments and the branch's rule instance.                             *)
(* ===================================================================== *)

#[local] Hint Resolve supply_fresh_notin mem_true_in mem_false_notin
  guarded_shape_ck_sound ghost_free_ck_sound lc_pskl_all_syn_inv : lookdec.
#[local] Hint Constructors e_lookeq e_looksub lc_pskl : lookdec.
#[local] Hint Extern 4 (_ <> _) => congruence : lookdec.
#[local] Hint Extern 4 (_ `notin` _) =>
  solve [ apply mem_false_notin; assumption | simpl in *; fsetdec ] : lookdec.
#[local] Hint Extern 4 (_ `in` _) =>
  solve [ apply mem_true_in; assumption | simpl in *; fsetdec ] : lookdec.

#[local] Ltac select_shape_premises :=
  repeat match goal with
         | Hp : forall _ _ _ _ _, _ = _ -> _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ _ eq_refl eq_refl eq_refl)
                   | clear Hp ]
         | Hp : forall _ _ _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl) | clear Hp ]
         | Hp : _ = _ -> _ |- _ =>
             first [ specialize (Hp eq_refl) | clear Hp ]
         | Hp : _ /\ _ |- _ => destruct Hp
         end.

(** Non-destructive: the originals stay (Equations' catch-all splitting
    let-binds aliases of the scrutinees, whose lc goals close by conversion
    against the ORIGINAL hypotheses), the components are added beside. *)
#[local] Ltac saturate_lc :=
  repeat match goal with
         | Hlc : lc_pskl (pskl_arrow ?a ?b) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a, _ : lc_pskl b |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_arrow_inv in Hx;
                    destruct Hx
             end
         | Hlc : lc_pskl (pskl_tophole ?a) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_tophole_inv in Hx
             end
         end.

#[local] Ltac look_impl_tac :=
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

(* ===================================================================== *)
(*  §3  [e_lookeq_impl]  (≈ constr_collect_eq, type.ml:542)               *)
(* ===================================================================== *)

#[tactic="look_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_lookeq_impl (S0 : supply) (Θ : aenv) (α : atom) (P P' : pskl)
    (HP : lc_pskl P) (HP' : lc_pskl P')
    (H : e_lookeq_order S0 Θ α P P')
    : option (sig (lookeq_spec S0 Θ α P P')) by struct H :=

(* LE-Var / LE-Absent — a variable subject is one or the other *)
| S0, Θ, α, pskl_var_f β, P', HP, HP', H =>
    match α == β with
    | left _ =>
        Some (exist _ (mk_look_result S0 nil (a_cstr_eq P' :: nil)) _)
    | right _ =>
        Some (exist _ (mk_look_result S0 nil nil) _)
    end
(* subjects with no free variables at all — LE-Absent *)
| S0, Θ, α, pskl_unit, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, pskl_var_b n, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)
| S0, Θ, α, pskl_hole, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)

(* ---- arrow subject ---- *)
| S0, Θ, α, pskl_arrow P1 P2, pskl_hole, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)          (* LE-Vacuous *)
| S0, Θ, α, pskl_arrow P1 P2, pskl_var_f β, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-FlexR *)
        Some (exist _ (mk_look_result (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_flex_mono) ++ nil)
                (a_cstr_eq (pskl_var_f (supply_fresh S0)) :: nil)) _)
    end
| S0, Θ, α, pskl_arrow P1 P2, pskl_arrow P1' P2', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-Arrow *)
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
| S0, Θ, α, pskl_arrow P1 P2, pskl_tophole Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-UnivGhostR *)
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

(* ---- ∀ subject ---- *)
| S0, Θ, α, pskl_all_syn Q, pskl_hole, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)          (* LE-Vacuous *)
| S0, Θ, α, pskl_all_syn Q, pskl_var_f β, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-FlexR *)
        Some (exist _ (mk_look_result (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_flex_mono) ++ nil)
                (a_cstr_eq (pskl_var_f (supply_fresh S0)) :: nil)) _)
    end
| S0, Θ, α, pskl_all_syn Q, pskl_all_syn Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-ForallInh *)
        match e_lookeq_impl (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
                (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))
                _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_all_syn Q, pskl_tophole Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-ForallSyn *)
        match e_lookeq_impl (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
                (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                (pskl_tophole Q') _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_all_syn Q, P', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ => None
    end

(* ---- ⫯ subject ---- *)
| S0, Θ, α, pskl_tophole Q, pskl_hole, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)          (* LE-Vacuous *)
| S0, Θ, α, pskl_tophole Q, pskl_var_f β, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_tophole Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-FlexR *)
        Some (exist _ (mk_look_result (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_flex_mono) ++ nil)
                (a_cstr_eq (pskl_var_f (supply_fresh S0)) :: nil)) _)
    end
| S0, Θ, α, pskl_tophole Q, pskl_tophole Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_tophole Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-UnivGhost *)
        match e_lookeq_impl S0 Θ α Q Q' _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_tophole Q, pskl_all_syn Q', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_tophole Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-UnivGhost1 *)
        match e_lookeq_impl (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
                (pskl_tophole Q)
                (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))
                _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_tophole Q, pskl_unit, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_tophole Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-UnivGhost2 *)
        match e_lookeq_impl S0 Θ α Q pskl_unit _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_tophole Q, pskl_arrow P1' P2', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_tophole Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LE-UnivGhost2 *)
        match e_lookeq_impl S0 Θ α Q (pskl_arrow P1' P2') _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| S0, Θ, α, pskl_tophole Q, pskl_var_b n, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_tophole Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ => None
    end.

(* ===================================================================== *)
(*  §4  [e_looksub_impl]  (≈ constr_collect_sub, type.ml:649)             *)
(*                                                                        *)
(*  Priority where shapes overlap, per the reference: ForallR (:663)      *)
(*  BEFORE ForallL (:680) / UnivGhostL (:690), Check LAST (:695).         *)
(* ===================================================================== *)

#[tactic="look_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_looksub_impl (S0 : supply) (Θ : aenv) (α : atom) (m : mode)
    (P P' : pskl) (HP : lc_pskl P) (HP' : lc_pskl P')
    (H : e_looksub_order S0 Θ α m P P')
    : option (sig (looksub_spec S0 Θ α m P P')) by struct H :=

(* LS-Var / LS-Absent *)
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
| S0, Θ, α, m, pskl_hole, P', HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)

(* ---- arrow subject ---- *)
| S0, Θ, α, m, pskl_arrow P1 P2, pskl_hole, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)          (* LS-Vacuous *)
| S0, Θ, α, mode_tc, pskl_arrow P1 P2, pskl_all_syn B, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_arrow P1 P2))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LS-ForallR *)
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
    | left _ =>                                            (* LS-Arrow *)
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
    | left _ =>                                            (* LS-Check *)
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

(* ---- ∀ subject ---- *)
| S0, Θ, α, m, pskl_all_syn Q, pskl_hole, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)          (* LS-Vacuous *)
| S0, Θ, α, mode_tc, pskl_all_syn Q, pskl_all_syn B, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_all_syn Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match sumbool_of_bool (ghost_free_ck (pskl_all_syn B)) with
        | left _ =>                                        (* LS-ForallR *)
            match e_looksub_impl (add (supply_fresh S0) S0)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc
                    (pskl_all_syn Q)
                    (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
                    _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>                                       (* LS-ForallL *)
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
    | left _ =>                                            (* LS-ForallL *)
        match e_looksub_impl (add (supply_fresh S0) S0)
                ((supply_fresh S0 ~ abind_tvar) ++ Θ) α m
                (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                P' _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end

(* ---- ⫯ subject ---- *)
| S0, Θ, α, m, pskl_tophole Q, pskl_hole, HP, HP', H =>
    Some (exist _ (mk_look_result S0 nil nil) _)          (* LS-Vacuous *)
| S0, Θ, α, mode_tc, pskl_tophole Q, pskl_all_syn B, HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_tophole Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>
        match sumbool_of_bool (ghost_free_ck (pskl_all_syn B)) with
        | left _ =>                                        (* LS-ForallR *)
            match e_looksub_impl (add (supply_fresh S0) S0)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc
                    (pskl_tophole Q)
                    (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
                    _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>                                       (* LS-UnivGhostL *)
            match e_looksub_impl S0 Θ α mode_tc Q (pskl_all_syn B) _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        end
    end
| S0, Θ, α, m, pskl_tophole Q, P', HP, HP', H =>
    match sumbool_of_bool (mem α (ftvar_in_pskl (pskl_tophole Q))) with
    | right _ => Some (exist _ (mk_look_result S0 nil nil) _)
    | left _ =>                                            (* LS-UnivGhostL *)
        match e_looksub_impl S0 Θ α m Q P' _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end.

(* ===================================================================== *)
(*  §5  Totality-backed argument-free runners, and their soundness        *)
(* ===================================================================== *)

(** The collection's totality is UNCONDITIONAL (prop_termination.v §11), so
    the runners carry only the lc preconditions the guarded-evidence
    branches need. *)
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
