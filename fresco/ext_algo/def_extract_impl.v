(** ext_algo — [extract] as an EXECUTABLE FUNCTION: the collection →
    solving → guess pipeline composed.  Phase 4 step 4.

    One rule, no recursion of its own — the implementation is a plain
    three-stage chain of the runners already built (def_look_impl.v,
    def_solve_impl.v, def_guess_impl_sk.v), written as a non-recursive
    [Equations] so its obligations follow the same tactic recipe.  This is
    [type.ml]'s [look] (:703-713) with the [guess^N] stage folded in, as
    [e_extract__solve] specifies.

    ⚙ THE STAGE PRECONDITIONS COMPOSE, WHICH IS THE POINT: the fold's seed
    is [◇] (lc by constructor), the constraints' local closure is stage 1's
    output property ([e_looksub_cstrs_lc]), and the guess subject's is
    stage 2's ([e_solve_cstr_lc]) — each consumed from the PREVIOUS stage's
    spec evidence, exactly as the totality proof composed them
    (prop_termination.v §11's [e_extract_order_total]).  The third stage
    uses [e_guess_run] (total at an lc subject), so the order's [e_guess]
    premise is never consulted. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_uip.
Require Import src.fresco.ext_algo.def_dec.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_guess_impl.
Require Import src.fresco.ext_algo.def_guess_impl_sk.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.def_order.
Require Import src.fresco.ext_algo.prop_termination.
Require Import src.fresco.ext_algo.def_look_impl.
Require Import src.fresco.ext_algo.def_solve_impl.

(* ⚠️ NO [Set Implicit Arguments] in an implementation file — see
   def_guess_impl.v's header. *)

(* ⭐ §8c.4 — the unfolding equations, derived against def_uip.v's
   Hedberg UIP so no axiom is incurred.  ⚠️ per-FILE flag. *)
Set Equations With UIP.

Open Scope fresco_e_scope.

Record extract_result : Type := mk_extract_result {
  ex_supply : supply;
  ex_block  : aenv;      (* Ξ ++ Ξs ++ Ξ' — the three stages' blocks *)
  ex_out    : pskl       (* Q' — the extracted instantiation *)
}.

Definition extract_spec (S0 : supply) (Θ0 : aenv) (NM : a_sub_mode)
    (α : atom) (m : mode) (P P' : pskl) (r : extract_result) : Prop :=
  {{ S0 ↝ (ex_supply r) ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ (ex_block r)
     ↪ (ex_out r) }}e.

#[local] Hint Resolve e_looksub_cstrs_lc e_solve_cstr_lc
  e_guess_run_sound : extrdec.
#[local] Hint Constructors e_extract lc_pskl : extrdec.

#[local] Ltac extract_impl_tac :=
  cbv zeta; intros;
  try match goal with
      | H : e_extract_order _ _ _ _ _ _ _ |- _ => inversion H; subst
      end;
  unfold extract_spec, looksub_spec, solve_cstr_spec in *; simpl in *;
  try solve [ eauto 6 with extrdec ];
  (* the assembled rule instance — three stage runs in premise order *)
  solve [ eapply e_extract__solve;
          [ eassumption | eassumption | apply e_guess_run_sound ] ].

#[tactic="extract_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_extract_impl (S0 : supply) (Θ0 : aenv) (NM : a_sub_mode)
    (α : atom) (m : mode) (P P' : pskl)
    (HP : lc_pskl P) (HP' : lc_pskl P')
    (H : e_extract_order S0 Θ0 NM α m P P')
    : option (sig (extract_spec S0 Θ0 NM α m P P')) :=

| S0, Θ0, NM, α, m, P, P', HP, HP', H =>
    match e_looksub_impl S0 Θ0 α m P P' HP HP' _ with
    | None => None
    | Some (exist _ r1 Hr1) =>
        match e_solve_cstr_impl (lk_supply r1) (lk_block r1 ++ Θ0)
                (lk_cstrs r1) pskl_hole _ _ _ with
        | None => None
        | Some (exist _ r2 Hr2) =>
            let r3 := e_guess_run (sv_supply r2) NM (sv_out r2) _ in
            Some (exist _ (mk_extract_result (gs_supply r3)
                    (lk_block r1 ++ sv_block r2 ++ gs_block r3)
                    (gs_skel r3)) _)
        end
    end.

(** The argument-free runner: the extraction is total at lc inputs
    (prop_termination.v §11, [e_extract_order_total]). *)
Definition e_extract_run (S0 : supply) (Θ0 : aenv) (NM : a_sub_mode)
    (α : atom) (m : mode) (P P' : pskl)
    (HP : lc_pskl P) (HP' : lc_pskl P') : option extract_result :=
  match e_extract_impl S0 Θ0 NM α m P P' HP HP'
          (@e_extract_order_total S0 Θ0 NM α m P P' HP HP') with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_extract_run_sound : forall S0 Θ0 NM α m P P' HP HP' r,
  e_extract_run S0 Θ0 NM α m P P' HP HP' = Some r ->
  {{ S0 ↝ (ex_supply r) ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ (ex_block r)
     ↪ (ex_out r) }}e.
Proof.
  intros *. unfold e_extract_run.
  destruct (e_extract_impl S0 Θ0 NM α m P P' HP HP'
              (@e_extract_order_total S0 Θ0 NM α m P P' HP HP'))
    as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.
