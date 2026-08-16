(** ext_algo — COMPLETENESS OF THE RUNNERS (campaign §8c.3/§8c.5): an
    `a_*` derivation at the runner's committed names means the runner does
    not return [None].  The plan is §8c.3's — ONE induction per judgement,
    on the ORDER, inverting the `a_*` derivation at each level — and the
    runners' unfolding equations (§8c.4) are what make the dispatch
    analysable at all.

    §1 opens the file with the ENTRY-POINT EXHIBIT: the AT-Unit branch at
    infer mode, end to end, through every layer this campaign depends on —
    [simp e_typing_impl] (the derived clause equation), the [e_sub_impl]
    wrapper, [simp e_sub_call_impl] (the tagged block's §8c.4 equation),
    the term-level dispatch reducing at concrete mode/shape, and
    [pskl_readback] computing.  ⚙ No [vm_compute]/[Eval] can do this: the
    runners recurse on a Qed-opaque totality proof, so plain reduction is
    stuck by design — the equations are quantified over the domain proof,
    which is exactly why the chain goes through (§8c.3's "insensitive to
    which domain proof was supplied").

    The check-mode twin runs one layer deeper — SI-Check calls
    [e_consis_impl], so it additionally exercises the consistency block's
    §8c.4 equations ([simp e_consis_call_impl]; U-Unit answers).  It
    became provable the moment def_consis_impl.v flipped, and it is the
    end-to-end witness that ALL TWELVE runner blocks are now
    computationally analysable.

    ⭐ §2 is the campaign's FIRST LEVEL, CLOSED: completeness of the LOOK
    block's two runners ([e_lookeq_run_complete] /
    [e_looksub_run_complete]) — an [a_*] derivation whose inputs the
    supply covers means the runner does not return [None].  The coverage
    premise is the ONLY hypothesis beyond the derivation: the e-side
    rules state freshness against the supply, so the runner's own fresh
    draws need nothing, and coverage is consumed exactly at the
    transposition steps (and re-established trivially at every recursive
    call).  §2's structure — hand strong induction on the order, the
    runner-dispatch case bash through [simp], one swap per binder row —
    is the template every level above copies (§8c.6).

    ⭐ §3 and §4 CLOSE the SOLVE level, both layers
    ([e_solve_eq_run_complete] / [e_solve_sub_run_complete]): the arrow
    rows thread the CONTEXT, so the motive carries the derivation's
    context separately, related to the runner's by [flex_agree] on the
    inputs' variables (§3's banner).  §4 additionally pays the sub
    dispatch's LEFT-first priorities with the two reorder lemmas
    ([a_solve_sub_tophole_l_first] / [a_solve_sub_forall_l_first] — the
    latter split into a fixed-context HOIST and a sanitizing wrapper,
    §4's banner). *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_ln.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_tag.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_dec.
Require Import src.frost.ext_algo.prop_dec.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_sub.
Require Import src.frost.ext_algo.def_order.
Require Import src.frost.ext_algo.prop_termination.
Require Import src.frost.ext_algo.def_look_impl.
Require Import src.frost.ext_algo.prop_look.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.algo.sub.look.prop_rsubst.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_guess_impl.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_solve_impl.
Require Import src.frost.ext_algo.prop_solve.
Require Import src.frost.ext_algo.prop_guess.
Require Import src.frost.ext_algo.prop_solve_det.
Require Import src.frost.ext_algo.prop_look_equiv.
Require Import src.frost.ext_algo.def_consis_impl.
Require Import src.frost.ext_algo.def_sub_impl.
Require Import src.frost.ext_algo.def_pat_impl.
Require Import src.frost.ext_algo.def_typing_impl.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The entry-point exhibit: AT-Unit, infer mode                      *)
(* ===================================================================== *)

Lemma e_typing_run_complete_unit_infer : forall S0,
  e_typing_run S0 mode_ti nil pskl_hole exp_unit
  = Some (mk_typing_result S0 nil ptyp_unit).
Proof.
  intros. unfold e_typing_run.
  simp e_typing_impl.
  cbn.
  unfold e_sub_impl.
  simp e_sub_call_impl.
  cbn.
  reflexivity.
Qed.

(** The check-mode twin, at the paper's own pattern shape [⌈unit⌉]: one
    layer deeper — SI-Check runs the consistency block, whose U-Unit row
    answers. *)
Lemma e_typing_run_complete_unit_check : forall S0,
  e_typing_run S0 mode_tc nil (ptyp_to_pskl ptyp_unit) exp_unit
  = Some (mk_typing_result S0 nil ptyp_unit).
Proof.
  intros. unfold e_typing_run.
  simp e_typing_impl.
  cbn.
  unfold e_sub_impl.
  simp e_sub_call_impl.
  cbn.
  unfold e_consis_impl.
  simp e_consis_call_impl.
  cbn.
  reflexivity.
Qed.

(* ===================================================================== *)
(*  §2  The LOOK block — completeness of both runners (§8c.3, level 1)    *)
(*                                                                        *)
(*  §2a  Hand STRONG-INDUCTION principles for the two orders.  ⚠️ The     *)
(*       auto [_ind] is unusable: the Arrow premise nests its recursive    *)
(*       order under a conjunction, and Coq generates no IH through [/\].  *)
(*       So each order gets ONE hand [fix] with an abstract motive, every  *)
(*       premise doubled with its motive companion — the [Acc_inv]         *)
(*       pattern of the §8c.4 injections ([e_sub_order_to_call]), and the  *)
(*       reusable idiom for EVERY order of this campaign.                  *)
(*  §2b  The transposition kit: a binder-row premise, opened at the        *)
(*       rule's own witness, MOVES to the runner's committed name by ONE   *)
(*       swap ([a_looksub_lookeq_swap]); the outputs are requantified      *)
(*       EXISTENTIALLY, which is why — unlike [a_lookeq_forall_move] —     *)
(*       no freshness for [Ξ]/[𝒞] is owed.  Plus the one rule-overlap      *)
(*       fact the sub layer needs: at a ghost-free ∀ target the runner     *)
(*       commits LS-ForallR, so a ForallL/UnivGhostL-rooted derivation     *)
(*       must REORDER — [a_looksub_forall_r_first].                        *)
(*  §2c  The two inductions themselves, walking the RUNNER's dispatch      *)
(*       through the §8c.4 equations ([simp]; never reduction — the        *)
(*       domain argument is Qed-opaque), inverting the [a_*] derivation    *)
(*       only to feed the recursive branches.                              *)
(*                                                                        *)
(*  ⚙ The [a_*]-side §2b facts live here, not in frost/, only because     *)
(*  this campaign leaves frost/ alone (the [ftvar_in_a_cstrs] precedent,   *)
(*  def_look.v); if a frost-side consumer appears, move them to            *)
(*  algo/sub/prop_looksub.v beside the [_move] family.                     *)
(* ===================================================================== *)

Set Implicit Arguments.

(* --------------------------------------------------------------------- *)
(*  §2a  Strong induction for [e_lookeq_order] / [e_looksub_order]        *)
(* --------------------------------------------------------------------- *)

Section e_lookeq_order_sind.

Variable Qe : supply -> aenv -> atom -> pskl -> pskl -> Prop.

Hypothesis Hstep : forall S0 Θ α P P',
    (* LE-Arrow — order premise, then its motive companion *)
    (forall P1 P2 P1' P2',
       P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       e_lookeq_order S0 Θ α P1 P1'
       /\ (forall S1 Ξ1 C1,
             {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
             e_lookeq_order S1 Θ α P2 P2')) ->
    (forall P1 P2 P1' P2',
       P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       Qe S0 Θ α P1 P1'
       /\ (forall S1 Ξ1 C1,
             {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
             Qe S1 Θ α P2 P2')) ->
    (* LE-ForallInh *)
    (forall Q Q',
       P = pskl_all_syn Q -> P' = pskl_all_syn Q' ->
       e_lookeq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))) ->
    (forall Q Q',
       P = pskl_all_syn Q -> P' = pskl_all_syn Q' ->
       Qe (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))) ->
    (* LE-ForallSyn *)
    (forall Q Q',
       P = pskl_all_syn Q -> P' = pskl_tophole Q' ->
       e_lookeq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
         (pskl_tophole Q')) ->
    (forall Q Q',
       P = pskl_all_syn Q -> P' = pskl_tophole Q' ->
       Qe (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
         (pskl_tophole Q')) ->
    (* LE-UnivGhost *)
    (forall Q Q',
       P = pskl_tophole Q -> P' = pskl_tophole Q' ->
       e_lookeq_order S0 Θ α Q Q') ->
    (forall Q Q',
       P = pskl_tophole Q -> P' = pskl_tophole Q' ->
       Qe S0 Θ α Q Q') ->
    (* LE-UnivGhost1 *)
    (forall Q Q',
       P = pskl_tophole Q -> P' = pskl_all_syn Q' ->
       e_lookeq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (pskl_tophole Q)
         (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))) ->
    (forall Q Q',
       P = pskl_tophole Q -> P' = pskl_all_syn Q' ->
       Qe (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (pskl_tophole Q)
         (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))) ->
    (* LE-UnivGhost2 *)
    (forall Q,
       P = pskl_tophole Q ->
       e_lookeq_order S0 Θ α Q P') ->
    (forall Q,
       P = pskl_tophole Q ->
       Qe S0 Θ α Q P') ->
    (* LE-UnivGhostR *)
    (forall Q',
       P' = pskl_tophole Q' ->
       e_lookeq_order S0 Θ α P Q') ->
    (forall Q',
       P' = pskl_tophole Q' ->
       Qe S0 Θ α P Q') ->
    Qe S0 Θ α P P'.

Fixpoint e_lookeq_order_sind S0 Θ α P P'
    (H : e_lookeq_order S0 Θ α P P') {struct H} : Qe S0 Θ α P P' :=
  match H in e_lookeq_order S0' Θ' α' Pa Pb return Qe S0' Θ' α' Pa Pb with
  | e_lookeq_order__intro _ _ _ _ _ p1 p2 p3 p4 p5 p6 p7 =>
      Hstep
        p1
        (fun P1 P2 P1' P2' e1 e2 =>
           match p1 P1 P2 P1' P2' e1 e2 with
           | conj Ha Hb =>
               conj (e_lookeq_order_sind Ha)
                    (fun S1 Ξ1 C1 Hrun =>
                       e_lookeq_order_sind (Hb S1 Ξ1 C1 Hrun))
           end)
        p2
        (fun Q Q' e1 e2 => e_lookeq_order_sind (p2 Q Q' e1 e2))
        p3
        (fun Q Q' e1 e2 => e_lookeq_order_sind (p3 Q Q' e1 e2))
        p4
        (fun Q Q' e1 e2 => e_lookeq_order_sind (p4 Q Q' e1 e2))
        p5
        (fun Q Q' e1 e2 => e_lookeq_order_sind (p5 Q Q' e1 e2))
        p6
        (fun Q e1 => e_lookeq_order_sind (p6 Q e1))
        p7
        (fun Q' e1 => e_lookeq_order_sind (p7 Q' e1))
  end.

End e_lookeq_order_sind.

Section e_looksub_order_sind.

Variable Qs : supply -> aenv -> atom -> mode -> pskl -> pskl -> Prop.

Hypothesis Hstep : forall S0 Θ α m P P',
    (* LS-Check — the drop into the (already-closed) eq layer *)
    (m = mode_tc -> e_lookeq_order S0 Θ α P P') ->
    (* LS-ForallR *)
    (forall B,
       m = mode_tc -> P' = pskl_all_syn B ->
       e_looksub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc P
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))) ->
    (forall B,
       m = mode_tc -> P' = pskl_all_syn B ->
       Qs (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc P
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))) ->
    (* LS-Arrow — the eq-order sibling stays as-is; only the recursive
       looksub half gets a companion *)
    (forall m' P1 P2 P1' P2',
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       e_lookeq_order S0 Θ α P1 P1'
       /\ (forall S1 Ξ1 C1,
             {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
             e_looksub_order S1 Θ α m' P2 P2')) ->
    (forall m' P1 P2 P1' P2',
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       forall S1 Ξ1 C1,
         {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
         Qs S1 Θ α m' P2 P2') ->
    (* LS-ForallL *)
    (forall Q,
       P = pskl_all_syn Q ->
       e_looksub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α m
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P') ->
    (forall Q,
       P = pskl_all_syn Q ->
       Qs (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α m
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P') ->
    (* LS-UnivGhostL *)
    (forall Q,
       P = pskl_tophole Q ->
       e_looksub_order S0 Θ α m Q P') ->
    (forall Q,
       P = pskl_tophole Q ->
       Qs S0 Θ α m Q P') ->
    Qs S0 Θ α m P P'.

Fixpoint e_looksub_order_sind S0 Θ α m P P'
    (H : e_looksub_order S0 Θ α m P P') {struct H} : Qs S0 Θ α m P P' :=
  match H in e_looksub_order S0' Θ' α' m' Pa Pb
        return Qs S0' Θ' α' m' Pa Pb with
  | e_looksub_order__intro _ _ _ _ _ _ pck pfr par pfl pug =>
      Hstep
        pck
        pfr
        (fun B e1 e2 => e_looksub_order_sind (pfr B e1 e2))
        par
        (fun m' P1 P2 P1' P2' e1 e2 e3 S1 Ξ1 C1 Hrun =>
           e_looksub_order_sind
             (match par m' P1 P2 P1' P2' e1 e2 e3 with
              | conj _ Hb => Hb
              end S1 Ξ1 C1 Hrun))
        pfl
        (fun Q e1 => e_looksub_order_sind (pfl Q e1))
        pug
        (fun Q e1 => e_looksub_order_sind (pug Q e1))
  end.

End e_looksub_order_sind.

(* --------------------------------------------------------------------- *)
(*  §2b  The transposition kit: ONE swap moves a binder-row premise from  *)
(*  the rule's own witness [b] to the runner's committed name [β].  The   *)
(*  outputs are requantified existentially — the completeness motive is    *)
(*  ∀ [Ξ] [𝒞], so nothing about them needs preserving, and the swap        *)
(*  therefore owes freshness only for the INPUTS, which the rule's own     *)
(*  side condition (for [b]) and the coverage premise (for [β]) supply.    *)
(* --------------------------------------------------------------------- *)

(** Both sides opened (LE-ForallInh). *)
Lemma a_lookeq_rebind : forall Θ α P P' Ξ C b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f b)) ∼[ α ]
     (open_pskl_wrt_pskl P' (pskl_var_f b)) ⤳ Ξ ⨾ C }}a ->
  b `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') ->
  β `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') ->
  exists Ξ' C',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
       (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ' ⨾ C' }}a.
Proof.
  intros * Hp Hb Hβ.
  destruct (β == b) as [-> | Hne]; [ exists Ξ, C; exact Hp | ].
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ Θ).
  { simpl. rewrite swap_atom_l.
    rewrite (swap_aenv_fresh_id b β Θ) by (clear - Hb Hβ; fsetdec).
    reflexivity. }
  pose proof (proj2 (a_looksub_lookeq_swap b β) _ _ _ _ _ _ Hp) as Hs.
  rewrite Hctx in Hs.
  rewrite (swap_atom_other b β α) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite ! swap_pskl_open_var in Hs.
  rewrite ! swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β P) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β P') in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_cstrs b β C). exact Hs.
Qed.
Arguments a_lookeq_rebind {Θ α P P' Ξ C b β}.

(** Only the SUBJECT opened, target fixed (LE-ForallSyn's shape). *)
Lemma a_lookeq_rebind_l : forall Θ α P Pt Ξ C b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f b)) ∼[ α ]
     Pt ⤳ Ξ ⨾ C }}a ->
  b `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Pt) ->
  β `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Pt) ->
  exists Ξ' C',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
       Pt ⤳ Ξ' ⨾ C' }}a.
Proof.
  intros * Hp Hb Hβ.
  destruct (β == b) as [-> | Hne]; [ exists Ξ, C; exact Hp | ].
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ Θ).
  { simpl. rewrite swap_atom_l.
    rewrite (swap_aenv_fresh_id b β Θ) by (clear - Hb Hβ; fsetdec).
    reflexivity. }
  pose proof (proj2 (a_looksub_lookeq_swap b β) _ _ _ _ _ _ Hp) as Hs.
  rewrite Hctx in Hs.
  rewrite (swap_atom_other b β α) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite swap_pskl_open_var in Hs.
  rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β P) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β Pt) in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_cstrs b β C). exact Hs.
Qed.
Arguments a_lookeq_rebind_l {Θ α P Pt Ξ C b β}.

(** Only the TARGET opened, subject fixed (LE-UnivGhost1's shape). *)
Lemma a_lookeq_rebind_r : forall Θ α Ps P' Ξ C b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ Ps ∼[ α ]
     (open_pskl_wrt_pskl P' (pskl_var_f b)) ⤳ Ξ ⨾ C }}a ->
  b `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Ps ∪ ftvar_in_pskl P') ->
  β `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Ps ∪ ftvar_in_pskl P') ->
  exists Ξ' C',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ Ps ∼[ α ]
       (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ' ⨾ C' }}a.
Proof.
  intros * Hp Hb Hβ.
  destruct (β == b) as [-> | Hne]; [ exists Ξ, C; exact Hp | ].
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ Θ).
  { simpl. rewrite swap_atom_l.
    rewrite (swap_aenv_fresh_id b β Θ) by (clear - Hb Hβ; fsetdec).
    reflexivity. }
  pose proof (proj2 (a_looksub_lookeq_swap b β) _ _ _ _ _ _ Hp) as Hs.
  rewrite Hctx in Hs.
  rewrite (swap_atom_other b β α) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite swap_pskl_open_var in Hs.
  rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β Ps) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β P') in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_cstrs b β C). exact Hs.
Qed.
Arguments a_lookeq_rebind_r {Θ α Ps P' Ξ C b β}.

(** The looksub twins — LS-ForallL's shape (subject opened, any mode) and
    LS-ForallR's (target opened). *)
Lemma a_looksub_rebind_l : forall Θ α m P Pt Ξ C b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f b))
     ≼[ α , m ] Pt ⤳ Ξ ⨾ C }}a ->
  b `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Pt) ->
  β `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Pt) ->
  exists Ξ' C',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl P (pskl_var_f β))
       ≼[ α , m ] Pt ⤳ Ξ' ⨾ C' }}a.
Proof.
  intros * Hp Hb Hβ.
  destruct (β == b) as [-> | Hne]; [ exists Ξ, C; exact Hp | ].
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ Θ).
  { simpl. rewrite swap_atom_l.
    rewrite (swap_aenv_fresh_id b β Θ) by (clear - Hb Hβ; fsetdec).
    reflexivity. }
  pose proof (proj1 (a_looksub_lookeq_swap b β) _ _ _ _ _ _ _ Hp) as Hs.
  rewrite Hctx in Hs.
  rewrite (swap_atom_other b β α) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite swap_pskl_open_var in Hs.
  rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β P) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β Pt) in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_cstrs b β C). exact Hs.
Qed.
Arguments a_looksub_rebind_l {Θ α m P Pt Ξ C b β}.

Lemma a_looksub_rebind_r : forall Θ α m Ps P' Ξ C b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ Ps ≼[ α , m ]
     (open_pskl_wrt_pskl P' (pskl_var_f b)) ⤳ Ξ ⨾ C }}a ->
  b `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Ps ∪ ftvar_in_pskl P') ->
  β `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Ps ∪ ftvar_in_pskl P') ->
  exists Ξ' C',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ Ps ≼[ α , m ]
       (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ' ⨾ C' }}a.
Proof.
  intros * Hp Hb Hβ.
  destruct (β == b) as [-> | Hne]; [ exists Ξ, C; exact Hp | ].
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ Θ).
  { simpl. rewrite swap_atom_l.
    rewrite (swap_aenv_fresh_id b β Θ) by (clear - Hb Hβ; fsetdec).
    reflexivity. }
  pose proof (proj1 (a_looksub_lookeq_swap b β) _ _ _ _ _ _ _ Hp) as Hs.
  rewrite Hctx in Hs.
  rewrite (swap_atom_other b β α) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite swap_pskl_open_var in Hs.
  rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β Ps) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β P') in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_cstrs b β C). exact Hs.
Qed.
Arguments a_looksub_rebind_r {Θ α m Ps P' Ξ C b β}.

(** ⭐ THE ONE RULE-OVERLAP FACT the sub layer needs.  At mode TC with a
    ghost-free ∀ target, THREE rules can end a derivation — LS-ForallR,
    LS-ForallL (∀ subject), LS-UnivGhostL (⫯ subject) — and the runner
    commits to ForallR (the reference implementation's priority,
    type.ml:663).  So a derivation rooted in either LEFT rule must be
    REORDERED into the ForallR-premise shape the runner recurses on.
    Induction on the derivation; the left-rule cases re-derive their
    premise at the opened target (IH), then swap the two binders back into
    place — the swaps come AFTER the IH, so plain structural induction
    suffices, and [a_looksub_ctx_exchange] (the look judgement reads its
    context only through freshness) glues the two entries.  The outputs
    are existential for the §2b reason. *)
Lemma a_looksub_forall_r_first : forall Θ α m P P' Ξ C,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  forall B β, P' = pskl_all_syn B -> m = mode_tc ->
  β `notin` add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B) ->
  exists Ξ' C',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ P ≼[ α , mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ' ⨾ C' }}a.
Proof.
  intros Θ α m P P' Ξ C Hd.
  induction Hd; intros B0 βr HeqP' Heqm Hβ; try discriminate.
  - (* LS-Var — answer by LS-Var at the opened target *)
    subst P. do 2 eexists. apply a_looksub__var.
  - (* LS-Absent *)
    subst P'. do 2 eexists. apply a_looksub__absent. assumption.
  - (* LS-Check — a ∀ target is never guarded *)
    subst B. exfalso.
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  - (* LS-ForallR — move the rule's witness to [βr] *)
    injection HeqP' as ->.
    match goal with
    | Hfr : ?b `notin` add α _,
      Hp : a_looksub ((?b ~ abind_tvar) ++ Θ) α mode_tc _ _ _ _ |- _ =>
        destruct (a_looksub_rebind_r Hp Hfr Hβ) as [Ξ' [C' E]]
    end.
    exists Ξ', C'. exact E.
  - (* LS-ForallL — re-derive the premise at the opened target (IH), then
       swap the two binders into place *)
    subst m. subst P'. simpl in Hβ.
    match goal with
    | Hfr : ?b `notin` add α _,
      Hp : a_looksub ((?b ~ abind_tvar) ++ Θ) α mode_tc _ _ _ _,
      IH : forall _ _, _ -> _ -> _ -> _ |- _ =>
        simpl in Hfr;
        (* δ: the IH's target opener, fresh for everything in sight *)
        destruct (atom_fresh (add α (add βr (add b
                    (ftvar_in_aenv Θ ∪ ftvar_in_pskl P
                       ∪ ftvar_in_pskl B0))))) as [δ Hδ];
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b))
          as HupPb;
        assert (Hδ' : δ `notin`
                  add α (ftvar_in_aenv ((b ~ abind_tvar) ++ Θ)
                           ∪ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f b))
                           ∪ ftvar_in_pskl B0))
          by (clear - Hδ HupPb; simpl in *; fsetdec);
        destruct (IH B0 δ eq_refl eq_refl Hδ') as [Ξ1 [C1 E1]];
        apply a_looksub_ctx_exchange in E1;
        (* γ': the final ForallL witness *)
        destruct (atom_fresh (add α (add βr (add b (add δ
                    (ftvar_in_aenv Θ ∪ ftvar_in_pskl P
                       ∪ ftvar_in_pskl B0)))))) as [γ' Hγ'];
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B0 (pskl_var_f δ))
          as HupBδ;
        assert (Hf1 : b `notin`
                  add α (ftvar_in_aenv ((δ ~ abind_tvar) ++ Θ)
                           ∪ ftvar_in_pskl P
                           ∪ ftvar_in_pskl (open_pskl_wrt_pskl B0 (pskl_var_f δ))))
          by (clear - Hfr Hδ HupBδ; simpl in *; fsetdec);
        assert (Hf2 : γ' `notin`
                  add α (ftvar_in_aenv ((δ ~ abind_tvar) ++ Θ)
                           ∪ ftvar_in_pskl P
                           ∪ ftvar_in_pskl (open_pskl_wrt_pskl B0 (pskl_var_f δ))))
          by (clear - Hγ' HupBδ; simpl in *; fsetdec);
        destruct (a_looksub_rebind_l E1 Hf1 Hf2) as [Ξ2 [C2 E2]];
        apply a_looksub_ctx_exchange in E2;
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f γ'))
          as HupPγ;
        assert (Hf3 : δ `notin`
                  add α (ftvar_in_aenv ((γ' ~ abind_tvar) ++ Θ)
                           ∪ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f γ'))
                           ∪ ftvar_in_pskl B0))
          by (clear - Hδ Hγ' HupPγ; simpl in *; fsetdec);
        assert (Hf4 : βr `notin`
                  add α (ftvar_in_aenv ((γ' ~ abind_tvar) ++ Θ)
                           ∪ ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f γ'))
                           ∪ ftvar_in_pskl B0))
          by (clear - Hβ Hγ' HupPγ; simpl in *; fsetdec);
        destruct (a_looksub_rebind_r E2 Hf3 Hf4) as [Ξ3 [C3 E3]];
        apply a_looksub_ctx_exchange in E3;
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B0 (pskl_var_f βr))
          as HupBβ;
        exists Ξ3, C3;
        apply a_looksub__forall_l with (β := γ');
        [ clear - Hγ' HupBβ; simpl in *; fsetdec | exact E3 ]
    end.
  - (* LS-UnivGhostL — strip, IH, re-strip *)
    subst m. simpl in Hβ.
    match goal with
    | IH : forall _ _, _ -> _ -> _ -> _ |- _ =>
        destruct (IH B0 βr HeqP' eq_refl Hβ) as [Ξ' [C' E]]
    end.
    exists Ξ', C'. apply a_looksub__univ_ghost_l. exact E.
Qed.
Arguments a_looksub_forall_r_first {Θ α m P P' Ξ C} _ {B β}.

(* --------------------------------------------------------------------- *)
(*  §2c  The completeness inductions                                      *)
(*                                                                        *)
(*  Each walks the RUNNER's dispatch: [simp] fires the branch's §8c.4     *)
(*  equation, the branch's decision tests hand over hypotheses, and the   *)
(*  [a_*] derivation is inverted only to FEED the recursive calls — a     *)
(*  branch may answer by a different rule than the derivation's root      *)
(*  (LE-Absent answers anything the looked-for variable misses), and      *)
(*  [Some] is [Some].                                                     *)
(* --------------------------------------------------------------------- *)

Local Ltac case_test :=
  match goal with
  | |- context [ sumbool_of_bool ?b ] =>
      let Hm := fresh "Htest" in
      destruct (sumbool_of_bool b) as [Hm | Hm]
  end.

(** Close an impossible inversion case: the branch's decision tests
    contradict the rule's own side conditions. *)
Local Ltac look_absurd :=
  solve [ discriminate
        | match goal with
          | Hm : mem ?a ?s = true, Hn : ?a `notin` ?s |- _ =>
              exfalso; apply Hn; apply mem_true_in; exact Hm
          end
        | match goal with
          | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
          | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
          | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
          | Hg : nonghost_pskl (pskl_tophole _) |- _ => inversion Hg
          | Hg : nonghost_pskl pskl_hole |- _ => inversion Hg
          end
        | match goal with
          | Hck : ghost_free_ck ?P = false, Hg : pskl_ghost_free ?P |- _ =>
              apply ghost_free_ck_complete in Hg; congruence
          end
        | match goal with
          | Hck : guarded_shape_ck ?P && ghost_free_ck ?P = false,
            Hg : guarded_pskl ?P, Hgf : pskl_ghost_free ?P |- _ =>
              apply guarded_shape_ck_complete in Hg;
              apply ghost_free_ck_complete in Hgf;
              rewrite Hg, Hgf in Hck; discriminate
          end
        (* the sub-solve level's Check clause tests a 3-conjunct *)
        | match goal with
          | Hck : guarded_shape_ck ?P && guarded_shape_ck ?Q
                  && ghost_free_ck ?Q = false,
            HgP : guarded_pskl ?P, HgQ : guarded_pskl ?Q,
            Hgf : pskl_ghost_free ?Q |- _ =>
              apply guarded_shape_ck_complete in HgP;
              apply guarded_shape_ck_complete in HgQ;
              apply ghost_free_ck_complete in Hgf;
              rewrite HgP, HgQ, Hgf in Hck; discriminate
          end
        | match goal with
          | Hlc : lc_pskl (pskl_var_b _) |- _ => inversion Hlc
          end ].

(** Discharge the branch's recursive [e_lookeq_impl] call: the IH (or the
    eq layer's finished lemma) says it cannot be [None], so it is [Some],
    and the branch continues behind it. *)
Local Ltac kill_eq_call IH Hder Hcv r Hr :=
  match goal with
  | |- context [ e_lookeq_impl ?S ?T ?A ?p ?p' ?hp ?hp' ?h ] =>
      let Hne := fresh "Hne" in
      let Hcl := fresh "Hcl" in
      assert (Hne : e_lookeq_impl S T A p p' hp hp' h <> None)
        by (exact (IH hp hp' h _ _ Hder Hcv));
      destruct (e_lookeq_impl S T A p p' hp hp' h)
        as [ [r Hr] | ] eqn:Hcl;
      [ cbv beta iota; clear Hne Hcl | exact (False_ind _ (Hne eq_refl)) ]
  end.

Lemma e_lookeq_impl_complete : forall S0 Θ α P P'
    (HP : lc_pskl P) (HP' : lc_pskl P')
    (H : e_lookeq_order S0 Θ α P P') Ξ C,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
  ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0 ->
  e_lookeq_impl S0 Θ α P P' HP HP' H <> None.
Proof.
  intros S0 Θ α P P'.
  apply (e_lookeq_order_sind
           (fun S0 Θ α P P' =>
              forall (HP : lc_pskl P) (HP' : lc_pskl P')
                     (H : e_lookeq_order S0 Θ α P P') Ξ C,
                {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
                ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P
                  ∪ ftvar_in_pskl P' [<=] S0 ->
                e_lookeq_impl S0 Θ α P P' HP HP' H <> None));
    [ | apply e_lookeq_order_total ].
  clear S0 Θ α P P'.
  intros S0 Θ α P P' p1 q1 p2 q2 p3 q3 p4 q4 p5 q5 p6 q6 p7 q7
         HP HP' H Ξ C Hd Hcov.
  destruct P as [ | n | β | P1 P2 | Q | | Q ].
  - (* unit — LE-Absent *)
    simp e_lookeq_impl. discriminate.
  - (* var_b — LE-Absent *)
    simp e_lookeq_impl. discriminate.
  - (* var_f — LE-Var / LE-Absent *)
    simp e_lookeq_impl. destruct (α == β); discriminate.
  - (* subject arrow *)
    destruct P' as [ | n' | β' | P1' P2' | Q' | | Q' ].
    + (* unit — no rule fits *)
      simp e_lookeq_impl. case_test;
        [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
    + (* var_b — no lc *)
      simp e_lookeq_impl. case_test; [ inversion HP' | discriminate ].
    + (* var_f — LE-FlexR / LE-Absent, both answer *)
      simp e_lookeq_impl. case_test; discriminate.
    + (* arrow — LE-Arrow *)
      simp e_lookeq_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      destruct (q1 P1 P2 P1' P2' eq_refl eq_refl) as [IH1 IH2].
      match goal with
      | Hda : a_lookeq Θ α P1 P1' _ _ |- _ => rename Hda into HD1
      end.
      match goal with
      | Hdb : a_lookeq Θ α P2 P2' _ _ |- _ => rename Hdb into HD2
      end.
      assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P1
                       ∪ ftvar_in_pskl P1' [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_eq_call IH1 HD1 Hcv1 r1 Hr1.
      unfold lookeq_spec in Hr1.
      pose proof (e_lookeq_supply_grows Hr1) as Hgrow.
      specialize (IH2 _ _ _ Hr1).
      assert (Hcv2 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P2
                       ∪ ftvar_in_pskl P2' [<=] lk_supply r1)
        by (clear - Hcov Hgrow; simpl in *; fsetdec).
      kill_eq_call IH2 HD2 Hcv2 r2 Hr2.
      discriminate.
    + (* all_syn — no rule fits *)
      simp e_lookeq_impl. case_test;
        [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
    + (* hole — LE-Vacuous *)
      simp e_lookeq_impl. discriminate.
    + (* tophole — LE-UnivGhostR *)
      simp e_lookeq_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_lookeq Θ α (pskl_arrow P1 P2) Q' _ _ |- _ =>
          rename Hp0 into HPREM
      end.
      pose proof (q7 Q' eq_refl) as IH7.
      assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }}
                       ∪ ftvar_in_pskl (pskl_arrow P1 P2)
                       ∪ ftvar_in_pskl Q' [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_eq_call IH7 HPREM Hcv1 r1 Hr1.
      discriminate.
  - (* subject all_syn *)
    destruct P' as [ | n' | β' | P1' P2' | Q' | | Q' ].
    + (* unit — no rule fits *)
      simp e_lookeq_impl. case_test;
        [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
    + (* var_b *)
      simp e_lookeq_impl. case_test; [ inversion HP' | discriminate ].
    + (* var_f — LE-FlexR / LE-Absent *)
      simp e_lookeq_impl. case_test; discriminate.
    + (* arrow — no rule fits *)
      simp e_lookeq_impl. case_test;
        [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
    + (* all_syn — LE-ForallInh: one swap to the committed name *)
      simp e_lookeq_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` add α _,
        Hp0 : a_lookeq ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ |- _ =>
          rename Hfr0 into HFR; rename Hp0 into HPREM
      end.
      assert (HFRESH : supply_fresh S0 `notin`
                add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q ∪ ftvar_in_pskl Q'))
        by (pose proof (supply_fresh_notin S0) as Hsf;
            clear - Hcov Hsf; simpl in *; fsetdec).
      destruct (a_lookeq_rebind HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
      pose proof (q2 Q Q' eq_refl eq_refl) as IHf.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q
                    (pskl_var_f (supply_fresh S0))) as Hup1.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q'
                    (pskl_var_f (supply_fresh S0))) as Hup2.
      assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                       ∪ {{ α }}
                       ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q
                            (pskl_var_f (supply_fresh S0)))
                       ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q'
                            (pskl_var_f (supply_fresh S0)))
                       [<=] add (supply_fresh S0) S0)
        by (clear - Hcov Hup1 Hup2; simpl in *; fsetdec).
      kill_eq_call IHf HP2 Hcv1 r1 Hr1.
      discriminate.
    + (* hole — LE-Vacuous *)
      simp e_lookeq_impl. discriminate.
    + (* tophole — LE-ForallSyn: subject side opens, target fixed *)
      simp e_lookeq_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` add α _,
        Hp0 : a_lookeq ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ |- _ =>
          rename Hfr0 into HFR; rename Hp0 into HPREM
      end.
      assert (HFRESH : supply_fresh S0 `notin`
                add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q ∪ ftvar_in_pskl Q'))
        by (pose proof (supply_fresh_notin S0) as Hsf;
            clear - Hcov Hsf; simpl in *; fsetdec).
      destruct (a_lookeq_rebind_l HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
      pose proof (q3 Q Q' eq_refl eq_refl) as IHf.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q
                    (pskl_var_f (supply_fresh S0))) as Hup1.
      assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                       ∪ {{ α }}
                       ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q
                            (pskl_var_f (supply_fresh S0)))
                       ∪ ftvar_in_pskl (pskl_tophole Q')
                       [<=] add (supply_fresh S0) S0)
        by (clear - Hcov Hup1; simpl in *; fsetdec).
      kill_eq_call IHf HP2 Hcv1 r1 Hr1.
      discriminate.
  - (* subject hole — LE-Absent *)
    simp e_lookeq_impl. discriminate.
  - (* subject tophole *)
    destruct P' as [ | n' | β' | P1' P2' | Q' | | Q' ].
    + (* unit — LE-UnivGhost2 *)
      simp e_lookeq_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_lookeq Θ α Q pskl_unit _ _ |- _ => rename Hp0 into HPREM
      end.
      pose proof (q6 Q eq_refl) as IH6.
      assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                       ∪ ftvar_in_pskl pskl_unit [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_eq_call IH6 HPREM Hcv1 r1 Hr1.
      discriminate.
    + (* var_b *)
      simp e_lookeq_impl. case_test; [ inversion HP' | discriminate ].
    + (* var_f — LE-FlexR / LE-Absent *)
      simp e_lookeq_impl. case_test; discriminate.
    + (* arrow — LE-UnivGhost2 *)
      simp e_lookeq_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_lookeq Θ α Q (pskl_arrow P1' P2') _ _ |- _ =>
          rename Hp0 into HPREM
      end.
      pose proof (q6 Q eq_refl) as IH6.
      assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                       ∪ ftvar_in_pskl (pskl_arrow P1' P2') [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_eq_call IH6 HPREM Hcv1 r1 Hr1.
      discriminate.
    + (* all_syn — LE-UnivGhost1: target side opens, subject fixed *)
      simp e_lookeq_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` add α _,
        Hp0 : a_lookeq ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ |- _ =>
          rename Hfr0 into HFR; rename Hp0 into HPREM
      end.
      assert (HFRESH : supply_fresh S0 `notin`
                add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q ∪ ftvar_in_pskl Q'))
        by (pose proof (supply_fresh_notin S0) as Hsf;
            clear - Hcov Hsf; simpl in *; fsetdec).
      destruct (a_lookeq_rebind_r HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
      pose proof (q5 Q Q' eq_refl eq_refl) as IHf.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q'
                    (pskl_var_f (supply_fresh S0))) as Hup1.
      assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                       ∪ {{ α }}
                       ∪ ftvar_in_pskl (pskl_tophole Q)
                       ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q'
                            (pskl_var_f (supply_fresh S0)))
                       [<=] add (supply_fresh S0) S0)
        by (clear - Hcov Hup1; simpl in *; fsetdec).
      kill_eq_call IHf HP2 Hcv1 r1 Hr1.
      discriminate.
    + (* hole — LE-Vacuous *)
      simp e_lookeq_impl. discriminate.
    + (* tophole — LE-UnivGhost *)
      simp e_lookeq_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_lookeq Θ α Q Q' _ _ |- _ => rename Hp0 into HPREM
      end.
      pose proof (q4 Q Q' eq_refl eq_refl) as IH4.
      assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                       ∪ ftvar_in_pskl Q' [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_eq_call IH4 HPREM Hcv1 r1 Hr1.
      discriminate.
Qed.

(** ⭐ The eq layer's headline: a derivation at covered inputs means the
    RUNNER answers. *)
Lemma e_lookeq_run_complete : forall S0 Θ α P P' HP HP' Ξ C,
  {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
  ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0 ->
  e_lookeq_run S0 Θ α P P' HP HP' <> None.
Proof.
  intros * Hd Hcov. unfold e_lookeq_run.
  pose proof (e_lookeq_impl_complete HP HP'
                (e_lookeq_order_total S0 Θ α P P') Hd Hcov) as Hne.
  revert Hne.
  destruct (e_lookeq_impl S0 Θ α P P' HP HP'
              (e_lookeq_order_total S0 Θ α P P')) as [ [r Hr] | ];
    intros Hne.
  - discriminate.
  - exact (False_ind _ (Hne eq_refl)).
Qed.

(** The looksub twins of the two kill tactics: one for motive IHs (all
    arguments explicit), one dropping into the FINISHED eq lemma. *)
Local Ltac kill_sub_call IH Hder Hcv r Hr :=
  match goal with
  | |- context [ e_looksub_impl ?S ?T ?A ?M ?p ?p' ?hp ?hp' ?h ] =>
      let Hne := fresh "Hne" in
      let Hcl := fresh "Hcl" in
      assert (Hne : e_looksub_impl S T A M p p' hp hp' h <> None)
        by (exact (IH hp hp' h _ _ Hder Hcv));
      destruct (e_looksub_impl S T A M p p' hp hp' h)
        as [ [r Hr] | ] eqn:Hcl;
      [ cbv beta iota; clear Hne Hcl | exact (False_ind _ (Hne eq_refl)) ]
  end.

Local Ltac kill_eq_call_g Hder Hcv r Hr :=
  match goal with
  | |- context [ e_lookeq_impl ?S ?T ?A ?p ?p' ?hp ?hp' ?h ] =>
      let Hne := fresh "Hne" in
      let Hcl := fresh "Hcl" in
      assert (Hne : e_lookeq_impl S T A p p' hp hp' h <> None)
        by (exact (e_lookeq_impl_complete hp hp' h Hder Hcv));
      destruct (e_lookeq_impl S T A p p' hp hp' h)
        as [ [r Hr] | ] eqn:Hcl;
      [ cbv beta iota; clear Hne Hcl | exact (False_ind _ (Hne eq_refl)) ]
  end.

Lemma e_looksub_impl_complete : forall S0 Θ α m P P'
    (HP : lc_pskl P) (HP' : lc_pskl P')
    (H : e_looksub_order S0 Θ α m P P') Ξ C,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0 ->
  e_looksub_impl S0 Θ α m P P' HP HP' H <> None.
Proof.
  intros S0 Θ α m P P'.
  apply (e_looksub_order_sind
           (fun S0 Θ α m P P' =>
              forall (HP : lc_pskl P) (HP' : lc_pskl P')
                     (H : e_looksub_order S0 Θ α m P P') Ξ C,
                {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
                ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P
                  ∪ ftvar_in_pskl P' [<=] S0 ->
                e_looksub_impl S0 Θ α m P P' HP HP' H <> None));
    [ | apply e_looksub_order_total ].
  clear S0 Θ α m P P'.
  intros S0 Θ α m P P' pck pfr qfr par qar pfl qfl pug qug
         HP HP' H Ξ C Hd Hcov.
  destruct P as [ | n | β | P1 P2 | Q | | Q ].
  - (* unit — LS-Absent *)
    simp e_looksub_impl. discriminate.
  - (* var_b — LS-Absent *)
    simp e_looksub_impl. discriminate.
  - (* var_f — LS-Var / LS-Absent *)
    simp e_looksub_impl. destruct (α == β); discriminate.
  - (* subject arrow — the runner's dispatch splits on the mode *)
    destruct P' as [ | n' | β' | P1' P2' | B | | Q' ].
    + (* unit *)
      destruct m as [ | | m' ].
      * simp e_looksub_impl. case_test;
          [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
      * (* tc — LS-Check *)
        simp e_looksub_impl. case_test; [ | discriminate ]. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_lookeq Θ α (pskl_arrow P1 P2) pskl_unit _ _ |- _ =>
               rename Hp0 into HPREM
           end.
           assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }}
                            ∪ ftvar_in_pskl (pskl_arrow P1 P2)
                            ∪ ftvar_in_pskl pskl_unit [<=] S0)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_eq_call_g HPREM Hcv1 r1 Hr1. discriminate.
        -- exfalso; inversion Hd; subst; look_absurd.
      * simp e_looksub_impl. case_test;
          [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
    + (* var_b *)
      destruct m as [ | | m' ];
        simp e_looksub_impl; case_test; solve [ inversion HP' | discriminate ].
    + (* var_f *)
      destruct m as [ | | m' ].
      * simp e_looksub_impl. case_test;
          [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
      * simp e_looksub_impl. case_test; [ | discriminate ]. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_lookeq Θ α (pskl_arrow P1 P2) (pskl_var_f β') _ _ |- _ =>
               rename Hp0 into HPREM
           end.
           assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }}
                            ∪ ftvar_in_pskl (pskl_arrow P1 P2)
                            ∪ ftvar_in_pskl (pskl_var_f β') [<=] S0)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_eq_call_g HPREM Hcv1 r1 Hr1. discriminate.
        -- exfalso; inversion Hd; subst; look_absurd.
      * simp e_looksub_impl. case_test;
          [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
    + (* arrow *)
      destruct m as [ | | m' ].
      * simp e_looksub_impl. case_test;
          [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
      * (* tc — LS-Check (LS-Arrow is fn-only) *)
        simp e_looksub_impl. case_test; [ | discriminate ]. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_lookeq Θ α (pskl_arrow P1 P2) (pskl_arrow P1' P2') _ _
             |- _ => rename Hp0 into HPREM
           end.
           assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }}
                            ∪ ftvar_in_pskl (pskl_arrow P1 P2)
                            ∪ ftvar_in_pskl (pskl_arrow P1' P2') [<=] S0)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_eq_call_g HPREM Hcv1 r1 Hr1. discriminate.
        -- exfalso; inversion Hd; subst; look_absurd.
      * (* fn — LS-Arrow *)
        simp e_looksub_impl. case_test; [ | discriminate ].
        inversion Hd; subst; try look_absurd.
        match goal with
        | Hda : a_lookeq Θ α P1 P1' _ _ |- _ => rename Hda into HD1
        end.
        match goal with
        | Hdb : a_looksub Θ α m' P2 P2' _ _ |- _ => rename Hdb into HD2
        end.
        assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P1
                         ∪ ftvar_in_pskl P1' [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        kill_eq_call_g HD1 Hcv1 r1 Hr1.
        unfold lookeq_spec in Hr1.
        pose proof (e_lookeq_supply_grows Hr1) as Hgrow.
        pose proof (qar m' P1 P2 P1' P2' eq_refl eq_refl eq_refl
                      _ _ _ Hr1) as IH2.
        assert (Hcv2 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P2
                         ∪ ftvar_in_pskl P2' [<=] lk_supply r1)
          by (clear - Hcov Hgrow; simpl in *; fsetdec).
        kill_sub_call IH2 HD2 Hcv2 r2 Hr2. discriminate.
    + (* all_syn *)
      destruct m as [ | | m' ].
      * simp e_looksub_impl. case_test;
          [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
      * (* tc — LS-ForallR, via the reorder *)
        simp e_looksub_impl. case_test; [ | discriminate ]. case_test.
        -- assert (HFRESH : supply_fresh S0 `notin`
                     add α (ftvar_in_aenv Θ
                              ∪ ftvar_in_pskl (pskl_arrow P1 P2)
                              ∪ ftvar_in_pskl B))
             by (pose proof (supply_fresh_notin S0) as Hsf;
                 clear - Hcov Hsf; simpl in *; fsetdec).
           destruct (a_looksub_forall_r_first Hd eq_refl eq_refl HFRESH)
             as [Ξ2 [C2 HP2]].
           pose proof (qfr B eq_refl eq_refl) as IHf.
           pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                         (pskl_var_f (supply_fresh S0))) as Hup1.
           assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                            ∪ {{ α }}
                            ∪ ftvar_in_pskl (pskl_arrow P1 P2)
                            ∪ ftvar_in_pskl (open_pskl_wrt_pskl B
                                 (pskl_var_f (supply_fresh S0)))
                            [<=] add (supply_fresh S0) S0)
             by (clear - Hcov Hup1; simpl in *; fsetdec).
           kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
        -- exfalso; inversion Hd; subst; look_absurd.
      * simp e_looksub_impl. case_test;
          [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
    + (* hole — LS-Vacuous *)
      simp e_looksub_impl. discriminate.
    + (* tophole *)
      destruct m as [ | | m' ].
      * simp e_looksub_impl. case_test;
          [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
      * (* tc — the Check clause tests a ⫯ target, which is never guarded *)
        simp e_looksub_impl. case_test; [ | discriminate ]. case_test.
        -- match goal with
           | Ht : _ && _ = true |- _ => simpl in Ht; discriminate Ht
           end.
        -- exfalso; inversion Hd; subst; look_absurd.
      * simp e_looksub_impl. case_test;
          [ exfalso; inversion Hd; subst; look_absurd | discriminate ].
  - (* subject all_syn — LS-ForallL at every mode; ForallR first at a
       ghost-free ∀ target under tc *)
    destruct P' as [ | n' | β' | P1' P2' | B | | Q' ].
    + (* unit — LS-ForallL *)
      simp e_looksub_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` add α _,
        Hp0 : a_looksub ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ _ |- _ =>
          rename Hfr0 into HFR; rename Hp0 into HPREM
      end.
      assert (HFRESH : supply_fresh S0 `notin`
                add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q
                         ∪ ftvar_in_pskl pskl_unit))
        by (pose proof (supply_fresh_notin S0) as Hsf;
            clear - Hcov Hsf; simpl in *; fsetdec).
      destruct (a_looksub_rebind_l HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
      pose proof (qfl Q eq_refl) as IHf.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q
                    (pskl_var_f (supply_fresh S0))) as Hup1.
      assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                       ∪ {{ α }}
                       ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q
                            (pskl_var_f (supply_fresh S0)))
                       ∪ ftvar_in_pskl pskl_unit
                       [<=] add (supply_fresh S0) S0)
        by (clear - Hcov Hup1; simpl in *; fsetdec).
      kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
    + (* var_b *)
      simp e_looksub_impl. case_test; [ inversion HP' | discriminate ].
    + (* var_f — LS-ForallL *)
      simp e_looksub_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` add α _,
        Hp0 : a_looksub ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ _ |- _ =>
          rename Hfr0 into HFR; rename Hp0 into HPREM
      end.
      assert (HFRESH : supply_fresh S0 `notin`
                add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q
                         ∪ ftvar_in_pskl (pskl_var_f β')))
        by (pose proof (supply_fresh_notin S0) as Hsf;
            clear - Hcov Hsf; simpl in *; fsetdec).
      destruct (a_looksub_rebind_l HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
      pose proof (qfl Q eq_refl) as IHf.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q
                    (pskl_var_f (supply_fresh S0))) as Hup1.
      assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                       ∪ {{ α }}
                       ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q
                            (pskl_var_f (supply_fresh S0)))
                       ∪ ftvar_in_pskl (pskl_var_f β')
                       [<=] add (supply_fresh S0) S0)
        by (clear - Hcov Hup1; simpl in *; fsetdec).
      kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
    + (* arrow — LS-ForallL *)
      simp e_looksub_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` add α _,
        Hp0 : a_looksub ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ _ |- _ =>
          rename Hfr0 into HFR; rename Hp0 into HPREM
      end.
      assert (HFRESH : supply_fresh S0 `notin`
                add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q
                         ∪ ftvar_in_pskl (pskl_arrow P1' P2')))
        by (pose proof (supply_fresh_notin S0) as Hsf;
            clear - Hcov Hsf; simpl in *; fsetdec).
      destruct (a_looksub_rebind_l HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
      pose proof (qfl Q eq_refl) as IHf.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q
                    (pskl_var_f (supply_fresh S0))) as Hup1.
      assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                       ∪ {{ α }}
                       ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q
                            (pskl_var_f (supply_fresh S0)))
                       ∪ ftvar_in_pskl (pskl_arrow P1' P2')
                       [<=] add (supply_fresh S0) S0)
        by (clear - Hcov Hup1; simpl in *; fsetdec).
      kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
    + (* all_syn target *)
      destruct m as [ | | m' ].
      * (* ti — LS-ForallL *)
        simp e_looksub_impl. case_test; [ | discriminate ].
        inversion Hd; subst; try look_absurd.
        match goal with
        | Hfr0 : ?b `notin` add α _,
          Hp0 : a_looksub ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ _ |- _ =>
            rename Hfr0 into HFR; rename Hp0 into HPREM
        end.
        assert (HFRESH : supply_fresh S0 `notin`
                  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q
                           ∪ ftvar_in_pskl (pskl_all_syn B)))
          by (pose proof (supply_fresh_notin S0) as Hsf;
              clear - Hcov Hsf; simpl in *; fsetdec).
        destruct (a_looksub_rebind_l HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
        pose proof (qfl Q eq_refl) as IHf.
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q
                      (pskl_var_f (supply_fresh S0))) as Hup1.
        assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                         ∪ {{ α }}
                         ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q
                              (pskl_var_f (supply_fresh S0)))
                         ∪ ftvar_in_pskl (pskl_all_syn B)
                         [<=] add (supply_fresh S0) S0)
          by (clear - Hcov Hup1; simpl in *; fsetdec).
        kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
      * (* tc — ForallR if the target is ghost-free, else ForallL *)
        simp e_looksub_impl. case_test; [ | discriminate ]. case_test.
        -- (* ghost-free — LS-ForallR via the reorder *)
           assert (HFRESH : supply_fresh S0 `notin`
                     add α (ftvar_in_aenv Θ
                              ∪ ftvar_in_pskl (pskl_all_syn Q)
                              ∪ ftvar_in_pskl B))
             by (pose proof (supply_fresh_notin S0) as Hsf;
                 clear - Hcov Hsf; simpl in *; fsetdec).
           destruct (a_looksub_forall_r_first Hd eq_refl eq_refl HFRESH)
             as [Ξ2 [C2 HP2]].
           pose proof (qfr B eq_refl eq_refl) as IHf.
           pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                         (pskl_var_f (supply_fresh S0))) as Hup1.
           assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                            ∪ {{ α }}
                            ∪ ftvar_in_pskl (pskl_all_syn Q)
                            ∪ ftvar_in_pskl (open_pskl_wrt_pskl B
                                 (pskl_var_f (supply_fresh S0)))
                            [<=] add (supply_fresh S0) S0)
             by (clear - Hcov Hup1; simpl in *; fsetdec).
           kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
        -- (* not ghost-free — LS-ForallL *)
           inversion Hd; subst; try look_absurd.
           match goal with
           | Hfr0 : ?b `notin` add α _,
             Hp0 : a_looksub ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ _ |- _ =>
               rename Hfr0 into HFR; rename Hp0 into HPREM
           end.
           assert (HFRESH : supply_fresh S0 `notin`
                     add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q
                              ∪ ftvar_in_pskl (pskl_all_syn B)))
             by (pose proof (supply_fresh_notin S0) as Hsf;
                 clear - Hcov Hsf; simpl in *; fsetdec).
           destruct (a_looksub_rebind_l HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
           pose proof (qfl Q eq_refl) as IHf.
           pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q
                         (pskl_var_f (supply_fresh S0))) as Hup1.
           assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                            ∪ {{ α }}
                            ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q
                                 (pskl_var_f (supply_fresh S0)))
                            ∪ ftvar_in_pskl (pskl_all_syn B)
                            [<=] add (supply_fresh S0) S0)
             by (clear - Hcov Hup1; simpl in *; fsetdec).
           kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
      * (* fn — LS-ForallL *)
        simp e_looksub_impl. case_test; [ | discriminate ].
        inversion Hd; subst; try look_absurd.
        match goal with
        | Hfr0 : ?b `notin` add α _,
          Hp0 : a_looksub ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ _ |- _ =>
            rename Hfr0 into HFR; rename Hp0 into HPREM
        end.
        assert (HFRESH : supply_fresh S0 `notin`
                  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q
                           ∪ ftvar_in_pskl (pskl_all_syn B)))
          by (pose proof (supply_fresh_notin S0) as Hsf;
              clear - Hcov Hsf; simpl in *; fsetdec).
        destruct (a_looksub_rebind_l HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
        pose proof (qfl Q eq_refl) as IHf.
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q
                      (pskl_var_f (supply_fresh S0))) as Hup1.
        assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                         ∪ {{ α }}
                         ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q
                              (pskl_var_f (supply_fresh S0)))
                         ∪ ftvar_in_pskl (pskl_all_syn B)
                         [<=] add (supply_fresh S0) S0)
          by (clear - Hcov Hup1; simpl in *; fsetdec).
        kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
    + (* hole — LS-Vacuous *)
      simp e_looksub_impl. discriminate.
    + (* tophole — LS-ForallL *)
      simp e_looksub_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` add α _,
        Hp0 : a_looksub ((?b ~ abind_tvar) ++ Θ) α _ _ _ _ _ |- _ =>
          rename Hfr0 into HFR; rename Hp0 into HPREM
      end.
      assert (HFRESH : supply_fresh S0 `notin`
                add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl Q
                         ∪ ftvar_in_pskl (pskl_tophole Q')))
        by (pose proof (supply_fresh_notin S0) as Hsf;
            clear - Hcov Hsf; simpl in *; fsetdec).
      destruct (a_looksub_rebind_l HPREM HFR HFRESH) as [Ξ2 [C2 HP2]].
      pose proof (qfl Q eq_refl) as IHf.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q
                    (pskl_var_f (supply_fresh S0))) as Hup1.
      assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                       ∪ {{ α }}
                       ∪ ftvar_in_pskl (open_pskl_wrt_pskl Q
                            (pskl_var_f (supply_fresh S0)))
                       ∪ ftvar_in_pskl (pskl_tophole Q')
                       [<=] add (supply_fresh S0) S0)
        by (clear - Hcov Hup1; simpl in *; fsetdec).
      kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
  - (* subject hole — LS-Absent *)
    simp e_looksub_impl. discriminate.
  - (* subject tophole — LS-UnivGhostL at every mode; ForallR first at a
       ghost-free ∀ target under tc *)
    destruct P' as [ | n' | β' | P1' P2' | B | | Q' ].
    + (* unit — LS-UnivGhostL *)
      simp e_looksub_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_looksub Θ α _ Q _ _ _ |- _ => rename Hp0 into HPREM
      end.
      pose proof (qug Q eq_refl) as IHf.
      assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                       ∪ ftvar_in_pskl pskl_unit [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_sub_call IHf HPREM Hcv1 r1 Hr1. discriminate.
    + (* var_b *)
      simp e_looksub_impl. case_test; [ inversion HP' | discriminate ].
    + (* var_f — LS-UnivGhostL *)
      simp e_looksub_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_looksub Θ α _ Q _ _ _ |- _ => rename Hp0 into HPREM
      end.
      pose proof (qug Q eq_refl) as IHf.
      assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                       ∪ ftvar_in_pskl (pskl_var_f β') [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_sub_call IHf HPREM Hcv1 r1 Hr1. discriminate.
    + (* arrow — LS-UnivGhostL *)
      simp e_looksub_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_looksub Θ α _ Q _ _ _ |- _ => rename Hp0 into HPREM
      end.
      pose proof (qug Q eq_refl) as IHf.
      assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                       ∪ ftvar_in_pskl (pskl_arrow P1' P2') [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_sub_call IHf HPREM Hcv1 r1 Hr1. discriminate.
    + (* all_syn target *)
      destruct m as [ | | m' ].
      * (* ti — LS-UnivGhostL *)
        simp e_looksub_impl. case_test; [ | discriminate ].
        inversion Hd; subst; try look_absurd.
        match goal with
        | Hp0 : a_looksub Θ α _ Q _ _ _ |- _ => rename Hp0 into HPREM
        end.
        pose proof (qug Q eq_refl) as IHf.
        assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                         ∪ ftvar_in_pskl (pskl_all_syn B) [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        kill_sub_call IHf HPREM Hcv1 r1 Hr1. discriminate.
      * (* tc — ForallR if ghost-free, else UnivGhostL *)
        simp e_looksub_impl. case_test; [ | discriminate ]. case_test.
        -- assert (HFRESH : supply_fresh S0 `notin`
                     add α (ftvar_in_aenv Θ
                              ∪ ftvar_in_pskl (pskl_tophole Q)
                              ∪ ftvar_in_pskl B))
             by (pose proof (supply_fresh_notin S0) as Hsf;
                 clear - Hcov Hsf; simpl in *; fsetdec).
           destruct (a_looksub_forall_r_first Hd eq_refl eq_refl HFRESH)
             as [Ξ2 [C2 HP2]].
           pose proof (qfr B eq_refl eq_refl) as IHf.
           pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                         (pskl_var_f (supply_fresh S0))) as Hup1.
           assert (Hcv1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                            ∪ {{ α }}
                            ∪ ftvar_in_pskl (pskl_tophole Q)
                            ∪ ftvar_in_pskl (open_pskl_wrt_pskl B
                                 (pskl_var_f (supply_fresh S0)))
                            [<=] add (supply_fresh S0) S0)
             by (clear - Hcov Hup1; simpl in *; fsetdec).
           kill_sub_call IHf HP2 Hcv1 r1 Hr1. discriminate.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_looksub Θ α _ Q _ _ _ |- _ => rename Hp0 into HPREM
           end.
           pose proof (qug Q eq_refl) as IHf.
           assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                            ∪ ftvar_in_pskl (pskl_all_syn B) [<=] S0)
             by (clear - Hcov; simpl in *; fsetdec).
           kill_sub_call IHf HPREM Hcv1 r1 Hr1. discriminate.
      * (* fn — LS-UnivGhostL *)
        simp e_looksub_impl. case_test; [ | discriminate ].
        inversion Hd; subst; try look_absurd.
        match goal with
        | Hp0 : a_looksub Θ α _ Q _ _ _ |- _ => rename Hp0 into HPREM
        end.
        pose proof (qug Q eq_refl) as IHf.
        assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                         ∪ ftvar_in_pskl (pskl_all_syn B) [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        kill_sub_call IHf HPREM Hcv1 r1 Hr1. discriminate.
    + (* hole — LS-Vacuous *)
      simp e_looksub_impl. discriminate.
    + (* tophole — LS-UnivGhostL *)
      simp e_looksub_impl. case_test; [ | discriminate ].
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_looksub Θ α _ Q _ _ _ |- _ => rename Hp0 into HPREM
      end.
      pose proof (qug Q eq_refl) as IHf.
      assert (Hcv1 : ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl Q
                       ∪ ftvar_in_pskl (pskl_tophole Q') [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_sub_call IHf HPREM Hcv1 r1 Hr1. discriminate.
Qed.

(** ⭐ The sub layer's headline. *)
Lemma e_looksub_run_complete : forall S0 Θ α m P P' HP HP' Ξ C,
  {{ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}a ->
  ftvar_in_aenv Θ ∪ {{ α }} ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0 ->
  e_looksub_run S0 Θ α m P P' HP HP' <> None.
Proof.
  intros * Hd Hcov. unfold e_looksub_run.
  pose proof (e_looksub_impl_complete HP HP'
                (e_looksub_order_total S0 Θ α m P P') Hd Hcov) as Hne.
  revert Hne.
  destruct (e_looksub_impl S0 Θ α m P P' HP HP'
              (e_looksub_order_total S0 Θ α m P P')) as [ [r Hr] | ];
    intros Hne.
  - discriminate.
  - exact (False_ind _ (Hne eq_refl)).
Qed.

(* ===================================================================== *)
(*  §3  The SOLVE level, eq layer (§8c.3, level 2a)                       *)
(*                                                                        *)
(*  New over §2's template, and the reason for §3a: the solve's ARROW     *)
(*  row threads the CONTEXT — the second premise runs at [Ξ1 ++ Θ] with   *)
(*  the FIRST premise's own fresh block Ξ1.  The runner's second call     *)
(*  therefore runs at ITS block while the inverted derivation's second    *)
(*  premise sits at the DERIVATION's block, and the two contexts diverge. *)
(*  The motive carries the derivation's context [Θd] separately, related  *)
(*  to the runner's by FLEX-AGREEMENT ON THE INPUTS' VARIABLES            *)
(*  ([flex_agree]): the only context-sensitive rule in the whole solve    *)
(*  cluster is SE-FlexR ([a_flex_tvar] on the target variable — see the   *)
(*  box above [a_extract], algo/def_rules.v), so agreement on the inputs' *)
(*  variables is the WHOLE interface, and junk flex blocks on either      *)
(*  side ride along ([flex_agree_push_blocks]): the derivation's block    *)
(*  avoids [ftvar_in_aenv Θd] ([a_solve_sub_eq_generated_fresh_set]) ⊇    *)
(*  the inputs by the scoped-inputs premise, and the runner's block       *)
(*  avoids the covering supply ([e_solve_sub_eq_block]).                  *)
(*                                                                        *)
(*  The d-side transposition consequently lets the CONTEXT RIDE the swap  *)
(*  ([a_solve_eq_rebind*] conclude at [swap_aenv b β Θd], not at [Θd]) —  *)
(*  agreement survives because the two swapped atoms avoid the inputs'    *)
(*  variables ([flex_agree_swap_left]).                                   *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(*  §3a  flex-agreement on a variable set                                 *)
(* --------------------------------------------------------------------- *)

Definition flex_agree (V : atoms) (Θ1 Θ2 : aenv) : Prop :=
  forall α, α `in` V -> (a_flex_tvar Θ1 α <-> a_flex_tvar Θ2 α).

Lemma flex_agree_refl : forall V Θ, flex_agree V Θ Θ.
Proof. intros V Θ α _. tauto. Qed.

Lemma flex_agree_weaken : forall V V' Θ1 Θ2,
  flex_agree V Θ1 Θ2 -> V' [<=] V -> flex_agree V' Θ1 Θ2.
Proof. intros * H Hsub α Hα. apply H. fsetdec. Qed.

Lemma binds_swap_aenv : forall a b (Θ : aenv) x (bd : abind),
  binds x bd Θ ->
  binds (swap_atom a b x) (swap_abind a b bd) (swap_aenv a b Θ).
Proof.
  intros * Hb. unfold binds in *. unfold swap_aenv.
  change (swap_atom a b x, swap_abind a b bd)
    with ((fun e => (swap_atom a b (fst e), swap_abind a b (snd e))) (x, bd)).
  apply List.in_map. exact Hb.
Qed.

Lemma a_flex_tvar_swap_other : forall a b (Θ : aenv) α,
  α <> a -> α <> b ->
  a_flex_tvar (swap_aenv a b Θ) α <-> a_flex_tvar Θ α.
Proof.
  intros * Hna Hnb. split.
  - intros [Hb1 | [τ Hb1]].
    + apply (binds_swap_aenv a b) in Hb1.
      rewrite swap_aenv_invol in Hb1.
      rewrite (swap_atom_other a b α Hna Hnb) in Hb1.
      left. exact Hb1.
    + apply (binds_swap_aenv a b) in Hb1.
      rewrite swap_aenv_invol in Hb1.
      rewrite (swap_atom_other a b α Hna Hnb) in Hb1.
      right. eexists. exact Hb1.
  - intros [Hb1 | [τ Hb1]].
    + apply (binds_swap_aenv a b) in Hb1.
      rewrite (swap_atom_other a b α Hna Hnb) in Hb1.
      left. exact Hb1.
    + apply (binds_swap_aenv a b) in Hb1.
      rewrite (swap_atom_other a b α Hna Hnb) in Hb1.
      right. eexists. exact Hb1.
Qed.

Lemma flex_agree_swap_left : forall a b V Θ1 Θ2,
  a `notin` V -> b `notin` V ->
  flex_agree V Θ1 Θ2 ->
  flex_agree V (swap_aenv a b Θ1) Θ2.
Proof.
  intros * Hna Hnb Hag α Hα.
  rewrite a_flex_tvar_swap_other;
    [ apply Hag; exact Hα
    | clear - Hna Hα; fsetdec
    | clear - Hnb Hα; fsetdec ].
Qed.

Lemma a_flex_tvar_notin_app : forall (Ξ Θ : aenv) α,
  α `notin` dom Ξ ->
  (a_flex_tvar (Ξ ++ Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros * Hn. split.
  - intros [Hb | [τ Hb]]; unfold binds in *;
      apply in_app_or in Hb; destruct Hb as [Hb | Hb];
      try solve [ exfalso; apply Hn; eapply binds_In; exact Hb ];
      [ left; exact Hb | right; eexists; exact Hb ].
  - intros [Hb | [τ Hb]]; unfold binds in *;
      [ left | right; eexists ]; apply in_or_app; right; eassumption.
Qed.

Lemma flex_agree_push_blocks : forall V Ξ1 Ξ2 Θ1 Θ2,
  dom Ξ1 ∩ V [=] empty ->
  dom Ξ2 ∩ V [=] empty ->
  flex_agree V Θ1 Θ2 ->
  flex_agree V (Ξ1 ++ Θ1) (Ξ2 ++ Θ2).
Proof.
  intros * H1 H2 Hag α Hα.
  rewrite (a_flex_tvar_notin_app Ξ1) by (clear - H1 Hα; fsetdec).
  rewrite (a_flex_tvar_notin_app Ξ2) by (clear - H2 Hα; fsetdec).
  apply Hag; exact Hα.
Qed.

Lemma a_flex_tvar_cons_tvar_other : forall β (Θ : aenv) α,
  α <> β ->
  (a_flex_tvar ((β ~ abind_tvar) ++ Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros * Hne. split.
  - intros [Hb | [τ Hb]]; unfold binds in Hb; simpl in Hb;
      (destruct Hb as [Hb | Hb]; [ solve [ inversion Hb; congruence ] | ]);
      [ left; exact Hb | right; eexists; exact Hb ].
  - intros [Hb | [τ Hb]]; [ left | right; eexists ];
      unfold binds in *; simpl; right; eassumption.
Qed.

Lemma flex_agree_push_tvar : forall V β Θ1 Θ2,
  β `notin` dom Θ1 -> β `notin` dom Θ2 ->
  flex_agree V Θ1 Θ2 ->
  flex_agree (add β V) ((β ~ abind_tvar) ++ Θ1) ((β ~ abind_tvar) ++ Θ2).
Proof.
  intros * Hn1 Hn2 Hag α Hα.
  destruct (α == β) as [-> | Hne].
  - split; intros [Hb | [τ Hb]]; exfalso;
      unfold binds in Hb; simpl in Hb; destruct Hb as [Hb | Hb];
      try solve [ inversion Hb ];
      solve [ apply Hn1; eapply binds_In; exact Hb
            | apply Hn2; eapply binds_In; exact Hb ].
  - assert (Hin : α `in` V) by (clear - Hα Hne; fsetdec).
    split; intro Hx.
    + apply (proj2 (a_flex_tvar_cons_tvar_other Θ2 Hne)).
      apply (proj1 (Hag α Hin)).
      apply (proj1 (a_flex_tvar_cons_tvar_other Θ1 Hne)). exact Hx.
    + apply (proj2 (a_flex_tvar_cons_tvar_other Θ1 Hne)).
      apply (proj2 (Hag α Hin)).
      apply (proj1 (a_flex_tvar_cons_tvar_other Θ2 Hne)). exact Hx.
Qed.

(* --------------------------------------------------------------------- *)
(*  §3b  Transposition, solve shape: the context RIDES the swap           *)
(*                                                                        *)
(*  Unlike §2b there is no looked-for variable to fix and no reason to    *)
(*  fix the context either — the motive relates the derivation's context  *)
(*  to the runner's by [flex_agree], which survives the swap              *)
(*  ([flex_agree_swap_left]).  So the helpers demand freshness only for   *)
(*  the two SKELETONS, and no case split on [β == b] is needed (a swap    *)
(*  at equal atoms is still a swap).                                      *)
(* --------------------------------------------------------------------- *)

Lemma a_solve_eq_rebind : forall Θ P Q Ξ P' b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f b))
     ∼ (open_pskl_wrt_pskl Q (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P ∪ ftvar_in_pskl Q ->
  β `notin` ftvar_in_pskl P ∪ ftvar_in_pskl Q ->
  exists Ξ' P'',
    {{ ((β ~ abind_tvar) ++ swap_aenv b β Θ) ⊢ₑ
       (open_pskl_wrt_pskl P (pskl_var_f β))
       ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros * Hp Hb Hβ.
  pose proof (proj2 (a_solve_sub_eq_swap b β) _ _ _ _ _ Hp) as Hs.
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ swap_aenv b β Θ)
    by (simpl; rewrite swap_atom_l; reflexivity).
  rewrite Hctx in Hs.
  rewrite ! swap_pskl_open_var in Hs.
  rewrite ! swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β P) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β Q) in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_pskl b β P'). exact Hs.
Qed.
Arguments a_solve_eq_rebind {Θ P Q Ξ P' b β}.

(** Subject opens, target fixed (SE-ForallGhost's shape). *)
Lemma a_solve_eq_rebind_l : forall Θ P Qt Ξ P' b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f b))
     ∼ Qt ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P ∪ ftvar_in_pskl Qt ->
  β `notin` ftvar_in_pskl P ∪ ftvar_in_pskl Qt ->
  exists Ξ' P'',
    {{ ((β ~ abind_tvar) ++ swap_aenv b β Θ) ⊢ₑ
       (open_pskl_wrt_pskl P (pskl_var_f β)) ∼ Qt ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros * Hp Hb Hβ.
  pose proof (proj2 (a_solve_sub_eq_swap b β) _ _ _ _ _ Hp) as Hs.
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ swap_aenv b β Θ)
    by (simpl; rewrite swap_atom_l; reflexivity).
  rewrite Hctx in Hs.
  rewrite swap_pskl_open_var in Hs.
  rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β P) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β Qt) in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_pskl b β P'). exact Hs.
Qed.
Arguments a_solve_eq_rebind_l {Θ P Qt Ξ P' b β}.

(** Subject fixed, target opens (SE-GhostForall's shape). *)
Lemma a_solve_eq_rebind_r : forall Θ Ps Q Ξ P' b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₑ Ps
     ∼ (open_pskl_wrt_pskl Q (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl Ps ∪ ftvar_in_pskl Q ->
  β `notin` ftvar_in_pskl Ps ∪ ftvar_in_pskl Q ->
  exists Ξ' P'',
    {{ ((β ~ abind_tvar) ++ swap_aenv b β Θ) ⊢ₑ Ps
       ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros * Hp Hb Hβ.
  pose proof (proj2 (a_solve_sub_eq_swap b β) _ _ _ _ _ Hp) as Hs.
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ swap_aenv b β Θ)
    by (simpl; rewrite swap_atom_l; reflexivity).
  rewrite Hctx in Hs.
  rewrite swap_pskl_open_var in Hs.
  rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β Ps) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β Q) in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_pskl b β P'). exact Hs.
Qed.
Arguments a_solve_eq_rebind_r {Θ Ps Q Ξ P' b β}.

(* --------------------------------------------------------------------- *)
(*  §3c  Strong induction for [e_solve_eq_order]                          *)
(*                                                                        *)
(*  §2a's idiom.  The FlexR premise is the GUESS layer's order and stays  *)
(*  undoubled — the guess runner is total, so the branch owes nothing.    *)
(* --------------------------------------------------------------------- *)

Section e_solve_eq_order_sind.

Variable Qe : supply -> aenv -> pskl -> pskl -> Prop.

Hypothesis Hstep : forall S0 Θ P Q,
    (* SE-FlexR — the guess layer's order, as-is *)
    (forall β, Q = pskl_var_f β -> e_guess_mono_order S0 P) ->
    (* SE-Arrow — order premise + motive companion *)
    (forall P1 P2 Q1 Q2,
       P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       e_solve_eq_order S0 Θ P1 Q1
       /\ (forall S1 Ξ1 P1',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
             e_solve_eq_order S1 (Ξ1 ++ Θ) P2 Q2)) ->
    (forall P1 P2 Q1 Q2,
       P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       Qe S0 Θ P1 Q1
       /\ (forall S1 Ξ1 P1',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
             Qe S1 (Ξ1 ++ Θ) P2 Q2)) ->
    (* SE-Forall *)
    (forall P1 Q1,
       P = pskl_all_syn P1 -> Q = pskl_all_syn Q1 ->
       e_solve_eq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))) ->
    (forall P1 Q1,
       P = pskl_all_syn P1 -> Q = pskl_all_syn Q1 ->
       Qe (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))) ->
    (* SE-UnivGhost *)
    (forall P1 Q1,
       P = pskl_tophole P1 -> Q = pskl_tophole Q1 ->
       e_solve_eq_order S0 Θ P1 Q1) ->
    (forall P1 Q1,
       P = pskl_tophole P1 -> Q = pskl_tophole Q1 ->
       Qe S0 Θ P1 Q1) ->
    (* SE-GhostForall *)
    (forall P1 Q1,
       P = pskl_tophole P1 -> Q = pskl_all_syn Q1 ->
       e_solve_eq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (pskl_tophole P1)
         (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))) ->
    (forall P1 Q1,
       P = pskl_tophole P1 -> Q = pskl_all_syn Q1 ->
       Qe (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (pskl_tophole P1)
         (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))) ->
    (* SE-GhostGuarded *)
    (forall P1,
       P = pskl_tophole P1 ->
       e_solve_eq_order S0 Θ P1 Q) ->
    (forall P1,
       P = pskl_tophole P1 ->
       Qe S0 Θ P1 Q) ->
    (* SE-ForallGhost *)
    (forall P1 Q1,
       P = pskl_all_syn P1 -> Q = pskl_tophole Q1 ->
       e_solve_eq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
         (pskl_tophole Q1)) ->
    (forall P1 Q1,
       P = pskl_all_syn P1 -> Q = pskl_tophole Q1 ->
       Qe (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
         (pskl_tophole Q1)) ->
    (* SE-GuardedGhost *)
    (forall Q1,
       Q = pskl_tophole Q1 ->
       e_solve_eq_order S0 Θ P Q1) ->
    (forall Q1,
       Q = pskl_tophole Q1 ->
       Qe S0 Θ P Q1) ->
    Qe S0 Θ P Q.

Fixpoint e_solve_eq_order_sind S0 Θ P Q
    (H : e_solve_eq_order S0 Θ P Q) {struct H} : Qe S0 Θ P Q :=
  match H in e_solve_eq_order S0' Θ' Pa Qa return Qe S0' Θ' Pa Qa with
  | e_solve_eq_order__intro _ _ _ _ p1 p2 p3 p4 p5 p6 p7 p8 =>
      Hstep
        p1
        p2
        (fun P1 P2 Q1 Q2 e1 e2 =>
           match p2 P1 P2 Q1 Q2 e1 e2 with
           | conj Ha Hb =>
               conj (e_solve_eq_order_sind Ha)
                    (fun S1 Ξ1 P1' Hrun =>
                       e_solve_eq_order_sind (Hb S1 Ξ1 P1' Hrun))
           end)
        p3
        (fun P1 Q1 e1 e2 => e_solve_eq_order_sind (p3 P1 Q1 e1 e2))
        p4
        (fun P1 Q1 e1 e2 => e_solve_eq_order_sind (p4 P1 Q1 e1 e2))
        p5
        (fun P1 Q1 e1 e2 => e_solve_eq_order_sind (p5 P1 Q1 e1 e2))
        p6
        (fun P1 e1 => e_solve_eq_order_sind (p6 P1 e1))
        p7
        (fun P1 Q1 e1 e2 => e_solve_eq_order_sind (p7 P1 Q1 e1 e2))
        p8
        (fun Q1 e1 => e_solve_eq_order_sind (p8 Q1 e1))
  end.

End e_solve_eq_order_sind.

(* --------------------------------------------------------------------- *)
(*  §3d  Completeness of the eq-solve runner                              *)
(* --------------------------------------------------------------------- *)

(** Set-level corollary of [swap_aenv_ftvar_in]: a variable set inside the
    context's support, avoided by both swapped atoms, stays inside it. *)
Lemma ftvar_in_aenv_swap_subset : forall a b (Θ : aenv) V,
  V [<=] ftvar_in_aenv Θ ->
  a `notin` V -> b `notin` V ->
  V [<=] ftvar_in_aenv (swap_aenv a b Θ).
Proof.
  intros * Hsub Ha Hb α Hα.
  pose proof (swap_aenv_ftvar_in a b Θ α (Hsub α Hα)) as Hin.
  rewrite swap_atom_other in Hin;
    [ exact Hin
    | clear - Ha Hα; fsetdec
    | clear - Hb Hα; fsetdec ].
Qed.

Local Ltac kill_seq_call IH Hder Hagr Hscp Hcv r Hr :=
  match goal with
  | |- context [ e_solve_eq_impl ?S ?T ?p ?q ?hp ?hq ?h ] =>
      let Hne := fresh "Hne" in
      let Hcl := fresh "Hcl" in
      assert (Hne : e_solve_eq_impl S T p q hp hq h <> None)
        by (exact (IH hp hq h _ _ _ Hder Hagr Hscp Hcv));
      destruct (e_solve_eq_impl S T p q hp hq h)
        as [ [r Hr] | ] eqn:Hcl;
      [ cbv beta iota; clear Hne Hcl | exact (False_ind _ (Hne eq_refl)) ]
  end.

Lemma e_solve_eq_impl_complete : forall S0 Θ P Q
    (HP : lc_pskl P) (HQ : lc_pskl Q)
    (H : e_solve_eq_order S0 Θ P Q) Θd Ξd P'd,
  {{ Θd ⊢ₑ P ∼ Q ⤳ Ξd ⨾ P'd }}a ->
  flex_agree (ftvar_in_pskl P ∪ ftvar_in_pskl Q) Θd Θ ->
  ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] ftvar_in_aenv Θd ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  e_solve_eq_impl S0 Θ P Q HP HQ H <> None.
Proof.
  intros S0 Θ P Q HP HQ H Θd Ξd P'd Hd Hagr Hscp Hcov.
  pose proof H as Hind.
  revert HP HQ H Θd Ξd P'd Hd Hagr Hscp Hcov.
  apply (e_solve_eq_order_sind
           (fun S0 Θ P Q =>
              forall (HP : lc_pskl P) (HQ : lc_pskl Q)
                     (H : e_solve_eq_order S0 Θ P Q) Θd Ξd P'd,
                {{ Θd ⊢ₑ P ∼ Q ⤳ Ξd ⨾ P'd }}a ->
                flex_agree (ftvar_in_pskl P ∪ ftvar_in_pskl Q) Θd Θ ->
                ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] ftvar_in_aenv Θd ->
                ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
                e_solve_eq_impl S0 Θ P Q HP HQ H <> None));
    [ | exact Hind ].
  clear.
  intros S0 Θ P Q p1 p2 q2 p3 q3 p4 q4 p5 q5 p6 q6 p7 q7 p8 q8
         HP HQ H Θd Ξd P'd Hd Hagr Hscp Hcov.
  destruct P as [ | n | βs | P1 P2 | P1 | | P1 ].
  - (* subject unit *)
    destruct Q as [ | n' | β' | Q1 Q2 | Q1 | | Q1 ].
    + (* unit — SE-Unit *) simp e_solve_eq_impl. discriminate.
    + (* var_b — no lc *) inversion HQ.
    + (* var_f — SE-FlexR *)
      simp e_solve_eq_impl. case_test.
      * match goal with
        | |- context [ e_guess_mono_impl ?s ?p ?h ] =>
            destruct (e_guess_mono_impl s p h) as [gr Hgr]
        end.
        discriminate.
      * exfalso. inversion Hd; subst.
        match goal with
        | Hfx : a_flex_tvar Θd ?bv |- _ =>
            let Hfr := fresh "Hfr" in
            assert (Hfr : a_flex_tvar Θ bv)
              by (apply (proj1 (Hagr bv ltac:(simpl; clear; fsetdec)));
                  exact Hfx);
            apply flex_bound_ck_complete in Hfr;
            rewrite Hfr in Htest; simpl in Htest; discriminate
        end.
    + (* arrow — no rule *) inversion Hd.
    + (* all_syn — no rule *) inversion Hd.
    + (* hole — SE-VacuousR *) simp e_solve_eq_impl. discriminate.
    + (* tophole — SE-GuardedGhost *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_solve_eq Θd pskl_unit Q1 _ _ |- _ => rename Hp0 into HPREM
      end.
      pose proof (q8 Q1 eq_refl) as IHf.
      assert (Hagr1 : flex_agree (ftvar_in_pskl pskl_unit ∪ ftvar_in_pskl Q1)
                        Θd Θ)
        by (eapply flex_agree_weaken; [ exact Hagr | simpl; clear; fsetdec ]).
      assert (Hscp1 : ftvar_in_pskl pskl_unit ∪ ftvar_in_pskl Q1
                        [<=] ftvar_in_aenv Θd)
        by (clear - Hscp; simpl in *; fsetdec).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl pskl_unit
                        ∪ ftvar_in_pskl Q1 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_seq_call IHf HPREM Hagr1 Hscp1 Hcov1 r1 Hr1. discriminate.
  - (* subject var_b — no lc *)
    inversion HP.
  - (* subject var_f — SE-Var *)
    simp e_solve_eq_impl. discriminate.
  - (* subject arrow *)
    destruct Q as [ | n' | β' | Q1 Q2 | Q1 | | Q1 ].
    + (* unit — no rule *) inversion Hd.
    + (* var_b — no lc *) inversion HQ.
    + (* var_f — SE-FlexR *)
      simp e_solve_eq_impl. case_test.
      * match goal with
        | |- context [ e_guess_mono_impl ?s ?p ?h ] =>
            destruct (e_guess_mono_impl s p h) as [gr Hgr]
        end.
        discriminate.
      * exfalso. inversion Hd; subst.
        match goal with
        | Hfx : a_flex_tvar Θd ?bv |- _ =>
            let Hfr := fresh "Hfr" in
            assert (Hfr : a_flex_tvar Θ bv)
              by (apply (proj1 (Hagr bv ltac:(simpl; clear; fsetdec)));
                  exact Hfx);
            apply flex_bound_ck_complete in Hfr;
            rewrite Hfr in Htest; simpl in Htest; discriminate
        end.
    + (* arrow — SE-Arrow: the context-threading case *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      destruct (q2 P1 P2 Q1 Q2 eq_refl eq_refl) as [IH1 IH2].
      match goal with
      | Hda : a_solve_eq Θd P1 Q1 _ _ |- _ => rename Hda into HD1
      end.
      match goal with
      | Hdb : a_solve_eq (_ ++ Θd) P2 Q2 _ _ |- _ => rename Hdb into HD2
      end.
      pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                    _ _ _ _ _ HD1) as HXd.
      assert (Hagr1 : flex_agree (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1) Θd Θ)
        by (eapply flex_agree_weaken; [ exact Hagr | simpl; clear; fsetdec ]).
      assert (Hscp1 : ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1
                        [<=] ftvar_in_aenv Θd)
        by (clear - Hscp; simpl in *; fsetdec).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1
                        [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_seq_call IH1 HD1 Hagr1 Hscp1 Hcov1 r1 Hr1.
      unfold solve_eq_spec in Hr1.
      pose proof (e_solve_eq_supply_grows Hr1) as Hgrow.
      pose proof ((proj2 e_solve_sub_eq_block) _ _ _ _ _ _ _ Hr1)
        as [Hb1 [Hb2 [Hb3 Hb4]]].
      specialize (IH2 _ _ _ Hr1).
      match goal with
      | HD2' : a_solve_eq (?X ++ Θd) P2 Q2 _ _ |- _ =>
          assert (Hagr2 : flex_agree
                            (ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2)
                            (X ++ Θd) (sv_block r1 ++ Θ))
            by (apply flex_agree_push_blocks;
                [ clear - HXd Hscp; simpl in Hscp; fsetdec
                | clear - Hb2 Hcov; simpl in Hcov; fsetdec
                | eapply flex_agree_weaken;
                  [ exact Hagr | simpl; clear; fsetdec ] ]);
          assert (Hscp2 : ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2
                            [<=] ftvar_in_aenv (X ++ Θd))
            by (rewrite ftvar_in_aenv_app; clear - Hscp; simpl in Hscp;
                fsetdec)
      end.
      assert (Hcov2 : ftvar_in_aenv (sv_block r1 ++ Θ)
                        ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2
                        [<=] sv_supply r1)
        by (rewrite ftvar_in_aenv_app;
            clear - Hb1 Hb4 Hgrow Hcov; simpl in Hcov; fsetdec).
      kill_seq_call IH2 HD2 Hagr2 Hscp2 Hcov2 r2 Hr2. discriminate.
    + (* all_syn — no rule *) inversion Hd.
    + (* hole — SE-VacuousR *) simp e_solve_eq_impl. discriminate.
    + (* tophole — SE-GuardedGhost *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_solve_eq Θd (pskl_arrow P1 P2) Q1 _ _ |- _ =>
          rename Hp0 into HPREM
      end.
      pose proof (q8 Q1 eq_refl) as IHf.
      assert (Hagr1 : flex_agree (ftvar_in_pskl (pskl_arrow P1 P2)
                                    ∪ ftvar_in_pskl Q1) Θd Θ)
        by (eapply flex_agree_weaken; [ exact Hagr | simpl; clear; fsetdec ]).
      assert (Hscp1 : ftvar_in_pskl (pskl_arrow P1 P2) ∪ ftvar_in_pskl Q1
                        [<=] ftvar_in_aenv Θd)
        by (clear - Hscp; simpl in *; fsetdec).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl (pskl_arrow P1 P2)
                        ∪ ftvar_in_pskl Q1 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_seq_call IHf HPREM Hagr1 Hscp1 Hcov1 r1 Hr1. discriminate.
  - (* subject all_syn *)
    destruct Q as [ | n' | β' | Q1 Q2 | Q1 | | Q1 ].
    + (* unit — no rule *) inversion Hd.
    + (* var_b — no lc *) inversion HQ.
    + (* var_f — SE-FlexR *)
      simp e_solve_eq_impl. case_test.
      * match goal with
        | |- context [ e_guess_mono_impl ?s ?p ?h ] =>
            destruct (e_guess_mono_impl s p h) as [gr Hgr]
        end.
        discriminate.
      * exfalso. inversion Hd; subst.
        match goal with
        | Hfx : a_flex_tvar Θd ?bv |- _ =>
            let Hfr := fresh "Hfr" in
            assert (Hfr : a_flex_tvar Θ bv)
              by (apply (proj1 (Hagr bv ltac:(simpl; clear; fsetdec)));
                  exact Hfx);
            apply flex_bound_ck_complete in Hfr;
            rewrite Hfr in Htest; simpl in Htest; discriminate
        end.
    + (* arrow — no rule *) inversion Hd.
    + (* all_syn — SE-Forall: the transposition case *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` _,
        Hp0 : a_solve_eq ((?b ~ abind_tvar) ++ Θd) _ _ _ _ |- _ =>
          assert (Hbfr : b `notin` ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1)
            by (clear - Hfr0; fsetdec);
          assert (Hβfr : supply_fresh S0 `notin`
                    ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1)
            by (pose proof (supply_fresh_notin S0) as Hsf;
                clear - Hcov Hsf; simpl in Hcov; fsetdec);
          destruct (a_solve_eq_rebind Hp0 Hbfr Hβfr) as [Ξ2 [P2' HP2]];
          assert (HbΘ : b `notin` dom Θd)
            by (pose proof (dom_subset_ftvar_in_aenv Θd);
                clear - Hfr0 H0; fsetdec);
          assert (Hag0 : flex_agree (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1)
                           (swap_aenv b (supply_fresh S0) Θd) Θ)
            by (apply flex_agree_swap_left;
                [ clear - Hfr0; fsetdec
                | pose proof (supply_fresh_notin S0);
                  clear - Hcov H0; simpl in Hcov; fsetdec
                | eapply flex_agree_weaken;
                  [ exact Hagr | simpl; clear; fsetdec ] ]);
          assert (Hag1 : flex_agree
                    (add (supply_fresh S0)
                       (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1))
                    ((supply_fresh S0 ~ abind_tvar)
                       ++ swap_aenv b (supply_fresh S0) Θd)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ))
            by (apply flex_agree_push_tvar;
                [ rewrite <- (swap_atom_l b (supply_fresh S0)) at 1;
                  apply swap_aenv_dom_notin; exact HbΘ
                | pose proof (dom_subset_ftvar_in_aenv Θ);
                  pose proof (supply_fresh_notin S0);
                  clear - Hcov H0 H1; fsetdec
                | exact Hag0 ]);
          assert (Hagr2 : flex_agree
                    (ftvar_in_pskl
                       (open_pskl_wrt_pskl P1
                          (pskl_var_f (supply_fresh S0)))
                     ∪ ftvar_in_pskl
                         (open_pskl_wrt_pskl Q1
                            (pskl_var_f (supply_fresh S0))))
                    ((supply_fresh S0 ~ abind_tvar) ++ swap_aenv b (supply_fresh S0) Θd)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ))
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
                              (pskl_var_f (supply_fresh S0))) as Hu1;
                pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q1
                              (pskl_var_f (supply_fresh S0))) as Hu2;
                eapply flex_agree_weaken;
                [ exact Hag1 | clear - Hu1 Hu2; simpl in *; fsetdec ]);
          assert (Hscp2 : ftvar_in_pskl
                            (open_pskl_wrt_pskl P1
                               (pskl_var_f (supply_fresh S0)))
                          ∪ ftvar_in_pskl
                              (open_pskl_wrt_pskl Q1
                                 (pskl_var_f (supply_fresh S0)))
                          [<=] ftvar_in_aenv
                                 ((supply_fresh S0 ~ abind_tvar)
                                    ++ swap_aenv b (supply_fresh S0) Θd));
          [ pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
                          (pskl_var_f (supply_fresh S0))) as Hu1;
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q1
                          (pskl_var_f (supply_fresh S0))) as Hu2;
            assert (Hsw : ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1
                            [<=] ftvar_in_aenv
                                   (swap_aenv b (supply_fresh S0) Θd))
              by (apply ftvar_in_aenv_swap_subset;
                  [ clear - Hscp; simpl in Hscp; fsetdec
                  | exact Hbfr | exact Hβfr ]);
            rewrite ftvar_in_aenv_cons_tvar;
            clear - Hu1 Hu2 Hsw; simpl in *; fsetdec
          | ]
      end.
      pose proof (q3 P1 Q1 eq_refl eq_refl) as IHf.
      assert (Hcov2 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                        ∪ ftvar_in_pskl
                            (open_pskl_wrt_pskl P1
                               (pskl_var_f (supply_fresh S0)))
                        ∪ ftvar_in_pskl
                            (open_pskl_wrt_pskl Q1
                               (pskl_var_f (supply_fresh S0)))
                        [<=] add (supply_fresh S0) S0).
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
                      (pskl_var_f (supply_fresh S0))) as Hu1.
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q1
                      (pskl_var_f (supply_fresh S0))) as Hu2.
        rewrite ftvar_in_aenv_cons_tvar.
        clear - Hu1 Hu2 Hcov. simpl in *. fsetdec. }
      kill_seq_call IHf HP2 Hagr2 Hscp2 Hcov2 r1 Hr1. discriminate.
    + (* hole — SE-VacuousR *) simp e_solve_eq_impl. discriminate.
    + (* tophole — SE-ForallGhost *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` _,
        Hp0 : a_solve_eq ((?b ~ abind_tvar) ++ Θd) _ _ _ _ |- _ =>
          assert (Hbfr : b `notin`
                    ftvar_in_pskl P1 ∪ ftvar_in_pskl (pskl_tophole Q1))
            by (clear - Hfr0; simpl in *; fsetdec);
          assert (Hβfr : supply_fresh S0 `notin`
                    ftvar_in_pskl P1 ∪ ftvar_in_pskl (pskl_tophole Q1))
            by (pose proof (supply_fresh_notin S0) as Hsf;
                clear - Hcov Hsf; simpl in *; fsetdec);
          destruct (a_solve_eq_rebind_l Hp0 Hbfr Hβfr) as [Ξ2 [P2' HP2]];
          assert (HbΘ : b `notin` dom Θd)
            by (pose proof (dom_subset_ftvar_in_aenv Θd);
                clear - Hfr0 H0; fsetdec);
          assert (Hag0 : flex_agree (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1)
                           (swap_aenv b (supply_fresh S0) Θd) Θ)
            by (apply flex_agree_swap_left;
                [ clear - Hfr0; fsetdec
                | pose proof (supply_fresh_notin S0);
                  clear - Hcov H0; simpl in Hcov; fsetdec
                | eapply flex_agree_weaken;
                  [ exact Hagr | simpl; clear; fsetdec ] ]);
          assert (Hag1 : flex_agree
                    (add (supply_fresh S0)
                       (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1))
                    ((supply_fresh S0 ~ abind_tvar)
                       ++ swap_aenv b (supply_fresh S0) Θd)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ))
            by (apply flex_agree_push_tvar;
                [ rewrite <- (swap_atom_l b (supply_fresh S0)) at 1;
                  apply swap_aenv_dom_notin; exact HbΘ
                | pose proof (dom_subset_ftvar_in_aenv Θ);
                  pose proof (supply_fresh_notin S0);
                  clear - Hcov H0 H1; fsetdec
                | exact Hag0 ]);
          assert (Hagr2 : flex_agree
                    (ftvar_in_pskl
                       (open_pskl_wrt_pskl P1
                          (pskl_var_f (supply_fresh S0)))
                     ∪ ftvar_in_pskl (pskl_tophole Q1))
                    ((supply_fresh S0 ~ abind_tvar)
                       ++ swap_aenv b (supply_fresh S0) Θd)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ))
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
                              (pskl_var_f (supply_fresh S0))) as Hu1;
                eapply flex_agree_weaken;
                [ exact Hag1 | clear - Hu1; simpl in *; fsetdec ]);
          assert (Hscp2 : ftvar_in_pskl
                            (open_pskl_wrt_pskl P1
                               (pskl_var_f (supply_fresh S0)))
                          ∪ ftvar_in_pskl (pskl_tophole Q1)
                          [<=] ftvar_in_aenv
                                 ((supply_fresh S0 ~ abind_tvar)
                                    ++ swap_aenv b (supply_fresh S0) Θd));
          [ pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
                          (pskl_var_f (supply_fresh S0))) as Hu1;
            assert (Hsw : ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1
                            [<=] ftvar_in_aenv
                                   (swap_aenv b (supply_fresh S0) Θd))
              by (apply ftvar_in_aenv_swap_subset;
                  [ clear - Hscp; simpl in Hscp; fsetdec
                  | clear - Hbfr; simpl in *; fsetdec
                  | clear - Hβfr; simpl in *; fsetdec ]);
            rewrite ftvar_in_aenv_cons_tvar;
            clear - Hu1 Hsw; simpl in *; fsetdec
          | ]
      end.
      pose proof (q7 P1 Q1 eq_refl eq_refl) as IHf.
      assert (Hcov2 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                        ∪ ftvar_in_pskl
                            (open_pskl_wrt_pskl P1
                               (pskl_var_f (supply_fresh S0)))
                        ∪ ftvar_in_pskl (pskl_tophole Q1)
                        [<=] add (supply_fresh S0) S0).
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
                      (pskl_var_f (supply_fresh S0))) as Hu1.
        rewrite ftvar_in_aenv_cons_tvar.
        clear - Hu1 Hcov. simpl in *. fsetdec. }
      kill_seq_call IHf HP2 Hagr2 Hscp2 Hcov2 r1 Hr1. discriminate.
  - (* subject hole — SE-GhostL *)
    simp e_solve_eq_impl. discriminate.
  - (* subject tophole *)
    destruct Q as [ | n' | β' | Q1 Q2 | Q1 | | Q1 ].
    + (* unit — SE-GhostGuarded *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_solve_eq Θd P1 pskl_unit _ _ |- _ => rename Hp0 into HPREM
      end.
      pose proof (q6 P1 eq_refl) as IHf.
      assert (Hagr1 : flex_agree (ftvar_in_pskl P1 ∪ ftvar_in_pskl pskl_unit)
                        Θd Θ)
        by (eapply flex_agree_weaken; [ exact Hagr | simpl; clear; fsetdec ]).
      assert (Hscp1 : ftvar_in_pskl P1 ∪ ftvar_in_pskl pskl_unit
                        [<=] ftvar_in_aenv Θd)
        by (clear - Hscp; simpl in *; fsetdec).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P1
                        ∪ ftvar_in_pskl pskl_unit [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_seq_call IHf HPREM Hagr1 Hscp1 Hcov1 r1 Hr1. discriminate.
    + (* var_b — no lc *) inversion HQ.
    + (* var_f — SE-GhostGuarded *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_solve_eq Θd P1 (pskl_var_f β') _ _ |- _ =>
          rename Hp0 into HPREM
      end.
      pose proof (q6 P1 eq_refl) as IHf.
      assert (Hagr1 : flex_agree (ftvar_in_pskl P1
                                    ∪ ftvar_in_pskl (pskl_var_f β')) Θd Θ)
        by (eapply flex_agree_weaken; [ exact Hagr | simpl; clear; fsetdec ]).
      assert (Hscp1 : ftvar_in_pskl P1 ∪ ftvar_in_pskl (pskl_var_f β')
                        [<=] ftvar_in_aenv Θd)
        by (clear - Hscp; simpl in *; fsetdec).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P1
                        ∪ ftvar_in_pskl (pskl_var_f β') [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_seq_call IHf HPREM Hagr1 Hscp1 Hcov1 r1 Hr1. discriminate.
    + (* arrow — SE-GhostGuarded *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_solve_eq Θd P1 (pskl_arrow Q1 Q2) _ _ |- _ =>
          rename Hp0 into HPREM
      end.
      pose proof (q6 P1 eq_refl) as IHf.
      assert (Hagr1 : flex_agree (ftvar_in_pskl P1
                                    ∪ ftvar_in_pskl (pskl_arrow Q1 Q2)) Θd Θ)
        by (eapply flex_agree_weaken; [ exact Hagr | simpl; clear; fsetdec ]).
      assert (Hscp1 : ftvar_in_pskl P1 ∪ ftvar_in_pskl (pskl_arrow Q1 Q2)
                        [<=] ftvar_in_aenv Θd)
        by (clear - Hscp; simpl in *; fsetdec).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P1
                        ∪ ftvar_in_pskl (pskl_arrow Q1 Q2) [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_seq_call IHf HPREM Hagr1 Hscp1 Hcov1 r1 Hr1. discriminate.
    + (* all_syn — SE-GhostForall *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hfr0 : ?b `notin` _,
        Hp0 : a_solve_eq ((?b ~ abind_tvar) ++ Θd) _ _ _ _ |- _ =>
          assert (Hbfr : b `notin`
                    ftvar_in_pskl (pskl_tophole P1) ∪ ftvar_in_pskl Q1)
            by (clear - Hfr0; simpl in *; fsetdec);
          assert (Hβfr : supply_fresh S0 `notin`
                    ftvar_in_pskl (pskl_tophole P1) ∪ ftvar_in_pskl Q1)
            by (pose proof (supply_fresh_notin S0) as Hsf;
                clear - Hcov Hsf; simpl in *; fsetdec);
          destruct (a_solve_eq_rebind_r Hp0 Hbfr Hβfr) as [Ξ2 [P2' HP2]];
          assert (HbΘ : b `notin` dom Θd)
            by (pose proof (dom_subset_ftvar_in_aenv Θd);
                clear - Hfr0 H0; fsetdec);
          assert (Hag0 : flex_agree (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1)
                           (swap_aenv b (supply_fresh S0) Θd) Θ)
            by (apply flex_agree_swap_left;
                [ clear - Hfr0; fsetdec
                | pose proof (supply_fresh_notin S0);
                  clear - Hcov H0; simpl in Hcov; fsetdec
                | eapply flex_agree_weaken;
                  [ exact Hagr | simpl; clear; fsetdec ] ]);
          assert (Hag1 : flex_agree
                    (add (supply_fresh S0)
                       (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1))
                    ((supply_fresh S0 ~ abind_tvar)
                       ++ swap_aenv b (supply_fresh S0) Θd)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ))
            by (apply flex_agree_push_tvar;
                [ rewrite <- (swap_atom_l b (supply_fresh S0)) at 1;
                  apply swap_aenv_dom_notin; exact HbΘ
                | pose proof (dom_subset_ftvar_in_aenv Θ);
                  pose proof (supply_fresh_notin S0);
                  clear - Hcov H0 H1; fsetdec
                | exact Hag0 ]);
          assert (Hagr2 : flex_agree
                    (ftvar_in_pskl (pskl_tophole P1)
                     ∪ ftvar_in_pskl
                         (open_pskl_wrt_pskl Q1
                            (pskl_var_f (supply_fresh S0))))
                    ((supply_fresh S0 ~ abind_tvar)
                       ++ swap_aenv b (supply_fresh S0) Θd)
                    ((supply_fresh S0 ~ abind_tvar) ++ Θ))
            by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q1
                              (pskl_var_f (supply_fresh S0))) as Hu1;
                eapply flex_agree_weaken;
                [ exact Hag1 | clear - Hu1; simpl in *; fsetdec ]);
          assert (Hscp2 : ftvar_in_pskl (pskl_tophole P1)
                          ∪ ftvar_in_pskl
                              (open_pskl_wrt_pskl Q1
                                 (pskl_var_f (supply_fresh S0)))
                          [<=] ftvar_in_aenv
                                 ((supply_fresh S0 ~ abind_tvar)
                                    ++ swap_aenv b (supply_fresh S0) Θd));
          [ pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q1
                          (pskl_var_f (supply_fresh S0))) as Hu1;
            assert (Hsw : ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1
                            [<=] ftvar_in_aenv
                                   (swap_aenv b (supply_fresh S0) Θd))
              by (apply ftvar_in_aenv_swap_subset;
                  [ clear - Hscp; simpl in Hscp; fsetdec
                  | clear - Hbfr; simpl in *; fsetdec
                  | clear - Hβfr; simpl in *; fsetdec ]);
            rewrite ftvar_in_aenv_cons_tvar;
            clear - Hu1 Hsw; simpl in *; fsetdec
          | ]
      end.
      pose proof (q5 P1 Q1 eq_refl eq_refl) as IHf.
      assert (Hcov2 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                        ∪ ftvar_in_pskl (pskl_tophole P1)
                        ∪ ftvar_in_pskl
                            (open_pskl_wrt_pskl Q1
                               (pskl_var_f (supply_fresh S0)))
                        [<=] add (supply_fresh S0) S0).
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q1
                      (pskl_var_f (supply_fresh S0))) as Hu1.
        rewrite ftvar_in_aenv_cons_tvar.
        clear - Hu1 Hcov. simpl in *. fsetdec. }
      kill_seq_call IHf HP2 Hagr2 Hscp2 Hcov2 r1 Hr1. discriminate.
    + (* hole — SE-VacuousR *) simp e_solve_eq_impl. discriminate.
    + (* tophole — SE-UnivGhost *)
      simp e_solve_eq_impl.
      inversion Hd; subst; try look_absurd.
      match goal with
      | Hp0 : a_solve_eq Θd P1 Q1 _ _ |- _ => rename Hp0 into HPREM
      end.
      pose proof (q4 P1 Q1 eq_refl eq_refl) as IHf.
      assert (Hagr1 : flex_agree (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1) Θd Θ)
        by (eapply flex_agree_weaken; [ exact Hagr | simpl; clear; fsetdec ]).
      assert (Hscp1 : ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1
                        [<=] ftvar_in_aenv Θd)
        by (clear - Hscp; simpl in *; fsetdec).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1
                        [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_seq_call IHf HPREM Hagr1 Hscp1 Hcov1 r1 Hr1. discriminate.
Qed.

(** ⭐ The eq-solve headline: a derivation at scoped, covered inputs means
    the runner answers.  The context equality at the entry point makes the
    agreement premise reflexive. *)
Lemma e_solve_eq_run_complete : forall S0 Θ P Q HP HQ Ξ P',
  {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
  ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] ftvar_in_aenv Θ ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  e_solve_eq_run S0 Θ P Q HP HQ <> None.
Proof.
  intros * Hd Hscp Hcov. unfold e_solve_eq_run.
  assert (Hagr : flex_agree (ftvar_in_pskl P ∪ ftvar_in_pskl Q) Θ Θ)
    by apply flex_agree_refl.
  pose proof (e_solve_eq_impl_complete HP HQ
                (@e_solve_eq_order_total S0 Θ P Q HP)
                Hd Hagr Hscp Hcov) as Hne.
  revert Hne.
  destruct (e_solve_eq_impl S0 Θ P Q HP HQ
              (@e_solve_eq_order_total S0 Θ P Q HP)) as [ [r Hr] | ];
    intros Hne.
  - discriminate.
  - exact (False_ind _ (Hne eq_refl)).
Qed.

(* ===================================================================== *)
(*  §4  The SOLVE level, sub layer (§8c.3, level 2b)                      *)
(*                                                                        *)
(*  Same motive as §3 (the context [Θd] rides, related to the runner's    *)
(*  by [flex_agree] on the inputs' variables, plus scoped inputs).  New   *)
(*  over §3: the dispatch peels ∀/⫯ SUBJECTS FIRST (type.ml:489-533 —     *)
(*  the OPPOSITE of the look walk), so the two §2b-style reorder facts    *)
(*  this level owes are LEFT-rule-first:                                  *)
(*                                                                        *)
(*   - [a_solve_sub_tophole_l_first]: at a ⫯ subject the runner strips    *)
(*     before Vacuous/ForallR — easy, no swaps, the witness stays put.    *)
(*   - [a_solve_sub_forall_l_first]: at an ∀ subject the runner commits   *)
(*     SS-ForallL before Vacuous/ForallR/Check.  ⚠️⚠️ Unlike the look      *)
(*     level, the committed opener [supply_fresh S0] is NOT covered       *)
(*     against [Θd], so the reorder cannot keep the context fixed.  It    *)
(*     splits: an inner HOIST ([a_solve_sub_forall_l_hoist]) with the     *)
(*     look level's fixed-context dance under the STRONG freshness        *)
(*     [β ∉ ftvar_in_aenv Θd], and a wrapper that buys that freshness     *)
(*     with ONE sanitizing pre-swap (β δ) on the input derivation — the   *)
(*     inputs are fixed (β, δ avoid them), the context rides, and the     *)
(*     wrapper hands the case bash the motive facts at the sanitized      *)
(*     context, including the [β ∉ dom Θd'] that                          *)
(*     [flex_agree_push_tvar] needs.                                      *)
(*                                                                        *)
(*  The ForallR-committing clauses (ghost-free ∀ target over a            *)
(*  unit/arrow/◇ subject) rebind the rule's witness with the context      *)
(*  RIDING ([a_solve_sub_rebind_r_ctx], §3b's shape); the Check clause    *)
(*  drops into the FINISHED §3 eq lemma; Arrow/GhostLF thread blocks      *)
(*  exactly as §3d's arrow case.                                          *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §4a  The sub-layer transposition kit                                  *)
(* ===================================================================== *)

Lemma a_solve_sub_rebind_l : forall Θ m P Qt Ξ P' b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f b))
     ≼[ m ] Qt ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Qt ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Qt ->
  exists Ξ' P'',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f β))
       ≼[ m ] Qt ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros * Hp Hb Hβ.
  destruct (β == b) as [-> | Hne]; [ exists Ξ, P'; exact Hp | ].
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ Θ).
  { simpl. rewrite swap_atom_l.
    rewrite (swap_aenv_fresh_id b β Θ) by (clear - Hb Hβ; fsetdec).
    reflexivity. }
  pose proof (proj1 (a_solve_sub_eq_swap b β) _ _ _ _ _ _ Hp) as Hs.
  rewrite Hctx in Hs.
  rewrite swap_pskl_open_var in Hs.
  rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β P) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β Qt) in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_pskl b β P'). exact Hs.
Qed.
Arguments a_solve_sub_rebind_l {Θ m P Qt Ξ P' b β}.

Lemma a_solve_sub_rebind_r : forall Θ m Ps Q Ξ P' b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₛ Ps ≼[ m ]
     (open_pskl_wrt_pskl Q (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl Ps ∪ ftvar_in_pskl Q ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl Ps ∪ ftvar_in_pskl Q ->
  exists Ξ' P'',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ Ps ≼[ m ]
       (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros * Hp Hb Hβ.
  destruct (β == b) as [-> | Hne]; [ exists Ξ, P'; exact Hp | ].
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ Θ).
  { simpl. rewrite swap_atom_l.
    rewrite (swap_aenv_fresh_id b β Θ) by (clear - Hb Hβ; fsetdec).
    reflexivity. }
  pose proof (proj1 (a_solve_sub_eq_swap b β) _ _ _ _ _ _ Hp) as Hs.
  rewrite Hctx in Hs.
  rewrite swap_pskl_open_var in Hs.
  rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β Ps) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β Q) in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_pskl b β P'). exact Hs.
Qed.
Arguments a_solve_sub_rebind_r {Θ m Ps Q Ξ P' b β}.

Lemma a_solve_sub_rebind_r_ctx : forall Θ m Ps Q Ξ P' b β,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₛ Ps ≼[ m ]
     (open_pskl_wrt_pskl Q (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl Ps ∪ ftvar_in_pskl Q ->
  β `notin` ftvar_in_pskl Ps ∪ ftvar_in_pskl Q ->
  exists Ξ' P'',
    {{ ((β ~ abind_tvar) ++ swap_aenv b β Θ) ⊢ₛ Ps ≼[ m ]
       (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros * Hp Hb Hβ.
  pose proof (proj1 (a_solve_sub_eq_swap b β) _ _ _ _ _ _ Hp) as Hs.
  assert (Hctx : swap_aenv b β ((b ~ abind_tvar) ++ Θ)
                 = (β ~ abind_tvar) ++ swap_aenv b β Θ)
    by (simpl; rewrite swap_atom_l; reflexivity).
  rewrite Hctx in Hs.
  rewrite swap_pskl_open_var in Hs.
  rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id b β Ps) in Hs by (clear - Hb Hβ; fsetdec).
  rewrite (swap_pskl_fresh_id b β Q) in Hs by (clear - Hb Hβ; fsetdec).
  exists (swap_aenv b β Ξ), (swap_pskl b β P'). exact Hs.
Qed.
Arguments a_solve_sub_rebind_r_ctx {Θ m Ps Q Ξ P' b β}.

(** Exchange of two rigid tvar conses — an [a_solve_sub_eq_ctx_change]
    instance (the judgement reads its context only through the freshness
    avoid-sets and the flex tests, and both are order-blind). *)
Lemma a_solve_sub_ctx_exchange : forall β1 β2 (Θ : aenv) m P Q Ξ P',
  {{ ((β1 ~ abind_tvar) ++ (β2 ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ m ] Q
     ⤳ Ξ ⨾ P' }}a ->
  {{ ((β2 ~ abind_tvar) ++ (β1 ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ m ] Q
     ⤳ Ξ ⨾ P' }}a.
Proof.
  intros * H.
  eapply (proj1 a_solve_sub_eq_ctx_change); [ exact H | | | ].
  - simpl. fsetdec.
  - intros α0 Hf. unfold a_flex_tvar, binds in *; simpl in *.
    destruct Hf as [Hb | [τ Hb]]; [ left | right; exists τ ]; tauto.
  - intros P0 Hf. inversion Hf; subst;
      match goal with
      | Hb : binds _ _ _ |- _ =>
          unfold binds in Hb; simpl in Hb;
          destruct Hb as [E | [E | HbIn]];
          [ discriminate E | discriminate E | ]
      end;
      [ apply a_flex__var | eapply a_flex__var_def ];
      unfold binds; simpl; right; right; exact HbIn.
Qed.
Arguments a_solve_sub_ctx_exchange {β1 β2 Θ m P Q Ξ P'}.

(* --------------------------------------------------------------------- *)
(*  §4b  The two reorder lemmas                                           *)
(* --------------------------------------------------------------------- *)

(** At a ⫯ subject the runner strips (SS-UnivGhostL) before Vacuous and
    ForallR.  No swaps: a ForallR-rooted derivation re-applies ForallR at
    the SAME witness after the IH (the freshness set only shrinks), a
    Vacuous root answers with a fresh Vacuous, and a Check root dies
    (a ⫯ subject is never guarded). *)
Lemma a_solve_sub_tophole_l_first : forall Θ m Ps Q Ξ P',
  {{ Θ ⊢ₛ Ps ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
  forall P0, Ps = pskl_tophole P0 ->
  exists Ξ' P'',
    {{ Θ ⊢ₛ P0 ≼[ m ] Q ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros Θ m Ps Q Ξ P' Hd.
  induction Hd; intros P0' HeqP; try discriminate.
  - (* SS-UnivGhostL — the premise is the answer *)
    injection HeqP as ->. eauto.
  - (* SS-Vacuous *)
    subst. do 2 eexists. apply a_solve_sub__vacuous.
  - (* SS-Check — a ⫯ subject is never guarded *)
    subst. match goal with
    | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
    end.
  - (* SS-ForallR — IH under the SAME witness, then re-apply *)
    subst.
    match goal with
    | Hfr : ?b `notin` _,
      IH : forall _, _ -> _ |- _ =>
        destruct (IH P0' eq_refl) as [Ξ' [P'' E]];
        exists Ξ', P'';
        apply a_solve_sub__forall_r with (β := b);
        [ assumption
        | clear - Hfr; simpl in *; fsetdec
        | exact E ]
    end.
Qed.
Arguments a_solve_sub_tophole_l_first {Θ m Ps Q Ξ P'} _ {P0}.

(** ⭐ The ForallL-first HOIST, at a β already fresh for the CONTEXT: at an
    ∀ subject the runner commits SS-ForallL before Vacuous/ForallR/Check,
    so a derivation rooted in any of those must be reordered into the
    ForallL-premise shape.  Plain structural induction; the recursion is
    through a chain of SS-ForallR's, and — as in the look level's R-first
    — the swaps come AFTER the IH: the IH opens the subject at an interim
    δ on TOP of the premise's context, and the two fixed-context rebinds
    + exchanges walk the two openers into the ForallR-inside nesting.
    The strong freshness [β ∉ ftvar_in_aenv Θ] is what keeps every
    context in the dance CONCRETE; the wrapper below discharges it. *)
Lemma a_solve_sub_forall_l_hoist : forall Θ m Ps Q Ξ P',
  {{ Θ ⊢ₛ Ps ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
  forall P0 β, Ps = pskl_all_syn P0 ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl Q ->
  exists Ξ' P'',
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ (open_pskl_wrt_pskl P0 (pskl_var_f β))
       ≼[ m ] Q ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros Θ m Ps Q Ξ P' Hd.
  induction Hd; intros P0' βh HeqP Hβ; try discriminate.
  - (* SS-ForallL — one fixed-context rebind *)
    injection HeqP as ->.
    match goal with
    | Hfr : ?b `notin` _,
      Hp : a_solve_sub _ _ (open_pskl_wrt_pskl _ (pskl_var_f ?b)) _ _ _
      |- _ =>
        destruct (a_solve_sub_rebind_l Hp Hfr Hβ) as [Ξ2 [P2 E]]
    end.
    exists Ξ2, P2. exact E.
  - (* SS-Vacuous — answer with a fresh Vacuous on the opened subject *)
    subst. do 2 eexists. apply a_solve_sub__vacuous.
  - (* SS-Check — an ∀ subject is never guarded *)
    subst. match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  - (* SS-ForallR — IH first (interim opener δ on TOP of the premise's
       context), then two rebinds + exchanges renest the two openers *)
    subst.
    match goal with
    | Hfr : ?b `notin` _,
      Hp : a_solve_sub ((?b ~ abind_tvar) ++ ?Th) mode_tc _
             (open_pskl_wrt_pskl ?B0 (pskl_var_f ?b)) _ _,
      IH : forall _ _, _ -> _ -> _ |- _ =>
        (* δ: the subject's interim opener *)
        destruct (atom_fresh (add βh (add b (ftvar_in_aenv Th
                    ∪ ftvar_in_pskl P0' ∪ ftvar_in_pskl B0)))) as [δ Hδ];
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B0 (pskl_var_f b))
          as HupBb;
        assert (Hδ' : δ `notin`
                  ftvar_in_aenv ((b ~ abind_tvar) ++ Th)
                    ∪ ftvar_in_pskl P0'
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B0 (pskl_var_f b)))
          by (clear - Hδ HupBb; simpl in *; fsetdec);
        destruct (IH P0' δ eq_refl Hδ') as [Ξ1 [P1 E1]];
        apply a_solve_sub_ctx_exchange in E1;
        (* γ': the re-applied ForallR's witness *)
        destruct (atom_fresh (add βh (add b (add δ (ftvar_in_aenv Th
                    ∪ ftvar_in_pskl P0' ∪ ftvar_in_pskl B0))))) as [γ' Hγ'];
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0' (pskl_var_f δ))
          as HupPδ;
        assert (Hf1 : b `notin`
                  ftvar_in_aenv ((δ ~ abind_tvar) ++ Th)
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0' (pskl_var_f δ))
                    ∪ ftvar_in_pskl B0)
          by (clear - Hfr Hδ HupPδ; simpl in *; fsetdec);
        assert (Hf2 : γ' `notin`
                  ftvar_in_aenv ((δ ~ abind_tvar) ++ Th)
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0' (pskl_var_f δ))
                    ∪ ftvar_in_pskl B0)
          by (clear - Hγ' HupPδ; simpl in *; fsetdec);
        destruct (a_solve_sub_rebind_r E1 Hf1 Hf2) as [Ξ2 [P2 E2]];
        apply a_solve_sub_ctx_exchange in E2;
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B0 (pskl_var_f γ'))
          as HupBγ;
        assert (Hf3 : δ `notin`
                  ftvar_in_aenv ((γ' ~ abind_tvar) ++ Th)
                    ∪ ftvar_in_pskl P0'
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B0 (pskl_var_f γ')))
          by (clear - Hδ Hγ' HupBγ; simpl in *; fsetdec);
        assert (Hf4 : βh `notin`
                  ftvar_in_aenv ((γ' ~ abind_tvar) ++ Th)
                    ∪ ftvar_in_pskl P0'
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B0 (pskl_var_f γ')))
          by (clear - Hβ Hγ' HupBγ; simpl in *; fsetdec);
        destruct (a_solve_sub_rebind_l E2 Hf3 Hf4) as [Ξ3 [P3 E3]];
        apply a_solve_sub_ctx_exchange in E3;
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0' (pskl_var_f βh))
          as HupPβ;
        exists Ξ3, P3;
        apply a_solve_sub__forall_r with (β := γ');
        [ assumption
        | clear - Hγ' HupPβ; simpl in *; fsetdec
        | exact E3 ]
    end.
Qed.
Arguments a_solve_sub_forall_l_hoist {Θ m Ps Q Ξ P'} _ {P0 β}.

(** ⭐ The reorder the case bash consumes.  Unlike the look level, the
    derivation's context [Θd] is NOT covered by the supply, so the
    committed β may occur in it as junk — ONE sanitizing pre-swap (β δ)
    on the input derivation makes the hoist's strong freshness true (the
    inputs are fixed: β and δ avoid them), and the context RIDES: the
    conclusion delivers the motive facts at the sanitized [Θd'], with
    [β ∉ dom Θd'] — what [flex_agree_push_tvar] needs — for free. *)
Lemma a_solve_sub_forall_l_first : forall Θd Θr m P0 Q Ξ P' β,
  {{ Θd ⊢ₛ (pskl_all_syn P0) ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
  flex_agree (ftvar_in_pskl P0 ∪ ftvar_in_pskl Q) Θd Θr ->
  ftvar_in_pskl P0 ∪ ftvar_in_pskl Q [<=] ftvar_in_aenv Θd ->
  β `notin` ftvar_in_pskl P0 ∪ ftvar_in_pskl Q ->
  exists Θd' Ξ' P'',
    {{ ((β ~ abind_tvar) ++ Θd') ⊢ₛ (open_pskl_wrt_pskl P0 (pskl_var_f β))
       ≼[ m ] Q ⤳ Ξ' ⨾ P'' }}a
    /\ flex_agree (ftvar_in_pskl P0 ∪ ftvar_in_pskl Q) Θd' Θr
    /\ ftvar_in_pskl P0 ∪ ftvar_in_pskl Q [<=] ftvar_in_aenv Θd'
    /\ β `notin` dom Θd'.
Proof.
  intros * Hd Hagr Hscp Hβ.
  destruct (atom_fresh (add β (ftvar_in_aenv Θd ∪ ftvar_in_pskl P0
              ∪ ftvar_in_pskl Q))) as [δ Hδ].
  pose proof (proj1 (a_solve_sub_eq_swap β δ) _ _ _ _ _ _ Hd) as Hs.
  rewrite (swap_pskl_fresh_id β δ (pskl_all_syn P0)) in Hs
    by (simpl; clear - Hβ Hδ; fsetdec).
  rewrite (swap_pskl_fresh_id β δ Q) in Hs by (clear - Hβ Hδ; fsetdec).
  assert (HβΘ : β `notin` ftvar_in_aenv (swap_aenv β δ Θd)).
  { intro Hin.
    pose proof (swap_aenv_ftvar_in β δ (swap_aenv β δ Θd) β Hin) as Hin'.
    rewrite swap_aenv_invol in Hin'.
    rewrite swap_atom_l in Hin'.
    clear - Hδ Hin'. fsetdec. }
  assert (Hβ' : β `notin` ftvar_in_aenv (swap_aenv β δ Θd)
                  ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl Q)
    by (clear - HβΘ Hβ; fsetdec).
  destruct (a_solve_sub_forall_l_hoist Hs eq_refl Hβ') as [Ξ' [P'' E]].
  exists (swap_aenv β δ Θd), Ξ', P''.
  split; [ exact E | ].
  split.
  { apply flex_agree_swap_left;
      [ clear - Hβ; fsetdec
      | clear - Hδ; fsetdec
      | exact Hagr ]. }
  split.
  { apply ftvar_in_aenv_swap_subset;
      [ exact Hscp
      | clear - Hβ; fsetdec
      | clear - Hδ; fsetdec ]. }
  pose proof (dom_subset_ftvar_in_aenv (swap_aenv β δ Θd)) as Hds.
  clear - HβΘ Hds. fsetdec.
Qed.
Arguments a_solve_sub_forall_l_first {Θd Θr m P0 Q Ξ P' β}.

(* --------------------------------------------------------------------- *)
(*  §4c  Strong induction for [e_solve_sub_order]                         *)
(*                                                                        *)
(*  §2a/§3c's idiom.  The Check premise and the Arrow/GhostLF eq halves   *)
(*  stay UNDOUBLED — the eq layer is a finished lemma, ∀-quantified over  *)
(*  its domain proof.                                                     *)
(* --------------------------------------------------------------------- *)

Section e_solve_sub_order_sind.

Variable Qs : supply -> aenv -> mode -> pskl -> pskl -> Prop.

Hypothesis Hstep : forall S0 Θ m P Q,
    (* SS-ForallL *)
    (forall P1,
       P = pskl_all_syn P1 ->
       e_solve_sub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) m
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))) Q) ->
    (forall P1,
       P = pskl_all_syn P1 ->
       Qs (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) m
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))) Q) ->
    (* SS-UnivGhostL *)
    (forall P1,
       P = pskl_tophole P1 ->
       e_solve_sub_order S0 Θ m P1 Q) ->
    (forall P1,
       P = pskl_tophole P1 ->
       Qs S0 Θ m P1 Q) ->
    (* SS-Check — the drop into the (already-closed) eq layer *)
    (m = mode_tc -> e_solve_eq_order S0 Θ P Q) ->
    (* SS-ForallR *)
    (forall B,
       m = mode_tc -> Q = pskl_all_syn B ->
       e_solve_sub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) mode_tc P
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))) ->
    (forall B,
       m = mode_tc -> Q = pskl_all_syn B ->
       Qs (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) mode_tc P
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))) ->
    (* SS-Arrow — the eq half stays as-is; only the sub half gets a
       companion *)
    (forall m' P1 P2 Q1 Q2,
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       e_solve_eq_order S0 Θ P1 Q1
       /\ (forall S1 Ξ1 P1',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
             e_solve_sub_order S1 (Ξ1 ++ Θ) m' P2 Q2)) ->
    (forall m' P1 P2 Q1 Q2,
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       forall S1 Ξ1 P1',
         {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
         Qs S1 (Ξ1 ++ Θ) m' P2 Q2) ->
    (* SS-GhostLF — same conj shape, ◇ halves *)
    (forall m' Q1 Q2,
       m = mode_fn m' -> P = pskl_hole -> Q = pskl_arrow Q1 Q2 ->
       e_solve_eq_order S0 Θ pskl_hole Q1
       /\ (forall S1 Ξ1 P1',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_hole ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
             e_solve_sub_order S1 (Ξ1 ++ Θ) m' pskl_hole Q2)) ->
    (forall m' Q1 Q2,
       m = mode_fn m' -> P = pskl_hole -> Q = pskl_arrow Q1 Q2 ->
       forall S1 Ξ1 P1',
         {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_hole ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
         Qs S1 (Ξ1 ++ Θ) m' pskl_hole Q2) ->
    Qs S0 Θ m P Q.

Fixpoint e_solve_sub_order_sind S0 Θ m P Q
    (H : e_solve_sub_order S0 Θ m P Q) {struct H} : Qs S0 Θ m P Q :=
  match H in e_solve_sub_order S0' Θ' m' Pa Qa return Qs S0' Θ' m' Pa Qa with
  | e_solve_sub_order__intro _ _ _ _ _ p1 p2 p3 p4 p5 p6 =>
      Hstep
        p1
        (fun P1 e1 => e_solve_sub_order_sind (p1 P1 e1))
        p2
        (fun P1 e1 => e_solve_sub_order_sind (p2 P1 e1))
        p3
        p4
        (fun B e1 e2 => e_solve_sub_order_sind (p4 B e1 e2))
        p5
        (fun m' P1 P2 Q1 Q2 e1 e2 e3 S1 Ξ1 P1' Hrun =>
           e_solve_sub_order_sind
             (match p5 m' P1 P2 Q1 Q2 e1 e2 e3 with
              | conj _ Hb => Hb
              end S1 Ξ1 P1' Hrun))
        p6
        (fun m' Q1 Q2 e1 e2 e3 S1 Ξ1 P1' Hrun =>
           e_solve_sub_order_sind
             (match p6 m' Q1 Q2 e1 e2 e3 with
              | conj _ Hb => Hb
              end S1 Ξ1 P1' Hrun))
  end.

End e_solve_sub_order_sind.

(* --------------------------------------------------------------------- *)
(*  §4d  Completeness of the sub-solve runner                             *)
(* --------------------------------------------------------------------- *)

Local Ltac kill_seq_call_g Hder Hagr Hscp Hcv r Hr :=
  match goal with
  | |- context [ e_solve_eq_impl ?S ?T ?p ?q ?hp ?hq ?h ] =>
      let Hne := fresh "Hne" in
      let Hcl := fresh "Hcl" in
      assert (Hne : e_solve_eq_impl S T p q hp hq h <> None)
        by (exact (e_solve_eq_impl_complete hp hq h Hder Hagr Hscp Hcv));
      destruct (e_solve_eq_impl S T p q hp hq h)
        as [ [r Hr] | ] eqn:Hcl;
      [ cbv beta iota; clear Hne Hcl | exact (False_ind _ (Hne eq_refl)) ]
  end.

Local Ltac kill_ssub_call IH Hder Hagr Hscp Hcv r Hr :=
  match goal with
  | |- context [ e_solve_sub_impl ?S ?T ?M ?p ?q ?hp ?hq ?h ] =>
      let Hne := fresh "Hne" in
      let Hcl := fresh "Hcl" in
      assert (Hne : e_solve_sub_impl S T M p q hp hq h <> None)
        by (exact (IH hp hq h _ _ _ Hder Hagr Hscp Hcv));
      destruct (e_solve_sub_impl S T M p q hp hq h)
        as [ [r Hr] | ] eqn:Hcl;
      [ cbv beta iota; clear Hne Hcl | exact (False_ind _ (Hne eq_refl)) ]
  end.

Lemma e_solve_sub_impl_complete : forall S0 Θ m P Q
    (HP : lc_pskl P) (HQ : lc_pskl Q)
    (H : e_solve_sub_order S0 Θ m P Q) Θd Ξd P'd,
  {{ Θd ⊢ₛ P ≼[ m ] Q ⤳ Ξd ⨾ P'd }}a ->
  flex_agree (ftvar_in_pskl P ∪ ftvar_in_pskl Q) Θd Θ ->
  ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] ftvar_in_aenv Θd ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  e_solve_sub_impl S0 Θ m P Q HP HQ H <> None.
Proof.
  intros S0 Θ m P Q HP HQ H Θd Ξd P'd Hd Hagr Hscp Hcov.
  pose proof H as Hind.
  revert HP HQ H Θd Ξd P'd Hd Hagr Hscp Hcov.
  apply (e_solve_sub_order_sind
           (fun S0 Θ m P Q =>
              forall (HP : lc_pskl P) (HQ : lc_pskl Q)
                     (H : e_solve_sub_order S0 Θ m P Q) Θd Ξd P'd,
                {{ Θd ⊢ₛ P ≼[ m ] Q ⤳ Ξd ⨾ P'd }}a ->
                flex_agree (ftvar_in_pskl P ∪ ftvar_in_pskl Q) Θd Θ ->
                ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] ftvar_in_aenv Θd ->
                ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q
                  [<=] S0 ->
                e_solve_sub_impl S0 Θ m P Q HP HQ H <> None));
    [ | exact Hind ].
  clear.
  intros S0 Θ m P Q p1 q1 p2 q2 p3 p4 q4 p5 q5 p6 q6
         HP HQ H Θd Ξd P'd Hd Hagr Hscp Hcov.
  destruct P as [ | n | βv | P1 P2 | P1 | | P1 ].
  - (* subject unit *)
    destruct Q as [ | n' | β' | Q1 Q2 | B | | Q1 ].
    + (* unit *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * (* tc — SS-Check *)
        simp e_solve_sub_impl. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_solve_eq Θd pskl_unit pskl_unit _ _ |- _ =>
               rename Hp0 into HPREM
           end.
           kill_seq_call_g HPREM Hagr Hscp Hcov
             r1 Hr1.
           discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* var_b *) inversion HQ.
    + (* var_f *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * (* tc — SS-Check *)
        simp e_solve_sub_impl. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_solve_eq Θd pskl_unit (pskl_var_f β') _ _ |- _ =>
               rename Hp0 into HPREM
           end.
           kill_seq_call_g HPREM Hagr Hscp Hcov
             r1 Hr1.
           discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* arrow *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * (* tc — SS-Check *)
        simp e_solve_sub_impl. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_solve_eq Θd pskl_unit (pskl_arrow Q1 Q2) _ _ |- _ =>
               rename Hp0 into HPREM
           end.
           kill_seq_call_g HPREM Hagr Hscp Hcov
             r1 Hr1.
           discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* all_syn — SS-ForallR at the committed opener *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hfr0 : ?b `notin` _,
             Hp0 : a_solve_sub ((?b ~ abind_tvar) ++ Θd) mode_tc _ _ _ _
             |- _ =>
               assert (Hbfr : b `notin`
                         ftvar_in_pskl pskl_unit ∪ ftvar_in_pskl B)
                 by (clear - Hfr0; simpl in *; fsetdec);
               assert (Hβfr : supply_fresh S0 `notin`
                         ftvar_in_pskl pskl_unit ∪ ftvar_in_pskl B)
                 by (pose proof (supply_fresh_notin S0) as Hsf;
                     clear - Hcov Hsf; simpl in *; fsetdec);
               destruct (a_solve_sub_rebind_r_ctx Hp0 Hbfr Hβfr)
                 as [Ξ2 [P2' HP2]];
               assert (HbΘ : b `notin` dom Θd)
                 by (pose proof (dom_subset_ftvar_in_aenv Θd) as Hds;
                     clear - Hfr0 Hds; fsetdec);
               assert (Hag0 : flex_agree
                         (ftvar_in_pskl pskl_unit ∪ ftvar_in_pskl B)
                         (swap_aenv b (supply_fresh S0) Θd) Θ)
                 by (apply flex_agree_swap_left;
                     [ clear - Hfr0; simpl in *; fsetdec
                     | pose proof (supply_fresh_notin S0) as Hsf;
                       clear - Hcov Hsf; simpl in *; fsetdec
                     | eapply flex_agree_weaken;
                       [ exact Hagr | simpl; clear; fsetdec ] ]);
               assert (Hag1 : flex_agree
                         (add (supply_fresh S0)
                            (ftvar_in_pskl pskl_unit ∪ ftvar_in_pskl B))
                         ((supply_fresh S0 ~ abind_tvar)
                            ++ swap_aenv b (supply_fresh S0) Θd)
                         ((supply_fresh S0 ~ abind_tvar) ++ Θ))
                 by (apply flex_agree_push_tvar;
                     [ rewrite <- (swap_atom_l b (supply_fresh S0)) at 1;
                       apply swap_aenv_dom_notin; exact HbΘ
                     | pose proof (dom_subset_ftvar_in_aenv Θ) as Hds;
                       pose proof (supply_fresh_notin S0) as Hsf;
                       clear - Hcov Hds Hsf; fsetdec
                     | exact Hag0 ]);
               assert (Hagr2 : flex_agree
                         (ftvar_in_pskl pskl_unit
                          ∪ ftvar_in_pskl
                              (open_pskl_wrt_pskl B
                                 (pskl_var_f (supply_fresh S0))))
                         ((supply_fresh S0 ~ abind_tvar)
                            ++ swap_aenv b (supply_fresh S0) Θd)
                         ((supply_fresh S0 ~ abind_tvar) ++ Θ))
                 by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                                   (pskl_var_f (supply_fresh S0))) as Hu1;
                     eapply flex_agree_weaken;
                     [ exact Hag1 | clear - Hu1; simpl in *; fsetdec ]);
               assert (Hscp2 : ftvar_in_pskl pskl_unit
                               ∪ ftvar_in_pskl
                                   (open_pskl_wrt_pskl B
                                      (pskl_var_f (supply_fresh S0)))
                               [<=] ftvar_in_aenv
                                      ((supply_fresh S0 ~ abind_tvar)
                                         ++ swap_aenv b (supply_fresh S0)
                                              Θd))
                 by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                                   (pskl_var_f (supply_fresh S0))) as Hu1;
                     assert (Hsw : ftvar_in_pskl pskl_unit
                                     ∪ ftvar_in_pskl B
                                     [<=] ftvar_in_aenv
                                            (swap_aenv b (supply_fresh S0)
                                               Θd))
                       by (apply ftvar_in_aenv_swap_subset;
                           [ clear - Hscp; simpl in *; fsetdec
                           | clear - Hbfr; simpl in *; fsetdec
                           | clear - Hβfr; simpl in *; fsetdec ]);
                     rewrite ftvar_in_aenv_cons_tvar;
                     clear - Hu1 Hsw; simpl in *; fsetdec)
           end.
           pose proof (q4 B eq_refl eq_refl) as IHf.
           assert (Hcov2 : ftvar_in_aenv
                             ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                           ∪ ftvar_in_pskl pskl_unit
                           ∪ ftvar_in_pskl
                               (open_pskl_wrt_pskl B
                                  (pskl_var_f (supply_fresh S0)))
                           [<=] add (supply_fresh S0) S0).
           { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                           (pskl_var_f (supply_fresh S0))) as Hu1.
             rewrite ftvar_in_aenv_cons_tvar.
             clear - Hu1 Hcov. simpl in *. fsetdec. }
           kill_ssub_call IHf HP2 Hagr2 Hscp2 Hcov2 r1 Hr1. discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* hole — SS-Vacuous *) simp e_solve_sub_impl. discriminate.
    + (* tophole *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- match goal with
           | Ht : _ && _ = true |- _ => simpl in Ht; discriminate Ht
           end.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
  - (* subject var_b — no lc *) inversion HP.
  - (* subject var_f — SS-Var/Flex *)
    simp e_solve_sub_impl. discriminate.
  - (* subject arrow *)
    destruct Q as [ | n' | β' | Q1 Q2 | B | | Q1 ].
    + (* unit *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_solve_eq Θd (pskl_arrow P1 P2) pskl_unit _ _ |- _ =>
               rename Hp0 into HPREM
           end.
           kill_seq_call_g HPREM Hagr Hscp Hcov
             r1 Hr1.
           discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* var_b *) inversion HQ.
    + (* var_f *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_solve_eq Θd (pskl_arrow P1 P2) (pskl_var_f β') _ _
             |- _ => rename Hp0 into HPREM
           end.
           kill_seq_call_g HPREM Hagr Hscp Hcov
             r1 Hr1.
           discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* arrow *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * (* tc — SS-Check *)
        simp e_solve_sub_impl. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hp0 : a_solve_eq Θd (pskl_arrow P1 P2) (pskl_arrow Q1 Q2) _ _
             |- _ => rename Hp0 into HPREM
           end.
           kill_seq_call_g HPREM Hagr Hscp Hcov
             r1 Hr1.
           discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * (* fn — SS-Arrow: the context-threading case *)
        simp e_solve_sub_impl.
        inversion Hd; subst; try look_absurd.
        match goal with
        | Hda : a_solve_eq Θd P1 Q1 _ _ |- _ => rename Hda into HD1
        end.
        match goal with
        | Hdb : a_solve_sub (_ ++ Θd) _ P2 Q2 _ _ |- _ =>
            rename Hdb into HD2
        end.
        pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                      _ _ _ _ _ HD1) as HXd.
        assert (Hagr1 : flex_agree (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1)
                          Θd Θ)
          by (eapply flex_agree_weaken;
              [ exact Hagr | simpl; clear; fsetdec ]).
        assert (Hscp1 : ftvar_in_pskl P1 ∪ ftvar_in_pskl Q1
                          [<=] ftvar_in_aenv Θd)
          by (clear - Hscp; simpl in *; fsetdec).
        assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P1
                          ∪ ftvar_in_pskl Q1 [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        kill_seq_call_g HD1 Hagr1 Hscp1 Hcov1
          r1 Hr1.
        unfold solve_eq_spec in Hr1.
        pose proof (e_solve_eq_supply_grows Hr1) as Hgrow.
        pose proof ((proj2 e_solve_sub_eq_block) _ _ _ _ _ _ _ Hr1)
          as [Hb1 [Hb2 [Hb3 Hb4]]].
        pose proof (q5 m'2 P1 P2 Q1 Q2 eq_refl eq_refl eq_refl
                      _ _ _ Hr1) as IH2.
        match goal with
        | HD2' : a_solve_sub (?X ++ Θd) _ P2 Q2 _ _ |- _ =>
            assert (Hagr2 : flex_agree
                              (ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2)
                              (X ++ Θd) (sv_block r1 ++ Θ))
              by (apply flex_agree_push_blocks;
                  [ clear - HXd Hscp; simpl in *; fsetdec
                  | clear - Hb2 Hcov; simpl in *; fsetdec
                  | eapply flex_agree_weaken;
                    [ exact Hagr | simpl; clear; fsetdec ] ]);
            assert (Hscp2 : ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2
                              [<=] ftvar_in_aenv (X ++ Θd))
              by (rewrite ftvar_in_aenv_app; clear - Hscp; simpl in Hscp;
                  fsetdec)
        end.
        assert (Hcov2 : ftvar_in_aenv (sv_block r1 ++ Θ)
                          ∪ ftvar_in_pskl P2 ∪ ftvar_in_pskl Q2
                          [<=] sv_supply r1)
          by (rewrite ftvar_in_aenv_app;
              clear - Hb1 Hb4 Hgrow Hcov; simpl in *; fsetdec).
        kill_ssub_call IH2 HD2 Hagr2 Hscp2 Hcov2 r2 Hr2. discriminate.
    + (* all_syn — SS-ForallR at the committed opener *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hfr0 : ?b `notin` _,
             Hp0 : a_solve_sub ((?b ~ abind_tvar) ++ Θd) mode_tc _ _ _ _
             |- _ =>
               assert (Hbfr : b `notin`
                         ftvar_in_pskl (pskl_arrow P1 P2)
                           ∪ ftvar_in_pskl B)
                 by (clear - Hfr0; simpl in *; fsetdec);
               assert (Hβfr : supply_fresh S0 `notin`
                         ftvar_in_pskl (pskl_arrow P1 P2)
                           ∪ ftvar_in_pskl B)
                 by (pose proof (supply_fresh_notin S0) as Hsf;
                     clear - Hcov Hsf; simpl in *; fsetdec);
               destruct (a_solve_sub_rebind_r_ctx Hp0 Hbfr Hβfr)
                 as [Ξ2 [P2' HP2]];
               assert (HbΘ : b `notin` dom Θd)
                 by (pose proof (dom_subset_ftvar_in_aenv Θd) as Hds;
                     clear - Hfr0 Hds; fsetdec);
               assert (Hag0 : flex_agree
                         (ftvar_in_pskl (pskl_arrow P1 P2)
                            ∪ ftvar_in_pskl B)
                         (swap_aenv b (supply_fresh S0) Θd) Θ)
                 by (apply flex_agree_swap_left;
                     [ clear - Hfr0; simpl in *; fsetdec
                     | pose proof (supply_fresh_notin S0) as Hsf;
                       clear - Hcov Hsf; simpl in *; fsetdec
                     | eapply flex_agree_weaken;
                       [ exact Hagr | simpl; clear; fsetdec ] ]);
               assert (Hag1 : flex_agree
                         (add (supply_fresh S0)
                            (ftvar_in_pskl (pskl_arrow P1 P2)
                               ∪ ftvar_in_pskl B))
                         ((supply_fresh S0 ~ abind_tvar)
                            ++ swap_aenv b (supply_fresh S0) Θd)
                         ((supply_fresh S0 ~ abind_tvar) ++ Θ))
                 by (apply flex_agree_push_tvar;
                     [ rewrite <- (swap_atom_l b (supply_fresh S0)) at 1;
                       apply swap_aenv_dom_notin; exact HbΘ
                     | pose proof (dom_subset_ftvar_in_aenv Θ) as Hds;
                       pose proof (supply_fresh_notin S0) as Hsf;
                       clear - Hcov Hds Hsf; fsetdec
                     | exact Hag0 ]);
               assert (Hagr2 : flex_agree
                         (ftvar_in_pskl (pskl_arrow P1 P2)
                          ∪ ftvar_in_pskl
                              (open_pskl_wrt_pskl B
                                 (pskl_var_f (supply_fresh S0))))
                         ((supply_fresh S0 ~ abind_tvar)
                            ++ swap_aenv b (supply_fresh S0) Θd)
                         ((supply_fresh S0 ~ abind_tvar) ++ Θ))
                 by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                                   (pskl_var_f (supply_fresh S0))) as Hu1;
                     eapply flex_agree_weaken;
                     [ exact Hag1 | clear - Hu1; simpl in *; fsetdec ]);
               assert (Hscp2 : ftvar_in_pskl (pskl_arrow P1 P2)
                               ∪ ftvar_in_pskl
                                   (open_pskl_wrt_pskl B
                                      (pskl_var_f (supply_fresh S0)))
                               [<=] ftvar_in_aenv
                                      ((supply_fresh S0 ~ abind_tvar)
                                         ++ swap_aenv b (supply_fresh S0)
                                              Θd))
                 by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                                   (pskl_var_f (supply_fresh S0))) as Hu1;
                     assert (Hsw : ftvar_in_pskl (pskl_arrow P1 P2)
                                     ∪ ftvar_in_pskl B
                                     [<=] ftvar_in_aenv
                                            (swap_aenv b (supply_fresh S0)
                                               Θd))
                       by (apply ftvar_in_aenv_swap_subset;
                           [ clear - Hscp; simpl in *; fsetdec
                           | clear - Hbfr; simpl in *; fsetdec
                           | clear - Hβfr; simpl in *; fsetdec ]);
                     rewrite ftvar_in_aenv_cons_tvar;
                     clear - Hu1 Hsw; simpl in *; fsetdec)
           end.
           pose proof (q4 B eq_refl eq_refl) as IHf.
           assert (Hcov2 : ftvar_in_aenv
                             ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                           ∪ ftvar_in_pskl (pskl_arrow P1 P2)
                           ∪ ftvar_in_pskl
                               (open_pskl_wrt_pskl B
                                  (pskl_var_f (supply_fresh S0)))
                           [<=] add (supply_fresh S0) S0).
           { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                           (pskl_var_f (supply_fresh S0))) as Hu1.
             rewrite ftvar_in_aenv_cons_tvar.
             clear - Hu1 Hcov. simpl in *. fsetdec. }
           kill_ssub_call IHf HP2 Hagr2 Hscp2 Hcov2 r1 Hr1. discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* hole — SS-Vacuous *) simp e_solve_sub_impl. discriminate.
    + (* tophole *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- match goal with
           | Ht : _ && _ = true |- _ => simpl in Ht; discriminate Ht
           end.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
  - (* subject all_syn — the ForallL-first reorder, uniformly: any root *)
    simp e_solve_sub_impl.
    assert (Hβfr : supply_fresh S0 `notin`
              ftvar_in_pskl P1 ∪ ftvar_in_pskl Q)
      by (pose proof (supply_fresh_notin S0) as Hsf;
          clear - Hcov Hsf; simpl in *; fsetdec).
    assert (Hagr' : flex_agree (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q) Θd Θ)
      by (eapply flex_agree_weaken; [ exact Hagr | simpl; clear; fsetdec ]).
    assert (Hscp' : ftvar_in_pskl P1 ∪ ftvar_in_pskl Q
                      [<=] ftvar_in_aenv Θd)
      by (clear - Hscp; simpl in *; fsetdec).
    destruct (a_solve_sub_forall_l_first Hd Hagr' Hscp' Hβfr)
      as [Θd1 [Ξ2 [P2' [E [Hagr1 [Hscp1 Hdom1]]]]]].
    pose proof (q1 P1 eq_refl) as IHf.
    assert (Hag1 : flex_agree
              (add (supply_fresh S0)
                 (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q))
              ((supply_fresh S0 ~ abind_tvar) ++ Θd1)
              ((supply_fresh S0 ~ abind_tvar) ++ Θ))
      by (apply flex_agree_push_tvar;
          [ exact Hdom1
          | pose proof (dom_subset_ftvar_in_aenv Θ) as Hds;
            pose proof (supply_fresh_notin S0) as Hsf;
            clear - Hcov Hds Hsf; fsetdec
          | exact Hagr1 ]).
    assert (Hagr2 : flex_agree
              (ftvar_in_pskl (open_pskl_wrt_pskl P1
                                (pskl_var_f (supply_fresh S0)))
               ∪ ftvar_in_pskl Q)
              ((supply_fresh S0 ~ abind_tvar) ++ Θd1)
              ((supply_fresh S0 ~ abind_tvar) ++ Θ))
      by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
                        (pskl_var_f (supply_fresh S0))) as Hu1;
          eapply flex_agree_weaken;
          [ exact Hag1 | clear - Hu1; simpl in *; fsetdec ]).
    assert (Hscp2 : ftvar_in_pskl (open_pskl_wrt_pskl P1
                       (pskl_var_f (supply_fresh S0)))
                    ∪ ftvar_in_pskl Q
                    [<=] ftvar_in_aenv
                           ((supply_fresh S0 ~ abind_tvar) ++ Θd1))
      by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
                        (pskl_var_f (supply_fresh S0))) as Hu1;
          rewrite ftvar_in_aenv_cons_tvar;
          clear - Hu1 Hscp1; simpl in *; fsetdec).
    assert (Hcov2 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl P1
                           (pskl_var_f (supply_fresh S0)))
                      ∪ ftvar_in_pskl Q
                      [<=] add (supply_fresh S0) S0)
      by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P1
                        (pskl_var_f (supply_fresh S0))) as Hu1;
          rewrite ftvar_in_aenv_cons_tvar;
          clear - Hu1 Hcov; simpl in *; fsetdec).
    kill_ssub_call IHf E Hagr2 Hscp2 Hcov2 r1 Hr1. discriminate.
  - (* subject hole *)
    destruct Q as [ | n' | β' | Q1 Q2 | B | | Q1 ].
    + (* unit — SS-GhostL *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* var_b *) inversion HQ.
    + (* var_f — SS-GhostL *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* arrow *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * (* tc — SS-GhostL *)
        simp e_solve_sub_impl. case_test.
        -- discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * (* fn — SS-GhostLF: the ◇ expands along the counterpart's arrow *)
        simp e_solve_sub_impl.
        inversion Hd; subst; try look_absurd.
        match goal with
        | Hda : a_solve_eq Θd pskl_hole Q1 _ _ |- _ => rename Hda into HD1
        end.
        match goal with
        | Hdb : a_solve_sub (_ ++ Θd) _ pskl_hole Q2 _ _ |- _ =>
            rename Hdb into HD2
        end.
        pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                      _ _ _ _ _ HD1) as HXd.
        assert (Hagr1 : flex_agree
                          (ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl Q1)
                          Θd Θ)
          by (eapply flex_agree_weaken;
              [ exact Hagr | simpl; clear; fsetdec ]).
        assert (Hscp1 : ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl Q1
                          [<=] ftvar_in_aenv Θd)
          by (clear - Hscp; simpl in *; fsetdec).
        assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl pskl_hole
                          ∪ ftvar_in_pskl Q1 [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        kill_seq_call_g HD1 Hagr1 Hscp1 Hcov1
          r1 Hr1.
        unfold solve_eq_spec in Hr1.
        pose proof (e_solve_eq_supply_grows Hr1) as Hgrow.
        pose proof ((proj2 e_solve_sub_eq_block) _ _ _ _ _ _ _ Hr1)
          as [Hb1 [Hb2 [Hb3 Hb4]]].
        pose proof (q6 m'2 Q1 Q2 eq_refl eq_refl eq_refl _ _ _ Hr1)
          as IH2.
        match goal with
        | HD2' : a_solve_sub (?X ++ Θd) _ pskl_hole Q2 _ _ |- _ =>
            assert (Hagr2 : flex_agree
                              (ftvar_in_pskl pskl_hole
                                 ∪ ftvar_in_pskl Q2)
                              (X ++ Θd) (sv_block r1 ++ Θ))
              by (apply flex_agree_push_blocks;
                  [ clear - HXd Hscp; simpl in *; fsetdec
                  | clear - Hb2 Hcov; simpl in *; fsetdec
                  | eapply flex_agree_weaken;
                    [ exact Hagr | simpl; clear; fsetdec ] ]);
            assert (Hscp2 : ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl Q2
                              [<=] ftvar_in_aenv (X ++ Θd))
              by (rewrite ftvar_in_aenv_app; clear - Hscp; simpl in Hscp;
                  fsetdec)
        end.
        assert (Hcov2 : ftvar_in_aenv (sv_block r1 ++ Θ)
                          ∪ ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl Q2
                          [<=] sv_supply r1)
          by (rewrite ftvar_in_aenv_app;
              clear - Hb1 Hb4 Hgrow Hcov; simpl in *; fsetdec).
        kill_ssub_call IH2 HD2 Hagr2 Hscp2 Hcov2 r2 Hr2. discriminate.
    + (* all_syn — SS-ForallR at the committed opener *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- inversion Hd; subst; try look_absurd.
           match goal with
           | Hfr0 : ?b `notin` _,
             Hp0 : a_solve_sub ((?b ~ abind_tvar) ++ Θd) mode_tc _ _ _ _
             |- _ =>
               assert (Hbfr : b `notin`
                         ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl B)
                 by (clear - Hfr0; simpl in *; fsetdec);
               assert (Hβfr : supply_fresh S0 `notin`
                         ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl B)
                 by (pose proof (supply_fresh_notin S0) as Hsf;
                     clear - Hcov Hsf; simpl in *; fsetdec);
               destruct (a_solve_sub_rebind_r_ctx Hp0 Hbfr Hβfr)
                 as [Ξ2 [P2' HP2]];
               assert (HbΘ : b `notin` dom Θd)
                 by (pose proof (dom_subset_ftvar_in_aenv Θd) as Hds;
                     clear - Hfr0 Hds; fsetdec);
               assert (Hag0 : flex_agree
                         (ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl B)
                         (swap_aenv b (supply_fresh S0) Θd) Θ)
                 by (apply flex_agree_swap_left;
                     [ clear - Hfr0; simpl in *; fsetdec
                     | pose proof (supply_fresh_notin S0) as Hsf;
                       clear - Hcov Hsf; simpl in *; fsetdec
                     | eapply flex_agree_weaken;
                       [ exact Hagr | simpl; clear; fsetdec ] ]);
               assert (Hag1 : flex_agree
                         (add (supply_fresh S0)
                            (ftvar_in_pskl pskl_hole ∪ ftvar_in_pskl B))
                         ((supply_fresh S0 ~ abind_tvar)
                            ++ swap_aenv b (supply_fresh S0) Θd)
                         ((supply_fresh S0 ~ abind_tvar) ++ Θ))
                 by (apply flex_agree_push_tvar;
                     [ rewrite <- (swap_atom_l b (supply_fresh S0)) at 1;
                       apply swap_aenv_dom_notin; exact HbΘ
                     | pose proof (dom_subset_ftvar_in_aenv Θ) as Hds;
                       pose proof (supply_fresh_notin S0) as Hsf;
                       clear - Hcov Hds Hsf; fsetdec
                     | exact Hag0 ]);
               assert (Hagr2 : flex_agree
                         (ftvar_in_pskl pskl_hole
                          ∪ ftvar_in_pskl
                              (open_pskl_wrt_pskl B
                                 (pskl_var_f (supply_fresh S0))))
                         ((supply_fresh S0 ~ abind_tvar)
                            ++ swap_aenv b (supply_fresh S0) Θd)
                         ((supply_fresh S0 ~ abind_tvar) ++ Θ))
                 by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                                   (pskl_var_f (supply_fresh S0))) as Hu1;
                     eapply flex_agree_weaken;
                     [ exact Hag1 | clear - Hu1; simpl in *; fsetdec ]);
               assert (Hscp2 : ftvar_in_pskl pskl_hole
                               ∪ ftvar_in_pskl
                                   (open_pskl_wrt_pskl B
                                      (pskl_var_f (supply_fresh S0)))
                               [<=] ftvar_in_aenv
                                      ((supply_fresh S0 ~ abind_tvar)
                                         ++ swap_aenv b (supply_fresh S0)
                                              Θd))
                 by (pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                                   (pskl_var_f (supply_fresh S0))) as Hu1;
                     assert (Hsw : ftvar_in_pskl pskl_hole
                                     ∪ ftvar_in_pskl B
                                     [<=] ftvar_in_aenv
                                            (swap_aenv b (supply_fresh S0)
                                               Θd))
                       by (apply ftvar_in_aenv_swap_subset;
                           [ clear - Hscp; simpl in *; fsetdec
                           | clear - Hbfr; simpl in *; fsetdec
                           | clear - Hβfr; simpl in *; fsetdec ]);
                     rewrite ftvar_in_aenv_cons_tvar;
                     clear - Hu1 Hsw; simpl in *; fsetdec)
           end.
           pose proof (q4 B eq_refl eq_refl) as IHf.
           assert (Hcov2 : ftvar_in_aenv
                             ((supply_fresh S0 ~ abind_tvar) ++ Θ)
                           ∪ ftvar_in_pskl pskl_hole
                           ∪ ftvar_in_pskl
                               (open_pskl_wrt_pskl B
                                  (pskl_var_f (supply_fresh S0)))
                           [<=] add (supply_fresh S0) S0).
           { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                           (pskl_var_f (supply_fresh S0))) as Hu1.
             rewrite ftvar_in_aenv_cons_tvar.
             clear - Hu1 Hcov. simpl in *. fsetdec. }
           kill_ssub_call IHf HP2 Hagr2 Hscp2 Hcov2 r1 Hr1. discriminate.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
    + (* hole — SS-Vacuous *) simp e_solve_sub_impl. discriminate.
    + (* tophole — SS-GhostL's clause at a ⫯ target *)
      destruct m as [ | | m'2 ].
      * inversion Hd.
      * simp e_solve_sub_impl. case_test.
        -- match goal with
           | Ht : _ && _ = true |- _ => simpl in Ht; discriminate Ht
           end.
        -- exfalso. inversion Hd; subst; look_absurd.
      * inversion Hd.
  - (* subject tophole — the strip reorder, uniformly: any root *)
    simp e_solve_sub_impl.
    destruct (a_solve_sub_tophole_l_first Hd eq_refl) as [Ξ2 [P2' HP2]].
    pose proof (q2 P1 eq_refl) as IHf.
    assert (Hagr1 : flex_agree (ftvar_in_pskl P1 ∪ ftvar_in_pskl Q) Θd Θ)
      by (eapply flex_agree_weaken; [ exact Hagr | simpl; clear; fsetdec ]).
    assert (Hscp1 : ftvar_in_pskl P1 ∪ ftvar_in_pskl Q
                      [<=] ftvar_in_aenv Θd)
      by (clear - Hscp; simpl in *; fsetdec).
    assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P1 ∪ ftvar_in_pskl Q
                      [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    kill_ssub_call IHf HP2 Hagr1 Hscp1 Hcov1 r1 Hr1. discriminate.
Qed.

(** ⭐ The sub-solve headline: a derivation at scoped, covered inputs means
    the runner answers.  The context equality at the entry point makes the
    agreement premise reflexive. *)
Lemma e_solve_sub_run_complete : forall S0 Θ m P Q HP HQ Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
  ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] ftvar_in_aenv Θ ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  e_solve_sub_run S0 Θ m P Q HP HQ <> None.
Proof.
  intros * Hd Hscp Hcov. unfold e_solve_sub_run.
  assert (Hagr : flex_agree (ftvar_in_pskl P ∪ ftvar_in_pskl Q) Θ Θ)
    by apply flex_agree_refl.
  pose proof (e_solve_sub_impl_complete HP HQ
                (@e_solve_sub_order_total S0 Θ m P Q HP)
                Hd Hagr Hscp Hcov) as Hne.
  revert Hne.
  destruct (e_solve_sub_impl S0 Θ m P Q HP HQ
              (@e_solve_sub_order_total S0 Θ m P Q HP)) as [ [r Hr] | ];
    intros Hne.
  - discriminate.
  - exact (False_ind _ (Hne eq_refl)).
Qed.

(* ===================================================================== *)
(*  §5  The CSTR fold (§8c.3, level 3)                                    *)
(*                                                                        *)
(*  The fold's eq-cons row is where the campaign's ⛔ YIELD MISMATCH      *)
(*  lands: the runner's tail runs on the RUNNER's yield [sv_out r1] while *)
(*  the inverted derivation's tail sits on the DERIVATION's yield.        *)
(*  Yields are SUBJECTS, so — unlike contexts — [flex_agree] cannot       *)
(*  absorb the difference.  The fork was resolved as option (a) (user     *)
(*  decision, §8c.6): the solve layer is DETERMINISTIC UP TO FRESH        *)
(*  RENAMING (frost/ext_algo/prop_solve_det.v), so the two yields differ  *)
(*  by an aligned fresh-pair list ρ, and the derivation's TAIL is         *)
(*  transported along ρ's palindromic swap chain                          *)
(*  ([a_solve_cstr_swaps] on [chain ρ zs]) before it feeds the IH:        *)
(*                                                                        *)
(*    - the context      [swaps_aenv_app_dist] + [chain_flex_pairs]:      *)
(*      the derivation's block IS the runner's block, entry by entry;     *)
(*    - the subject      [rel_pskl_chain]: the chain realizes the         *)
(*      relation, so the transported yield IS [sv_out r1];                *)
(*    - the constraints  [swaps_cstrs_fresh_id]: [C'] is FIXED — every    *)
(*      chain atom avoids it (the left column dodges [ftvar_in_aenv Θd],  *)
(*      the right one dodges the supply, the intermediates are freshly    *)
(*      drawn).                                                           *)
(*                                                                        *)
(*  ⚠️ [uniq Ξd] is a REQUIRED premise, not a defensive one: the a-side   *)
(*  may guess the SAME flexible for two holes ([a_guess_mono__arrow] runs *)
(*  both halves at one Θ), and then no renaming to the runner's run       *)
(*  exists at all.  It splits recursively — blocks only append upward —   *)
(*  and the flagships' derivations carry it (the e-bridge, or             *)
(*  wf-preservation).                                                     *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(*  §5a  The chain-folded context kit                                     *)
(*                                                                        *)
(*  Three n-fold companions of §3a's singles, all under the same          *)
(*  hypothesis — every chain pair avoids the fold's variable set — plus   *)
(*  the one genuinely new fact: both sides gain the SAME flex block at    *)
(*  the head, so agreement EXTENDS to that block's own atoms (which is    *)
(*  what [rel_pskl_ftv_r] then needs, since the transported yield may     *)
(*  mention them).                                                        *)
(* --------------------------------------------------------------------- *)

Lemma a_flex_tvar_cons_flex_other : forall b (Θ : aenv) α,
  α <> b ->
  (a_flex_tvar ((b, abind_flex_mono) :: Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros * Hne. split.
  - intros [Hb | [τ Hb]]; unfold binds in Hb; simpl in Hb;
      (destruct Hb as [Hb | Hb]; [ solve [ inversion Hb; congruence ] | ]);
      [ left; exact Hb | right; eexists; exact Hb ].
  - intros [Hb | [τ Hb]]; [ left | right; eexists ];
      unfold binds in *; simpl; right; eassumption.
Qed.

Lemma flex_agree_flex_block : forall ρ V Θ1 Θ2,
  flex_agree V Θ1 Θ2 ->
  flex_agree (V ∪ cols_r ρ) (flex_pairs_r ρ ++ Θ1) (flex_pairs_r ρ ++ Θ2).
Proof.
  induction ρ as [ | [a b] ρ IH ]; intros V Θ1 Θ2 Hag.
  - eapply flex_agree_weaken; [ exact Hag | simpl; clear; fsetdec ].
  - replace (flex_pairs_r ((a, b) :: ρ))
      with ((b, abind_flex_mono) :: flex_pairs_r ρ) by reflexivity.
    replace (cols_r ((a, b) :: ρ)) with (add b (cols_r ρ)) by reflexivity.
    intros α Hα.
    destruct (α == b) as [-> | Hne].
    + (* the head atom is flexible on BOTH sides, by construction *)
      split; intros _; left; unfold binds; simpl; left; reflexivity.
    + rewrite (a_flex_tvar_cons_flex_other (flex_pairs_r ρ ++ Θ1) Hne),
              (a_flex_tvar_cons_flex_other (flex_pairs_r ρ ++ Θ2) Hne).
      apply (IH V Θ1 Θ2 Hag α). clear - Hα Hne. fsetdec.
Qed.

Lemma flex_agree_swaps_left : forall ps V Θ1 Θ2,
  (forall a b, In (a, b) ps -> a `notin` V /\ b `notin` V) ->
  flex_agree V Θ1 Θ2 ->
  flex_agree V (swaps_aenv ps Θ1) Θ2.
Proof.
  induction ps as [ | [a b] ps IH ]; intros V Θ1 Θ2 Hav Hag; simpl;
    [ exact Hag | ].
  destruct (Hav a b (or_introl eq_refl)) as [Hna Hnb].
  apply IH; [ intros a' b' Hin; apply Hav; right; exact Hin | ].
  apply flex_agree_swap_left; assumption.
Qed.

Lemma ftvar_in_aenv_swaps_subset : forall ps (Θ : aenv) V,
  V [<=] ftvar_in_aenv Θ ->
  (forall a b, In (a, b) ps -> a `notin` V /\ b `notin` V) ->
  V [<=] ftvar_in_aenv (swaps_aenv ps Θ).
Proof.
  induction ps as [ | [a b] ps IH ]; intros Θ V Hsub Hav; simpl;
    [ exact Hsub | ].
  destruct (Hav a b (or_introl eq_refl)) as [Hna Hnb].
  apply IH; [ apply ftvar_in_aenv_swap_subset; assumption
            | intros a' b' Hin; apply Hav; right; exact Hin ].
Qed.

(* ⚙ The fold's two head inversions ([a_solve_cstr_sub_inv] /
   [a_solve_cstr_eq_inv]) MOVED to ext_algo/prop_look_equiv.v (2026-08-16,
   with the extract level's foundations — that file sits below this one
   and §6 will consume both). *)

(* --------------------------------------------------------------------- *)
(*  §5b  Strong induction for [e_solve_cstr_order]                        *)
(*                                                                        *)
(*  §2a/§3c/§4c's idiom.  The sub premise and the eq-order half stay      *)
(*  UNDOUBLED (levels 2b and 2a are finished lemmas, ∀-quantified over    *)
(*  their domain proofs); only the TAIL companion — which already sits at *)
(*  the RUNNER's yield — gets a motive twin.                              *)
(* --------------------------------------------------------------------- *)

Section e_solve_cstr_order_sind.

Variable Qc : supply -> aenv -> a_cstrs -> pskl -> Prop.

Hypothesis Hstep : forall S0 Θ C P,
    (* the sub-SINGLETON row — level 2b, as-is *)
    (forall m Q,
       C = a_cstr_sub m Q :: nil ->
       e_solve_sub_order S0 Θ m P Q) ->
    (* the eq-cons row: head order (level 2a, as-is) + threaded tail *)
    (forall Q C',
       C = a_cstr_eq Q :: C' ->
       e_solve_eq_order S0 Θ P Q
       /\ (forall S1 Ξ1 P'',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}e ->
             e_solve_cstr_order S1 (Ξ1 ++ Θ) C' P'')) ->
    (forall Q C',
       C = a_cstr_eq Q :: C' ->
       forall S1 Ξ1 P'',
         {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}e ->
         Qc S1 (Ξ1 ++ Θ) C' P'') ->
    Qc S0 Θ C P.

Fixpoint e_solve_cstr_order_sind S0 Θ C P
    (H : e_solve_cstr_order S0 Θ C P) {struct H} : Qc S0 Θ C P :=
  match H in e_solve_cstr_order S0' Θ' C0 P0 return Qc S0' Θ' C0 P0 with
  | e_solve_cstr_order__intro _ _ _ _ p1 p2 =>
      Hstep
        p1
        p2
        (fun Q C' e1 S1 Ξ1 P'' Hrun =>
           e_solve_cstr_order_sind
             (match p2 Q C' e1 with
              | conj _ Hb => Hb
              end S1 Ξ1 P'' Hrun))
  end.

End e_solve_cstr_order_sind.

(* --------------------------------------------------------------------- *)
(*  §5c  Completeness of the constraint-fold runner                       *)
(* --------------------------------------------------------------------- *)

(** The direct-lemma kill for the sub-SINGLETON leaf (level 2b's finished
    lemma has [Θd Ξd P'd] implicit — no placeholders, cf. §4d). *)
Local Ltac kill_ssub_call_g Hder Hagr Hscp Hcv r Hr :=
  match goal with
  | |- context [ e_solve_sub_impl ?S ?T ?M ?p ?q ?hp ?hq ?h ] =>
      let Hne := fresh "Hne" in
      let Hcl := fresh "Hcl" in
      assert (Hne : e_solve_sub_impl S T M p q hp hq h <> None)
        by (exact (e_solve_sub_impl_complete hp hq h Hder Hagr Hscp Hcv));
      destruct (e_solve_sub_impl S T M p q hp hq h)
        as [ [r Hr] | ] eqn:Hcl;
      [ cbv beta iota; clear Hne Hcl | exact (False_ind _ (Hne eq_refl)) ]
  end.

(** The fold's own recursive call — the sind companion's variant, so the
    three result-side arguments ARE passed. *)
Local Ltac kill_scstr_call IH Hder Hun Hagr Hscp Hcv r Hr :=
  match goal with
  | |- context [ e_solve_cstr_impl ?S ?T ?c ?p ?hp ?hc ?h ] =>
      let Hne := fresh "Hne" in
      let Hcl := fresh "Hcl" in
      assert (Hne : e_solve_cstr_impl S T c p hp hc h <> None)
        by (exact (IH hp hc h _ _ _ Hder Hun Hagr Hscp Hcv));
      destruct (e_solve_cstr_impl S T c p hp hc h)
        as [ [r Hr] | ] eqn:Hcl;
      [ cbv beta iota; clear Hne Hcl | exact (False_ind _ (Hne eq_refl)) ]
  end.

Lemma e_solve_cstr_impl_complete : forall S0 Θ C P
    (HP : lc_pskl P) (HC : Forall lc_a_cstr C)
    (H : e_solve_cstr_order S0 Θ C P) Θd Ξd P'd,
  {{ Θd ⊩ C ⨾ P ⤳ Ξd ⨾ P'd }}a ->
  uniq Ξd ->
  flex_agree (ftvar_in_pskl P ∪ ftvar_in_a_cstrs C) Θd Θ ->
  ftvar_in_pskl P ∪ ftvar_in_a_cstrs C [<=] ftvar_in_aenv Θd ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_a_cstrs C [<=] S0 ->
  e_solve_cstr_impl S0 Θ C P HP HC H <> None.
Proof.
  intros S0 Θ C P HP HC H Θd Ξd P'd Hd Hun Hagr Hscp Hcov.
  pose proof H as Hind.
  revert HP HC H Θd Ξd P'd Hd Hun Hagr Hscp Hcov.
  apply (e_solve_cstr_order_sind
           (fun S0 Θ C P =>
              forall (HP : lc_pskl P) (HC : Forall lc_a_cstr C)
                     (H : e_solve_cstr_order S0 Θ C P) Θd Ξd P'd,
                {{ Θd ⊩ C ⨾ P ⤳ Ξd ⨾ P'd }}a ->
                uniq Ξd ->
                flex_agree (ftvar_in_pskl P ∪ ftvar_in_a_cstrs C) Θd Θ ->
                ftvar_in_pskl P ∪ ftvar_in_a_cstrs C [<=] ftvar_in_aenv Θd ->
                ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_a_cstrs C
                  [<=] S0 ->
                e_solve_cstr_impl S0 Θ C P HP HC H <> None));
    [ | exact Hind ].
  clear.
  intros S0 Θ C P p1 p2 q2 HP HC H Θd Ξd P'd Hd Hun Hagr Hscp Hcov.
  destruct C as [ | c C' ].
  - (* nil — SC-Empty; the runner answers outright *)
    simp e_solve_cstr_impl. discriminate.
  - destruct c as [ m Q0 | Q0 ].
    + (* a sub constraint: TERMINAL, so the tail must be empty *)
      destruct C' as [ | c2 C'' ];
        [ | (* no rule fits a sub with a tail *) inversion Hd ].
      simp e_solve_cstr_impl.
      destruct (a_solve_cstr_sub_inv Hd) as [_ Ds].
      assert (Hagr1 : flex_agree (ftvar_in_pskl P ∪ ftvar_in_pskl Q0) Θd Θ)
        by (eapply flex_agree_weaken;
            [ exact Hagr | simpl; clear; fsetdec ]).
      assert (Hscp1 : ftvar_in_pskl P ∪ ftvar_in_pskl Q0
                        [<=] ftvar_in_aenv Θd)
        by (clear - Hscp; simpl in *; fsetdec).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q0
                        [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      kill_ssub_call_g Ds Hagr1 Hscp1 Hcov1 r1 Hr1. discriminate.
    + (* an eq constraint — THE case: the fold's threading row *)
      simp e_solve_cstr_impl.
      destruct (a_solve_cstr_eq_inv Hd) as [Ξd1 [Ξd2 [Pmid [-> [Dd Td]]]]].
      assert (Hu1 : uniq Ξd1) by (eapply uniq_app_2; exact Hun).
      assert (Hu2 : uniq Ξd2) by (eapply uniq_app_1; exact Hun).
      (* ⚠️⚠️ THE FOLD'S VARIABLE SET IS HELD OPAQUE.  [fsetdec] on a
         DISJOINTNESS goal is exponential in the number of set variables
         it can see — measured on this very case: 4 vars 0.25 s, 5 vars
         2 s, 6 vars > 120 s.  Spelling the set out as
         [ftv P ∪ ftv Q0 ∪ ftv 𝒞'] costs THREE variables in every
         column-freshness goal below and puts all of them over the cliff;
         [clearbody] keeps it at one, and [HVdef] re-opens it in the four
         places that need to look inside. *)
      pose (V := ftvar_in_pskl P ∪ ftvar_in_pskl Q0
                 ∪ ftvar_in_a_cstrs C').
      assert (HVdef : V = ftvar_in_pskl P ∪ ftvar_in_pskl Q0
                          ∪ ftvar_in_a_cstrs C') by reflexivity.
      clearbody V.
      assert (HPQV : ftvar_in_pskl P ∪ ftvar_in_pskl Q0 [<=] V)
        by (rewrite HVdef; clear; fsetdec).
      assert (HCV : ftvar_in_a_cstrs C' [<=] V)
        by (rewrite HVdef; clear; fsetdec).
      assert (HscpV : V [<=] ftvar_in_aenv Θd)
        by (rewrite HVdef; clear - Hscp; simpl in *; fsetdec).
      assert (HcovV : ftvar_in_aenv Θ ∪ V [<=] S0)
        by (rewrite HVdef; clear - Hcov; simpl in *; fsetdec).
      assert (HagrV : flex_agree V Θd Θ)
        by (eapply flex_agree_weaken;
            [ exact Hagr | rewrite HVdef; simpl; clear; fsetdec ]).
      (* the HEAD: level 2a's finished lemma answers it *)
      assert (Hagr1 : flex_agree (ftvar_in_pskl P ∪ ftvar_in_pskl Q0) Θd Θ)
        by (eapply flex_agree_weaken; [ exact HagrV | exact HPQV ]).
      assert (Hscp1 : ftvar_in_pskl P ∪ ftvar_in_pskl Q0
                        [<=] ftvar_in_aenv Θd)
        by (clear - HscpV HPQV; fsetdec).
      assert (Hcov1 : ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q0
                        [<=] S0)
        by (clear - HcovV HPQV; fsetdec).
      kill_seq_call_g Dd Hagr1 Hscp1 Hcov1 r1 Hr1.
      unfold solve_eq_spec in Hr1.
      (* bridge the runner's run back to an a-side derivation, then read
         off the aligned renaming ρ *)
      pose proof (e_solve_eq_sound Hr1 Hcov1) as Da.
      destruct (a_solve_eq_det _ _ _ _ _ _ _ _ Dd Da)
        as [ρ [Elρ [Erρ Hrel]]].
      pose proof (Hrel V HPQV) as Hrl.
      pose proof (rel_pskl_ftv_r _ _ _ _ Hrl) as Hftr.
      pose proof (e_solve_eq_supply_grows Hr1) as Hgrow.
      pose proof ((proj2 e_solve_sub_eq_block) _ _ _ _ _ _ _ Hr1)
        as [Hb1 [Hb2 [Hb3 Hb4]]].
      pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                    _ _ _ _ _ Dd) as HXd.
      (* the two columns dodge the fold's variables: the derivation's
         block dodges [ftvar_in_aenv Θd], the runner's dodges the supply *)
      assert (Hclv : cols_l ρ ∩ V [=] empty)
        by (rewrite <- dom_flex_pairs_l; rewrite <- Elρ;
            clear - HXd HscpV; fsetdec).
      assert (Hcrv : cols_r ρ ∩ V [=] empty)
        by (rewrite <- dom_flex_pairs_r; rewrite <- Erρ;
            clear - Hb2 HcovV; fsetdec).
      assert (Hnl : NoDup (List.map fst ρ))
        by (apply uniq_flex_pairs_l_nodup; rewrite <- Elρ; exact Hu1).
      assert (Hnr : NoDup (List.map snd ρ))
        by (apply uniq_flex_pairs_r_nodup; rewrite <- Erρ; exact Hb3).
      destruct (atoms_fresh_list (length ρ) (cols_l ρ ∪ cols_r ρ ∪ V))
        as [zs [Hlen [Hnz Hdisz]]].
      assert (Hdz2 : atoms_of zs ∩ (cols_l ρ ∪ cols_r ρ) [=] empty)
        by (clear - Hdisz; fsetdec).
      assert (Hav : forall a b, In (a, b) (chain ρ zs) ->
                a `notin` V /\ b `notin` V).
      { intros a b Hin. destruct (chain_atoms _ _ _ _ Hin) as [Ha Hb].
        split; [ clear - Ha Hclv Hdisz | clear - Hb Hcrv Hdisz ]; fsetdec. }
      (* TRANSPORT the derivation's tail along the chain *)
      pose proof (a_solve_cstr_swaps (chain ρ zs) _ _ _ _ _ Td) as Td'.
      rewrite swaps_aenv_app_dist in Td'.
      rewrite Elρ in Td'.
      rewrite (chain_flex_pairs ρ ρ zs (fun p Hp => Hp) Hnl Hnr Hnz Hlen
                 Hdz2) in Td'.
      rewrite <- Erρ in Td'.
      rewrite (rel_pskl_chain ρ V Pmid (sv_out r1) zs
                 Hrl Hnl Hnr Hnz Hlen Hdisz
                 ltac:(clear - Hclv Hcrv; fsetdec)) in Td'.
      rewrite (swaps_cstrs_fresh_id (chain ρ zs) C'
                 ltac:(intros a b Hin; destruct (Hav a b Hin) as [Ha Hb];
                       clear - Ha Hb HCV; split; fsetdec)) in Td'.
      (* the tail's motive facts, at the transported context *)
      assert (Hu2' : uniq (swaps_aenv (chain ρ zs) Ξd2))
        by (apply swaps_aenv_uniq; exact Hu2).
      assert (Hagsw : flex_agree V (swaps_aenv (chain ρ zs) Θd) Θ)
        by (apply flex_agree_swaps_left; [ exact Hav | exact HagrV ]).
      assert (Hagblk : flex_agree (V ∪ cols_r ρ)
                        (flex_pairs_r ρ ++ swaps_aenv (chain ρ zs) Θd)
                        (flex_pairs_r ρ ++ Θ))
        by (apply flex_agree_flex_block; exact Hagsw).
      rewrite <- Erρ in Hagblk.
      assert (Hagr2 : flex_agree (ftvar_in_pskl (sv_out r1)
                                  ∪ ftvar_in_a_cstrs C')
                        (sv_block r1 ++ swaps_aenv (chain ρ zs) Θd)
                        (sv_block r1 ++ Θ))
        by (eapply flex_agree_weaken;
            [ exact Hagblk | clear - Hftr HCV; fsetdec ]).
      assert (Hscpsw : V [<=] ftvar_in_aenv (swaps_aenv (chain ρ zs) Θd))
        by (apply ftvar_in_aenv_swaps_subset; [ exact HscpV | exact Hav ]).
      pose proof (ftvar_in_aenv_flex_pairs_r ρ) as Hfr.
      rewrite <- Erρ in Hfr.
      assert (Hscp2 : ftvar_in_pskl (sv_out r1) ∪ ftvar_in_a_cstrs C'
                        [<=] ftvar_in_aenv (sv_block r1
                                            ++ swaps_aenv (chain ρ zs) Θd))
        by (rewrite ftvar_in_aenv_app;
            clear - Hftr Hscpsw Hfr HCV; fsetdec).
      assert (Hcov2 : ftvar_in_aenv (sv_block r1 ++ Θ)
                        ∪ ftvar_in_pskl (sv_out r1) ∪ ftvar_in_a_cstrs C'
                        [<=] sv_supply r1)
        by (rewrite ftvar_in_aenv_app;
            clear - Hb1 Hb4 Hgrow HcovV Hftr Hfr HCV; fsetdec).
      pose proof (q2 Q0 C' eq_refl _ _ _ Hr1) as IHt.
      kill_scstr_call IHt Td' Hu2' Hagr2 Hscp2 Hcov2 r2 Hr2. discriminate.
Qed.

(** ⭐ The fold's headline — the campaign's level 3.  [uniq Ξ] stays a
    premise: it is what makes the derivation's block a RENAMING of the
    runner's (§5's banner). *)
Lemma e_solve_cstr_run_complete : forall S0 Θ C P HP HC Ξ P',
  {{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ P' }}a ->
  uniq Ξ ->
  ftvar_in_pskl P ∪ ftvar_in_a_cstrs C [<=] ftvar_in_aenv Θ ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_a_cstrs C [<=] S0 ->
  e_solve_cstr_run S0 Θ C P HP HC <> None.
Proof.
  intros * Hd Hun Hscp Hcov. unfold e_solve_cstr_run.
  assert (Hagr : flex_agree (ftvar_in_pskl P ∪ ftvar_in_a_cstrs C) Θ Θ)
    by apply flex_agree_refl.
  pose proof (e_solve_cstr_impl_complete HP HC
                (@e_solve_cstr_order_total C S0 Θ P HP HC)
                Hd Hun Hagr Hscp Hcov) as Hne.
  revert Hne.
  destruct (e_solve_cstr_impl S0 Θ C P HP HC
              (@e_solve_cstr_order_total C S0 Θ P HP HC)) as [ [r Hr] | ];
    intros Hne.
  - discriminate.
  - exact (False_ind _ (Hne eq_refl)).
Qed.

(* ===================================================================== *)
(*  §6  The EXTRACT level (§8c.3 level 4) — §8c.9's plan                  *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(*  §6a  The ∀-peel on the solve layer — crossing 2's engine              *)
(*                                                                        *)
(*  A ghost-free ∀ target may be read WHOLE by the collection (LS-Var    *)
(*  now) or PEELED first (LS-ForallR), and the fold pays the difference  *)
(*  here: at a ∀ target only SS-Var (target ignored), the two            *)
(*  subject-peels, and SS-ForallR itself can root a solve, so the peel   *)
(*  commutes all the way down.  EXISTENCE-only, deliberately: the        *)
(*  extract level's run-completeness consumes a bare ∃-fold (level 3's   *)
(*  statement); the yield relation is the SUB level's business and will  *)
(*  strengthen this lemma when that level needs it (§8c.9).              *)
(*                                                                        *)
(*  ⚙ The SS-ForallR case rebinds its opener to the REQUESTED β and then *)
(*  STRIPS the now-spent [β ~ tvar] entry by [a_solve_sub_eq_ctx_change] *)
(*  — a rigid entry is invisible to the solve: [a_flex_tvar] is false at *)
(*  it either way, and the freshness avoid-sets only shrink.             *)
(* --------------------------------------------------------------------- *)

Lemma a_flex_tvar_strip_tvar : forall β (Θ : aenv) α,
  β `notin` dom Θ ->
  a_flex_tvar ((β ~ abind_tvar) ++ Θ) α ->
  a_flex_tvar Θ α.
Proof.
  intros * Hfr Hf.
  unfold a_flex_tvar in *.
  destruct Hf as [Hb | [τ Hb]].
  - apply binds_cons_1 in Hb.
    destruct Hb as [[Heqx Heqa] | Hb']; [ discriminate | ].
    left; exact Hb'.
  - apply binds_cons_1 in Hb.
    destruct Hb as [[Heqx Heqa] | Hb']; [ discriminate | ].
    right; exists τ; exact Hb'.
Qed.

Lemma a_flex_weaken_cons : forall (e : atom * abind) (Θ : aenv) P,
  a_flex Θ P ->
  a_flex (e :: Θ) P.
Proof.
  intros * Hf.
  inversion Hf; subst.
  - apply a_flex__var. right. assumption.
  - eapply a_flex__var_def. right. eassumption.
Qed.

Lemma a_solve_sub_peel_forall_r_n : forall n P B Θ Ξ P' β,
  size_pskl P + size_pskl B < n ->
  {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
  exists Ξ' P'',
    {{ Θ ⊢ₛ P ≼[ mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f β))
       ⤳ Ξ' ⨾ P'' }}a.
Proof.
  induction n as [ | n IH ]; intros P B Θ Ξ P' β Hsz Hd Hβ;
    [ exfalso; clear - Hsz; lia | ].
  inversion Hd; subst.
  - (* SS-Var: the target is ignored *)
    do 2 eexists. apply a_solve_sub__var.
  - (* SS-ForallL: rebind the subject opener away from β, IH, rebuild *)
    match goal with
    | Hfr : ?g `notin` union _ _ ,
      Hp : a_solve_sub ((?g ~ abind_tvar) ++ _) _ _ _ _ _ |- _ =>
        rename Hfr into Hγfr; rename Hp into Hprem
    end.
    match goal with
    | Hprem : a_solve_sub _ _ (open_pskl_wrt_pskl ?B0 _) _ _ _ |- _ =>
        rename B0 into P0
    end.
    destruct (atom_fresh (ftvar_in_aenv Θ ∪ ftvar_in_pskl P0
                ∪ ftvar_in_pskl B ∪ {{ β }})) as [γ' Hγ'].
    assert (Hγ'r : γ' `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P0
                     ∪ ftvar_in_pskl (pskl_all_syn B))
      by (simpl; clear - Hγ'; fsetdec).
    destruct (a_solve_sub_rebind_l Hprem Hγfr Hγ'r) as [Ξ2 [P2 Hp']].
    assert (Hsz' : size_pskl (open_pskl_wrt_pskl P0 (pskl_var_f γ'))
                     + size_pskl B < n)
      by (rewrite size_pskl_open_pskl_wrt_pskl_var;
          clear - Hsz; simpl in *; lia).
    assert (Hβ' : β `notin`
              ftvar_in_aenv ((γ' ~ abind_tvar) ++ Θ)
              ∪ ftvar_in_pskl (open_pskl_wrt_pskl P0 (pskl_var_f γ'))
              ∪ ftvar_in_pskl B).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0
                    (pskl_var_f γ')) as Hup.
      clear - Hβ Hγ' Hup. simpl in *. fsetdec. }
    destruct (IH _ _ _ _ _ β Hsz' Hp' Hβ') as [Ξ3 [P3 Hpeel]].
    do 2 eexists.
    apply a_solve_sub__forall_l with (β := γ').
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                    (pskl_var_f β)) as Hup.
      clear - Hγ' Hup. simpl in *. fsetdec.
    + exact Hpeel.
  - (* SS-UnivGhostL *)
    match goal with
    | Hp : a_solve_sub _ _ ?P0 (pskl_all_syn _) _ _ |- _ =>
        assert (Hsz' : size_pskl P0 + size_pskl B < n)
          by (clear - Hsz; simpl in *; lia);
        assert (Hβ' : β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P0
                        ∪ ftvar_in_pskl B)
          by (clear - Hβ; simpl in *; fsetdec);
        destruct (IH _ _ _ _ _ β Hsz' Hp Hβ') as [Ξ3 [P3 Hpeel]]
    end.
    do 2 eexists. apply a_solve_sub__univ_ghost_l. exact Hpeel.
  - (* SS-Check: guarded ∀ has no constructor *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  - (* SS-ForallR: rebind its opener to β, then strip the spent entry *)
    match goal with
    | Hfr : ?g `notin` union _ _ ,
      Hp : a_solve_sub ((?g ~ abind_tvar) ++ _) _ _ _ _ _ |- _ =>
        rename Hfr into Hγfr; rename Hp into Hprem
    end.
    assert (Hβr : β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P
                    ∪ ftvar_in_pskl B)
      by (clear - Hβ; fsetdec).
    destruct (a_solve_sub_rebind_r Hprem Hγfr Hβr) as [Ξ2 [P2 Hp']].
    exists Ξ2, P2.
    apply (proj1 a_solve_sub_eq_ctx_change) with
      (Θ := (β ~ abind_tvar) ++ Θ).
    + exact Hp'.
    + clear - Hβ. simpl. fsetdec.
    + intros α0 Hf0.
      eapply a_flex_tvar_strip_tvar; [ | exact Hf0 ].
      pose proof (dom_subset_ftvar_in_aenv Θ) as Hds.
      clear - Hβ Hds. fsetdec.
    + intros P0 Hf0. apply a_flex_weaken_cons. exact Hf0.
  - (* SS-GhostL: guarded ∀ has no constructor *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
Qed.

(** Crossing 2's engine, packaged (see the box above). *)
Lemma a_solve_sub_peel_forall_r : forall P B Θ Ξ P' β,
  {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
  exists Ξ' P'',
    {{ Θ ⊢ₛ P ≼[ mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f β))
       ⤳ Ξ' ⨾ P'' }}a.
Proof.
  intros.
  eapply a_solve_sub_peel_forall_r_n
    with (n := S (size_pskl P + size_pskl B)); eauto.
Qed.
