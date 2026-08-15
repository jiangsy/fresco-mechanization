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
    is the template every level above copies (§8c.6). *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.
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
