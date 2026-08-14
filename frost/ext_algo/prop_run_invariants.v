(** ext_algo — the invariants the runners TEST, as theorems the RELATION
    guarantees.  (Completeness campaign, §8c step 2b.)

    prop_dec.v (step 2a) says each test ACCEPTS whenever its guard holds.
    That is only half of what completeness needs: the other half is that the
    guard DOES hold on everything a run hands to the next test.  A runner
    threads its own output into the next call's precondition, so a test that
    the relation cannot guarantee would be a hole in the argument no amount
    of decider completeness could fill.

    §1  ⭐ def-payload discipline through the SUBTYPING walk — the missing
        twin of [e_consis_defs_mono] (prop_termination.v §12)
    §2  ⭐ local closure of the consistency block's and the subtyping walk's
        OUTPUT SKELETON — the two the §10 pipeline kit does not reach

    ⚙ WHY THIS ONE WAS MISSING.  §12 proved the consistency block preserves
    [aenv_defs_mono] because the TERMINATION argument needed it there — the
    Arrow row hands the domain's output context to the codomain, and the
    measure's [nall]/[hnall] components are stable under mono substitution
    only.  The subtyping walk never needed it for termination, because
    [e_sub_order_total] takes [aenv_defs_mono Θ0] as a hypothesis about its
    INPUT and no rule of [e_sub] re-enters at a context the walk itself
    built without going through the order.  Completeness is what makes the
    output side load-bearing: [def_typing_impl.v]'s AT-Anno and AT-Freeze
    rows TEST [defs_mono_ck (ty_ctx r1)] on a subtyping run's result, and
    [def_sub_impl.v]'s recursive calls must satisfy the order at the context
    the previous call produced.

    ⭐ EVERY ROW IS ONE OF FOUR SHAPES, and none of them can break the
    discipline:
    - the rows that return their input context (Infer, Ghost, UnivGhostR)
      have nothing to prove;
    - the rows that delegate (Check, Arrow's first premise) go to the
      consistency block, i.e. to §12;
    - the rows that GENERATE a block ([ForallL]'s [Ξ]) generate a FLEX-ONLY
      one ([e_extract_block_flex]), and a flexible with no definition
      carries no payload obligation;
    - the flex walk's rows re-attach exactly what they walked past, and the
      one row that INSTALLS a definition — [Flex-Solve] — installs
      [α̂ → β̂], an arrow of two variables, which is mono by construction.
    ⭐ So the discipline is not preserved by accident: the only definitions
    the walk can create are the ones the paper's "never guess polytypes out
    of thin air" allows it to. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_coercions.               (* mono_ptyp_lc *)
Require Import src.frost.algo.prop_metasubst.          (* all_flex_mono *)
Require Import src.frost.algo.sub.prop_solve_sub.      (* lc_pskl_*_inv *)
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.def_sub.
Require Import src.frost.ext_algo.def_dec.             (* lc_pskl_open_graft *)
Require Import src.frost.ext_algo.prop_termination.

Set Implicit Arguments.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  Def payloads stay MONO through the subtyping walk                 *)
(* ===================================================================== *)

(** ⚠️ The flex walk's motive carries the accumulated block [Ξ] as a SECOND
    hypothesis, exactly as [e_assign]'s does in §12 — [Flex-Depend] moves an
    entry from the context into [Ξ] and [Flex-Solve] puts [Ξ] back in front
    of the context it re-enters at, so the block's discipline and the
    context's are mutually needed and must ride together. *)
Lemma e_sub_sub_flex_defs_mono :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     aenv_defs_mono Θ0 -> aenv_defs_mono Θ1) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     aenv_defs_mono Θ0 -> aenv_defs_mono Ξ -> aenv_defs_mono Θ1).
Proof.
  apply e_sub_sub_flex_mutind;
    intros;
    (* [(x ~ b) ++ Θ] is [one (x,b) ++ Θ]; the [Forall] patterns below see
       the cons only after [simpl] (the §8b.6 metalib trap) *)
    simpl in *;
    (* unpack every input context *)
    repeat match goal with
    | H : Forall entry_def_mono (_ ++ _) |- _ =>
        apply Forall_app in H; destruct H
    | H : Forall entry_def_mono (_ :: _) |- _ =>
        inversion H; subst; clear H
    end;
    (* the Check row and Arrow's first premise delegate to §12 *)
    repeat match goal with
    | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
    end;
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ ?Θ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e,
      Hd : Forall entry_def_mono ?Θ |- _ =>
        lazymatch goal with
        | _ : Forall entry_def_mono _ |- _ =>
            let HH := fresh "Hdm" in
            pose proof (e_consis_defs_mono H Hd) as HH; clear H
        end
    end;
    (* ForallR's IH yields the output under the fresh rigid entry AND the
       junk suffix — peel both off *)
    repeat match goal with
    | IH : Forall entry_def_mono ?Θin -> Forall entry_def_mono (_ ++ _)
      |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(eauto using Forall_app_intro, Forall_cons,
                                 Forall_nil, entry_def_mono_tvar));
        simpl in HH;
        repeat (apply Forall_app in HH; destruct HH as [? HH]);
        repeat match goal with
        | H : Forall entry_def_mono (_ :: _) |- _ =>
            inversion H; subst; clear H
        end;
        clear IH
    end;
    (* ForallL's generated block is FLEX-ONLY, so it needs no payload
       obligation at all *)
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊢ _ ⊳[ _ , _ , _ ] _ ⤳ ?Ξ ↪ _ }}e |- _ =>
        lazymatch goal with
        | _ : all_flex_mono Ξ |- _ => fail
        | _ => pose proof (e_extract_block_flex H)
        end
    end;
    eauto 10 using Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_flex, entry_def_mono_tvar, entry_def_mono_def,
      entry_def_mono_var_typ, entry_def_mono_var_skl,
      all_flex_mono_defs_mono,
      mono_ptyp__var, mono_ptyp__arrow.
Qed.

(** ⭐ The twin of [e_consis_defs_mono] the campaign was missing. *)
Corollary e_sub_defs_mono : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> aenv_defs_mono Θ1.
Proof.
  intros. eapply (proj1 e_sub_sub_flex_defs_mono); eassumption.
Qed.

Corollary e_sub_flex_defs_mono : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
  aenv_defs_mono Θ0 -> aenv_defs_mono Ξ -> aenv_defs_mono Θ1.
Proof.
  intros. eapply (proj2 e_sub_sub_flex_defs_mono); eassumption.
Qed.

(* ===================================================================== *)
(*  §2  Local closure of the OUTPUT skeleton                              *)
(*                                                                        *)
(*  prop_termination.v §10 carries local closure through the pipeline —   *)
(*  guess, the collection, the solving layer, its fold, extraction —      *)
(*  because that is what the totality proofs consume.  The two            *)
(*  judgements it stops short of are the two that RETURN a skeleton to a  *)
(*  caller: the consistency block and the subtyping walk.  Completeness   *)
(*  needs both, because the runners test [degree_pskl_ck 0] on those      *)
(*  outputs before handing them on.                                       *)
(* ===================================================================== *)

(** The ∀ rows of the consistency block return a CLOSE, so their output's
    local closure is the body's, one binder up. *)
Lemma lc_pskl_all_syn_close : forall α Q,
  lc_pskl Q -> lc_pskl (pskl_all_syn (close_pskl_wrt_pskl α Q)).
Proof.
  intros α Q HQ. apply (lc_pskl_all_syn_exists α).
  rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl. exact HQ.
Qed.

(** ⚙ Only the [e_consis] motive has content — [e_assign] and [e_unify]
    return no skeleton — but the [Scheme] is mutual, so the other two
    motives are supplied as [True]. *)
Lemma e_consis_lc : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  lc_pskl P -> lc_pskl P0 -> lc_pskl Q.
Proof.
  intros Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1 H.
  revert H.
  apply (e_consis_mind
           (fun S0 Θ Ξ α P S1 Θ' (_ : {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e)
              => True)
           (fun S0 Θ α β S1 Θ' (_ : {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e)
              => True)
           (fun Δ1 Δ2 S0 Θ P0 P Q S1 Θ' _ =>
              lc_pskl P -> lc_pskl P0 -> lc_pskl Q));
    intros; try exact I;
    (* peel the subject's and the counterpart's head constructors *)
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        destruct (lc_pskl_arrow_inv H); clear H
    | H : lc_pskl (pskl_tophole _) |- _ =>
        pose proof (lc_pskl_tophole_inv H); clear H
    end;
    eauto using lc_pskl_all_syn_close, lc_pskl_all_syn_inv,
      lc_pskl_var_f, lc_pskl_unit, lc_pskl_arrow, lc_pskl_tophole.
Qed.

(** ⚠️ [aenv_defs_mono Θ0] is not decoration here: [Flex-Assign] substitutes
    a context DEFINITION into the counterpart, so the counterpart's local
    closure survives only if the payload is locally closed — which is what
    the mono discipline gives ([mono_ptyp_to_pskl_lc]).  §1 is what keeps
    the hypothesis available down the walk.

    ⚙ And the flex walk's motive carries [aenv_defs_mono Ξ] for §1's reason:
    [Flex-Solve] re-enters at [Ξ ++ …], so the [e_sub] IH there demands the
    block's discipline as well as the context's. *)
Lemma e_sub_sub_flex_lc :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 -> lc_pskl Q) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     lc_pskl P0 -> aenv_defs_mono Θ0 -> aenv_defs_mono Ξ -> lc_pskl Q).
Proof.
  apply e_sub_sub_flex_mutind;
    intros;
    simpl in *;
    (* unpack the context discipline the substituting row needs *)
    repeat match goal with
    | H : Forall entry_def_mono (_ ++ _) |- _ =>
        apply Forall_app in H; destruct H
    | H : Forall entry_def_mono (_ :: _) |- _ =>
        inversion H; subst; clear H
    end;
    (* peel the subject's and the counterpart's head constructors *)
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        destruct (lc_pskl_arrow_inv H); clear H
    | H : lc_pskl (pskl_tophole _) |- _ =>
        pose proof (lc_pskl_tophole_inv H); clear H
    end;
    (* ⭐ Arrow's first premise is a consistency run, and it owes the second
       premise BOTH facts: its output skeleton is lc (§2) and its output
       CONTEXT keeps the def discipline (§12).  Posed as implications so
       [eauto] chains them itself. *)
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e |- _ =>
        pose proof (e_consis_lc H); pose proof (e_consis_defs_mono H); clear H
    end;
    (* ⭐ ForallL: the instantiation it recurses on is lc because the
       extraction's yield is, and the block it prepends is flex-only *)
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊢ _ ⊳[ _ , _ , _ ] _ ⤳ _ ↪ _ }}e |- _ =>
        pose proof (e_extract_lc H);
        pose proof (all_flex_mono_defs_mono (e_extract_block_flex H));
        clear H
    end;
    (* the def payload's mono-ness arrives wrapped in [entry_def_mono];
       unwrap it so [mono_ptyp_to_pskl_lc] is applicable *)
    repeat match goal with
    | H : entry_def_mono (_, abind_flex_mono_def ?tau) |- _ =>
        let HH := fresh "Hmono" in
        assert (HH : mono_ptyp tau) by exact H; clear H
    end;
    (* ⚠️ [Flex-Assign] substitutes into a VARIABLE, and [simpl] turns that
       into an [if α == β then … else …] (the §8b.7 trap).  Decide the
       comparison, or nothing downstream can see a skeleton at all. *)
    repeat match goal with
    | |- context [ if ?a == ?b then _ else _ ] => destruct (a == b); subst
    | H : context [ if ?a == ?b then _ else _ ] |- _ =>
        destruct (a == b); subst
    end;
    eauto 12 using lc_pskl_var_f, lc_pskl_unit, lc_pskl_arrow,
      lc_pskl_tophole, lc_pskl_open_graft, lc_pskl_all_syn_inv,
      subst_pskl_in_pskl_lc_pskl, mono_ptyp_to_pskl_lc,
      Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_flex, entry_def_mono_tvar, entry_def_mono_def,
      entry_def_mono_var_typ, entry_def_mono_var_skl,
      mono_ptyp__var, mono_ptyp__arrow.
Qed.

Corollary e_sub_lc : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 -> lc_pskl Q.
Proof. intros. eapply (proj1 e_sub_sub_flex_lc); eassumption. Qed.

Corollary e_sub_flex_lc : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
  lc_pskl P0 -> aenv_defs_mono Θ0 -> aenv_defs_mono Ξ -> lc_pskl Q.
Proof. intros. eapply (proj2 e_sub_sub_flex_lc); eassumption. Qed.
