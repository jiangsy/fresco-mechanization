(** ext_algo — the invariants the runners TEST, as theorems the RELATION
    guarantees.  (Completeness campaign, §8c step 2b.)

    prop_dec.v (step 2a) says each test ACCEPTS whenever its guard holds.
    That is only half of what completeness needs: the other half is that the
    guard DOES hold on everything a run hands to the next test.  A runner
    threads its own output into the next call's precondition, so a test that
    the relation cannot guarantee would be a ghost in the argument no amount
    of decider completeness could fill.

    §1  ⭐ def-payload discipline through the SUBTYPING walk — the missing
        twin of [e_consis_defs_mono] (prop_termination.v §12)
    §2  ⭐ local closure of the consistency block's and the subtyping walk's
        OUTPUT SKELETON — the two the §10 pipeline kit does not reach
    §3  ⭐ the def-payload discipline through SPLITTING, SKELETON INFERENCE
        and TYPE INFERENCE — closing the chain over all fourteen judgements

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

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_coercions.               (* mono_ptyp_lc *)
Require Import src.fresco.algo.prop_inc.                (* lc_aenv *)
Require Import src.fresco.algo.prop_metasubst.          (* all_flex_mono *)
Require Import src.fresco.algo.sub.prop_solve_sub.      (* lc_pskl_*_inv *)
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.def_sub.
Require Import src.fresco.ext_algo.def_pat.
Require Import src.fresco.ext_algo.def_typing.
Require Import src.fresco.ext_algo.def_dec.             (* lc_pskl_open_graft *)
Require Import src.fresco.ext_algo.prop_termination.

Set Implicit Arguments.

Open Scope fresco_e_scope.

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
    | H : lc_pskl (pskl_univ_ghost _) |- _ =>
        pose proof (lc_pskl_univ_ghost_inv H); clear H
    end;
    eauto using lc_pskl_all_syn_close, lc_pskl_all_syn_inv,
      lc_pskl_var_f, lc_pskl_unit, lc_pskl_arrow, lc_pskl_univ_ghost.
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
    | H : lc_pskl (pskl_univ_ghost _) |- _ =>
        pose proof (lc_pskl_univ_ghost_inv H); clear H
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
      lc_pskl_univ_ghost, lc_pskl_open_graft, lc_pskl_all_syn_inv,
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

(* ===================================================================== *)
(*  §3  Def payloads stay MONO through the whole algorithm                *)
(*                                                                        *)
(*  §1 closed the subtyping walk; the three judgements above it —         *)
(*  splitting, skeleton inference, type inference — close the chain, so   *)
(*  the discipline now holds from the ENTRY POINT down.  That is what     *)
(*  the runners' [defs_mono_ck] tests need: [def_typing_impl.v] tests it  *)
(*  on [ty_ctx r1], the context a RECURSIVE CALL produced, and only a     *)
(*  statement about outputs can discharge that.                           *)
(*                                                                        *)
(*  ⭐ Two rows generate a block, and both generate a FLEX-ONLY one:       *)
(*  [e_split__flex] invents the pair [β̂ → α1̂] as undefined flexibles,     *)
(*  and [AT-Abs]'s [guess^TY] block is all-flexible                       *)
(*  ([e_guess_mono_block_flex]).  A flexible with no definition carries   *)
(*  no payload obligation, so neither row can break the discipline.       *)
(* ===================================================================== *)

Lemma e_split_defs_mono : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> aenv_defs_mono Θ1.
Proof.
  intros * H Hdm. destruct H; try exact Hdm.
  (* the flex row runs consistency under two invented FLEXIBLES *)
  eapply e_consis_defs_mono; [ eassumption | ].
  simpl. eauto using Forall_cons, entry_def_mono_flex.
Qed.

(** ⚙ The abs rows' shape is uniform: the body runs under a term-variable
    marker (and, at [AT-Abs], under [guess^TY]'s flex block), and returns
    [Ξ ++ <marker> ++ Θout] — so the IH's output is peeled twice, once for
    the junk suffix and once for the marker. *)
Lemma e_pat_defs_mono : forall S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> aenv_defs_mono Θ1.
Proof.
  intros S0 m Θ0 P0 e Q S1 Θ1 H; induction H; intros Hdm;
    (* splitting, subtyping and consistency all delegate *)
    repeat match goal with
    | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
    end;
    (* ⚙ Posed as IMPLICATIONS, not applied: a row like AP-App threads
       Θ0 → Θ1 → Θ2 through two premises, and only the FIRST link's input
       is in context up front.  [eauto] chains the rest itself. *)
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊲ _ ▹ _ ⇢ _ ⊣ _ }}e |- _ =>
        pose proof (e_split_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ⩽ _ ⊣ _ }}e |- _ =>
        pose proof (e_sub_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e |- _ =>
        pose proof (e_consis_defs_mono H); clear H
    end;
    (* the abs rows: feed the IH the marker-extended context, then peel the
       junk suffix and the marker back off its output *)
    repeat match goal with
    | IH : aenv_defs_mono ?Θin -> aenv_defs_mono (_ ++ _) |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(simpl; eauto using Forall_app_intro,
                                 Forall_cons, Forall_nil,
                                 entry_def_mono_var_skl,
                                 entry_def_mono_var_typ));
        simpl in HH;
        repeat (apply Forall_app in HH; destruct HH as [? HH]);
        repeat match goal with
        | H : Forall entry_def_mono (_ :: _) |- _ =>
            inversion H; subst; clear H
        end;
        clear IH
    end;
    eauto 8 using Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_var_skl, entry_def_mono_var_typ.
Qed.

Lemma e_typing_defs_mono : forall S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> aenv_defs_mono Θ1.
Proof.
  intros S0 m Θ0 P0 e B S1 Θ1 H; induction H; intros Hdm;
    repeat match goal with
    | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
    end;
    (* ⚙ As in [e_pat_defs_mono]: implications, so [eauto] can chain the
       AT-Anno / AT-Freeze / AT-App sequences whose middle contexts are
       nobody's hypothesis. *)
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊲ _ ▹ _ ⇢ _ ⊣ _ }}e |- _ =>
        pose proof (e_split_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢ˢ[ _ ; _ ] _ ⦂ _ ⊣ _ }}e |- _ =>
        pose proof (e_pat_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ⩽ _ ⊣ _ }}e |- _ =>
        pose proof (e_sub_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e |- _ =>
        pose proof (e_consis_defs_mono H); clear H
    end;
    (* ⭐ AT-Abs runs the body under [guess^TY]'s block, which is flex-only *)
    repeat match goal with
    | H : e_guess_mono _ _ _ ?Xs _ |- _ =>
        lazymatch goal with
        | _ : all_flex_mono Xs |- _ => fail
        | _ => pose proof (e_guess_mono_block_flex H)
        end
    end;
    repeat match goal with
    | IH : aenv_defs_mono ?Θin -> aenv_defs_mono (_ ++ _) |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(simpl; eauto 8 using Forall_app_intro,
                                 Forall_cons, Forall_nil,
                                 entry_def_mono_var_typ, entry_def_mono_tvar,
                                 all_flex_mono_defs_mono));
        simpl in HH;
        repeat (apply Forall_app in HH; destruct HH as [? HH]);
        repeat match goal with
        | H : Forall entry_def_mono (_ :: _) |- _ =>
            inversion H; subst; clear H
        end;
        clear IH
    end;
    eauto 8 using Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_var_typ, entry_def_mono_tvar,
      all_flex_mono_defs_mono.
Qed.

(* ===================================================================== *)
(*  §4  Context PAYLOADS stay LOCALLY CLOSED, and the outputs with them   *)
(*                                                                        *)
(*  §8c.2's (2b), taken by the LIGHTER of its two routes.  The alternative *)
(*  was to compose the bridge with [a_pat_sound] / [a_typing_sound], which *)
(*  already return output well-formedness — but that drags soundness' four *)
(*  premises ([{{ ⊢ Θ0 }}a], [a_wf_pskl], mode compatibility,             *)
(*  [{{ Θ0 ⊢ᵉ e }}a]) into every completeness motive above, and each has   *)
(*  to be re-established at every recursive call.  A direct invariant      *)
(*  costs ONE context hypothesis instead, and it costs almost nothing to   *)
(*  prove: [lc_abind] (algo/prop_inc.v) sends [tvar], [flex_mono] AND      *)
(*  [flex_mono_def] to [True], so every block the algorithm generates is   *)
(*  [lc_aenv] for free, and only the four rows that push a TERM VARIABLE   *)
(*  have anything to discharge.                                           *)
(*                                                                        *)
(*  ⚙ The predicate is not new — [lc_aenv] is algo/prop_inc.v's, and it is *)
(*  what [a_wf_aenv_lc_aenv] projects a well-formed context to.  What is   *)
(*  new is that the RUN preserves it.                                     *)
(* ===================================================================== *)

Lemma lc_abind_tvar : lc_abind abind_tvar.
Proof. exact I. Qed.

Lemma lc_abind_flex_mono : lc_abind abind_flex_mono.
Proof. exact I. Qed.

Lemma lc_abind_def : forall τ, lc_abind (abind_flex_mono_def τ).
Proof. intros; exact I. Qed.

Lemma lc_abind_var_typ : forall A, lc_ptyp A -> lc_abind (abind_var_typ A).
Proof. intros; assumption. Qed.

Lemma lc_abind_var_skl : forall P, lc_pskl P -> lc_abind (abind_var_skl P).
Proof. intros; assumption. Qed.

(** ⭐ Every block the algorithm generates is flexible-only, so it satisfies
    the discipline outright — this is the whole reason the invariant is
    cheap. *)
Lemma all_flex_mono_lc_aenv : forall Ξ, all_flex_mono Ξ -> lc_aenv Ξ.
Proof.
  intros Ξ H. unfold lc_aenv. induction H as [ | [x b] Ξ' Hb Ht IH ];
    [ constructor | ].
  constructor; [ simpl in *; subst; exact I | exact IH ].
Qed.

(** A [a_suffix] block is flexible-only too ([a_suffix_binding] is
    [flex_mono | flex_mono_def]), and both payload shapes are [True]. *)
Lemma a_suffix_lc_aenv : forall Ξ, a_suffix Ξ -> lc_aenv Ξ.
Proof.
  intros Ξ H. unfold lc_aenv. induction H as [ | Ξ' x b Ht IH Hb ];
    [ constructor | ].
  simpl. constructor; [ destruct Hb; exact I | exact IH ].
Qed.

(** ⚠️ [eauto] indexes hints by the head symbol of their CONCLUSION, and the
    scripts below run with [lc_aenv] unfolded (the [Forall] surgery needs it),
    so a hint whose conclusion says [lc_aenv] is never even tried.  Restate
    the two block facts with [Forall] at the head. *)
Lemma all_flex_mono_lc_forall : forall Ξ,
  all_flex_mono Ξ -> Forall (fun e : atom * abind => lc_abind (snd e)) Ξ.
Proof. exact all_flex_mono_lc_aenv. Qed.

Lemma a_suffix_lc_forall : forall Ξ,
  a_suffix Ξ -> Forall (fun e : atom * abind => lc_abind (snd e)) Ξ.
Proof. exact a_suffix_lc_aenv. Qed.

Lemma lc_aenv_binds : forall (x : atom) b (Θ : aenv),
  lc_aenv Θ -> binds x b Θ -> lc_abind b.
Proof.
  intros x b Θ H. unfold lc_aenv in H.
  induction H as [ | [y b'] Θ' Hb Ht IH ]; intros Hbd; [ inversion Hbd | ].
  destruct Hbd as [Heq | Hin];
    [ inversion Heq; subst; exact Hb | exact (IH Hin) ].
Qed.

(* ⚠️ [binds] / [lc_aenv] / [lc_abind] are DEFINITIONS, so none of the three
   indexes is a strict implicit — pin the prefix rather than counting. *)
Arguments lc_aenv_binds {x b Θ} _ _.

(* --- §4a  the CONSISTENCY block, and the SUBTYPING walk ---------------- *)

Lemma e_assign_unify_consis_env_lc :
  (forall S0 Θ Ξ α P S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
     lc_aenv Θ -> lc_aenv Ξ -> lc_aenv Θ') /\
  (forall S0 Θ α β S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e ->
     lc_aenv Θ -> lc_aenv Θ') /\
  (forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
     lc_aenv Θ -> lc_aenv Θ').
Proof.
  apply (e_assign_unify_consis_mutind
           (fun S0 Θ Ξ α P S1 Θ' _ => lc_aenv Θ -> lc_aenv Ξ -> lc_aenv Θ')
           (fun S0 Θ α β S1 Θ' _ => lc_aenv Θ -> lc_aenv Θ')
           (fun Δ1 Δ2 S0 Θ P0 P Q S1 Θ' _ => lc_aenv Θ -> lc_aenv Θ'));
    intros;
    unfold lc_aenv in *;
    simpl in *;
    repeat match goal with
    | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H; destruct H
    | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end;
    (* the ∀ rows' IH yields the output UNDER the fresh rigid entry *)
    repeat match goal with
    | IH : Forall ?F ?Θin -> Forall ?F (_ :: _) |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(eauto using Forall_app_intro, Forall_cons,
                                 Forall_nil, lc_abind_tvar,
                                 lc_abind_flex_mono, lc_abind_def));
        inversion HH; subst; clear IH HH
    end;
    (* the guess's block is flex-only, so it is [lc_aenv] outright *)
    repeat match goal with
    | H : e_guess_mono _ _ _ ?Ξ _ |- _ =>
        lazymatch goal with
        | _ : all_flex_mono Ξ |- _ => fail
        | _ => pose proof (e_guess_mono_block_flex H)
        end
    end;
    eauto 8 using Forall_app_intro, Forall_cons, Forall_nil,
      all_flex_mono_lc_forall, a_suffix_lc_forall, lc_abind_tvar,
      lc_abind_flex_mono, lc_abind_def, lc_abind_var_typ, lc_abind_var_skl.
Qed.

Corollary e_consis_env_lc : forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
  {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
  lc_aenv Θ -> lc_aenv Θ'.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_env_lc)); eassumption.
Qed.

Lemma e_sub_sub_flex_env_lc :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     lc_aenv Θ0 -> lc_aenv Θ1) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     lc_aenv Θ0 -> lc_aenv Ξ -> lc_aenv Θ1).
Proof.
  apply e_sub_sub_flex_mutind;
    intros;
    unfold lc_aenv in *;
    simpl in *;
    repeat match goal with
    | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
    end;
    repeat match goal with
    | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H; destruct H
    | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end;
    (* the Check row and Arrow's first premise delegate to §4a *)
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ ?Θ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e |- _ =>
        let HH := fresh "Hlc" in
        pose proof (e_consis_env_lc H) as HH; unfold lc_aenv in HH; clear H
    end;
    (* ForallR's IH yields the output under the rigid entry AND the junk *)
    repeat match goal with
    | IH : Forall ?F ?Θin -> Forall ?F (_ ++ _) |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(eauto using Forall_app_intro, Forall_cons,
                                 Forall_nil, lc_abind_tvar,
                                 lc_abind_flex_mono, lc_abind_def));
        simpl in HH;
        repeat (apply Forall_app in HH; destruct HH as [? HH]);
        repeat match goal with
        | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
        end;
        clear IH
    end;
    (* ForallL's generated block is FLEX-ONLY *)
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊢ _ ⊳[ _ , _ , _ ] _ ⤳ ?Ξ ↪ _ }}e |- _ =>
        lazymatch goal with
        | _ : all_flex_mono Ξ |- _ => fail
        | _ => pose proof (e_extract_block_flex H)
        end
    end;
    eauto 10 using Forall_app_intro, Forall_cons, Forall_nil,
      all_flex_mono_lc_forall, a_suffix_lc_forall, lc_abind_tvar,
      lc_abind_flex_mono, lc_abind_def, lc_abind_var_typ, lc_abind_var_skl.
Qed.

Corollary e_sub_env_lc : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  lc_aenv Θ0 -> lc_aenv Θ1.
Proof. intros. eapply (proj1 e_sub_sub_flex_env_lc); eassumption. Qed.

(* --- §4b  the SPLIT, both outputs and the context --------------------- *)

Lemma e_split_lc : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  lc_pskl P0 -> lc_pskl P /\ lc_pskl Q.
Proof.
  intros * H Hlc. destruct H.
  - destruct (lc_pskl_arrow_inv Hlc). split; assumption.
  - split; constructor.
  - split; apply lc_pskl_var_f.
Qed.

(** ⚙ The flex row's output context is a CONSISTENCY run's, at the two
    freshly invented flexibles — so it delegates to §4a. *)
Lemma e_split_env_lc : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  lc_aenv Θ0 -> lc_aenv Θ1.
Proof.
  intros * H Hlc. destruct H; [ assumption | assumption | ].
  eapply e_consis_env_lc; [ eassumption | ].
  unfold lc_aenv in *; simpl.
  constructor; [ exact I | ]. constructor; [ exact I | ]. assumption.
Qed.

(* --- §4c  SKELETON INFERENCE — the output skeleton and the context ----- *)

(** ⚠️ [lc_exp]'s two binder rows are COFINITE, so their inversion yields a
    FAMILY; the [abs] rows need it at the rule's own witness, and the
    hypothesis' generated name shifts from row to row.  Select it by TYPE. *)
Local Ltac open_exp_lc x :=
  match goal with
  | Hx : forall _ : _, lc_exp (open_exp_wrt_exp _ (exp_var_f _)) |- _ =>
      exact (Hx x)
  end.

(** The abs rows discard the binder: the premise's output is
    [Ξ ++ (x ~ b) ++ Θ] and the conclusion's is [Ξ ++ Θ] — except at the two
    ∀-peeling CHECK rows of [e_typing], which discard the junk suffix too and
    conclude at [Θ] alone.  Both shapes, one tactic. *)
Local Ltac drop_binder H :=
  unfold lc_aenv in *; simpl in H;
  apply Forall_app in H; destruct H as [? H];
  inversion H; subst;
  solve [ apply Forall_app; split; assumption | assumption ].

(** The two conjuncts are proved TOGETHER: the abs rows recurse under a term
    variable whose payload comes from the SPLIT's output, so the output-lc
    conjunct feeds the context-lc one at the very next row. *)
Lemma e_pat_lc_env : forall S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 ->
  lc_pskl Q /\ lc_aenv Θ1.
Proof.
  intros S0 m Θ0 P0 e Q S1 Θ1 H.
  induction H; intros HP0 He HΘ Hdm.
  - (* AP-Unit *)
    split; [ eapply e_sub_lc | eapply e_sub_env_lc ];
      eauto using lc_pskl_unit.
  - (* AP-Var, type-bound *)
    assert (HA : lc_ptyp A)
      by (exact (lc_aenv_binds HΘ H)).
    split; [ eapply e_sub_lc | eapply e_sub_env_lc ];
      eauto using ptyp_to_pskl_lc.
  - (* AP-Var, skeleton-bound *)
    assert (HA : lc_pskl P)
      by (exact (lc_aenv_binds HΘ H)).
    split; [ eapply e_sub_lc | eapply e_sub_env_lc ]; eauto.
  - (* AP-Anno *)
    inversion He; subst.
    split; [ eapply e_sub_lc | eapply e_sub_env_lc ];
      eauto using ptyp_to_pskl_lc.
  - (* AP-Freeze *)
    inversion He; subst. apply IHe_pat; auto.
  - (* AP-Abs *)
    inversion He; subst.
    destruct (e_split_lc H0 HP0) as [HPlc HQ0lc].
    pose proof (e_split_env_lc H0 HΘ) as HΘ1.
    pose proof (e_split_defs_mono H0 Hdm) as Hdm1.
    destruct (IHe_pat HQ0lc ltac:(open_exp_lc x) ltac:(unfold lc_aenv in *; simpl;
                constructor; [ simpl; exact HPlc | exact HΘ1 ])
                ltac:(simpl; constructor;
                      [ exact I | exact Hdm1 ])) as [HQlc HΘout].
    split; [ apply lc_pskl_arrow; assumption | ].
    drop_binder HΘout.
  - (* AP-AbsAnno *)
    inversion He; subst.
    destruct (e_split_lc H0 HP0) as [HPlc HQ0lc].
    pose proof (e_split_env_lc H0 HΘ) as HΘ1.
    pose proof (e_split_defs_mono H0 Hdm) as Hdm1.
    destruct H1 as [Qm Hc].
    pose proof (e_consis_env_lc Hc HΘ1) as HΘ2.
    pose proof (e_consis_defs_mono Hc Hdm1) as Hdm2.
    destruct (IHe_pat HQ0lc ltac:(open_exp_lc x) ltac:(unfold lc_aenv in *; simpl;
                constructor; [ simpl; assumption | exact HΘ2 ])
                ltac:(simpl; constructor;
                      [ exact I | exact Hdm2 ])) as [HQlc HΘout].
    split; [ apply lc_pskl_arrow;
             [ apply ptyp_to_pskl_lc; assumption | assumption ] | ].
    drop_binder HΘout.
  - (* AP-AbsCheck *)
    inversion He; subst.
    destruct (IHe_pat (lc_pskl_ghost) ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl;
                      constructor; [ simpl; exact lc_pskl_ghost | exact HΘ ])
                ltac:(simpl; constructor; [ exact I | exact Hdm ]))
      as [HQlc HΘout].
    split; [ apply lc_pskl_univ_ghost; apply lc_pskl_arrow;
             [ exact lc_pskl_ghost | exact HQlc ] | ].
    drop_binder HΘout.
  - (* AP-AbsAnnoCheck *)
    inversion He; subst.
    destruct (IHe_pat (lc_pskl_ghost) ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl;
                      constructor; [ simpl; assumption | exact HΘ ])
                ltac:(simpl; constructor; [ exact I | exact Hdm ]))
      as [HQlc HΘout].
    split; [ apply lc_pskl_univ_ghost; apply lc_pskl_arrow;
             [ apply ptyp_to_pskl_lc; assumption | exact HQlc ] | ].
    drop_binder HΘout.
  - (* AP-App *)
    inversion He; subst.
    destruct (IHe_pat1 lc_pskl_ghost ltac:(assumption) HΘ Hdm)
      as [HP0lc HΘ1].
    pose proof (e_pat_defs_mono H Hdm) as Hdm1.
    destruct (IHe_pat2 ltac:(apply lc_pskl_arrow; assumption)
                ltac:(assumption) HΘ1 Hdm1) as [HPQlc HΘ2].
    split; [ exact (proj2 (lc_pskl_arrow_inv HPQlc)) | exact HΘ2 ].
Qed.

(* --- §4d  TYPE INFERENCE — the output type and the context ------------- *)

(** ⭐ Every row whose subtyping or splitting premise is PINNED to a
    painting [⌈A⌉] hands its caller [lc_pskl ⌈A⌉]; what the caller owes is
    [lc_ptyp A], and that is [ptyp_to_pskl_lc_inv] (prop_coercions.v). *)
Local Ltac paint_lc :=
  repeat match goal with
  | H : lc_pskl (ptyp_to_pskl ?A) |- _ =>
      lazymatch goal with
      | _ : lc_ptyp A |- _ => clear H
      | _ => apply ptyp_to_pskl_lc_inv in H
      end
  end.

(** The two ∀-peeling CHECK rows recurse at the OPENED pattern: peel the
    painting, invert the (cofinite) [lc_ptyp] of the [∀], instantiate. *)
Local Ltac open_all_lc :=
  apply ptyp_to_pskl_lc;
  match goal with
  | H : lc_ptyp (ptyp_all _) |- _ => inversion H; subst
  end;
  match goal with
  | Hx : forall _ : _, lc_ptyp (open_ptyp_wrt_ptyp _ (ptyp_var_f _)) |- _ =>
      apply Hx
  end.

Lemma e_typing_lc_env : forall S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 ->
  lc_ptyp B /\ lc_aenv Θ1.
Proof.
  intros S0 m Θ0 P0 e B S1 Θ1 H.
  induction H; intros HP0 He HΘ Hdm.
  - (* AT-Unit *)
    pose proof (e_sub_lc H lc_pskl_unit HP0 Hdm) as Hout. paint_lc.
    split; [ assumption | eapply e_sub_env_lc; eassumption ].
  - (* AT-Var *)
    assert (HA : lc_ptyp A) by (exact (lc_aenv_binds HΘ H)).
    pose proof (e_sub_lc H0 (ptyp_to_pskl_lc HA) HP0 Hdm) as Hout. paint_lc.
    split; [ assumption | eapply e_sub_env_lc; eassumption ].
  - (* AT-Anno *)
    inversion He; subst.
    destruct (IHe_typing ltac:(apply ptyp_to_pskl_lc; assumption)
                ltac:(assumption) HΘ Hdm) as [HAlc HΘ1].
    pose proof (e_typing_defs_mono H Hdm) as Hdm1.
    pose proof (e_sub_lc H0 (ptyp_to_pskl_lc HAlc) HP0 Hdm1) as Hout.
    paint_lc.
    split; [ assumption | eapply e_sub_env_lc; eassumption ].
  - (* AT-Freeze *)
    inversion He; subst. paint_lc.
    destruct H0 as [Qm Hc].
    destruct (IHe_typing lc_pskl_ghost ltac:(assumption) HΘ Hdm)
      as [HBlc HΘ1].
    pose proof (e_typing_defs_mono H Hdm) as Hdm1.
    split; [ assumption | eapply e_consis_env_lc; eassumption ].
  - (* AT-Abs *)
    inversion He; subst.
    destruct (e_split_lc H0 HP0) as [HPlc HQlc].
    pose proof (e_split_env_lc H0 HΘ) as HΘ1.
    pose proof (e_split_defs_mono H0 Hdm) as Hdm1.
    pose proof (e_guess_mono_lc H1) as HAlc.
    pose proof (e_guess_mono_block_flex H1) as Hflex.
    destruct (IHe_typing HQlc ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ simpl; exact HAlc
                      | apply Forall_app; split;
                        [ apply all_flex_mono_lc_forall; exact Hflex
                        | exact HΘ1 ] ])
                ltac:(simpl; constructor;
                      [ exact I
                      | apply Forall_app; split;
                        [ apply all_flex_mono_defs_mono; exact Hflex
                        | exact Hdm1 ] ])) as [HBlc HΘout].
    split; [ apply lc_ptyp_arrow; assumption | drop_binder HΘout ].
  - (* AT-AbsAnno *)
    inversion He; subst.
    destruct (e_split_lc H0 HP0) as [HPlc HQlc].
    pose proof (e_split_env_lc H0 HΘ) as HΘ1.
    pose proof (e_split_defs_mono H0 Hdm) as Hdm1.
    destruct H1 as [Qm Hc].
    pose proof (e_consis_env_lc Hc HΘ1) as HΘ2.
    pose proof (e_consis_defs_mono Hc Hdm1) as Hdm2.
    destruct (IHe_typing HQlc ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ simpl; assumption | exact HΘ2 ])
                ltac:(simpl; constructor; [ exact I | exact Hdm2 ]))
      as [HBlc HΘout].
    split; [ apply lc_ptyp_arrow; assumption | drop_binder HΘout ].
  - (* AT-AbsCheck, the ∀-peeling step *)
    paint_lc.
    destruct (IHe_typing
                ltac:(open_all_lc)
                ltac:(assumption)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ exact I | exact HΘ ])
                ltac:(simpl; constructor; [ exact I | exact Hdm ]))
      as [HAlc HΘout].
    split; [ apply (lc_ptyp_all_exists α); exact HAlc | drop_binder HΘout ].
  - (* AT-AbsCheck, the base *)
    inversion He; subst. paint_lc.
    destruct (e_split_lc H (ptyp_to_pskl_lc HP0)) as [HAlc HBlc]. paint_lc.
    pose proof (e_split_env_lc H HΘ) as HΘ1.
    pose proof (e_split_defs_mono H Hdm) as Hdm1.
    destruct (IHe_typing ltac:(apply ptyp_to_pskl_lc; assumption)
                ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ simpl; assumption | exact HΘ1 ])
                ltac:(simpl; constructor; [ exact I | exact Hdm1 ]))
      as [HB1lc HΘout].
    split; [ apply lc_ptyp_arrow; assumption | drop_binder HΘout ].
  - (* AT-AbsAnnoCheck, the ∀-peeling step *)
    paint_lc.
    destruct (IHe_typing
                ltac:(open_all_lc)
                ltac:(assumption)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ exact I | exact HΘ ])
                ltac:(simpl; constructor; [ exact I | exact Hdm ]))
      as [HAlc HΘout].
    split; [ apply (lc_ptyp_all_exists α); exact HAlc | drop_binder HΘout ].
  - (* AT-AbsAnnoCheck, the base *)
    inversion He; subst. paint_lc.
    destruct (e_split_lc H (ptyp_to_pskl_lc HP0)) as [HA'lc HBlc]. paint_lc.
    pose proof (e_split_env_lc H HΘ) as HΘ1.
    pose proof (e_split_defs_mono H Hdm) as Hdm1.
    destruct H0 as [Qm Hc].
    pose proof (e_consis_env_lc Hc HΘ1) as HΘ2.
    pose proof (e_consis_defs_mono Hc Hdm1) as Hdm2.
    destruct (IHe_typing ltac:(apply ptyp_to_pskl_lc; assumption)
                ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ simpl; assumption | exact HΘ2 ])
                ltac:(simpl; constructor; [ exact I | exact Hdm2 ]))
      as [HB1lc HΘout].
    split; [ apply lc_ptyp_arrow; assumption | drop_binder HΘout ].
  - (* AT-App *)
    inversion He; subst.
    destruct (e_pat_lc_env H lc_pskl_ghost ltac:(assumption) HΘ Hdm)
      as [HPlc HΘ1].
    pose proof (e_pat_defs_mono H Hdm) as Hdm1.
    destruct (IHe_typing1 ltac:(apply lc_pskl_arrow; assumption)
                ltac:(assumption) HΘ1 Hdm1) as [HABlc HΘ2].
    pose proof (e_typing_defs_mono H0 Hdm1) as Hdm2.
    inversion HABlc; subst.
    destruct (IHe_typing2 ltac:(apply ptyp_to_pskl_lc; assumption)
                ltac:(assumption) HΘ2 Hdm2) as [HA'lc HΘ3].
    split; [ assumption | exact HΘ3 ].
Qed.
