(** ext_algo — the subtyping walk's supply invariants, and its bridge.

    §1  supply growth
    §2  the domain upper bound — [prop_consis.v] §2's statement for this
        cluster, and what retires the six [Flex-*] output-freshness premises
    §3  ⭐ THE BRIDGE — [e_sub] / [e_sub_flex] imply [a_sub] / [a_sub_flex],
        over the SAME contexts
    §4  the two projections, and the hypothesis-free entry point

    ⚙ The shape is [prop_consis.v] §4's, not [prop_look.v]'s: [a_sub] has an
    OUTPUT CONTEXT, so three rows re-establish an output-shaped side condition
    and each forces one conjunct beyond the bridge itself.

    - [ForallR] re-establishes [α ∉ dom Θ1] and [α ∉ dom Ξ] from UNIQUENESS of
      the premise's output [Ξ ++ (α ~ tvar) ++ Θ1] — hence [uniq Θ1] in the
      motive.  ⚙ The domain bound cannot serve here: [α] is drawn OUT of [S0]
      and so lands in the bound's own [S1 ∖ S0] summand.
    - the six [Flex-*] re-attaching rows re-establish [β ∉ dom Θ1] from the
      DOMAIN UPPER BOUND — hence §2.  That one IS hypothesis-free (the ∀ rows
      pay for their binder exactly as above), so it is a separate induction.
    - [Arrow] and [ForallL] hand a later premise the earlier one's OUTPUT
      context and supply — hence [ftvar_in_aenv Θ1 [<=] S1].

    What it needs from outside is [e_extract_sound] (prop_extract.v) at
    [ForallL] and the consistency bridge (prop_consis.v §4) at [Check] and
    [Arrow] — both already stated inputs-pointwise, so both compose. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.prop_tag.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.prop_consis.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.prop_extract.
Require Import src.frost.ext_algo.def_sub.

Set Implicit Arguments.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The supply only grows                                             *)
(* ===================================================================== *)

Lemma e_sub_sub_flex_supply_grows :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e -> S0 [<=] S1) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 -> S0 [<=] S1).
Proof.
  apply (e_sub_sub_flex_mutind
           (fun S0 NM M P0 Θ0 P Q S1 Θ1 _ => S0 [<=] S1)
           (fun S0 NM M P0 Θ0 Ξ α Q S1 Θ1 _ => S0 [<=] S1));
    intros;
    (* [Check]'s premise is the consistency abbreviation, so its growth comes
       from M2 rather than from an IH *)
    try (match goal with
         | Hc : e_consis_chk _ _ _ _ _ _ |- _ =>
             destruct Hc as [Q0 Hc]; pose proof (e_consis_supply_grows Hc)
         end);
    (* [Arrow]'s first premise is a consistency run, [ForallL]'s first is an
       extraction *)
    try (match goal with
         | Hc : e_consis _ _ _ _ _ _ _ _ _ |- _ =>
             pose proof (e_consis_supply_grows Hc)
         end);
    try (match goal with
         | He : e_extract _ _ _ _ _ _ _ _ _ _ |- _ =>
             pose proof (e_extract_supply_grows He)
         end);
    fsetdec.
Qed.

Corollary e_sub_supply_grows : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e -> S0 [<=] S1.
Proof. apply e_sub_sub_flex_supply_grows. Qed.

Corollary e_sub_flex_supply_grows : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 -> S0 [<=] S1.
Proof. apply e_sub_sub_flex_supply_grows. Qed.

(* ===================================================================== *)
(*  §2  ⭐ THE DOMAIN UPPER BOUND — what retires the six [Flex-*] premises *)
(*                                                                        *)
(*      dom Θ1  [<=]  dom (inputs)  ∪  (S1 ∖ S0)                          *)
(*                                                                        *)
(*  Read against a re-attaching row it IS the retired premise: the        *)
(*  walked-past entry is in S0 (the supply covers the context) and not in *)
(*  the STRIPPED context (the context is uniq), so it is in neither       *)
(*  summand.  Verbatim [prop_consis.v] §2, and — like it — hypothesis-free *)
(*  even at the ∀ row, because the binder [α] is drawn OUT of [S0] and     *)
(*  growth puts it IN [S1], so it lands in the [S1 ∖ S0] summand on its    *)
(*  own.                                                                  *)
(* ===================================================================== *)

(** Every derivation in context becomes its growth fact, plus the two
    OUTSIDE bounds this walk consumes (consistency's own §2, and the
    extract block's).  Name-free and [lazymatch]-guarded, per the
    [Combined Scheme] rationale of prop_consis.v §2. *)
#[local] Ltac sub_dom_facts :=
  repeat match goal with
  | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
  end;
  repeat match goal with
  | H : e_sub ?S0 _ _ _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_sub_supply_grows H)
      end
  | H : e_sub_flex ?S0 _ _ _ _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_sub_flex_supply_grows H)
      end
  | H : e_consis _ _ ?S0 _ _ _ _ ?S1 _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_consis_supply_grows H)
      end
  | H : e_extract ?S0 _ _ _ _ _ _ ?S1 _ _ |- _ =>
      lazymatch goal with
      | _ : S0 [<=] S1 |- _ => fail
      | _ => pose proof (e_extract_supply_grows H)
      end
  end;
  repeat match goal with
  | H : e_consis _ _ _ ?Θ0 _ _ _ _ ?Θ1 |- _ =>
      lazymatch goal with
      | _ : dom Θ1 [<=] dom Θ0 ∪ _ |- _ => fail
      | _ => pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                           _ _ _ _ _ _ _ _ _ H)
      end
  | H : e_extract _ _ _ _ _ _ _ _ ?Ξ _ |- _ =>
      lazymatch goal with
      | _ : dom Ξ [<=] _ |- _ => fail
      (* ⚠️ ONLY the two conjuncts [ForallL] needs.  [e_extract_block]'s other
         two ([uniq Ξ], [ftvar_in_aenv Ξ [<=] dom Ξ]) are irrelevant here and
         the second one adds a set LEAF — which is what tipped this row's
         [fsetdec] over the tauto cliff (26 s, measured). *)
      | _ => pose proof (e_extract_block H) as [? [? _]]
      end
  end.

Lemma e_sub_sub_flex_dom_upper :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     dom Θ1 [<=] dom Θ0 ∪ (S1 ∖ S0)) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     dom Θ1 [<=] dom (Ξ ++ Θ0) ∪ (S1 ∖ S0)).
Proof.
  apply (e_sub_sub_flex_mutind
           (fun S0 NM M P0 Θ0 P Q S1 Θ1 _ => dom Θ1 [<=] dom Θ0 ∪ (S1 ∖ S0))
           (fun S0 NM M P0 Θ0 Ξ α Q S1 Θ1 _ =>
              dom Θ1 [<=] dom (Ξ ++ Θ0) ∪ (S1 ∖ S0)));
    intros; sub_dom_facts;
    (* ⭐ Every row is set arithmetic once the growth facts and the two
       outside bounds are in.  The three rows that DRAW from the supply
       ([ForallR], [ForallL], [Flex-Solve]) are the ones worth checking by
       hand: their IH is one or two [add]s too strong, and what pays for the
       drawn atom is that the rule picked it OUT of [S0] while growth put it
       IN [S1]. *)
    simpl_env in *; repeat rewrite dom_app in *; simpl dom in *; fsetdec.
Qed.

Corollary e_sub_dom_upper : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  dom Θ1 [<=] dom Θ0 ∪ (S1 ∖ S0).
Proof. apply e_sub_sub_flex_dom_upper. Qed.

Corollary e_sub_flex_dom_upper : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
  dom Θ1 [<=] dom (Ξ ++ Θ0) ∪ (S1 ∖ S0).
Proof. apply e_sub_sub_flex_dom_upper. Qed.

(* ===================================================================== *)
(*  §3  ⭐ THE BRIDGE — [e_sub] implies [a_sub], over the SAME contexts    *)
(*                                                                        *)
(*  Inputs fixed POINTWISE and the output [Θ1] carried across unchanged,   *)
(*  as at M1 / M2 / M3a — the discipline that makes this compose with the  *)
(*  theorems that fix [Θ0]/[Θ1].                                          *)
(*                                                                        *)
(*  TWO HYPOTHESES, both the supply's own discipline: [uniq (inputs)] and  *)
(*  supply coverage.  ⚠️ The FLEX component must cover the subject's        *)
(*  VARIABLE [α] too — [Flex-Solve]'s deposited names avoid it by name,    *)
(*  and it is reachable from neither the stripped context nor [P0].        *)
(*                                                                        *)
(*  THE MOTIVE CARRIES TWO MORE CONJUNCTS (the header says which row       *)
(*  forces each): [uniq Θ1] and [ftvar_in_aenv Θ1 [<=] S1].               *)
(* ===================================================================== *)

(** ⚙ [solve_uniq] with the [dom]s NORMALISED.  Metalib's own tactic runs
    [unfold disjoint] only at the very end, so the [dom (x ~ a ++ E)] it
    leaves inside a [disjoint] goal never reaches [simpl_env] and [fsetdec]
    sees an opaque set.  Needed by [Flex-Solve], the one row that inserts two
    entries into the middle of a context. *)
#[local] Ltac uniq_env :=
  simpl_env in *; destruct_uniq;
  repeat first [ apply uniq_push | apply uniq_cons_3 | apply uniq_app_4
               | apply uniq_one_1 | apply uniq_nil ];
  try unfold disjoint in *; simpl_env in *;
  solve [ assumption | fsetdec ].

(** [dom] / [ftvar_in_aenv] normalisation — prop_consis.v §3's, verbatim. *)
#[local] Ltac env_simp :=
  simpl_env in *;
  repeat (rewrite ftvar_in_aenv_app in * );
  repeat (rewrite dom_app in * );
  simpl ftvar_in_aenv in *; simpl dom in *; simpl_env in *.

Lemma e_sub_sub_flex_sound :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     uniq Θ0 ->
     ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P [<=] S0 ->
     {{ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}a
     /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_pskl Q [<=] S1) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     uniq (Ξ ++ Θ0) ->
     add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0 ->
     a_sub_flex NM M P0 Θ0 Ξ α Q Θ1
     /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_pskl Q [<=] S1).
Proof.
  apply (e_sub_sub_flex_mutind
    (fun S0 NM M P0 Θ0 P Q S1 Θ1 _ =>
       uniq Θ0 ->
       ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P [<=] S0 ->
       {{ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}a
       /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_pskl Q [<=] S1)
    (fun S0 NM M P0 Θ0 Ξ α Q S1 Θ1 _ =>
       uniq (Ξ ++ Θ0) ->
       add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0 ->
       a_sub_flex NM M P0 Θ0 Ξ α Q Θ1
       /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_pskl Q [<=] S1)).

  (* ---------------- a_sub ---------------- *)
  - (* Infer *)
    intros S NM P Θ0 Hu Hcov.
    repeat split; [ apply a_sub__infer | assumption
                  | clear - Hcov; fsetdec | clear - Hcov; fsetdec ].

  - (* Check — the consistency bridge, at [Δ1 = Δ2 = ∅] *)
    intros S0 S1 Θ0 Θ1 A B HgfA HgfB HgdA HgdB Hc Hu Hcov.
    destruct Hc as [Q0 Hc].
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc Hu ltac:(clear - Hcov; fsetdec))
      as [Hca [Hu1 Hcv1]].
    pose proof (e_consis_supply_grows Hc) as Hgc.
    repeat split; [ | assumption | assumption | clear - Hcov Hgc; fsetdec ].
    apply a_sub__check; try assumption. exists Q0. assumption.

  - (* ForallR — ⭐ the row the [uniq] conjunct is FOR: the retired
       [α ∉ dom Θ1] and [α ∉ dom Ξ] are both uniqueness of the premise's
       output [Ξ ++ (α ~ tvar) ++ Θ1] *)
    intros α S0 S1 Θ0 Θ1 Ξ A B Hgf Hsuf HuΞΘ Hnα Hs IH Hu Hcov.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    assert (Hαdom : α `notin` dom Θ0) by (clear - Hdc Hcov Hnα; fsetdec).
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0))
      by (clear - Hu Hαdom; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((α ~ abind_tvar) ++ Θ0)
                    ∪ ftvar_in_pskl (open_pskl_wrt_pskl B (pskl_var_f α))
                    ∪ ftvar_in_pskl A [<=] add α S0).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f α)) as H1.
      simpl in H1. clear - H1 Hcov. env_simp. fsetdec. }
    destruct (IH Hu' Hcov') as [Hsa [Hu1 [Hcv1 Hq1]]].
    assert (HαΞ : α `notin` dom Ξ) by (clear - Hu1; simpl_env in *; solve_uniq).
    assert (HαΘ1 : α `notin` dom Θ1)
      by (clear - Hu1; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_sub__forall_r with (α := α) (Ξ := Ξ); try assumption.
      clear - HαΞ HαΘ1 Hαdom Hnα Hcov. env_simp. fsetdec.
    + clear - Hu1; simpl_env in *; solve_uniq.
    + clear - Hcv1. env_simp. fsetdec.
    + pose proof (e_sub_supply_grows Hs) as Hgs.
      simpl. clear - Hcov Hgs. fsetdec.

  - (* UnivGhostR *)
    intros S Θ0 P Hgd Hu Hcov.
    repeat split; [ apply a_sub__univ_ghost_r; assumption | assumption
                  | clear - Hcov; fsetdec | simpl; clear - Hcov; fsetdec ].

  - (* FlexMono — the flex walk starts with an EMPTY accumulator *)
    intros S0 S1 NM M P0 Θ0 Θ1 α Q Hf IH Hu Hcov.
    simpl in Hcov.
    assert (Hu' : uniq (nil ++ Θ0)) by (clear - Hu; simpl_env; assumption).
    assert (Hcov' : add α (ftvar_in_aenv (nil ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_sub__flex_mono; assumption | assumption
                  | assumption | assumption ].

  - (* Arrow — ⭐ the row the output-coverage conjunct is FOR: its second
       premise runs at [Θ1] and [S1] *)
    intros S0 S1 S2 NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH Hu Hcov.
    simpl in Hcov.
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc Hu ltac:(clear - Hcov; fsetdec))
      as [Hca [Hu1 Hcv1]].
    pose proof (e_consis_supply_grows Hc) as Hg1.
    assert (Hcov2 : ftvar_in_aenv Θ1 ∪ ftvar_in_pskl P0b
                      ∪ ftvar_in_pskl P2 [<=] S1)
      by (clear - Hcov Hcv1 Hg1; fsetdec).
    destruct (IH Hu1 Hcov2) as [Hsa [Hu2 [Hcv2 Hq2]]].
    pose proof (e_consis_out_ftvar Hc Hu ltac:(clear - Hcov; fsetdec)) as HqC.
    pose proof (e_sub_supply_grows Hs) as Hg2.
    repeat split; [ eapply a_sub__arrow; eassumption | assumption
                  | assumption | simpl; clear - HqC Hq2 Hg2; fsetdec ].

  - (* ForallL — the extraction's block [Ξ] joins the context, and ⭐ its
       [uniq (Ξ ++ Θ0)] is a THEOREM here (prop_look.v §4's payoff, at the
       extraction level: prop_extract.v's [e_extract_block]) *)
    intros α S0 S1 S2 NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hgd Hnα Hex Hwf Hs IH Hu Hcov.
    simpl in Hcov.
    pose proof (e_extract_supply_grows Hex) as Hg1.
    pose proof (e_extract_block Hex) as [HinΞ [HfrΞ [HuΞ HftΞ]]].
    pose proof (e_extract_out_ftvar Hex) as Hout.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hop.
    simpl in Hop.
    assert (Hexa : {{ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α))
                      ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}a).
    { eapply e_extract_sound; [ exact Hex | ]. clear - Hop Hcov. fsetdec. }
    assert (HuΞΘ : uniq (Ξ ++ Θ0)).
    { apply uniq_app_4; [ assumption | assumption | ].
      unfold disjoint. intros y Hy.
      assert (Hy1 : y `in` dom Ξ) by (clear - Hy; fsetdec).
      assert (Hy2 : y `in` dom Θ0) by (clear - Hy; fsetdec).
      clear - Hy1 Hy2 HfrΞ Hdc Hcov. fsetdec. }
    assert (HcovP1 : ftvar_in_pskl P1 [<=] S1)
      by (clear - Hout Hop Hcov Hg1; fsetdec).
    assert (Hcov2 : ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0
                      ∪ ftvar_in_pskl (open_pskl_wrt_pskl P P1) [<=] S1).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P P1) as H2.
      rewrite ftvar_in_aenv_app.
      clear - H2 HcovP1 HinΞ HftΞ Hcov Hg1. fsetdec. }
    destruct (IH HuΞΘ Hcov2) as [Hsa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ | assumption | assumption | assumption ].
    apply a_sub__forall_l with (α := α) (Ξ := Ξ) (P1 := P1); try assumption.
    clear - Hnα Hcov. fsetdec.

  - (* Ghost *)
    intros S M Θ0 P0 Hne Hu Hcov.
    repeat split; [ apply a_sub__ghost; exact Hne | assumption
                  | clear - Hcov; fsetdec | clear - Hcov; fsetdec ].

  - (* UnivGhostL *)
    intros S0 S1 M Θ0 Θ1 P0 P Q Hne Hs IH Hu Hcov.
    simpl in Hcov.
    destruct (IH Hu ltac:(clear - Hcov; fsetdec)) as [Hsa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_sub__univ_ghost_l; assumption | assumption
                  | assumption | assumption ].

  (* ---------------- a_sub_flex ---------------- *)
  - (* Flex-Solve — ⭐ THREE prose-completions retired: the two deposited
       flexibles are drawn from the supply in SEQUENCE, so [α <> β] and both
       avoid-conditions are consequences *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α0 α β Q Hnα Hnβ Hs IH Hu Hcov.
    pose proof (dom_subset_ftvar_in_aenv (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      as Hdc.
    assert (HdomS : dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0) [<=] S0)
      by (clear - Hdc Hcov; fsetdec).
    assert (Hne : α <> β)
      by (intro Heq; subst; clear - Hnβ; fsetdec).
    assert (Hαd' : α `notin` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (clear - HdomS Hnα; fsetdec).
    assert (Hβd' : β `notin` dom (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (clear - HdomS Hnβ; fsetdec).
    assert (Hαd : α `notin` add α0 (dom (Ξ ++ Θ0)))
      by (clear - Hαd'; env_simp; fsetdec).
    assert (Hβd : β `notin` add α0 (dom (Ξ ++ Θ0)))
      by (clear - Hβd'; env_simp; fsetdec).
    assert (Hu' : uniq (Ξ ++ (α0 ~ abind_flex_mono_def
                                 (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                          ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                          ++ Θ0)).
    { clear - Hu Hαd' Hβd' Hne. uniq_env. }
    assert (Hcov' : ftvar_in_aenv
                      (Ξ ++ (α0 ~ abind_flex_mono_def
                                   (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
                         ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)
                         ++ Θ0)
                    ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl (pskl_arrow (pskl_var_f α) (pskl_var_f β))
                    [<=] add β (add α S0))
      by (clear - Hcov; env_simp; simpl in *; fsetdec).
    destruct (IH Hu' Hcov') as [Hsa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ | assumption | assumption | assumption ].
    apply a_sub_flex__solve with (α := α) (β := β); assumption.

  - (* Flex-Assign — ⭐ the retired [β ∉ dom Θ1] is §2 on the re-entered
       main premise, plus [β ∉ dom (Ξ ++ Θ0)] from uniqueness *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β τ Q Hs IH Hu Hcov.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HβS : β `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HαS : α `in` S0) by (clear - Hcov; fsetdec).
    assert (Hτ : ftvar_in_ptyp τ [<=] S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HcovΞΘ : ftvar_in_aenv (Ξ ++ Θ0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (HcovP0 : ftvar_in_pskl P0 [<=] S0) by (clear - Hcov; fsetdec).
    assert (Hcov' : ftvar_in_aenv (Ξ ++ Θ0)
              ∪ ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
              ∪ ftvar_in_pskl
                  (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))
              [<=] S0).
    { pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    P0 (ptyp_to_pskl τ) β) as H1.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    (pskl_var_f α) (ptyp_to_pskl τ) β) as H2.
      pose proof (ftvar_ptyp_to_pskl τ) as H3.
      simpl in H2. clear - H1 H2 H3 Hτ HcovΞΘ HcovP0 HαS. fsetdec. }
    destruct (IH HuΞΘ Hcov') as [Hsa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_supply_grows Hs) as Hgrow.
    assert (Hβ1 : β `notin` dom Θ1).
    { pose proof (e_sub_dom_upper Hs) as Hdu. clear - Hdu Hβd HβS. fsetdec. }
    repeat split.
    + apply a_sub_flex__assign; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HβS Hτ Hgrow. env_simp. fsetdec.
    + assumption.

  - (* Flex-Depend — the walked-past flexible joins the ACCUMULATOR *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hin Hf IH Hu Hcov.
    assert (Hu' : uniq ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hcov' : add α (ftvar_in_aenv ((Ξ ++ (β ~ abind_flex_mono)) ++ Θ0)
                             ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_sub_flex__depend | | | ]; assumption.

  - (* Flex-Skip *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hnin Hf IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HβS : β `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_flex_supply_grows Hf) as Hgrow.
    assert (Hβ1 : β `notin` dom Θ1).
    { pose proof (e_sub_flex_dom_upper Hf) as Hdu.
      clear - Hdu Hβd HβS. fsetdec. }
    repeat split.
    + apply a_sub_flex__skip; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HβS Hgrow. env_simp. fsetdec.
    + assumption.

  - (* Flex-SkipRigid *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hnin Hf IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hβd : β `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HβS : β `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_flex_supply_grows Hf) as Hgrow.
    assert (Hβ1 : β `notin` dom Θ1).
    { pose proof (e_sub_flex_dom_upper Hf) as Hdu.
      clear - Hdu Hβd HβS. fsetdec. }
    repeat split.
    + apply a_sub_flex__skip_rigid; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HβS Hgrow. env_simp. fsetdec.
    + assumption.

  - (* Flex-SkipTmVar *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Apay Q Hf IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HxS : x `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HA : ftvar_in_ptyp Apay [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_flex_supply_grows Hf) as Hgrow.
    assert (Hx1 : x `notin` dom Θ1).
    { pose proof (e_sub_flex_dom_upper Hf) as Hdu.
      clear - Hdu Hxd HxS. fsetdec. }
    repeat split.
    + apply a_sub_flex__skip_tm_var; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HxS HA Hgrow. env_simp. fsetdec.
    + assumption.

  - (* Flex-SkipTmVar (skl) *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hf IH Hu Hcov.
    assert (Hu' : uniq (Ξ ++ Θ0)) by (clear - Hu; simpl_env in *; solve_uniq).
    assert (Hxd : x `notin` dom (Ξ ++ Θ0))
      by (clear - Hu; simpl_env in *; solve_uniq).
    assert (HxS : x `in` S0) by (clear - Hcov; env_simp; fsetdec).
    assert (HQ : ftvar_in_pskl Qpay [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    assert (Hcov' : add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IH Hu' Hcov') as [Hfa [Hu1 [Hcv1 Hq1]]].
    pose proof (e_sub_flex_supply_grows Hf) as Hgrow.
    assert (Hx1 : x `notin` dom Θ1).
    { pose proof (e_sub_flex_dom_upper Hf) as Hdu.
      clear - Hdu Hxd HxS. fsetdec. }
    repeat split.
    + apply a_sub_flex__skip_tm_skl; assumption.
    + apply uniq_push; assumption.
    + clear - Hcv1 HxS HQ Hgrow. env_simp. fsetdec.
    + assumption.
Qed.

(* ===================================================================== *)
(*  §4  The projections, and the hypothesis-free entry point              *)
(* ===================================================================== *)

Corollary e_sub_sound : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P [<=] S0 ->
  {{ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}a.
Proof.
  intros. eapply (proj1 e_sub_sub_flex_sound); eassumption.
Qed.

Corollary e_sub_flex_sound : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
  uniq (Ξ ++ Θ0) ->
  add α (ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0) [<=] S0 ->
  a_sub_flex NM M P0 Θ0 Ξ α Q Θ1.
Proof.
  intros. eapply (proj2 e_sub_sub_flex_sound); eassumption.
Qed.

(** ⭐ AND AT THE ENTRY POINT THE PREMISES COST NOTHING — the driver starts
    with an empty context and CHOOSES the supply, so both conditions are
    [reflexivity].  prop_consis.v §6 makes the general argument; this is its
    instance for the flagship judgement of M3. *)
Corollary e_sub_sound_init : forall NM M P0 P Q S1 Θ1,
  {{ (ftvar_in_pskl P0 ∪ ftvar_in_pskl P) ↝ S1
     ⊨ nil ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  {{ nil ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}a.
Proof.
  intros * He. eapply e_sub_sound; [ exact He | apply uniq_nil | ].
  simpl. fsetdec.
Qed.

(* ===================================================================== *)
(*  §5  EQUIVARIANCE                                                      *)
(*                                                                        *)
(*  algo/prop_swap.v §12's [a_sub_sub_flex_swap] in the ∃-form the supply  *)
(*  forces (prop_guess.v §8's reason).  ⚙ Every [Δ-drop] premise the       *)
(*  a-side has to re-establish under the swap ([α ∉ dom Θ1],              *)
(*  [β ∉ dom Θ1], six of them) is simply GONE here, which is what makes    *)
(*  this the shorter proof of the two; what replaces them is one          *)
(*  [swap_notin_eq] per drawn atom and one [eq_swap_atoms_add] per premise *)
(*  supply.                                                               *)
(*                                                                        *)
(*  ⭐ WHY THE LEVEL NEEDS IT.  A derivation opens [SI-ForallR]'s binder,  *)
(*  [SI-ForallL]'s extraction opener and [SI-Flex-Solve]'s two deposited   *)
(*  flexibles at ANY atom fresh for the supply; the runner draws every one *)
(*  of them at [supply_fresh].  So the derivation has to be moved onto the *)
(*  runner's rails before an IH stated at the runner's inputs can apply,   *)
(*  and a transposition is the move (USER DIRECTIVE, swap kit).           *)
(* ===================================================================== *)

(** SUPPLY RESPECT.  A supply is a SET, so a caller that assembled one by a
    different route holds an [=]-variant rather than the term — and the
    judgement takes it as an INDEX, which no [rewrite] can move under.  This
    is what prop_sub_complete.v §3's CHAIN needs at length zero. *)
Lemma e_sub_sub_flex_supply_respect :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       {{ S0' ↝ S1' ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     forall S0', S0' [=] S0 ->
     exists S1', S1' [=] S1 /\
       e_sub_flex S0' NM M P0 Θ0 Ξ α Q S1' Θ1).
Proof.
  apply (e_sub_sub_flex_mutind
    (fun S0 NM M P0 Θ0 P Q S1 Θ1 _ =>
       forall S0', S0' [=] S0 ->
       exists S1', S1' [=] S1 /\
         {{ S0' ↝ S1' ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e)
    (fun S0 NM M P0 Θ0 Ξ α Q S1 Θ1 _ =>
       forall S0', S0' [=] S0 ->
       exists S1', S1' [=] S1 /\
         e_sub_flex S0' NM M P0 Θ0 Ξ α Q S1' Θ1)).

  (* --------------------------- e_sub --------------------------- *)
  - intros S NM P Θ0 S0' Heq.
    exists S0'. split; [ exact Heq | apply e_sub__infer ].
  - intros S0 S1 Θ0 Θ1 A B HgfA HgfB HgdA HgdB [Q Hc] S0' Heq.
    destruct (e_consis_supply_respect Hc Heq) as [S1' [HS1 Hc']].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub__check; try assumption. exists Q. exact Hc'.
  - intros α S0 S1 Θ0 Θ1 Ξ A B Hgf Hsuf HuΞΘ Hnα Hs IH S0' Heq.
    destruct (IH (add α S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub__forall_r with (α := α) (Ξ := Ξ);
      solve [ assumption | rewrite Heq; assumption ].
  - intros S Θ0 P Hgd S0' Heq.
    exists S0'. split; [ exact Heq | apply e_sub__univ_ghost_r; assumption ].
  - intros S0 S1 NM M P0 Θ0 Θ1 α Q Hf IH S0' Heq.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub__flex_mono; exact Hd ].
  - intros S0 S1 S2 NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH S0' Heq.
    destruct (e_consis_supply_respect Hc Heq) as [S1' [HS1 Hc']].
    destruct (IH _ HS1) as [S2' [HS2 Hd]].
    exists S2'. split; [ exact HS2 | eapply e_sub__arrow; eassumption ].
  - intros α S0 S1 S2 NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hgd Hnα Hex Hwf Hs IH S0' Heq.
    assert (Heqα : add α S0' [=] add α S0) by (rewrite Heq; reflexivity).
    destruct (e_extract_supply_respect Hex Heqα) as [S1' [HS1 Hex']].
    destruct (IH _ HS1) as [S2' [HS2 Hd]].
    exists S2'. split; [ exact HS2 | ].
    eapply e_sub__forall_l with (α := α) (Ξ := Ξ) (P1 := P1).
    + exact Hne.
    + exact Hgd.
    + rewrite Heq. exact Hnα.
    + exact Hex'.
    + exact Hwf.
    + exact Hd.
  - intros S M Θ0 P0 Hne S0' Heq.
    exists S0'. split; [ exact Heq | apply e_sub__ghost; exact Hne ].
  - intros S0 S1 M Θ0 Θ1 P0 P Q Hne Hs IH S0' Heq.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub__univ_ghost_l; assumption ].

  (* ------------------------- e_sub_flex ------------------------ *)
  - intros S0 S1 NM M P0 Θ0 Θ1 Ξ α0 α β Q Hnα Hnβ Hs IH S0' Heq.
    destruct (IH (add β (add α S0')) ltac:(rewrite Heq; reflexivity))
      as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__solve with (α := α) (β := β);
      [ rewrite Heq; exact Hnα | rewrite Heq; exact Hnβ | exact Hd ].
  - intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β τ Q Hs IH S0' Heq.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__assign; exact Hd ].
  - intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hin Hf IH S0' Heq.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__depend; assumption ].
  - intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hf IH S0' Heq.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__skip; assumption ].
  - intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hf IH S0' Heq.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__skip_rigid; assumption ].
  - intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Apay Q Hf IH S0' Heq.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__skip_tm_var; exact Hd ].
  - intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hf IH S0' Heq.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__skip_tm_skl; exact Hd ].
Qed.

Corollary e_sub_supply_respect : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\
    {{ S0' ↝ S1' ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e.
Proof. apply e_sub_sub_flex_supply_respect. Qed.

Corollary e_sub_flex_supply_respect : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ e_sub_flex S0' NM M P0 Θ0 Ξ α Q S1' Θ1.
Proof. apply e_sub_sub_flex_supply_respect. Qed.

(** The output-suppressed consistency abbreviation along a swap — [Check]'s
    premise, and the shape [Arrow]'s first premise reduces to. *)
Lemma e_consis_empty_swap : forall a b S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ empty | empty | (swap_pskl a b P0) ]
       (swap_pskl a b P) ∼ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1) }}e.
Proof.
  intros a b S0 Θ0 P0 P Q S1 Θ1 Hc S0' Heq.
  eapply e_consis_swap;
    [ exact Hc | apply empty_eq_swap_atoms_empty
    | apply empty_eq_swap_atoms_empty | exact Heq ].
Qed.

Lemma e_consis_chk_swap : forall a b S0 Θ0 A B S1 Θ1,
  e_consis_chk S0 Θ0 A B S1 Θ1 ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    e_consis_chk S0' (swap_aenv a b Θ0) (swap_pskl a b A) (swap_pskl a b B)
      S1' (swap_aenv a b Θ1).
Proof.
  intros a b S0 Θ0 A B S1 Θ1 [Q Hc] S0' Heq.
  destruct (e_consis_empty_swap Hc Heq) as [S1' [HS1 Hc']].
  exists S1'. split; [ exact HS1 | exists (swap_pskl a b Q); exact Hc' ].
Qed.

Lemma e_sub_sub_flex_swap : forall a b,
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ NM | M | (swap_pskl a b P0) ]
          (swap_pskl a b P) ⩽ (swap_pskl a b Q)
          ⊣ (swap_aenv a b Θ1) }}e) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     forall S0', S0' [=] swap_atoms a b S0 ->
     exists S1', S1' [=] swap_atoms a b S1 /\
       e_sub_flex S0' NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
         (swap_aenv a b Ξ) (swap_atom a b α) (swap_pskl a b Q)
         S1' (swap_aenv a b Θ1)).
Proof.
  intros a b.
  apply (e_sub_sub_flex_mutind
    (fun S0 NM M P0 Θ0 P Q S1 Θ1 _ =>
       forall S0', S0' [=] swap_atoms a b S0 ->
       exists S1', S1' [=] swap_atoms a b S1 /\
         {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ NM | M | (swap_pskl a b P0) ]
            (swap_pskl a b P) ⩽ (swap_pskl a b Q)
            ⊣ (swap_aenv a b Θ1) }}e)
    (fun S0 NM M P0 Θ0 Ξ α Q S1 Θ1 _ =>
       forall S0', S0' [=] swap_atoms a b S0 ->
       exists S1', S1' [=] swap_atoms a b S1 /\
         e_sub_flex S0' NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
           (swap_aenv a b Ξ) (swap_atom a b α) (swap_pskl a b Q)
           S1' (swap_aenv a b Θ1))).

  (* --------------------------- e_sub --------------------------- *)
  - (* SI-Infer *)
    intros S NM P Θ0 S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_sub__infer ].
  - (* SI-Check *)
    intros S0 S1 Θ0 Θ1 A B HgfA HgfB HgdA HgdB Hc S0' Heq. simpl.
    destruct (e_consis_chk_swap Hc Heq) as [S1' [HS1 Hc']].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub__check;
      auto using guarded_pskl_swap, pskl_ghost_free_swap.
  - (* SI-ForallR — the drawn binder rides the swap, on BOTH sides of the
       premise's output decomposition *)
    intros α S0 S1 Θ0 Θ1 Ξ A B Hgf Hsuf HuΞΘ Hnα Hs IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b α) S0')) as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub__forall_r with (α := swap_atom a b α) (Ξ := swap_aenv a b Ξ).
    + apply pskl_ghost_free_swap; exact Hgf.
    + apply a_suffix_swap; exact Hsuf.
    + rewrite <- swap_aenv_app. apply swap_aenv_uniq; exact HuΞΘ.
    + eapply swap_notin_eq; eassumption.
    + rewrite swap_pskl_open_var in Hd. rewrite !swap_aenv_app in Hd.
      exact Hd.
  - (* SI-UnivGhostR *)
    intros S Θ0 P Hgd S0' Heq. simpl.
    exists S0'. split; [ exact Heq | ].
    apply e_sub__univ_ghost_r; auto using guarded_pskl_swap.
  - (* SI-FlexMono — the walk starts at an EMPTY accumulator *)
    intros S0 S1 NM M P0 Θ0 Θ1 α Q Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub__flex_mono; exact Hd ].
  - (* SI-Arrow — threaded, so the two ∃-witnesses chain *)
    intros S0 S1 S2 NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs IH S0' Heq. simpl.
    destruct (e_consis_empty_swap Hc Heq) as [S1' [HS1 Hc']].
    destruct (IH _ HS1) as [S2' [HS2 Hd]].
    exists S2'. split; [ exact HS2 | ].
    eapply e_sub__arrow; [ exact Hc' | exact Hd ].
  - (* SI-ForallL — the extraction's opener and its block ride the swap *)
    intros α S0 S1 S2 NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hgd Hnα Hex Hwf Hs IH S0' Heq.
    simpl.
    assert (Heqα : add (swap_atom a b α) S0' [=] swap_atoms a b (add α S0))
      by (apply eq_swap_atoms_add; exact Heq).
    destruct (e_extract_swap Hex Heqα) as [S1' [HS1 Hex']].
    destruct (IH _ HS1) as [S2' [HS2 Hd]].
    exists S2'. split; [ exact HS2 | ].
    eapply e_sub__forall_l with (α := swap_atom a b α)
      (Ξ := swap_aenv a b Ξ) (P1 := swap_pskl a b P1).
    + exact Hne.
    + destruct Hgd as [hg | ->];
        [ left; apply guarded_pskl_swap; exact hg | right; reflexivity ].
    + eapply swap_notin_eq; eassumption.
    + rewrite swap_pskl_open_var in Hex'. exact Hex'.
    + rewrite <- swap_aenv_app.
      apply (a_wf_pskl_swap a b _ _ _ Hwf). apply empty_eq_swap_atoms_empty.
    + rewrite swap_pskl_open in Hd. rewrite swap_aenv_app in Hd. exact Hd.
  - (* SI-Ghost *)
    intros S M Θ0 P0 Hne S0' Heq. simpl.
    exists S0'. split; [ exact Heq | apply e_sub__ghost; exact Hne ].
  - (* SI-UnivGhostL *)
    intros S0 S1 M Θ0 Θ1 P0 P Q Hne Hs IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub__univ_ghost_l; [ exact Hne | exact Hd ].

  (* ------------------------- e_sub_flex ------------------------ *)
  - (* SI-Flex-Solve — TWO atoms drawn from the supply, in sequence *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α0 α β Q Hnα Hnβ Hs IH S0' Heq. simpl.
    destruct (IH (add (swap_atom a b β) (add (swap_atom a b α) S0')))
      as [S1' [HS1 Hd]];
      [ apply eq_swap_atoms_add; apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__solve with (α := swap_atom a b α)
      (β := swap_atom a b β).
    + eapply swap_notin_eq; eassumption.
    + eapply swap_notin_eq;
        [ apply eq_swap_atoms_add; exact Heq | exact Hnβ ].
    + rewrite !swap_aenv_app in Hd. exact Hd.
  - (* SI-Flex-Assign — the defined head is substituted away *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β τ Q Hs IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__assign.
    rewrite !swap_pskl_subst in Hd.
    rewrite !swap_pskl_ptyp_to_pskl in Hd.
    change (swap_pskl a b (pskl_var_f α)) with
      (pskl_var_f (swap_atom a b α)) in Hd.
    rewrite swap_aenv_app in Hd. exact Hd.
  - (* SI-Flex-Depend *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hin Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__depend;
      auto using swap_atom_neq, swap_pskl_ftv_in.
    rewrite swap_aenv_app in Hd. exact Hd.
  - (* SI-Flex-Skip *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__skip;
      auto using swap_atom_neq, swap_pskl_ftv_notin.
  - (* SI-Flex-SkipRigid *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q Hne Hni Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_sub_flex__skip_rigid;
      auto using swap_atom_neq, swap_pskl_ftv_notin.
  - (* SI-Flex-SkipTmVar, TYPE payload *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Apay Q Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__skip_tm_var; exact Hd ].
  - (* SI-Flex-SkipTmVar, SKELETON payload *)
    intros S0 S1 NM M P0 Θ0 Θ1 Ξ α x Qpay Q Hf IH S0' Heq. simpl.
    destruct (IH _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_sub_flex__skip_tm_skl; exact Hd ].
Qed.

Corollary e_sub_swap : forall a b S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ NM | M | (swap_pskl a b P0) ]
       (swap_pskl a b P) ⩽ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1) }}e.
Proof. intros a b. apply e_sub_sub_flex_swap. Qed.

Corollary e_sub_flex_swap : forall a b S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    e_sub_flex S0' NM M (swap_pskl a b P0) (swap_aenv a b Θ0)
      (swap_aenv a b Ξ) (swap_atom a b α) (swap_pskl a b Q)
      S1' (swap_aenv a b Θ1).
Proof. intros a b. apply e_sub_sub_flex_swap. Qed.
