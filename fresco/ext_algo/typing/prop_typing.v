(** ext_algo — the supply invariants of TYPE INFERENCE, and its bridge.
    (M4, second half — and the last judgement of TODO (1).)

    §1  supply growth
    §2  ⭐ THE BRIDGE, and with it the whole algorithm

    ⚙ FIVE CONJUNCTS.  Beside the bridge the motive carries [uniq Θ1],
    [ftvar_in_aenv Θ1 [<=] S1] and — the new one at this level —
    [ftvar_in_ptyp B [<=] S1], the OUTPUT TYPE's coverage.  Three rows force
    the last: [AT-App] runs the argument a second time at the function's
    inferred DOMAIN, [AT-Freeze] unifies against the inferred type, and
    [AT-Anno] hands its result on to subtyping.  All four are mutually
    needed, so all four ride together.

    ⭐ WHAT LANDS HERE.  [AT-Abs]'s [uniq (αs ++ Θ1)] — the premise
    docs/REPORT-postclosure-audit.md §1.3 priced at 316 occurrences and
    declined — is discharged by [e_guess_mono_uniq_app], and every binder
    row's freshness collapses to [x ∉ S]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.consistency.prop_consis.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.prop_extract.
Require Import src.fresco.ext_algo.subtyping.def_sub.
Require Import src.fresco.ext_algo.subtyping.prop_sub.
Require Import src.fresco.ext_algo.typing.def_pat.
Require Import src.fresco.ext_algo.typing.prop_pat.
Require Import src.fresco.ext_algo.typing.def_typing.

Set Implicit Arguments.

Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  The supply only grows                                             *)
(* ===================================================================== *)

Lemma e_typing_supply_grows : forall S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e -> S0 [<=] S1.
Proof.
  intros * H; induction H;
    repeat (match goal with
            | Hc : e_consis_chk _ _ _ _ _ _ |- _ => destruct Hc as [? Hc]
            end);
    repeat (match goal with
            | Hs : e_sub ?S0 _ _ _ _ _ _ ?S1 _ |- _ =>
                lazymatch goal with
                | _ : S0 [<=] S1 |- _ => fail
                | _ => pose proof (e_sub_supply_grows Hs)
                end
            | Hsp : e_split ?S0 _ _ _ _ ?S1 _ |- _ =>
                lazymatch goal with
                | _ : S0 [<=] S1 |- _ => fail
                | _ => pose proof (e_split_supply_grows Hsp)
                end
            | Hc : e_consis _ _ ?S0 _ _ _ _ ?S1 _ |- _ =>
                lazymatch goal with
                | _ : S0 [<=] S1 |- _ => fail
                | _ => pose proof (e_consis_supply_grows Hc)
                end
            | Hg : e_guess_mono ?S0 _ ?S1 _ _ |- _ =>
                lazymatch goal with
                | _ : S0 [<=] S1 |- _ => fail
                | _ => pose proof (e_guess_mono_supply_grows Hg)
                end
            | Hp : e_pat ?S0 _ _ _ _ _ ?S1 _ |- _ =>
                lazymatch goal with
                | _ : S0 [<=] S1 |- _ => fail
                | _ => pose proof (e_pat_supply_grows Hp)
                end
            end);
    fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  ⭐ THE BRIDGE                                                      *)
(* ===================================================================== *)

Lemma e_typing_sound : forall S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e
    ∪ ftvar_in_exp e [<=] S0 ->
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}a
  /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_ptyp B [<=] S1.
Proof.
  intros S0 m Θ0 P0 e B S1 Θ1 H; induction H; intros Hu Hcov.

  - (* AT-Unit *)
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H Hu
                  ltac:(clear - Hcov; simpl; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_typing__unit; exact Ha | exact Hu1 | exact Hcv1
                  | clear - Hq1 HAe; fsetdec ].

  - (* AT-Var *)
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    pose proof (ftvar_ptyp_to_pskl B) as HBe.
    assert (HA : ftvar_in_pskl (ptyp_to_pskl A) [<=] S0).
    { pose proof (@ftvar_in_aenv_binds_ftv _ _ _ H) as Hb. simpl in Hb.
      clear - Hb Hcov HAe. fsetdec. }
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H0 Hu
                  ltac:(clear - Hcov HA; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ eapply a_typing__var; eassumption | exact Hu1 | exact Hcv1
                  | clear - Hq1 HBe; fsetdec ].

  - (* AT-Anno *)
    simpl in Hcov.
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    pose proof (ftvar_ptyp_to_pskl B) as HBe.
    destruct (IHe_typing Hu ltac:(clear - Hcov HAe; fsetdec))
      as [Ha1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_typing_supply_grows H) as Hg1.
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H0 Hu1
                  ltac:(clear - Hcov Hcv1 Hg1 HAe; fsetdec))
      as [Ha2 [Hu2 [Hcv2 Hq2]]].
    repeat split; [ eapply a_typing__anno; eassumption | exact Hu2 | exact Hcv2
                  | clear - Hq2 HBe; fsetdec ].

  - (* AT-Freeze — the consistency stage runs at the INFERRED type, so it is
       the output-type conjunct that pays for its coverage *)
    simpl in Hcov.
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    pose proof (ftvar_ptyp_to_pskl B) as HBe.
    destruct (IHe_typing Hu ltac:(clear - Hcov; simpl; fsetdec))
      as [Ha1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_typing_supply_grows H) as Hg1.
    destruct H0 as [Qc Hc].
    pose proof (e_consis_supply_grows Hc) as Hgc.
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc Hu1
                  ltac:(clear - Hcov Hcv1 Hq1 Hg1 HAe HBe; fsetdec))
      as [Hca [Hu2 Hcv2]].
    repeat split.
    + eapply a_typing__freeze; [ exact Ha1 | exists Qc; exact Hca ].
    + exact Hu2.
    + exact Hcv2.
    + clear - Hcov Hg1 Hgc HAe. fsetdec.

  - (* ⭐ AT-Abs — where [uniq (αs ++ Θ1)] becomes a THEOREM *)
    simpl in Hcov.
    destruct (e_split_sound H0 Hu ltac:(clear - Hcov; fsetdec))
      as [Hsp [Hu1 [Hcv1 Hqs]]].
    pose proof (e_split_supply_grows H0) as Hgs.
    (* the guessed block *)
    pose proof (e_guess_mono_supply_grows H1) as Hgg.
    pose proof (e_guess_mono_generated_in_supply H1) as Hbin.
    pose proof (e_guess_mono_generated_ftvar H1) as Hbftv.
    pose proof (e_guess_mono_ftv H1) as Hgftv.
    assert (Hga : a_guess_mono Θ1 P αs A)
      by (eapply e_guess_mono_sound;
          [ exact H1 | exact Hcv1 | clear - Hqs; fsetdec ]).
    assert (Huαs : uniq (αs ++ Θ1))
      by (eapply e_guess_mono_uniq_app; [ exact H1 | exact Hcv1 | exact Hu1 ]).
    (* the binder *)
    pose proof (dom_subset_ftvar_in_aenv Θ1) as Hd1.
    assert (Hxd : x `notin` dom (αs ++ Θ1))
      by (clear - Hd1 Hcv1 Hbin H3 Hgg; env_simp; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_typ A) ++ αs ++ Θ1))
      by (clear - Huαs Hxd; simpl_env in *; solve_uniq).
    assert (HAcov : ftvar_in_ptyp A [<=] S2)
      by (clear - Hgftv Hbin Hqs Hgg; fsetdec).
    assert (Hsc : ftvar_in_aenv (αs ++ Θ1) ∪ ftvar_in_pskl Q
              ∪ ftvar_in_ptyp A ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S2)
      by (clear - Hcov Hcv1 Hqs Hgs Hgg Hbin Hbftv HAcov; env_simp; fsetdec).
    destruct (IHe_typing Hu' (cover_open_body_typ x Hsc))
      as [Ha [Hub [Hcvb Hqb]]].
    assert (HxΞ : x `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HxΘ2 : x `notin` dom Θ2)
      by (clear - Hub; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_typing__abs with (x := x) (Θ1 := Θ1) (P := P) (Q := Q) (αs := αs);
        try assumption.
      clear - Hxd HxΞ HxΘ2 Hcov H3 Hgs Hgg. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + pose proof (e_typing_supply_grows H4) as Hgb.
      simpl. clear - HAcov Hqb Hgb. fsetdec.

  - (* AT-AbsAnno *)
    simpl in Hcov.
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    destruct (e_split_sound H0 Hu ltac:(clear - Hcov; fsetdec))
      as [Hsp [Hu1 [Hcv1 Hqs]]].
    pose proof (e_split_supply_grows H0) as Hgs.
    destruct H1 as [Qc Hc].
    pose proof (e_consis_supply_grows Hc) as Hgc.
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc Hu1
                  ltac:(clear - Hcov Hcv1 Hqs Hgs HAe; fsetdec))
      as [Hca [Hu2 Hcv2]].
    pose proof (dom_subset_ftvar_in_aenv Θ2) as Hd2.
    assert (Hxd : x `notin` dom Θ2) by (clear - Hd2 Hcv2 H3; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_typ A) ++ Θ2))
      by (clear - Hu2 Hxd; solve_uniq).
    assert (Hsc : ftvar_in_aenv Θ2 ∪ ftvar_in_pskl Q
              ∪ ftvar_in_ptyp A ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S2)
      by (clear - Hcov Hcv2 Hqs Hgs Hgc HAe; env_simp; fsetdec).
    destruct (IHe_typing Hu' (cover_open_body_typ x Hsc))
      as [Ha [Hub [Hcvb Hqb]]].
    assert (HxΞ : x `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HxΘ3 : x `notin` dom Θ3)
      by (clear - Hub; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_typing__abs_anno with (x := x) (Θ1 := Θ1) (Θ2 := Θ2)
                                    (P := P) (Q := Q);
        try assumption; [ exists Qc; exact Hca | ].
      clear - Hxd HxΞ HxΘ3 Hcov H3 Hgs Hgc. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + pose proof (e_typing_supply_grows H4) as Hgb.
      simpl. clear - Hqb Hcov Hgs Hgc Hgb HAe. fsetdec.

  - (* AT-AbsCheck (step) *)
    pose proof (cover_open_tvar α Hcov) as Hcov'.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
    assert (Hαd : α `notin` dom Θ0) by (clear - Hd0 Hcov H3; fsetdec).
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0))
      by (clear - Hu Hαd; solve_uniq).
    destruct (IHe_typing Hu' Hcov') as [Ha [Hub [Hcvb Hqb]]].
    assert (HαΞ : α `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HαΘ1 : α `notin` dom Θ1)
      by (clear - Hub; simpl_env in *; solve_uniq).
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A (ptyp_var_f α)) as Hlo.
    repeat split.
    + apply a_typing__abs_check_step with (α := α) (Ξ := Ξ);
        try assumption.
      pose proof (ftvar_ptyp_to_pskl (ptyp_all A0)) as He2.
      simpl in He2, Hcov.
      clear - Hαd HαΞ HαΘ1 H2 H3 Hcov He2.
      simpl ftvar_in_exp. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + simpl. clear - Hqb Hlo. fsetdec.

  - (* AT-AbsCheck (base) *)
    simpl in Hcov.
    pose proof (ftvar_ptyp_to_pskl A0) as He0.
    pose proof (ftvar_ptyp_to_pskl A) as HeA.
    pose proof (ftvar_ptyp_to_pskl B) as HeB.
    destruct (e_split_sound H Hu ltac:(clear - Hcov He0; fsetdec))
      as [Hsp [Hu1 [Hcv1 Hqs]]].
    pose proof (e_split_supply_grows H) as Hgs.
    pose proof (dom_subset_ftvar_in_aenv Θ1) as Hd1.
    assert (Hxd : x `notin` dom Θ1) by (clear - Hd1 Hcv1 H3; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_typ A) ++ Θ1))
      by (clear - Hu1 Hxd; solve_uniq).
    assert (Hsc : ftvar_in_aenv Θ1 ∪ ftvar_in_pskl (ptyp_to_pskl B)
              ∪ ftvar_in_ptyp A ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S1)
      by (clear - Hcov Hcv1 Hqs Hgs HeA HeB; env_simp; fsetdec).
    destruct (IHe_typing Hu' (cover_open_body_typ x Hsc))
      as [Ha [Hub [Hcvb Hqb]]].
    assert (HxΞ : x `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HxΘ2 : x `notin` dom Θ2)
      by (clear - Hub; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_typing__abs_check_base with (x := x) (Θ1 := Θ1) (B := B)
                                          (Ξ := Ξ);
        try assumption.
      clear - Hxd HxΞ HxΘ2 Hcov H3 Hgs. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + pose proof (e_typing_supply_grows H4) as Hgb.
      simpl. clear - Hqs Hqb Hgb HeA. fsetdec.

  - (* AT-AbsAnnoCheck (step) *)
    pose proof (cover_open_tvar α Hcov) as Hcov'.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
    assert (Hαd : α `notin` dom Θ0) by (clear - Hd0 Hcov H3; fsetdec).
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0))
      by (clear - Hu Hαd; solve_uniq).
    destruct (IHe_typing Hu' Hcov') as [Ha [Hub [Hcvb Hqb]]].
    assert (HαΞ : α `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HαΘ1 : α `notin` dom Θ1)
      by (clear - Hub; simpl_env in *; solve_uniq).
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A (ptyp_var_f α)) as Hlo.
    repeat split.
    + apply a_typing__abs_anno_check_step with (α := α) (Ξ := Ξ);
        try assumption.
      pose proof (ftvar_ptyp_to_pskl (ptyp_all A0)) as He2.
      simpl in He2, Hcov.
      clear - Hαd HαΞ HαΘ1 H2 H3 Hcov He2.
      simpl ftvar_in_exp. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + simpl. clear - Hqb Hlo. fsetdec.

  - (* AT-AbsAnnoCheck (base) *)
    simpl in Hcov.
    pose proof (ftvar_ptyp_to_pskl A0) as He0.
    pose proof (ftvar_ptyp_to_pskl A') as HeA'.
    pose proof (ftvar_ptyp_to_pskl A) as HeA.
    pose proof (ftvar_ptyp_to_pskl B) as HeB.
    destruct (e_split_sound H Hu ltac:(clear - Hcov He0; fsetdec))
      as [Hsp [Hu1 [Hcv1 Hqs]]].
    pose proof (e_split_supply_grows H) as Hgs.
    destruct H0 as [Qc Hc].
    pose proof (e_consis_supply_grows Hc) as Hgc.
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc Hu1
                  ltac:(clear - Hcov Hcv1 Hqs Hgs HeA HeA'; fsetdec))
      as [Hca [Hu2 Hcv2]].
    pose proof (dom_subset_ftvar_in_aenv Θ2) as Hd2.
    assert (Hxd : x `notin` dom Θ2) by (clear - Hd2 Hcv2 H4; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_typ A) ++ Θ2))
      by (clear - Hu2 Hxd; solve_uniq).
    assert (Hsc : ftvar_in_aenv Θ2 ∪ ftvar_in_pskl (ptyp_to_pskl B)
              ∪ ftvar_in_ptyp A ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S2)
      by (clear - Hcov Hcv2 Hqs Hgs Hgc HeA HeB; env_simp; fsetdec).
    destruct (IHe_typing Hu' (cover_open_body_typ x Hsc))
      as [Ha [Hub [Hcvb Hqb]]].
    assert (HxΞ : x `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HxΘ3 : x `notin` dom Θ3)
      by (clear - Hub; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_typing__abs_anno_check_base with (x := x) (Θ1 := Θ1) (Θ2 := Θ2)
                                               (B := B) (Ξ := Ξ);
        try assumption; [ exists Qc; exact Hca | ].
      clear - Hxd HxΞ HxΘ3 Hcov H4 Hgs Hgc. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + pose proof (e_typing_supply_grows H5) as Hgb.
      simpl. clear - Hqs Hqb Hgb Hgc HeA'. fsetdec.

  - (* ⭐ AT-App — the argument runs TWICE, the second time at the function's
       inferred DOMAIN, which is what the output-type conjunct is for *)
    simpl in Hcov.
    destruct (e_pat_sound H Hu ltac:(clear - Hcov; simpl; fsetdec))
      as [Hp1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_pat_supply_grows H) as Hg1.
    destruct (IHe_typing1 Hu1
                ltac:(clear - Hcov Hcv1 Hq1 Hg1; simpl; fsetdec))
      as [Ha2 [Hu2 [Hcv2 Hq2]]].
    pose proof (e_typing_supply_grows H0) as Hg2.
    pose proof (ftvar_ptyp_to_pskl A) as HeA.
    destruct (IHe_typing2 Hu2
                ltac:(clear - Hcov Hcv2 Hq2 Hg1 Hg2 HeA; simpl in *; fsetdec))
      as [Ha3 [Hu3 [Hcv3 Hq3]]].
    pose proof (e_typing_supply_grows H1) as Hg3.
    repeat split.
    + eapply a_typing__app; eassumption.
    + exact Hu3.
    + exact Hcv3.
    + simpl in Hq2. clear - Hq2 Hg3. fsetdec.
Qed.

(** ⭐ THE ENTRY SUPPLY, NAMED.  Every entry-point statement — the two
    soundness corollaries, the completeness twin, decidability, and the
    certified entry point (prop_run_corollaries.v §1-§7) — is stated at
    THIS supply and no other: the atoms the inputs already mention, which
    is the least set that can cover them.  It is what [type.ml] starts its
    counter at, and naming it is what keeps those statements to a line.
    ⚙ A transparent [Definition], so a caller holding the spelled-out
    union still unifies. *)
Definition entry_supply (P0 : pskl) (e : exp) : supply :=
  ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e.

(** ⭐ AND AT THE ENTRY POINT THE PREMISES COST NOTHING.  A closed program is
    run at the empty context, and the driver CHOOSES the supply — so both
    conditions are [reflexivity], and the second encoding's type inference is
    [fresco/algo]'s, with no residue.  (prop_consis.v §6 makes the general
    argument; this is its instance at the top of the algorithm.) *)
Corollary e_typing_sound_init : forall m P0 e B S1 Θ1,
  {{ (entry_supply P0 e) ↝ S1 ⊨ nil ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  {{ nil ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}a.
Proof.
  intros * He.
  (* ⚙ [fsetdec] does not see through a [Definition] — unfold the name
     before the coverage obligation, which is then [reflexivity]-shaped. *)
  unfold entry_supply in He.
  destruct (e_typing_sound He ltac:(apply uniq_nil) ltac:(simpl; fsetdec))
    as [Ha _].
  exact Ha.
Qed.

(* ##################################################################### *)
(*  §3  EQUIVARIANCE — the SUPPLY-RESPECT and TRANSPOSITION halves        *)
(*                                                                       *)
(*  Equivariance of [e_typing], in the ∃-form the supply forces —         *)
(*  prop_pat.v §4's twin for the judgement above it.                      *)
(*                                                                       *)
(*  ⭐ WHY LEVEL 8 NEEDS IT.  The runner opens the four abs rows' TERM     *)
(*  binder and the two check-STEP rows' TYPE binder at [supply_fresh],    *)
(*  while a derivation opens at any atom fresh for the supply; the        *)
(*  induction's hypothesis is stated at the runner's inputs, so the       *)
(*  derivation is transposed onto them first.                            *)
(* ##################################################################### *)

Lemma e_typing_swap : forall a b S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢[ m ; (swap_pskl a b P0) ]
       (swap_exp a b e) ⦂ (swap_ptyp a b B) ⊣ (swap_aenv a b Θ1) }}e.
Proof.
  intros a b S0 m Θ0 P0 e B S1 Θ1 H; induction H; intros S0' Heq; simpl;
    try (rewrite ?swap_aenv_app in *;
         rewrite ?swap_pskl_ptyp_to_pskl in *;
         rewrite ?swap_ptyp_open in * ).

  - (* AT-Unit *)
    destruct (e_sub_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hd]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd.
    exists S1'. split; [ exact HS1 | apply e_typing__unit; exact Hd ].
  - (* AT-Var *)
    destruct (e_sub_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hd]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd.
    exists S1'. split; [ exact HS1 | ].
    apply e_typing__var with (A := swap_ptyp a b A);
      [ exact (swap_aenv_binds a b _ _ _ H) | exact Hd ].
  - (* AT-Anno *)
    destruct (IHe_typing _ Heq) as [S1' [HS1 Hd1]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd1.
    destruct (e_sub_swap (a := a) (b := b) H0 HS1) as [S2' [HS2 Hd2]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd2.
    exists S2'. split; [ exact HS2 | eapply e_typing__anno; eassumption ].
  - (* AT-Freeze *)
    destruct (IHe_typing _ Heq) as [S1' [HS1 Hd1]].
    destruct (e_consis_chk_swap (a := a) (b := b) H0 HS1)
      as [S2' [HS2 Hc']].
    rewrite ?swap_pskl_ptyp_to_pskl in Hc'.
    exists S2'. split; [ exact HS2 | ].
    eapply e_typing__freeze; [ exact Hd1 | exact Hc' ].
  - (* AT-Abs — the drawn TERM binder and the guess block ride the swap *)
    destruct (e_split_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hsp]].
    destruct (e_guess_mono_swap (a := a) (b := b) H1 HS1) as [S2' [HS2 Hg]].
    destruct (IHe_typing (add (swap_atom a b x) S2'))
      as [S3' [HS3 Hd]]; [ apply eq_swap_atoms_add; exact HS2 | ].
    exists S3'. split; [ exact HS3 | ].
    apply e_typing__abs with (x := swap_atom a b x) (S1 := S1') (S2 := S2')
      (Θ1 := swap_aenv a b Θ1) (Θ2 := swap_aenv a b Θ2)
      (P := swap_pskl a b P) (Q := swap_pskl a b Q)
      (αs := swap_aenv a b αs) (A := swap_ptyp a b A);
      [ assumption | exact Hsp | exact Hg | apply a_suffix_swap; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd. exact Hd.
  - (* AT-AbsAnno *)
    destruct (e_split_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hsp]].
    destruct (e_consis_chk_swap (a := a) (b := b) H1 HS1)
      as [S2' [HS2 Hc']].
    rewrite ?swap_pskl_ptyp_to_pskl in Hc'.
    destruct (IHe_typing (add (swap_atom a b x) S2'))
      as [S3' [HS3 Hd]]; [ apply eq_swap_atoms_add; exact HS2 | ].
    exists S3'. split; [ exact HS3 | ].
    apply e_typing__abs_anno with (x := swap_atom a b x) (S1 := S1')
      (S2 := S2') (Θ1 := swap_aenv a b Θ1) (Θ2 := swap_aenv a b Θ2)
      (P := swap_pskl a b P) (Q := swap_pskl a b Q)
      (A := swap_ptyp a b A);
      [ assumption | exact Hsp | exact Hc' | apply a_suffix_swap; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd. exact Hd.
  - (* AT-AbsCheck STEP — a TYPE binder, drawn from the supply *)
    destruct (IHe_typing (add (swap_atom a b α) S0'))
      as [S1' [HS1 Hd]]; [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_typing__abs_check_step with (α := swap_atom a b α)
      (Ξ := swap_aenv a b Ξ) (A0 := swap_ptyp a b A0);
      [ apply a_suffix_swap; assumption
      | rewrite <- swap_aenv_app; auto using swap_aenv_uniq
      | apply swap_block_ftv_filter; assumption
      | apply swap_ptyp_ftv_notin; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite ?swap_aenv_app in Hd. rewrite ?swap_ptyp_open in Hd. exact Hd.
  - (* AT-AbsCheck BASE *)
    destruct (e_split_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hsp]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hsp.
    destruct (IHe_typing (add (swap_atom a b x) S1'))
      as [S2' [HS2 Hd]]; [ apply eq_swap_atoms_add; exact HS1 | ].
    exists S2'. split; [ exact HS2 | ].
    apply e_typing__abs_check_base with (x := swap_atom a b x) (S1 := S1')
      (Θ1 := swap_aenv a b Θ1) (A0 := swap_ptyp a b A0)
      (A := swap_ptyp a b A) (B := swap_ptyp a b B) (Ξ := swap_aenv a b Ξ);
      [ exact Hsp | apply a_suffix_swap; assumption
      | rewrite <- swap_aenv_app; auto using swap_aenv_uniq
      | apply swap_block_ftv_filter; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd.
    rewrite ?swap_pskl_ptyp_to_pskl in Hd. exact Hd.
  - (* AT-AbsAnnoCheck STEP *)
    destruct (IHe_typing (add (swap_atom a b α) S0'))
      as [S1' [HS1 Hd]]; [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_typing__abs_anno_check_step with (α := swap_atom a b α)
      (Ξ := swap_aenv a b Ξ) (A0 := swap_ptyp a b A0);
      [ apply a_suffix_swap; assumption
      | rewrite <- swap_aenv_app; auto using swap_aenv_uniq
      | apply swap_block_ftv_filter; assumption
      | apply swap_ptyp_ftv_notin; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite ?swap_aenv_app in Hd. rewrite ?swap_ptyp_open in Hd. exact Hd.
  - (* AT-AbsAnnoCheck BASE *)
    destruct (e_split_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hsp]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hsp.
    destruct (e_consis_chk_swap (a := a) (b := b) H0 HS1)
      as [S2' [HS2 Hc']].
    rewrite ?swap_pskl_ptyp_to_pskl in Hc'.
    destruct (IHe_typing (add (swap_atom a b x) S2'))
      as [S3' [HS3 Hd]]; [ apply eq_swap_atoms_add; exact HS2 | ].
    exists S3'. split; [ exact HS3 | ].
    apply e_typing__abs_anno_check_base with (x := swap_atom a b x)
      (S1 := S1') (S2 := S2') (Θ1 := swap_aenv a b Θ1)
      (Θ2 := swap_aenv a b Θ2) (A0 := swap_ptyp a b A0)
      (A' := swap_ptyp a b A') (B := swap_ptyp a b B)
      (Ξ := swap_aenv a b Ξ);
      [ exact Hsp | exact Hc' | apply a_suffix_swap; assumption
      | rewrite <- swap_aenv_app; auto using swap_aenv_uniq
      | apply swap_block_ftv_filter; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd.
    rewrite ?swap_pskl_ptyp_to_pskl in Hd. exact Hd.
  - (* AT-App — the argument runs TWICE, the second time at the domain *)
    destruct (e_pat_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hp]].
    destruct (IHe_typing1 _ HS1) as [S2' [HS2 Hd1]].
    destruct (IHe_typing2 _ HS2) as [S3' [HS3 Hd2]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd2.
    exists S3'. split; [ exact HS3 | ].
    eapply e_typing__app; [ exact Hp | | exact Hd2 ].
    simpl in Hd1. exact Hd1.
Qed.

(** Supply equivalence is equivariance under the identity swap. *)
Lemma e_typing_supply_respect : forall S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\
    {{ S0' ↝ S1' ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e.
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_typing_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_ptyp_same in Hswap.
  setoid_rewrite swap_exp_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  exact Hswap.
Qed.
