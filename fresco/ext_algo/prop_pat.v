(** ext_algo — the supply invariants of SPLITTING and SKELETON INFERENCE,
    and their bridges.  (M4, first half.)

    §1  supply growth
    §2  the [e_split] bridge
    §3  ⭐ THE [e_pat] BRIDGE — and the four binder rows' side condition
        collapses to [x ∉ S1]

    ⚙ FOUR CONJUNCTS IN EACH MOTIVE, and here they really are mutually
    needed — unlike prop_consis.v §7, which could be a separate pass.
    [AP-App] runs the FUNCTION at the ARGUMENT's inferred skeleton, so its
    second premise's coverage is a statement about the first premise's
    output [Q]; and the coverage of the CONTEXT is needed at the same point.
    Neither can be established without the other, so both ride with the
    bridge and with [uniq].

    ⚠️ THE COVERAGE HYPOTHESIS NAMES THE SUBJECT'S TERM VARIABLES.  The
    binder rows draw [x] from the supply, so [x ∉ fvar_in_exp e] is exactly
    [fvar_in_exp e [<=] S1].  It costs nothing at the entry point: a
    well-formed subject's free term variables are bound in [Θ0], and
    [dom Θ0 [<=] ftvar_in_aenv Θ0] already. *)

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
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.prop_guess.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.prop_consis.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.prop_extract.
Require Import src.fresco.ext_algo.def_sub.
Require Import src.fresco.ext_algo.prop_sub.
Require Import src.fresco.ext_algo.def_pat.

Set Implicit Arguments.

Open Scope fresco_e_scope.

(** Every binding's PAYLOAD is part of what the context mentions.  ⚙ The
    general form of [ftvar_in_aenv_binds_def] (algo/prop_basic.v), which
    covers only flexible definitions; the two Var rows need it at [x : A]
    and [x : P]. *)
Lemma ftvar_in_aenv_binds_ftv : forall Θ x b,
  binds x b Θ -> ftvar_in_abind b [<=] ftvar_in_aenv Θ.
Proof.
  induction Θ as [ | [y bd] Θ' IH ]; intros x b Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [ [ Heq Hbd ] | Hb' ].
  - subst bd. simpl. fsetdec.
  - pose proof (IH _ _ Hb') as Hsub. simpl. fsetdec.
Qed.

(* ===================================================================== *)
(*  §1  The supply only grows                                             *)
(* ===================================================================== *)

Lemma e_split_supply_grows : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e -> S0 [<=] S1.
Proof.
  intros * H; destruct H as [ | | S0 S1 Θ0 Θ1 α β α1 Q Hβ Hα1 Hc ];
    [ fsetdec | fsetdec | ].
  pose proof (e_consis_supply_grows Hc). fsetdec.
Qed.

Lemma e_pat_supply_grows : forall S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e -> S0 [<=] S1.
Proof.
  intros * H; induction H;
    (* the leaf rows are a subtyping run; the two Anno-ish rows also cross a
       consistency run; the binder rows cross a split, and their body runs at
       [add x _], so the IH is one [add] too strong *)
    try (match goal with
         | Hs : e_sub _ _ _ _ _ _ _ _ _ |- _ =>
             pose proof (e_sub_supply_grows Hs)
         end);
    try (match goal with
         | Hsp : e_split _ _ _ _ _ _ _ |- _ =>
             pose proof (e_split_supply_grows Hsp)
         end);
    try (match goal with
         | Hc : e_consis_chk _ _ _ _ _ _ |- _ =>
             destruct Hc as [? Hc]; pose proof (e_consis_supply_grows Hc)
         end);
    fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  THE [e_split] BRIDGE                                              *)
(*                                                                        *)
(*  Four conjuncts, because [e_pat]'s and [e_typing]'s binder rows run the *)
(*  BODY at the split's outputs: they need the output context covered      *)
(*  ([x ∉ dom Θ1] comes from there) and BOTH output skeletons covered      *)
(*  ([P] goes into the context as the binder's payload, [Q] becomes the    *)
(*  body's input skeleton).                                               *)
(* ===================================================================== *)

Lemma e_split_sound : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0 ->
  {{ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}a /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1
  /\ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S1.
Proof.
  intros * H; destruct H as [ S Θ0 P Q | S Θ0
                            | S0 S1 Θ0 Θ1 α β α1 Q Hβ Hα1 Hc ];
    intros Hu Hcov.
  - (* arrow — both halves are parts of the INPUT skeleton *)
    repeat split; [ apply a_split__arrow | assumption
                  | clear - Hcov; fsetdec | clear - Hcov; simpl in *; fsetdec ].
  - (* ghost *)
    repeat split; [ apply a_split__ghost | assumption
                  | clear - Hcov; fsetdec | simpl; fsetdec ].
  - (* ⭐ flexible — the two invented flexibles are drawn from the supply in
       SEQUENCE, so [fresco/algo]'s two side conditions and the [α1 <> β] they
       imply are all consequences *)
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdc.
    assert (Hne : α1 <> β) by (intro Heq; subst; clear - Hα1; fsetdec).
    assert (Hβd : β `notin` dom Θ0) by (clear - Hdc Hcov Hβ; fsetdec).
    assert (Hα1d : α1 `notin` dom Θ0) by (clear - Hdc Hcov Hα1; fsetdec).
    assert (HαS : α `in` S0) by (clear - Hcov; simpl in *; fsetdec).
    assert (Hu' : uniq ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0))
      by (clear - Hu Hβd Hα1d Hne; simpl_env in *; solve_uniq).
    assert (Hcov' : ftvar_in_aenv
                      ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0)
                    ∪ ftvar_in_pskl (pskl_arrow (pskl_var_f β) (pskl_var_f α1))
                    ∪ ftvar_in_pskl (pskl_var_f α) ∪ empty ∪ empty
                    [<=] add α1 (add β S0))
      by (clear - Hcov HαS; env_simp; simpl in *; fsetdec).
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc Hu' Hcov') as [Hca [Hu1 Hcv1]].
    pose proof (e_consis_supply_grows Hc) as Hgrow.
    repeat split.
    + apply a_split__flex with (Q := Q);
        [ clear - Hcov Hβ; fsetdec | clear - Hcov Hα1; fsetdec | exact Hca ].
    + exact Hu1.
    + exact Hcv1.
    + (* both outputs are the drawn flexibles, and growth put them in [S1] *)
      clear - Hgrow. simpl. fsetdec.
Qed.

(* ===================================================================== *)
(*  §3  ⭐ THE [e_pat] BRIDGE                                              *)
(*                                                                        *)
(*  ⭐⭐ THE FOUR BINDER ROWS ARE WHERE THE SECOND ENCODING PAYS.  Since     *)
(*  2026-08-13 [fresco/algo]'s own rows are exists-fresh too, so the two    *)
(*  rule sets differ ONLY in the threading and the bridge is structural.   *)
(*  Each row's side condition                                             *)
(*                                                                        *)
(*      x ∉ dom (Ξ ++ Θ1) ∪ dom Θ2 ∪ fvar_in_exp e                        *)
(*                                                                        *)
(*  is discharged in three pieces, none of them a premise here:            *)
(*    [x ∉ dom Θ1]        coverage — [ftvar_in_aenv Θ1 [<=] S1] and        *)
(*                        [dom [<=] ftvar_in_aenv]                         *)
(*    [x ∉ fvar_in_exp e] coverage, at the SUBJECT                         *)
(*    [x ∉ dom Ξ ∪ dom Θ2] UNIQUENESS of the premise's output              *)
(*                        [Ξ ++ (x ~ b) ++ Θ2] — the motive's own conjunct *)
(* ===================================================================== *)

Lemma e_pat_sound : forall S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e
    ∪ ftvar_in_exp e [<=] S0 ->
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}a
  /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_pskl Q [<=] S1.
Proof.
  intros S0 m Θ0 P0 e Q S1 Θ1 H; induction H; intros Hu Hcov.

  - (* AP-Unit *)
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H Hu
                  ltac:(clear - Hcov; simpl; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_pat__unit | | | ]; assumption.

  - (* AP-Var (type-bound) — the payload's variables are the context's *)
    assert (HA : ftvar_in_pskl (ptyp_to_pskl A) [<=] S0).
    { rewrite ftvar_ptyp_to_pskl.
      pose proof (@ftvar_in_aenv_binds_ftv _ _ _ H) as Hb. simpl in Hb.
      clear - Hb Hcov. fsetdec. }
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H0 Hu
                  ltac:(clear - Hcov HA; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ eapply a_pat__var; eassumption | | | ]; assumption.

  - (* AP-Var (skeleton-bound) *)
    assert (HP : ftvar_in_pskl P [<=] S0).
    { pose proof (@ftvar_in_aenv_binds_ftv _ _ _ H) as Hb. simpl in Hb.
      clear - Hb Hcov. fsetdec. }
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H0 Hu
                  ltac:(clear - Hcov HP; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ eapply a_pat__var_skl; eassumption | | | ]; assumption.

  - (* AP-Anno — the annotation is part of the SUBJECT *)
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H Hu
                  ltac:(clear - Hcov; simpl in *;
                        rewrite ftvar_ptyp_to_pskl; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_pat__anno | | | ]; assumption.

  - (* AP-Freeze *)
    destruct (IHe_pat Hu ltac:(clear - Hcov; simpl in *; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_pat__freeze | | | ]; assumption.

  - (* ⭐ AP-Abs *)
    simpl in Hcov.
    destruct (e_split_sound H0 Hu ltac:(clear - Hcov; fsetdec))
      as [Hsp [Hu1 [Hcv1 Hqs]]].
    pose proof (e_split_supply_grows H0) as Hgs.
    pose proof (dom_subset_ftvar_in_aenv Θ1) as Hd1.
    assert (Hxd : x `notin` dom Θ1) by (clear - Hd1 Hcv1 H2; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_skl P) ++ Θ1))
      by (clear - Hu1 Hxd; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((x ~ abind_var_skl P) ++ Θ1)
                      ∪ ftvar_in_pskl Q0
                      ∪ fvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
                      [<=] add x S1).
    { pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hv.
      pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Ht.
      simpl in Hv, Ht.
      clear - Hv Ht Hcov Hcv1 Hqs Hgs. env_simp. fsetdec. }
    destruct (IHe_pat Hu' Hcov') as [Ha [Hub [Hcvb Hqb]]].
    (* the two OUTPUT halves of the side condition come from uniqueness *)
    assert (HxΞ : x `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HxΘ2 : x `notin` dom Θ2)
      by (clear - Hub; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_pat__abs with (x := x) (Θ1 := Θ1) (Q0 := Q0);
        try assumption.
      clear - Hxd HxΞ HxΘ2 Hcov H2 Hgs. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + pose proof (e_pat_supply_grows H3) as Hgb.
      simpl. clear - Hqs Hqb Hgb. fsetdec.

  - (* ⭐ AP-AbsAnno *)
    simpl in Hcov.
    destruct (e_split_sound H0 Hu ltac:(clear - Hcov; fsetdec))
      as [Hsp [Hu1 [Hcv1 Hqs]]].
    pose proof (e_split_supply_grows H0) as Hgs.
    destruct H1 as [Qc Hc].
    pose proof (e_consis_supply_grows Hc) as Hgc.
    assert (HA : ftvar_in_pskl (ptyp_to_pskl A) [<=] S1).
    { rewrite ftvar_ptyp_to_pskl. clear - Hcov Hgs. fsetdec. }
    pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hc Hu1 ltac:(clear - Hcv1 HA Hqs; fsetdec))
      as [Hca [Hu2 Hcv2]].
    pose proof (dom_subset_ftvar_in_aenv Θ2) as Hd2.
    assert (Hxd : x `notin` dom Θ2) by (clear - Hd2 Hcv2 H3; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_typ A) ++ Θ2))
      by (clear - Hu2 Hxd; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((x ~ abind_var_typ A) ++ Θ2)
                      ∪ ftvar_in_pskl Q0
                      ∪ fvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
                      [<=] add x S2).
    { pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hv.
      pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Ht.
      pose proof (ftvar_ptyp_to_pskl A) as HAe.
      simpl in Hv, Ht.
      clear - Hv Ht HAe Hcov Hcv2 Hqs Hgs Hgc. env_simp. fsetdec. }
    destruct (IHe_pat Hu' Hcov') as [Ha [Hub [Hcvb Hqb]]].
    assert (HxΞ : x `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HxΘ3 : x `notin` dom Θ3)
      by (clear - Hub; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_pat__abs_anno with (x := x) (Θ1 := Θ1) (Θ2 := Θ2)
                                 (P := P) (Q0 := Q0);
        try assumption; [ exists Qc; exact Hca | ].
      clear - Hxd HxΞ HxΘ3 Hcov H3 Hgs Hgc. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + pose proof (e_pat_supply_grows H4) as Hgb.
      simpl. rewrite ftvar_ptyp_to_pskl.
      clear - Hqb Hcov Hgs Hgc Hgb. fsetdec.

  - (* AP-AbsCheck *)
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
    assert (Hxd : x `notin` dom Θ0) by (clear - Hd0 Hcov H0; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_skl pskl_ghost) ++ Θ0))
      by (clear - Hu Hxd; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((x ~ abind_var_skl pskl_ghost) ++ Θ0)
                      ∪ ftvar_in_pskl pskl_ghost
                      ∪ fvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
                      [<=] add x S0).
    { pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hv.
      pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Ht.
      simpl in Hv, Ht. clear - Hv Ht Hcov. env_simp. fsetdec. }
    destruct (IHe_pat Hu' Hcov') as [Ha [Hub [Hcvb Hqb]]].
    assert (HxΞ : x `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HxΘ1 : x `notin` dom Θ1)
      by (clear - Hub; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_pat__abs_check with (x := x); try assumption.
      clear - Hxd HxΞ HxΘ1 Hcov H0. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + simpl. clear - Hqb. fsetdec.

  - (* AP-AbsAnnoCheck *)
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
    assert (Hxd : x `notin` dom Θ0) by (clear - Hd0 Hcov H0; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_typ A) ++ Θ0))
      by (clear - Hu Hxd; solve_uniq).
    assert (Hcov' : ftvar_in_aenv ((x ~ abind_var_typ A) ++ Θ0)
                      ∪ ftvar_in_pskl pskl_ghost
                      ∪ fvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
                      ∪ ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
                      [<=] add x S0).
    { pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hv.
      pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Ht.
      simpl in Hv, Ht. clear - Hv Ht Hcov. env_simp. fsetdec. }
    destruct (IHe_pat Hu' Hcov') as [Ha [Hub [Hcvb Hqb]]].
    assert (HxΞ : x `notin` dom Ξ)
      by (clear - Hub; simpl_env in *; solve_uniq).
    assert (HxΘ1 : x `notin` dom Θ1)
      by (clear - Hub; simpl_env in *; solve_uniq).
    repeat split.
    + apply a_pat__abs_anno_check with (x := x); try assumption.
      clear - Hxd HxΞ HxΘ1 Hcov H0. env_simp. fsetdec.
    + clear - Hub; simpl_env in *; solve_uniq.
    + clear - Hcvb. env_simp. fsetdec.
    + pose proof (e_pat_supply_grows H1) as Hgb.
      pose proof (ftvar_ptyp_to_pskl A) as HAe.
      simpl. clear - Hqb Hcov Hgb HAe. fsetdec.

  - (* ⭐ AP-App — the row that forces the output-skeleton conjunct: the
       FUNCTION runs at the ARGUMENT's inferred skeleton [P0] *)
    simpl in Hcov.
    destruct (IHe_pat1 Hu ltac:(clear - Hcov; simpl; fsetdec))
      as [Ha1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_pat_supply_grows H) as Hg1.
    destruct (IHe_pat2 Hu1
                ltac:(clear - Hcov Hcv1 Hq1 Hg1; simpl; fsetdec))
      as [Ha2 [Hu2 [Hcv2 Hq2]]].
    repeat split.
    + eapply a_pat__app; eassumption.
    + exact Hu2.
    + exact Hcv2.
    + clear - Hq2. simpl in Hq2. fsetdec.
Qed.

(* ##################################################################### *)
(*  §4  EQUIVARIANCE — the SUPPLY-RESPECT and TRANSPOSITION halves        *)
(*                                                                       *)
(*  Equivariance of [e_split] / [e_pat], in the ∃-form the supply forces  *)
(*  (prop_sub.v §5's reason, one level up).                               *)
(*                                                                       *)
(*  ⭐ WHY LEVELS 7/8 NEED IT.  The runner opens EVERY binder — the term  *)
(*  binder of the four abs rows included — at [supply_fresh], while a     *)
(*  derivation opens at any atom fresh for the supply.  So a derivation   *)
(*  must be moved onto the runner's rails before an induction hypothesis  *)
(*  stated at the runner's inputs can apply, and a transposition is the   *)
(*  move (USER DIRECTIVE, swap kit).                                     *)
(*                                                                       *)
(*  ⚠️ THE SUBJECT RIDES ALONG.  These rows bind a TERM variable, so the   *)
(*  transposition acts on the term too ([swap_exp], algo/prop_swap.v      *)
(*  §16.1) — a statement holding the term fixed would need [a <> x] and   *)
(*  [b <> x] for a binder the ROW chooses.  Read §16's header for why     *)
(*  this is NOT a resurrection of the retired [a_pat_rename_tm].          *)
(* ##################################################################### *)

(** SUPPLY RESPECT.  A supply is a SET, so a caller that assembled one by a
    different route holds an [=]-variant rather than the term — and the
    judgement takes it as an INDEX, which no [rewrite] can move under.  This
    is what the completeness level's chain needs at length zero. *)
Lemma e_split_supply_respect : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ {{ S0' ↝ S1' ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e.
Proof.
  intros S0 Θ0 P0 P Q S1 Θ1 H; destruct H as
    [ S Θ0 P Q | S Θ0 | S0 S1 Θ0 Θ1 α β α1 Q Hβ Hα1 Hc ]; intros S0' Heq.
  - exists S0'. split; [ exact Heq | apply e_split__arrow ].
  - exists S0'. split; [ exact Heq | apply e_split__ghost ].
  - destruct (e_consis_supply_respect Hc (S0' := add α1 (add β S0')))
      as [S1' [HS1 Hc']];
      [ rewrite Heq; reflexivity | ].
    exists S1'. split; [ exact HS1 | ].
    eapply e_split__flex; [ rewrite Heq; exact Hβ | rewrite Heq; exact Hα1
                          | exact Hc' ].
Qed.

Lemma e_pat_supply_respect : forall S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\
    {{ S0' ↝ S1' ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e.
Proof.
  intros S0 m Θ0 P0 e Q S1 Θ1 H; induction H; intros S0' Heq.

  - (* AP-Unit *)
    destruct (e_sub_supply_respect H Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_pat__unit; exact Hd ].
  - (* AP-Var, type payload *)
    destruct (e_sub_supply_respect H0 Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | eapply e_pat__var; eassumption ].
  - (* AP-Var, skeleton payload *)
    destruct (e_sub_supply_respect H0 Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | eapply e_pat__var_skl; eassumption ].
  - (* AP-Anno *)
    destruct (e_sub_supply_respect H Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_pat__anno; exact Hd ].
  - (* AP-Freeze *)
    destruct (IHe_pat _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_pat__freeze; exact Hd ].
  - (* AP-Abs *)
    destruct (e_split_supply_respect H0 Heq) as [S1' [HS1 Hsp]].
    destruct (IHe_pat (add x S1') ltac:(rewrite HS1; reflexivity))
      as [S2' [HS2 Hd]].
    exists S2'. split; [ exact HS2 | ].
    apply e_pat__abs with (x := x) (S1 := S1') (Θ1 := Θ1) (P := P)
      (Q0 := Q0);
      [ assumption | exact Hsp | assumption | rewrite HS1; assumption
      | exact Hd ].
  - (* AP-AbsAnno *)
    destruct (e_split_supply_respect H0 Heq) as [S1' [HS1 Hsp]].
    destruct H1 as [Qc Hc].
    destruct (e_consis_supply_respect Hc HS1) as [S2' [HS2 Hc']].
    destruct (IHe_pat (add x S2') ltac:(rewrite HS2; reflexivity))
      as [S3' [HS3 Hd]].
    exists S3'. split; [ exact HS3 | ].
    apply e_pat__abs_anno with (x := x) (S1 := S1') (S2 := S2')
      (Θ1 := Θ1) (Θ2 := Θ2) (P := P) (Q0 := Q0) (A := A);
      [ assumption | exact Hsp | exists Qc; exact Hc' | assumption
      | rewrite HS2; assumption | exact Hd ].
  - (* AP-AbsCheck *)
    destruct (IHe_pat (add x S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    eapply e_pat__abs_check; try eassumption; rewrite Heq; assumption.
  - (* AP-AbsAnnoCheck *)
    destruct (IHe_pat (add x S0') ltac:(rewrite Heq; reflexivity))
      as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    eapply e_pat__abs_anno_check; try eassumption; rewrite Heq; assumption.
  - (* AP-App *)
    destruct (IHe_pat1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IHe_pat2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | eapply e_pat__app; eassumption ].
Qed.

(** THE TRANSPOSITION.  ⚙ Every [Δ-drop] premise the a-side has to
    re-establish under the swap is GONE here (prop_sub.v §5's note); what
    replaces it is one [swap_notin_eq] per drawn atom and one
    [eq_swap_atoms_add] per premise supply. *)
Lemma e_split_swap : forall a b S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊲ (swap_pskl a b P0)
       ▹ (swap_pskl a b P) ⇢ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1) }}e.
Proof.
  intros a b S0 Θ0 P0 P Q S1 Θ1 H; destruct H as
    [ S Θ0 P Q | S Θ0 | S0 S1 Θ0 Θ1 α β α1 Q Hβ Hα1 Hc ]; intros S0' Heq;
    simpl.
  - exists S0'. split; [ exact Heq | apply e_split__arrow ].
  - exists S0'. split; [ exact Heq | apply e_split__ghost ].
  - (* the invented pair rides the swap, drawn in the same sequence *)
    destruct (e_consis_swap (a := a) (b := b) Hc (Δ1' := empty) (Δ2' := empty)
                (S0' := add (swap_atom a b α1) (add (swap_atom a b β) S0')))
      as [S1' [HS1 Hc']];
      [ apply empty_eq_swap_atoms_empty | apply empty_eq_swap_atoms_empty
      | apply eq_swap_atoms_add; apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    apply e_split__flex with (β := swap_atom a b β)
      (α1 := swap_atom a b α1) (Q := swap_pskl a b Q).
    + eapply swap_notin_eq; eassumption.
    + eapply swap_notin_eq;
        [ apply eq_swap_atoms_add; exact Heq | exact Hα1 ].
    + simpl in Hc'. exact Hc'.
Qed.

Lemma e_pat_swap : forall a b S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swap_atoms a b S0 ->
  exists S1', S1' [=] swap_atoms a b S1 /\
    {{ S0' ↝ S1' ⊨ (swap_aenv a b Θ0) ⊢ˢ[ m ; (swap_pskl a b P0) ]
       (swap_exp a b e) ⦂ (swap_pskl a b Q) ⊣ (swap_aenv a b Θ1) }}e.
Proof.
  intros a b S0 m Θ0 P0 e Q S1 Θ1 H; induction H; intros S0' Heq; simpl;
    try (rewrite ?swap_aenv_app in *; rewrite ?swap_pskl_ptyp_to_pskl in * ).

  - (* AP-Unit *)
    destruct (e_sub_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_pat__unit; exact Hd ].
  - (* AP-Var, type payload *)
    destruct (e_sub_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hd]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd.
    exists S1'. split; [ exact HS1 | ].
    apply e_pat__var with (A := swap_ptyp a b A);
      [ exact (swap_aenv_binds a b _ _ _ H) | exact Hd ].
  - (* AP-Var, skeleton payload *)
    destruct (e_sub_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_pat__var_skl with (P := swap_pskl a b P);
      [ exact (swap_aenv_binds a b _ _ _ H) | exact Hd ].
  - (* AP-Anno *)
    destruct (e_sub_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hd]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd.
    exists S1'. split; [ exact HS1 | apply e_pat__anno; exact Hd ].
  - (* AP-Freeze *)
    destruct (IHe_pat _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_pat__freeze; exact Hd ].
  - (* AP-Abs — the drawn TERM binder rides the swap *)
    destruct (e_split_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hsp]].
    destruct (IHe_pat (add (swap_atom a b x) S1'))
      as [S2' [HS2 Hd]]; [ apply eq_swap_atoms_add; exact HS1 | ].
    exists S2'. split; [ exact HS2 | ].
    eapply e_pat__abs with (x := swap_atom a b x)
      (Θ1 := swap_aenv a b Θ1) (P := swap_pskl a b P)
      (Q0 := swap_pskl a b Q0);
      [ assumption | exact Hsp | apply a_suffix_swap; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd. exact Hd.
  - (* AP-AbsAnno *)
    destruct (e_split_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hsp]].
    destruct (e_consis_chk_swap (a := a) (b := b) H1 HS1) as [S2' [HS2 Hc']].
    rewrite ?swap_pskl_ptyp_to_pskl in Hc'.
    destruct (IHe_pat (add (swap_atom a b x) S2'))
      as [S3' [HS3 Hd]]; [ apply eq_swap_atoms_add; exact HS2 | ].
    exists S3'. split; [ exact HS3 | ].
    eapply e_pat__abs_anno with (x := swap_atom a b x)
      (Θ1 := swap_aenv a b Θ1) (Θ2 := swap_aenv a b Θ2)
      (P := swap_pskl a b P) (Q0 := swap_pskl a b Q0);
      [ assumption | exact Hsp | exact Hc' | apply a_suffix_swap; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd. exact Hd.
  - (* AP-AbsCheck *)
    destruct (IHe_pat (add (swap_atom a b x) S0'))
      as [S1' [HS1 Hd]]; [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    eapply e_pat__abs_check with (x := swap_atom a b x)
      (Θ1 := swap_aenv a b Θ1);
      [ apply a_suffix_swap; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd. exact Hd.
  - (* AP-AbsAnnoCheck *)
    destruct (IHe_pat (add (swap_atom a b x) S0'))
      as [S1' [HS1 Hd]]; [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    eapply e_pat__abs_anno_check with (x := swap_atom a b x)
      (Θ1 := swap_aenv a b Θ1) (A := swap_ptyp a b A);
      [ apply a_suffix_swap; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd. exact Hd.
  - (* AP-App *)
    destruct (IHe_pat1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IHe_pat2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | eapply e_pat__app; eassumption ].
Qed.

(** A supply atom in the split output context was already in its input. *)
Lemma e_split_dom_upper : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  dom Θ1 [<=] dom Θ0 ∪ (S1 ∖ S0).
Proof.
  intros S0 Θ0 P0 P Q S1 Θ1 H;
    destruct H as [ Sa Θa Pa Qa | Sa Θa
                  | Sa Sb Θa Θb α β α1 Qc Hβ Hα1 Hc ];
    try (clear; fsetdec).
  pose proof ((proj2 (proj2 e_assign_unify_consis_dom_upper))
                _ _ _ _ _ _ _ _ _ Hc) as Hd.
  pose proof ((proj2 (proj2 e_assign_unify_consis_supply_grows))
                _ _ _ _ _ _ _ _ _ Hc) as Hg.
  simpl_env in Hd. clear - Hd Hg Hβ Hα1. fsetdec.
Qed.

