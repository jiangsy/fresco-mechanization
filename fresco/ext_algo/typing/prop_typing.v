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

Lemma e_typing_sound : forall S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e
    ∪ ftvar_in_exp e [<=] S0 ->
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}a
  /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_ptyp B [<=] S1.
Proof.
  intros S0 m Θ0 P0 e B S1 Θ1 H; induction H; intros Hu Hcov.

  -
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H Hu
                  ltac:(clear - Hcov; simpl; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_typing__unit; exact Ha | exact Hu1 | exact Hcv1
                  | clear - Hq1 HAe; fsetdec ].

  -
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

  -
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

  -
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

  -
    simpl in Hcov.
    destruct (e_split_sound H0 Hu ltac:(clear - Hcov; fsetdec))
      as [Hsp [Hu1 [Hcv1 Hqs]]].
    pose proof (e_split_supply_grows H0) as Hgs.

    pose proof (e_guess_mono_supply_grows H1) as Hgg.
    pose proof (e_guess_mono_generated_in_supply H1) as Hbin.
    pose proof (e_guess_mono_generated_ftvar H1) as Hbftv.
    pose proof (e_guess_mono_ftv H1) as Hgftv.
    assert (Hga : a_guess_mono Θ1 P αs A)
      by (eapply e_guess_mono_sound;
          [ exact H1 | exact Hcv1 | clear - Hqs; fsetdec ]).
    assert (Huαs : uniq (αs ++ Θ1))
      by (eapply e_guess_mono_uniq_app; [ exact H1 | exact Hcv1 | exact Hu1 ]).

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
    destruct (drop_binder_facts Hub Hcvb) as (HxΞ & HxΘ2 & Hub' & Hcvb').
    repeat split.
    + apply a_typing__abs with (x := x) (Θ1 := Θ1) (P := P) (Q := Q) (αs := αs);
        try assumption.
      clear - Hxd HxΞ HxΘ2 Hcov H3 Hgs Hgg. env_simp. fsetdec.
    + exact Hub'.
    + exact Hcvb'.
    + pose proof (e_typing_supply_grows H4) as Hgb.
      simpl. clear - HAcov Hqb Hgb. fsetdec.

  -
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
    destruct (drop_binder_facts Hub Hcvb) as (HxΞ & HxΘ3 & Hub' & Hcvb').
    repeat split.
    + apply a_typing__abs_anno with (x := x) (Θ1 := Θ1) (Θ2 := Θ2)
                                    (P := P) (Q := Q);
        try assumption; [ exists Qc; exact Hca | ].
      clear - Hxd HxΞ HxΘ3 Hcov H3 Hgs Hgc. env_simp. fsetdec.
    + exact Hub'.
    + exact Hcvb'.
    + pose proof (e_typing_supply_grows H4) as Hgb.
      simpl. clear - Hqb Hcov Hgs Hgc Hgb HAe. fsetdec.

  -
    pose proof (cover_open_tvar α Hcov) as Hcov'.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
    assert (Hαd : α `notin` dom Θ0) by (clear - Hd0 Hcov H3; fsetdec).
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0))
      by (clear - Hu Hαd; solve_uniq).
    destruct (IHe_typing Hu' Hcov') as [Ha [Hub [Hcvb Hqb]]].
    destruct (drop_binder_facts Hub Hcvb) as (HαΞ & HαΘ1 & Hub' & Hcvb').
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A (ptyp_var_f α)) as Hlo.
    repeat split.
    + apply a_typing__abs_check_step with (α := α) (Ξ := Ξ);
        try assumption.
      pose proof (ftvar_ptyp_to_pskl (ptyp_all A0)) as He2.
      simpl in He2, Hcov.
      clear - Hαd HαΞ HαΘ1 H2 H3 Hcov He2.
      simpl ftvar_in_exp. env_simp. fsetdec.
    + clear - Hub'; solve_uniq.
    + clear - Hcvb'. env_simp. fsetdec.
    + simpl. clear - Hqb Hlo. fsetdec.

  -
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
    destruct (drop_binder_facts Hub Hcvb) as (HxΞ & HxΘ2 & Hub' & Hcvb').
    repeat split.
    + apply a_typing__abs_check_base with (x := x) (Θ1 := Θ1) (B := B)
                                          (Ξ := Ξ);
        try assumption.
      clear - Hxd HxΞ HxΘ2 Hcov H3 Hgs. env_simp. fsetdec.
    + clear - Hub'; solve_uniq.
    + clear - Hcvb'. env_simp. fsetdec.
    + pose proof (e_typing_supply_grows H4) as Hgb.
      simpl. clear - Hqs Hqb Hgb HeA. fsetdec.

  -
    pose proof (cover_open_tvar α Hcov) as Hcov'.
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
    assert (Hαd : α `notin` dom Θ0) by (clear - Hd0 Hcov H3; fsetdec).
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0))
      by (clear - Hu Hαd; solve_uniq).
    destruct (IHe_typing Hu' Hcov') as [Ha [Hub [Hcvb Hqb]]].
    destruct (drop_binder_facts Hub Hcvb) as (HαΞ & HαΘ1 & Hub' & Hcvb').
    pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower A (ptyp_var_f α)) as Hlo.
    repeat split.
    + apply a_typing__abs_anno_check_step with (α := α) (Ξ := Ξ);
        try assumption.
      pose proof (ftvar_ptyp_to_pskl (ptyp_all A0)) as He2.
      simpl in He2, Hcov.
      clear - Hαd HαΞ HαΘ1 H2 H3 Hcov He2.
      simpl ftvar_in_exp. env_simp. fsetdec.
    + clear - Hub'; solve_uniq.
    + clear - Hcvb'. env_simp. fsetdec.
    + simpl. clear - Hqb Hlo. fsetdec.

  -
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
    destruct (drop_binder_facts Hub Hcvb) as (HxΞ & HxΘ3 & Hub' & Hcvb').
    repeat split.
    + apply a_typing__abs_anno_check_base with (x := x) (Θ1 := Θ1) (Θ2 := Θ2)
                                               (B := B) (Ξ := Ξ);
        try assumption; [ exists Qc; exact Hca | ].
      clear - Hxd HxΞ HxΘ3 Hcov H4 Hgs Hgc. env_simp. fsetdec.
    + clear - Hub'; solve_uniq.
    + clear - Hcvb'. env_simp. fsetdec.
    + pose proof (e_typing_supply_grows H5) as Hgb.
      simpl. clear - Hqs Hqb Hgb Hgc HeA'. fsetdec.

  -
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

Definition entry_supply (P0 : pskl) (e : exp) : supply :=
  ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e.

Corollary e_typing_sound_init : forall m P0 e B S1 Θ1,
  {{ (entry_supply P0 e) ↝ S1 ⊨ nil ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  {{ nil ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}a.
Proof.
  intros * He.
  unfold entry_supply in He.
  destruct (e_typing_sound He ltac:(apply uniq_nil) ltac:(simpl; fsetdec))
    as [Ha _].
  exact Ha.
Qed.

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

  -
    destruct (e_sub_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hd]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd.
    exists S1'. split; [ exact HS1 | apply e_typing__unit; exact Hd ].
  -
    destruct (e_sub_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hd]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd.
    exists S1'. split; [ exact HS1 | ].
    apply e_typing__var with (A := swap_ptyp a b A);
      [ exact (swap_aenv_binds a b _ _ _ H) | exact Hd ].
  -
    destruct (IHe_typing _ Heq) as [S1' [HS1 Hd1]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd1.
    destruct (e_sub_swap (a := a) (b := b) H0 HS1) as [S2' [HS2 Hd2]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd2.
    exists S2'. split; [ exact HS2 | eapply e_typing__anno; eassumption ].
  -
    destruct (IHe_typing _ Heq) as [S1' [HS1 Hd1]].
    destruct (e_consis_chk_swap (a := a) (b := b) H0 HS1)
      as [S2' [HS2 Hc']].
    rewrite ?swap_pskl_ptyp_to_pskl in Hc'.
    exists S2'. split; [ exact HS2 | ].
    eapply e_typing__freeze; [ exact Hd1 | exact Hc' ].
  -
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
  -
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
  -
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
  -
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
  -
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
  -
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
  -
    destruct (e_pat_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hp]].
    destruct (IHe_typing1 _ HS1) as [S2' [HS2 Hd1]].
    destruct (IHe_typing2 _ HS2) as [S3' [HS3 Hd2]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd2.
    exists S3'. split; [ exact HS3 | ].
    eapply e_typing__app; [ exact Hp | | exact Hd2 ].
    simpl in Hd1. exact Hd1.
Qed.

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
