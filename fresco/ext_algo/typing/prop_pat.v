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

Set Implicit Arguments.

Open Scope fresco_e_scope.

Lemma ftvar_in_aenv_binds_ftv : forall Θ x b,
  binds x b Θ -> ftvar_in_abind b [<=] ftvar_in_aenv Θ.
Proof.
  induction Θ as [ | [y bd] Θ' IH ]; intros x b Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [ [ Heq Hbd ] | Hb' ].
  - subst bd. simpl. fsetdec.
  - pose proof (IH _ _ Hb') as Hsub. simpl. fsetdec.
Qed.

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
  -
    repeat split; [ apply a_split__arrow | assumption
                  | clear - Hcov; fsetdec | clear - Hcov; simpl in *; fsetdec ].
  -
    repeat split; [ apply a_split__ghost | assumption
                  | clear - Hcov; fsetdec | simpl; fsetdec ].
  -
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
    +
      clear - Hgrow. simpl. fsetdec.
Qed.

Lemma cover_open_body_skl : forall (S : atoms) (Θ : aenv) P0 P e x,
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P
    ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S ->
  ftvar_in_aenv ((x ~ abind_var_skl P) ++ Θ) ∪ ftvar_in_pskl P0
    ∪ fvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
    ∪ ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) [<=] add x S.
Proof.
  intros * H.
  pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hfo.
  pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hto.
  simpl in *. fsetdec.
Qed.

Lemma cover_open_body_typ : forall (S : atoms) (Θ : aenv) P0 A e x,
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_ptyp A
    ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S ->
  ftvar_in_aenv ((x ~ abind_var_typ A) ++ Θ) ∪ ftvar_in_pskl P0
    ∪ fvar_in_exp (open_exp_wrt_exp e (exp_var_f x))
    ∪ ftvar_in_exp (open_exp_wrt_exp e (exp_var_f x)) [<=] add x S.
Proof.
  intros * H.
  pose proof (fvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hfo.
  pose proof (ftvar_in_exp_open_exp_wrt_exp_upper e (exp_var_f x)) as Hto.
  simpl in *. fsetdec.
Qed.

Lemma cover_open_tvar : forall (S : atoms) (Θ : aenv) A0 e α,
  ftvar_in_aenv Θ ∪ ftvar_in_pskl (ptyp_to_pskl (ptyp_all A0))
    ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S ->
  ftvar_in_aenv ((α ~ abind_tvar) ++ Θ)
    ∪ ftvar_in_pskl (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
    ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] add α S.
Proof.
  intros * H.
  pose proof (ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper A0 (ptyp_var_f α)) as Hup.
  pose proof (ftvar_ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α)))
    as He1.
  pose proof (ftvar_ptyp_to_pskl (ptyp_all A0)) as He2.
  simpl in *. fsetdec.
Qed.

Lemma drop_binder_facts {Ξ Θ : aenv} {x b} {S : atoms} :
  uniq (Ξ ++ (x ~ b) ++ Θ) -> ftvar_in_aenv (Ξ ++ (x ~ b) ++ Θ) [<=] S ->
  x `notin` dom Ξ /\ x `notin` dom Θ /\ uniq (Ξ ++ Θ)
  /\ ftvar_in_aenv (Ξ ++ Θ) [<=] S.
Proof.
  intros Hu Hcv. repeat split.
  - clear - Hu; simpl_env in *; solve_uniq.
  - clear - Hu; simpl_env in *; solve_uniq.
  - clear - Hu; simpl_env in *; solve_uniq.
  - clear - Hcv; env_simp; fsetdec.
Qed.

Arguments cover_open_body_skl {S Θ P0 P e} x _.
Arguments cover_open_body_typ {S Θ P0 A e} x _.
Arguments cover_open_tvar {S Θ A0 e} α _.

Lemma e_pat_sound : forall S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e
    ∪ ftvar_in_exp e [<=] S0 ->
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}a
  /\ uniq Θ1 /\ ftvar_in_aenv Θ1 [<=] S1 /\ ftvar_in_pskl Q [<=] S1.
Proof.
  intros S0 m Θ0 P0 e Q S1 Θ1 H; induction H; intros Hu Hcov.

  -
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H Hu
                  ltac:(clear - Hcov; simpl; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_pat__unit | | | ]; assumption.

  -
    assert (HA : ftvar_in_pskl (ptyp_to_pskl A) [<=] S0).
    { rewrite ftvar_ptyp_to_pskl.
      pose proof (@ftvar_in_aenv_binds_ftv _ _ _ H) as Hb. simpl in Hb.
      clear - Hb Hcov. fsetdec. }
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H0 Hu
                  ltac:(clear - Hcov HA; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ eapply a_pat__var; eassumption | | | ]; assumption.

  -
    assert (HP : ftvar_in_pskl P [<=] S0).
    { pose proof (@ftvar_in_aenv_binds_ftv _ _ _ H) as Hb. simpl in Hb.
      clear - Hb Hcov. fsetdec. }
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H0 Hu
                  ltac:(clear - Hcov HP; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ eapply a_pat__var_skl; eassumption | | | ]; assumption.

  -
    pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ H Hu
                  ltac:(clear - Hcov; simpl in *;
                        rewrite ftvar_ptyp_to_pskl; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_pat__anno | | | ]; assumption.

  -
    destruct (IHe_pat Hu ltac:(clear - Hcov; simpl in *; fsetdec))
      as [Ha [Hu1 [Hcv1 Hq1]]].
    repeat split; [ apply a_pat__freeze | | | ]; assumption.

  -
    simpl in Hcov.
    destruct (e_split_sound H0 Hu ltac:(clear - Hcov; fsetdec))
      as [Hsp [Hu1 [Hcv1 Hqs]]].
    pose proof (e_split_supply_grows H0) as Hgs.
    pose proof (dom_subset_ftvar_in_aenv Θ1) as Hd1.
    assert (Hxd : x `notin` dom Θ1) by (clear - Hd1 Hcv1 H2; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_skl P) ++ Θ1))
      by (clear - Hu1 Hxd; solve_uniq).
    assert (Hsc : ftvar_in_aenv Θ1 ∪ ftvar_in_pskl Q0
              ∪ ftvar_in_pskl P ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S1)
      by (clear - Hcov Hcv1 Hqs Hgs; env_simp; fsetdec).
    destruct (IHe_pat Hu' (cover_open_body_skl x Hsc))
      as [Ha [Hub [Hcvb Hqb]]].

    destruct (drop_binder_facts Hub Hcvb) as (HxΞ & HxΘ2 & Hub' & Hcvb').
    repeat split.
    + apply a_pat__abs with (x := x) (Θ1 := Θ1) (Q0 := Q0);
        try assumption.
      clear - Hxd HxΞ HxΘ2 Hcov H2 Hgs. env_simp. fsetdec.
    + exact Hub'.
    + exact Hcvb'.
    + pose proof (e_pat_supply_grows H3) as Hgb.
      simpl. clear - Hqs Hqb Hgb. fsetdec.

  -
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
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    assert (Hsc : ftvar_in_aenv Θ2 ∪ ftvar_in_pskl Q0
              ∪ ftvar_in_ptyp A ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S2)
      by (clear - HAe Hcov Hcv2 Hqs Hgs Hgc; env_simp; fsetdec).
    destruct (IHe_pat Hu' (cover_open_body_typ x Hsc))
      as [Ha [Hub [Hcvb Hqb]]].
    destruct (drop_binder_facts Hub Hcvb) as (HxΞ & HxΘ3 & Hub' & Hcvb').
    repeat split.
    + apply a_pat__abs_anno with (x := x) (Θ1 := Θ1) (Θ2 := Θ2)
                                 (P := P) (Q0 := Q0);
        try assumption; [ exists Qc; exact Hca | ].
      clear - Hxd HxΞ HxΘ3 Hcov H3 Hgs Hgc. env_simp. fsetdec.
    + exact Hub'.
    + exact Hcvb'.
    + pose proof (e_pat_supply_grows H4) as Hgb.
      simpl. rewrite ftvar_ptyp_to_pskl.
      clear - Hqb Hcov Hgs Hgc Hgb. fsetdec.

  -
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
    assert (Hxd : x `notin` dom Θ0) by (clear - Hd0 Hcov H0; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_skl pskl_ghost) ++ Θ0))
      by (clear - Hu Hxd; solve_uniq).
    assert (Hsc : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl pskl_ghost
              ∪ ftvar_in_pskl pskl_ghost ∪ fvar_in_exp e ∪ ftvar_in_exp e
              [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IHe_pat Hu' (cover_open_body_skl x Hsc))
      as [Ha [Hub [Hcvb Hqb]]].
    destruct (drop_binder_facts Hub Hcvb) as (HxΞ & HxΘ1 & Hub' & Hcvb').
    repeat split.
    + apply a_pat__abs_check with (x := x); try assumption.
      clear - Hxd HxΞ HxΘ1 Hcov H0. env_simp. fsetdec.
    + exact Hub'.
    + exact Hcvb'.
    + simpl. clear - Hqb. fsetdec.

  -
    simpl in Hcov.
    pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
    assert (Hxd : x `notin` dom Θ0) by (clear - Hd0 Hcov H0; fsetdec).
    assert (Hu' : uniq ((x ~ abind_var_typ A) ++ Θ0))
      by (clear - Hu Hxd; solve_uniq).
    assert (Hsc : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl pskl_ghost
              ∪ ftvar_in_ptyp A ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S0)
      by (clear - Hcov; env_simp; fsetdec).
    destruct (IHe_pat Hu' (cover_open_body_typ x Hsc))
      as [Ha [Hub [Hcvb Hqb]]].
    destruct (drop_binder_facts Hub Hcvb) as (HxΞ & HxΘ1 & Hub' & Hcvb').
    repeat split.
    + apply a_pat__abs_anno_check with (x := x); try assumption.
      clear - Hxd HxΞ HxΘ1 Hcov H0. env_simp. fsetdec.
    + exact Hub'.
    + exact Hcvb'.
    + pose proof (e_pat_supply_grows H1) as Hgb.
      pose proof (ftvar_ptyp_to_pskl A) as HAe.
      simpl. clear - Hqb Hcov Hgb HAe. fsetdec.

  -
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
  -
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

  -
    destruct (e_sub_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_pat__unit; exact Hd ].
  -
    destruct (e_sub_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hd]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd.
    exists S1'. split; [ exact HS1 | ].
    apply e_pat__var with (A := swap_ptyp a b A);
      [ exact (swap_aenv_binds a b _ _ _ H) | exact Hd ].
  -
    destruct (e_sub_swap (a := a) (b := b) H0 Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | ].
    apply e_pat__var_skl with (P := swap_pskl a b P);
      [ exact (swap_aenv_binds a b _ _ _ H) | exact Hd ].
  -
    destruct (e_sub_swap (a := a) (b := b) H Heq) as [S1' [HS1 Hd]].
    rewrite ?swap_pskl_ptyp_to_pskl in Hd.
    exists S1'. split; [ exact HS1 | apply e_pat__anno; exact Hd ].
  -
    destruct (IHe_pat _ Heq) as [S1' [HS1 Hd]].
    exists S1'. split; [ exact HS1 | apply e_pat__freeze; exact Hd ].
  -
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
  -
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
  -
    destruct (IHe_pat (add (swap_atom a b x) S0'))
      as [S1' [HS1 Hd]]; [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    eapply e_pat__abs_check with (x := swap_atom a b x)
      (Θ1 := swap_aenv a b Θ1);
      [ apply a_suffix_swap; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd. exact Hd.
  -
    destruct (IHe_pat (add (swap_atom a b x) S0'))
      as [S1' [HS1 Hd]]; [ apply eq_swap_atoms_add; exact Heq | ].
    exists S1'. split; [ exact HS1 | ].
    eapply e_pat__abs_anno_check with (x := swap_atom a b x)
      (Θ1 := swap_aenv a b Θ1) (A := swap_ptyp a b A);
      [ apply a_suffix_swap; assumption
      | eapply swap_notin_eq; eassumption | ].
    rewrite <- swap_exp_open_var. rewrite ?swap_aenv_app in Hd. exact Hd.
  -
    destruct (IHe_pat1 _ Heq) as [S1' [HS1 Hd1]].
    destruct (IHe_pat2 _ HS1) as [S2' [HS2 Hd2]].
    exists S2'. split; [ exact HS2 | eapply e_pat__app; eassumption ].
Qed.

Lemma e_split_supply_respect : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\ {{ S0' ↝ S1' ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e.
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_split_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  exact Hswap.
Qed.

Lemma e_pat_supply_respect : forall S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] S0 ->
  exists S1', S1' [=] S1 /\
    {{ S0' ↝ S1' ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e.
Proof.
  destruct (atom_fresh empty) as [a _].
  pose proof (@e_pat_swap a a) as Hswap.
  setoid_rewrite swap_aenv_same in Hswap.
  setoid_rewrite swap_pskl_same in Hswap.
  setoid_rewrite swap_exp_same in Hswap.
  setoid_rewrite swap_atoms_same in Hswap.
  exact Hswap.
Qed.

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
