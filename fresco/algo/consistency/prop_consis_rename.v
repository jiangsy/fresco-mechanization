Require Import src.fresco.prop_shapes.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.fresco.prop_coercions.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.prop_tag.
Require Import src.fresco.algo.basic.prop_swap.

Set Implicit Arguments.

Definition tvar_prefix (Ξ : aenv) : Prop :=
  forall x (b : abind), binds x b Ξ -> b = abind_tvar.

Lemma tvar_prefix_nil : tvar_prefix nil.
Proof. intros x b Hb. inversion Hb. Qed.

Lemma tvar_prefix_head : forall x (b : abind) Ξ,
  tvar_prefix ((x, b) :: Ξ) -> b = abind_tvar.
Proof. intros * H. apply (H x b). left. reflexivity. Qed.

Lemma tvar_prefix_tail : forall x (b : abind) Ξ,
  tvar_prefix ((x, b) :: Ξ) -> tvar_prefix Ξ.
Proof. intros * H y c Hb. apply (H y c). right. exact Hb. Qed.

Lemma tvar_prefix_cons : forall x Ξ,
  tvar_prefix Ξ -> tvar_prefix ((x, abind_tvar) :: Ξ).
Proof.
  intros * H y c Hb. destruct Hb as [Heq | Hb];
    [ inversion Heq; reflexivity | apply (H y c); exact Hb ].
Qed.

Ltac tvp_dispatch :=
  match goal with
  | Heq : _ = ?Ξr ++ _ |- _ =>
      destruct Ξr as [ | [?x ?bx] ?Ξr' ];
      [ eexists; reflexivity
      | simpl in Heq; inversion Heq; subst;
        try match goal with
        | Htv : tvar_prefix ((_, ?b) :: _) |- _ =>
            solve [ pose proof (tvar_prefix_head Htv); discriminate ]
        end ]
  end.

Lemma dom_sub_strip_tvar : forall α (Θ0 Θ1 : aenv),
  α `notin` dom Θ0 ->
  dom ((α ~ abind_tvar) ++ Θ0) [<=] dom ((α ~ abind_tvar) ++ Θ1) ->
  dom Θ0 [<=] dom Θ1.
Proof.
  intros α Θ0 Θ1 Hna Hsub. simpl_env in Hsub. simpl dom in Hsub.
  clear - Hna Hsub. fsetdec.
Qed.

Lemma a_assign_unify_consis_dom_mono :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> dom (Ξ ++ Θ0) [<=] dom Θ1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> dom Θ0 [<=] dom Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a -> dom Θ0 [<=] dom Θ1).
Proof.
  apply a_assign_unify_consis_mutind;
    intros;
    try (match goal with
         | IH : dom ((?α ~ abind_tvar) ++ ?A) [<=] dom ((?α ~ abind_tvar) ++ ?B)
             |- dom ?A [<=] dom ?B =>
             apply dom_sub_strip_tvar with (α := α);
               [ pose proof (dom_subset_ftvar_in_aenv A); fsetdec | exact IH ]
         end);
    repeat (rewrite dom_app in * || simpl dom in * );
    fsetdec.
Qed.

Lemma a_assign_unify_consis_tvar_prefix :
  (forall Θi Ξ α P Θo,
     {{ Θi ⊲[ Ξ ] α ≔ P ⊣ Θo }}a ->
     forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
     exists Θt', Θo = Ξr ++ Θt') /\
  (forall Θi α β Θo,
     {{ Θi ⊲ α ≈ᵘ β ⊣ Θo }}a ->
     forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
     exists Θt', Θo = Ξr ++ Θt') /\
  (forall Δ1 Δ2 Θi P0 P P' Θo,
     {{ Θi ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θo }}a ->
     forall Ξr Θt, Θi = Ξr ++ Θt -> tvar_prefix Ξr ->
     exists Θt', Θo = Ξr ++ Θt').
Proof.
  apply a_assign_unify_consis_mutind.
  -
    intros Θ0 α Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 Ξ α P βs τ Hnα Hg Hm Hu Hfr Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 Θ1 Ξ α β τ P P' Hf Hbar Hc IH Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 Θ1 Ξ α β P Hne Hin Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 Θ1 Ξ α β P Hne Hni Hbar Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 Θ1 Ξ α β P Hni Hbar Ha IH Ξr Θt Heq Htv. tvp_dispatch.
    destruct (IH Ξr' Θt eq_refl (tvar_prefix_tail Htv)) as [Θt' ->].
    exists Θt'. reflexivity.
  -
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 α Hf Ξr Θt Heq Htv. exists Θt. assumption.
  -
    intros Θ0 α β Hne Hf Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 α β Hne Hf Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 Θ1 α1 τ α β P' Hfα Hfβ Hbar Hc IH Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 Θ1 α1 α β Hne1 Hne2 Hbar Hu IH Ξr Θt Heq Htv. tvp_dispatch.
  -
    intros Θ0 Θ1 c b α β Hb Hbar Hu IH Ξr Θt Heq Htv. tvp_dispatch.
    destruct (IH Ξr' Θt eq_refl (tvar_prefix_tail Htv)) as [Θt' ->].
    exists Θt'. reflexivity.
  -
    intros Δ1 Δ2 Θ0 P0 Hi Ξr Θt Heq Htv. exists Θt. assumption.
  -
    intros Δ1 Δ2 Θ0 Ξr Θt Heq Htv. exists Θt. assumption.
  -
    intros Δ1 Δ2 Θ0 α Hb Ξr Θt Heq Htv. exists Θt. assumption.
  -
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2
      Ξr Θt Heq Htv.
    destruct (IH1 Ξr Θt Heq Htv) as [Θt1 ->].
    destruct (IH2 Ξr Θt1 eq_refl Htv) as [Θt2 ->].
    exists Θt2. reflexivity.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Ξr Θt Heq Htv.
    destruct (IH ((α, abind_tvar) :: Ξr) Θt
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)) as [Θt' HeqO].
    simpl in HeqO. inversion HeqO. exists Θt'. congruence.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Ξr Θt Heq Htv.
    destruct (IH ((α, abind_tvar) :: Ξr) Θt
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)) as [Θt' HeqO].
    simpl in HeqO. inversion HeqO. exists Θt'. congruence.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hc IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hprem IH Ξr Θt Heq Htv.
    destruct (IH ((α, abind_tvar) :: Ξr) Θt
                ltac:(rewrite Heq; reflexivity)
                (tvar_prefix_cons Htv)) as [Θt' HeqO].
    simpl in HeqO. inversion HeqO. exists Θt'. congruence.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  -
    intros Δ1 Δ2 Θ0 Θ1 α β Hu IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  -
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnhole Ha IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  -
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnhole Ha IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
  -
    intros Δ1 Δ2 Θ0 P Hi Ξr Θt Heq Htv. exists Θt. assumption.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH Ξr Θt Heq Htv.
    exact (IH Ξr Θt Heq Htv).
Qed.

Definition auc_dom_mono_consis := proj2 (proj2 a_assign_unify_consis_dom_mono).

Lemma a_assign_unify_subject_flex :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> a_flex_tvar (Ξ ++ Θ0) α) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a -> True).
Proof.
  apply a_assign_unify_consis_mutind;
    try solve [ intros; exact I ].
  -
    intros Θ0 α. simpl. left. left. reflexivity.
  -
    intros Θ0 Ξ α P βs τ Hnα Hg Hm Hu Hfr.
    left. unfold binds. apply in_or_app. right. left. reflexivity.
  -
    intros Θ0 Θ1 Ξ α β τ P P' Hfl Hbar Hc _.
    apply a_flex_tvar_weaken_app. exact Hfl.
  -
    intros Θ0 Θ1 Ξ α β P Hne Hin Ha IH.
    simpl_env in IH. exact IH.
  -
    intros Θ0 Θ1 Ξ α β P Hne Hni Hbar Ha IH.
    apply (a_flex_tvar_weaken_mid Ξ (β ~ abind_flex_mono) Θ0). exact IH.
  -
    intros Θ0 Θ1 Ξ α β P Hni Hbar Ha IH.
    apply (a_flex_tvar_weaken_mid Ξ (β ~ abind_tvar) Θ0). exact IH.
  -
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH.
    apply (a_flex_tvar_weaken_mid Ξ (x ~ abind_var_typ P') Θ0). exact IH.
  -
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH.
    apply (a_flex_tvar_weaken_mid Ξ (x ~ abind_var_skl P') Θ0). exact IH.
  -
    intros Θ0 α Hf. split; assumption.
  -
    intros Θ0 α β Hne Hf. split.
    + left. left. reflexivity.
    + apply (a_flex_tvar_weaken_app (α ~ abind_flex_mono)). exact Hf.
  -
    intros Θ0 α β Hne Hf. split.
    + apply (a_flex_tvar_weaken_app (β ~ abind_flex_mono)). exact Hf.
    + left. left. reflexivity.
  -
    intros Θ0 Θ1 α1 τ α β P' Hfα Hfβ Hbar Hc _. split; assumption.
  -
    intros Θ0 Θ1 α1 α β Hne1 Hne2 Hbar Hu [IHα IHβ]. split;
      apply (a_flex_tvar_weaken_app (α1 ~ abind_flex_mono)); assumption.
  -
    intros Θ0 Θ1 c b α β Hb Hbar Hu [IHα IHβ]. split;
      apply (a_flex_tvar_weaken_app (c ~ b)); assumption.
Qed.

Lemma disjoint_from_pointwise : forall (E G : aenv),
  (forall α1, α1 `in` dom E -> α1 `notin` dom G) -> disjoint E G.
Proof.
  intros * H. unfold disjoint.
  intros x Hx.
  apply inter_iff in Hx. destruct Hx as [H1 H2].
  exfalso. exact (H x H1 H2).
Qed.

Lemma a_assign_unify_consis_uniq :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a -> uniq (Ξ ++ Θ0) -> uniq Θ1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a -> uniq Θ0 -> uniq Θ1) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a -> uniq Θ0 -> uniq Θ1).
Proof.
  apply a_assign_unify_consis_mutind.

  -
    intros Θ0 α Hu. simpl_env in Hu. exact Hu.
  -
    intros Θ0 Ξ α P βs τ Hnα Hg Hm Huβ Hfr Hu.
    assert (HuΞΘ : uniq (Ξ ++ Θ0)) by solve_uniq.
    assert (HαΞΘ : α `notin` dom (Ξ ++ Θ0)) by solve_uniq.
    assert (Hdβ : disjoint βs (Ξ ++ Θ0)).
    { apply disjoint_from_pointwise. intros α1 Hα1.
      pose proof (Hfr α1 Hα1) as Hf. rewrite dom_app in *.
      clear - Hf. fsetdec. }
    assert (Hαβ : α `notin` dom βs).
    { intro Hαβ. pose proof (Hfr α Hαβ) as Hf. clear - Hf. fsetdec. }
    apply uniq_push; [ apply uniq_app_4; assumption | ].
    rewrite dom_app. clear - HαΞΘ Hαβ. fsetdec.
  -
    intros Θ0 Θ1 Ξ α β τ P P' Hfl Hbar Hc IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  -
    intros Θ0 Θ1 Ξ α β P Hne Hin Ha IH Hu.
    apply IH. simpl_env; solve_uniq.
  -
    intros Θ0 Θ1 Ξ α β P Hne Hni Hbar Ha IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  -
    intros Θ0 Θ1 Ξ α β P Hni Hbar Ha IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  -
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  -
    intros Θ0 Θ1 Ξ α x P' P Hbar Ha IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].

  -
    intros Θ0 α Hfα Hu. exact Hu.
  -
    intros Θ0 α β Hne Hfβ Hu. solve_uniq.
  -
    intros Θ0 α β Hne Hfα Hu. solve_uniq.
  -
    intros Θ0 Θ1 α1 τ α β Q Hfα Hfβ Hbar Hc IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  -
    intros Θ0 Θ1 α1 α β Hne1 Hne2 Hbar Hu0 IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].
  -
    intros Θ0 Θ1 c b α β Hb Hbar Hu0 IH Hu.
    apply uniq_push; [ apply IH; solve_uniq | exact Hbar ].

  -  intros Δ1 Δ2 Θ0 P0 Hi Hu. exact Hu.
  -  intros Δ1 Δ2 Θ0 Hu. exact Hu.
  -  intros Δ1 Δ2 Θ0 α Hb Hu. exact Hu.
  -
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2 Hu.
    apply IH2, IH1, Hu.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH Hu.
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0)).
    { apply uniq_push; [ exact Hu | ].
      pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec. }
    pose proof (IH Hu') as Hu1. solve_uniq.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH Hu.
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0)).
    { apply uniq_push; [ exact Hu | ].
      pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec. }
    pose proof (IH Hu') as Hu1. solve_uniq.
  -  intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hc IH Hu. apply IH, Hu.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc IH Hu.
    assert (Hu' : uniq ((α ~ abind_tvar) ++ Θ0)).
    { apply uniq_push; [ exact Hu | ].
      pose proof (dom_subset_ftvar_in_aenv Θ0); clear - Hfr H; fsetdec. }
    pose proof (IH Hu') as Hu1. solve_uniq.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH Hu. apply IH, Hu.
  -  intros Δ1 Δ2 Θ0 Θ1 α β Hu0 IH Hu. apply IH, Hu.
  -
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Hnhole Ha IH Hu. apply IH. simpl_env. exact Hu.
  -
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Hnhole Ha IH Hu. apply IH. simpl_env. exact Hu.
  -  intros Δ1 Δ2 Θ0 P Hi Hu. exact Hu.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH Hu. apply IH, Hu.
Qed.

Lemma subst_pskl_var_eq : forall P α,
  subst_pskl_in_pskl P α (pskl_var_f α) = P.
Proof.
  intros. simpl.
  destruct_if;
    [ reflexivity | congruence ].
Qed.

Lemma subst_pskl_var_neq : forall P α s,
  s <> α ->
  subst_pskl_in_pskl P α (pskl_var_f s) = pskl_var_f s.
Proof.
  intros. simpl.
  destruct_if;
    [ subst; congruence | reflexivity ].
Qed.

Definition auc_uniq_consis :=
  proj2 (proj2 a_assign_unify_consis_uniq).

Definition no_leak_free (Θi : aenv) (S : atoms) (Θo : aenv) (α : atom) :=
  α `notin` ftvar_in_aenv Θi `union` S ->
  α `notin` dom Θo -> α `notin` ftvar_in_aenv Θo.

Definition no_leak_pos (Θi Θo : aenv) (α : atom) :=
  forall Ξr Θb, Θi = Ξr ++ (α ~ abind_tvar) ++ Θb -> tvar_prefix Ξr ->
  α `notin` ftvar_in_aenv Θb ->
  exists Θt, Θo = Ξr ++ (α ~ abind_tvar) ++ Θt /\
             α `notin` ftvar_in_aenv Θt.

Lemma no_leak_refl : forall Θ S α,
  no_leak_free Θ S Θ α /\ no_leak_pos Θ Θ α.
Proof.
  unfold no_leak_free, no_leak_pos. intros Θ S α. split.
  - intros Hf _. clear - Hf. fsetdec.
  - intros Ξr Θb Heq Htv Hf. exists Θb. auto.
Qed.

Lemma no_leak_pos_vacuous : forall x b (Θ0 Θo : aenv) α,
  b <> abind_tvar -> no_leak_pos ((x ~ b) ++ Θ0) Θo α.
Proof.
  unfold no_leak_pos. intros * Hb Ξr Θb Heq Htv Hf.
  destruct Ξr as [ | [y c] Ξr' ]; inversion Heq; subst.
  - contradiction.
  - apply tvar_prefix_head in Htv. contradiction.
Qed.

Lemma no_leak_free_push : forall Ξ x b (Θ0 Θ1 : aenv) S α,
  no_leak_free (Ξ ++ Θ0) S Θ1 α ->
  no_leak_free (Ξ ++ (x ~ b) ++ Θ0) S ((x ~ b) ++ Θ1) α.
Proof.
  unfold no_leak_free. intros * IH Hf Hd.
  rewrite !ftvar_in_aenv_app in *. simpl in *.
  assert (h : α `notin` ftvar_in_aenv Θ1).
  { apply IH; clear - Hf Hd; fsetdec. }
  clear - Hf h. fsetdec.
Qed.

Lemma no_leak_pos_push : forall x b (Θ0 Θ1 : aenv) S α,
  (x = α -> b = abind_tvar -> α `notin` ftvar_in_aenv Θ0 ->
     α `notin` S /\ α `notin` dom Θ1) ->
  (α `notin` ftvar_in_aenv Θ0 `union` S -> α `notin` dom Θ1 ->
     α `notin` ftvar_in_aenv Θ1) ->
  no_leak_pos Θ0 Θ1 α ->
  no_leak_pos ((x ~ b) ++ Θ0) ((x ~ b) ++ Θ1) α.
Proof.
  unfold no_leak_pos. intros * Hcross Hfree Hpos Ξr Θb Heq Htv Hf.
  destruct Ξr as [ | [y c] Ξr' ]; inversion Heq; subst.
  - destruct (Hcross eq_refl eq_refl Hf) as [HS Hd].
    exists Θ1. split.
    + reflexivity.
    + refine (Hfree _ Hd). clear - Hf HS. fsetdec.
  - destruct (Hpos Ξr' Θb eq_refl (tvar_prefix_tail Htv) Hf)
      as [Θt [-> HΘt]].
    exists Θt. auto.
Qed.

Lemma no_leak_binder : forall α' (Θ0 Θ1 : aenv) (S S' : atoms),
  α' `notin` ftvar_in_aenv Θ0 ->
  S [<=] add α' S' ->
  (forall α, no_leak_free ((α' ~ abind_tvar) ++ Θ0) S
               ((α' ~ abind_tvar) ++ Θ1) α /\
             no_leak_pos ((α' ~ abind_tvar) ++ Θ0)
               ((α' ~ abind_tvar) ++ Θ1) α) ->
  forall α, no_leak_free Θ0 S' Θ1 α /\ no_leak_pos Θ0 Θ1 α.
Proof.
  unfold no_leak_free, no_leak_pos.
  intros α' Θ0 Θ1 S S' Hα' HS IH α. split.
  - intros Hf Hd. destruct (α == α') as [-> | Hne].
    + destruct (proj2 (IH α') nil Θ0 eq_refl tvar_prefix_nil Hα')
        as [Θt [Heq HΘt]].
      inversion Heq. subst. exact HΘt.
    + assert (h : α `notin` ftvar_in_aenv ((α' ~ abind_tvar) ++ Θ1)).
      { apply (proj1 (IH α)); simpl; clear - Hf Hd HS Hne; fsetdec. }
      simpl in h. clear - h. fsetdec.
  - intros Ξr Θb -> Htv Hf.
    destruct (proj2 (IH α) ((α', abind_tvar) :: Ξr) Θb eq_refl
                (tvar_prefix_cons Htv) Hf) as [Θt [HeqO HΘt]].
    inversion HeqO. exists Θt. auto.
Qed.

Lemma ftvar_subst_ptyp_to_pskl_upper : forall τ β P,
  ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
    [<=] ftvar_in_ptyp τ `union` ftvar_in_pskl P.
Proof.
  intros. rewrite ftvar_in_pskl_subst_pskl_in_pskl_upper,
    ftvar_ptyp_to_pskl. fsetdec.
Qed.

Lemma a_assign_unify_consis_no_leak :
  (forall Θi Ξ s P Θo,
     {{ Θi ⊲[ Ξ ] s ≔ P ⊣ Θo }}a -> forall α,
     no_leak_free (Ξ ++ Θi) (add s (ftvar_in_pskl P)) Θo α /\
     (α `notin` ftvar_in_aenv Ξ -> no_leak_pos Θi Θo α)) /\
  (forall Θi s1 s2 Θo,
     {{ Θi ⊲ s1 ≈ᵘ s2 ⊣ Θo }}a -> forall α,
     no_leak_free Θi (add s1 (singleton s2)) Θo α /\
     no_leak_pos Θi Θo α) /\
  (forall Δ1 Δ2 Θi P0 P Q Θo,
     {{ Θi ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θo }}a -> forall α,
     no_leak_free Θi (ftvar_in_pskl P0 `union` ftvar_in_pskl P) Θo α /\
     no_leak_pos Θi Θo α).
Proof.
  apply a_assign_unify_consis_mutind.

  -
    intros Θ0 s α. split.
    + apply (no_leak_refl _ _ _).
    + intros _. apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 Ξ s P βs τ Hnα Hg Hm Hu Hfr α. split.
    + unfold no_leak_free. intros Hf Hd.
      pose proof (a_guess_mono_ftv Hg) as Hτ.
      pose proof (a_guess_mono_generated_ftvar Hg) as Hβs.
      rewrite !ftvar_in_aenv_app, !dom_app in *. simpl in *.
      clear - Hf Hd Hτ Hβs. fsetdec.
    + intros _. apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 Θ1 Ξ s β τ P Q Hflex Hβ Hc IH α. split.
    + unfold no_leak_free. intros Hf Hd.
      pose proof (ftvar_subst_ptyp_to_pskl_upper τ β P) as H0.
      pose proof (ftvar_subst_ptyp_to_pskl_upper τ β (pskl_var_f s)) as H1.
      rewrite !ftvar_in_aenv_app in Hf. simpl in *.
      assert (h : α `notin` ftvar_in_aenv Θ1).
      { apply (proj1 (IH α)).
        - rewrite ftvar_in_aenv_app. clear - Hf H0 H1. fsetdec.
        - clear - Hd. fsetdec. }
      clear - Hf h. fsetdec.
    + intros _. apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 Θ1 Ξ s β P Hne Hin Ha IH α. split.
    + unfold no_leak_free. intros Hf Hd. refine (proj1 (IH α) _ Hd).
      rewrite !ftvar_in_aenv_app in *. simpl in *. clear - Hf. fsetdec.
    + intros _. apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 Θ1 Ξ s β P Hne Hni Hbar Ha IH α. split.
    + apply no_leak_free_push. exact (proj1 (IH α)).
    + intros _. apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 Θ1 Ξ s β P Hni Hbar Ha IH α. split.
    + apply no_leak_free_push. exact (proj1 (IH α)).
    + intros HΞ. apply no_leak_pos_push
        with (S := ftvar_in_aenv Ξ `union` add s (ftvar_in_pskl P)).
      * intros -> _ Hf. refine (conj _ Hbar).
        pose proof (a_flex_tvar_in_dom
                      (proj1 a_assign_unify_subject_flex _ _ _ _ _ Ha)) as Hs.
        pose proof (dom_subset_ftvar_in_aenv (Ξ ++ Θ0)) as Hdom.
        rewrite ftvar_in_aenv_app in Hdom.
        clear - HΞ Hf Hni Hs Hdom. fsetdec.
      * intros Hf. apply (proj1 (IH α)).
        rewrite ftvar_in_aenv_app. clear - Hf. fsetdec.
      * exact (proj2 (IH α) HΞ).
  -
    intros Θ0 Θ1 Ξ s x A P Hbar Ha IH α. split.
    + apply no_leak_free_push. exact (proj1 (IH α)).
    + intros _. apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 Θ1 Ξ s x Q P Hbar Ha IH α. split.
    + apply no_leak_free_push. exact (proj1 (IH α)).
    + intros _. apply no_leak_pos_vacuous. discriminate.

  -
    intros Θ0 s Hf α. apply no_leak_refl.
  -
    intros Θ0 s1 s2 Hne Hf α. split.
    + unfold no_leak_free. intros Hn _. simpl in *. clear - Hn. fsetdec.
    + apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 s1 s2 Hne Hf α. split.
    + unfold no_leak_free. intros Hn _. simpl in *. clear - Hn. fsetdec.
    + apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 Θ1 α1 τ s1 s2 Q Hf1 Hf2 Hbar Hc IH α. split.
    + unfold no_leak_free. intros Hn Hd.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                    (ptyp_var_f s1) τ α1) as H1.
      pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
                    (ptyp_var_f s2) τ α1) as H2.
      simpl in *.
      assert (h : α `notin` ftvar_in_aenv Θ1).
      { apply (proj1 (IH α)); rewrite ?ftvar_ptyp_to_pskl;
          clear - Hn Hd H1 H2; fsetdec. }
      clear - Hn h. fsetdec.
    + apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 Θ1 α1 s1 s2 Hne1 Hne2 Hbar Hu IH α. split.
    + apply no_leak_free_push with (Ξ := nil). exact (proj1 (IH α)).
    + apply no_leak_pos_vacuous. discriminate.
  -
    intros Θ0 Θ1 c b s1 s2 Hb Hbar Hu IH α. split.
    + apply no_leak_free_push with (Ξ := nil). exact (proj1 (IH α)).
    + apply no_leak_pos_push with (S := add s1 (singleton s2)).
      * intros -> _ Hf. refine (conj _ Hbar).
        destruct (proj1 (proj2 a_assign_unify_subject_flex) _ _ _ _ Hu)
          as [Hs1 Hs2].
        apply a_flex_tvar_in_dom in Hs1, Hs2.
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdom.
        clear - Hf Hs1 Hs2 Hdom. fsetdec.
      * exact (proj1 (IH α)).
      * exact (proj2 (IH α)).

  -
    intros Δ1 Δ2 Θ0 P0 Hi α. apply no_leak_refl.
  -
    intros Δ1 Δ2 Θ0 α. apply no_leak_refl.
  -
    intros Δ1 Δ2 Θ0 β Hb α. apply no_leak_refl.
  -
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2 α. split.
    + unfold no_leak_free. intros Hn Hd.
      pose proof (auc_dom_mono_consis Hc2) as Hdm.
      refine (proj1 (IH2 α) _ Hd).
      simpl in Hn.
      assert (h : α `notin` ftvar_in_aenv Θ1).
      { apply (proj1 (IH1 α)); clear - Hn Hd Hdm; fsetdec. }
      clear - Hn h. fsetdec.
    + intros Ξr Θb Heq Htv Hn.
      destruct (proj2 (IH1 α) Ξr Θb Heq Htv Hn) as [Θt1 [-> H1]].
      exact (proj2 (IH2 α) Ξr Θt1 eq_refl Htv H1).
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α' Hfr Hc IH.
    apply no_leak_binder with (α' := α') (S := ftvar_in_pskl
        (open_pskl_wrt_pskl P0 (pskl_var_f α')) `union` ftvar_in_pskl
        (open_pskl_wrt_pskl P (pskl_var_f α'))).
    + solve_notin_auto.
    + rewrite !ftvar_in_pskl_open_pskl_wrt_pskl_upper. simpl. fsetdec.
    + exact IH.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α' Hfr Hc IH.
    apply no_leak_binder with (α' := α') (S := ftvar_in_pskl
        (pskl_univ_ghost P0) `union` ftvar_in_pskl
        (open_pskl_wrt_pskl P (pskl_var_f α'))).
    + solve_notin_auto.
    + rewrite !ftvar_in_pskl_open_pskl_wrt_pskl_upper. simpl. fsetdec.
    + exact IH.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hc IH α. exact (IH α).
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q α' Hfr Hc IH.
    apply no_leak_binder with (α' := α') (S := ftvar_in_pskl
        (open_pskl_wrt_pskl P0 (pskl_var_f α')) `union` ftvar_in_pskl
        (pskl_univ_ghost P)).
    + solve_notin_auto.
    + rewrite !ftvar_in_pskl_open_pskl_wrt_pskl_upper. simpl. fsetdec.
    + exact IH.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH α. exact (IH α).
  -
    intros Δ1 Δ2 Θ0 Θ1 s1 s2 Hu IH α. split.
    + unfold no_leak_free. intros Hn Hd. refine (proj1 (IH α) _ Hd).
      simpl in *. clear - Hn. fsetdec.
    + exact (proj2 (IH α)).
  -
    intros Δ1 Δ2 Θ0 Θ1 s P0 Hnf Hng Ha IH α. split.
    + unfold no_leak_free. intros Hn Hd. refine (proj1 (IH α) _ Hd).
      simpl in *. clear - Hn. fsetdec.
    + apply (proj2 (IH α)). simpl. fsetdec.
  -
    intros Δ1 Δ2 Θ0 Θ1 s P Hnf Hng Ha IH α. split.
    + unfold no_leak_free. intros Hn Hd. refine (proj1 (IH α) _ Hd).
      simpl in *. clear - Hn. fsetdec.
    + apply (proj2 (IH α)). simpl. fsetdec.
  -
    intros Δ1 Δ2 Θ0 P Hi α. apply no_leak_refl.
  -
    intros Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH α. exact (IH α).
Qed.

Lemma a_consis_binder_no_leak : forall Δ1 Δ2 Θ0 Θ1 P0 P Q α,
  {{ ((α ~ abind_tvar) ++ Θ0) ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q
    ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
  α `notin` ftvar_in_aenv Θ0 ->
  α `notin` ftvar_in_aenv Θ1.
Proof.
  intros * Hc Hα.
  destruct (proj2 (proj2 (proj2 a_assign_unify_consis_no_leak)
                     _ _ _ _ _ _ _ Hc α) nil Θ0 eq_refl tvar_prefix_nil Hα)
    as [Θt [Heq HΘt]].
  inversion Heq. subst. exact HΘt.
Qed.

Lemma a_consis_move_binder : forall Δ1 Δ2 Δ1' Δ2' Θ0 Θ1 P0 P Q P0' P' α β,
  {{ ((α ~ abind_tvar) ++ Θ0) ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q
    ⊣ ((α ~ abind_tvar) ++ Θ1) }}a ->
  α `notin` ftvar_in_aenv Θ0 ->
  β `notin` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Θ1 `union` ftvar_in_pskl Q ->
  Δ1' [=] swap_atoms α β Δ1 -> Δ2' [=] swap_atoms α β Δ2 ->
  swap_pskl α β P0 = P0' -> swap_pskl α β P = P' ->
  {{ ((β ~ abind_tvar) ++ Θ0) ⊢[ Δ1' | Δ2' | P0' ] P' ∼
    (open_pskl_wrt_pskl (close_pskl_wrt_pskl α Q) (pskl_var_f β))
    ⊣ ((β ~ abind_tvar) ++ Θ1) }}a.
Proof.
  intros * Hc HαΘ0 Hβ H1 H2 <- <-.
  pose proof (a_consis_binder_no_leak Hc HαΘ0) as HαΘ1.
  pose proof (proj2 (proj2 (a_assign_unify_consis_swap α β))
                _ _ _ _ _ _ _ Hc _ _ H1 H2) as h.
  rewrite !swap_aenv_app, !swap_aenv_one_tvar in h.
  rewrite (swap_aenv_fresh_id α β Θ0), (swap_aenv_fresh_id α β Θ1),
    (swap_pskl_as_subst α β Q), subst_pskl_in_pskl_spec in h
    by solve_notin_auto.
  exact h.
Qed.

Lemma swap_pskl_open_binder : forall α β P,
  α `notin` ftvar_in_pskl P -> β `notin` ftvar_in_pskl P ->
  swap_pskl α β (open_pskl_wrt_pskl P (pskl_var_f α))
  = open_pskl_wrt_pskl P (pskl_var_f β).
Proof.
  intros * Hα Hβ.
  rewrite swap_pskl_open_var, swap_atom_l, swap_pskl_fresh_id; auto.
Qed.

Lemma uniq_push_tvar : forall (Θ : aenv) β,
  uniq Θ -> β `notin` ftvar_in_aenv Θ -> uniq ((β ~ abind_tvar) ++ Θ).
Proof.
  intros * Hu Hβ. apply uniq_push.
  - exact Hu.
  - pose proof (dom_subset_ftvar_in_aenv Θ). clear - Hβ H. fsetdec.
Qed.

Lemma eq_swap_atoms_add_binder : forall α β (Δ : atoms),
  α `notin` Δ -> β `notin` Δ ->
  add β Δ [=] swap_atoms α β (add α Δ).
Proof.
  intros * Hα Hβ.
  pose proof (eq_swap_atoms_add α β α Δ Δ (eq_swap_atoms_fresh α β Δ Hα Hβ))
    as h.
  rewrite swap_atom_l in h. exact h.
Qed.

Lemma a_consis_forall_inh_cofinite : forall L Δ1 Δ2 Θ0 Θ1 P0 P Q,
  (forall α, α `notin` L ->
     {{ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | (add α Δ2)
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼
       (open_pskl_wrt_pskl Q (pskl_var_f α))
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}a) ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
    (pskl_all_syn P) ∼ (pskl_all_syn Q) ⊣ Θ1 }}a.
Proof.
  intros L Δ1 Δ2 Θ0 Θ1 P0 P Q Hbody.
  pick fresh α for (L `union` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
                    `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                    `union` Δ1 `union` Δ2).
  replace Q with
    (close_pskl_wrt_pskl α (open_pskl_wrt_pskl Q (pskl_var_f α)))
    by (apply close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        clear - Fr; fsetdec).
  apply a_consis__forall_inh with (α := α);
    [ clear - Fr; fsetdec | apply Hbody; clear - Fr; fsetdec ].
Qed.

Lemma a_consis_forall_syn_cofinite : forall L Δ1 Δ2 Θ0 Θ1 P0 P Q,
  (forall α, α `notin` L ->
     {{ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ Δ1 | (add α Δ2) | (pskl_univ_ghost P0) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼
       (open_pskl_wrt_pskl Q (pskl_var_f α))
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}a) ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
    (pskl_all_syn P) ∼ (pskl_all_syn Q) ⊣ Θ1 }}a.
Proof.
  intros L Δ1 Δ2 Θ0 Θ1 P0 P Q Hbody.
  pick fresh α for (L `union` ftvar_in_aenv Θ0 `union` ftvar_in_pskl P0
                    `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                    `union` Δ1 `union` Δ2).
  replace Q with
    (close_pskl_wrt_pskl α (open_pskl_wrt_pskl Q (pskl_var_f α)))
    by (apply close_pskl_wrt_pskl_open_pskl_wrt_pskl;
        clear - Fr; fsetdec).
  apply a_consis__forall_syn with (α := α);
    [ clear - Fr; fsetdec | apply Hbody; clear - Fr; fsetdec ].
Qed.

Lemma a_consis_decorate_size : forall n Δ1 Δ2 Θ0 P0 P P' Θ1,
  size_pskl P + size_pskl P0 <= n ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
  uniq Θ0 ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | empty ] (pskl_to_uskl P) ∼ P' ⊣ Θ1 }}da.
Proof.
  induction n as [ | n IHn ];
    intros Δ1 Δ2 Θ0 P0 P P' Θ1 Hsz Hc Hu.
  { pose proof (size_pskl_min P); pose proof (size_pskl_min P0); lia. }
  revert Hsz Hu.
  destruct Hc as
    [ Δ1 Δ2 Θ0 P0 Hi
    | Δ1 Δ2 Θ0
    | Δ1 Δ2 Θ0 α Hb
    | Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hca Hcb
    | Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc
    | Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc
    | Δ1 Δ2 Θ0 Θ1 P0 P Q Hc
    | Δ1 Δ2 Θ0 Θ1 P0 P Q α Hfr Hc
    | Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc
    | Δ1 Δ2 Θ0 Θ1 α β Hun
    | Δ1 Δ2 Θ0 Θ1 α P0 Hnf Ha
    | Δ1 Δ2 Θ0 Θ1 α P Hnf Ha
    | Δ1 Δ2 Θ0 P Hi
    | Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc ];
    intros Hsz Hu; simpl in Hsz |- *.
  -
    apply a_consistag__ghost; auto. fsetdec.
  -
    apply a_consistag__unit. fsetdec.
  -
    apply a_consistag__rigid; auto. fsetdec.
  -
    eapply a_consistag__arrow;
      [ eapply IHn; [ | exact Hca | exact Hu ]; lia
      | eapply IHn;
        [ | exact Hcb | exact (auc_uniq_consis Hca Hu) ]; lia
      | fsetdec ].
  -
    apply a_consistag__forall_inh_untagged with
      (L := singleton α `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Θ1
            `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
            `union` ftvar_in_pskl Q `union` Δ1 `union` Δ2).
    intros β Hβ.
    rewrite <- pskl_to_uskl_open_var.
    eapply IHn.
    + rewrite ! size_pskl_open_pskl_wrt_pskl_var. lia.
    + eapply a_consis_move_binder.
      * exact Hc.
      * solve_notin_auto.
      * solve_notin_auto.
      * apply eq_swap_atoms_add_binder; solve_notin_auto.
      * apply eq_swap_atoms_add_binder; solve_notin_auto.
      * apply swap_pskl_open_binder; solve_notin_auto.
      * apply swap_pskl_open_binder; solve_notin_auto.
    + apply (uniq_push_tvar Hu). solve_notin_auto.
  -
    apply a_consistag__forall_syn_untagged with
      (L := singleton α `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Θ1
            `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
            `union` ftvar_in_pskl Q `union` Δ1 `union` Δ2).
    intros β Hβ.
    rewrite <- pskl_to_uskl_open_var.
    eapply IHn.
    + rewrite size_pskl_open_pskl_wrt_pskl_var. simpl. lia.
    + eapply a_consis_move_binder.
      * exact Hc.
      * solve_notin_auto.
      * solve_notin_auto.
      * apply eq_swap_atoms_fresh; solve_notin_auto.
      * apply eq_swap_atoms_add_binder; solve_notin_auto.
      * apply swap_pskl_fresh_id; simpl; solve_notin_auto.
      * apply swap_pskl_open_binder; solve_notin_auto.
    + apply (uniq_push_tvar Hu). solve_notin_auto.
  -
    apply a_consistag__univ_ghost.
    eapply IHn; [ | exact Hc | exact Hu ]; lia.
  -
    apply a_consistag__univ_ghost1 with
      (L := singleton α `union` ftvar_in_aenv Θ0 `union` ftvar_in_aenv Θ1
            `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
            `union` ftvar_in_pskl Q `union` Δ1 `union` Δ2).
    intros β Hβ.
    change (uskl_univ_ghost (pskl_to_uskl P))
      with (pskl_to_uskl (pskl_univ_ghost P)).
    eapply IHn.
    + rewrite size_pskl_open_pskl_wrt_pskl_var. simpl. lia.
    + eapply a_consis_move_binder.
      * exact Hc.
      * solve_notin_auto.
      * solve_notin_auto.
      * apply eq_swap_atoms_add_binder; solve_notin_auto.
      * apply eq_swap_atoms_fresh; solve_notin_auto.
      * apply swap_pskl_open_binder; solve_notin_auto.
      * apply swap_pskl_fresh_id; simpl; solve_notin_auto.
    + apply (uniq_push_tvar Hu). solve_notin_auto.
  -
    apply a_consistag__univ_ghost2; auto.
    eapply IHn; [ | exact Hc | exact Hu ]; lia.
  -
    apply a_consistag__flex; auto. fsetdec.
  -
    eapply a_consistag__flex_l; eauto. fsetdec.
  -
    apply a_consistag__flex_r;
      try rewrite uskl_to_pskl_pskl_to_uskl; auto; try fsetdec.
  -
    replace P with (uskl_to_pskl (pskl_to_uskl P)) at 2
      by apply uskl_to_pskl_pskl_to_uskl.
    apply a_consistag__ghost_r;
      try rewrite uskl_to_pskl_pskl_to_uskl; auto; try fsetdec.
  -
    apply a_consistag__univ_ghost_r; auto using pskl_to_uskl_guarded;
      try rewrite uskl_to_pskl_pskl_to_uskl; auto.
    eapply IHn; [ | exact Hc | exact Hu ]; lia.
Qed.

Lemma a_consis_decorate : forall Δ1 Δ2 Θ0 P0 P P' Θ1,
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
  uniq Θ0 ->
  {{ Θ0 ⊢[ Δ1 | Δ2 | P0 | empty ] (pskl_to_uskl P) ∼ P' ⊣ Θ1 }}da.
Proof.
  intros * Hc Hu.
  eapply a_consis_decorate_size; [ | exact Hc | exact Hu ].
  reflexivity.
Qed.
