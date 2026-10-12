Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.ltac_utils.
Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_ln.
Require Import src.fresco.def_shapes.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.prop_look.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

Lemma rel_pskl_degree : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  forall k, degree_pskl_wrt_pskl k P1 -> degree_pskl_wrt_pskl k P2.
Proof.
  intros * Hrel; induction Hrel; intros k Hd; inversion Hd; subst;
    constructor; auto.
Qed.

Lemma rel_pskl_lc : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> lc_pskl P1 -> lc_pskl P2.
Proof.
  intros * Hrel Hlc.
  apply lc_pskl_of_degree.
  eapply rel_pskl_degree; [ exact Hrel | ].
  apply degree_pskl_wrt_pskl_of_lc_pskl. exact Hlc.
Qed.

Lemma rel_pskl_nonghost : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> nonghost_pskl P1 -> nonghost_pskl P2.
Proof.
  intros * Hrel Hng; inversion Hng; subst; inversion Hrel; subst;
    constructor.
Qed.

Lemma rel_pskl_guarded : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> guarded_pskl P1 -> guarded_pskl P2.
Proof.
  intros * Hrel Hg; inversion Hg; subst; inversion Hrel; subst;
    constructor; eauto using rel_pskl_lc.
Qed.

Lemma rel_pskl_peel_l_off : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> peel_l_off P1 -> peel_l_off P2.
Proof.
  intros * Hrel [H1 H2]; inversion Hrel; subst;
    try solve [ split; intros; discriminate ];
    [ exfalso; exact (H1 _ eq_refl) | exfalso; exact (H2 _ eq_refl) ].
Qed.

Lemma rel_pskl_solve_l_off : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> solve_l_off P1 -> solve_l_off P2.
Proof.
  intros * Hrel [H0 [H1 H2]]; inversion Hrel; subst;
    try solve [ split;
                [ intros; discriminate | split; intros; discriminate ] ];
    [ exfalso; exact (H0 _ eq_refl)
    | exfalso; exact (H1 _ eq_refl)
    | exfalso; exact (H2 _ eq_refl) ].
Qed.

Lemma rel_pskl_ghost_free : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> pskl_ghost_free P1 -> pskl_ghost_free P2.
Proof.
  intros * Hrel; induction Hrel; simpl; intros; try tauto.
Qed.

Lemma rel_pskl_ghost_free_rev : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> pskl_ghost_free P2 -> pskl_ghost_free P1.
Proof.
  intros * Hrel; induction Hrel; simpl; intros; try tauto.
Qed.

Lemma rel_pskl_notin_r : forall ρ V P1 P2 α,
  rel_pskl ρ V P1 P2 ->
  α `notin` ftvar_in_pskl P1 ->
  α `notin` cols_r ρ ->
  α `notin` ftvar_in_pskl P2.
Proof.
  intros * Hrel; induction Hrel; simpl; intros Hn Hc; try fsetdec.
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
  end.
  - pose proof (cols_r_in _ _ _ ltac:(eassumption)). fsetdec.
  - fsetdec.
Qed.

Lemma rel_pskl_neq_var : forall ρ V P1 P2 α,
  rel_pskl ρ V P1 P2 ->
  P1 <> pskl_var_f α ->
  α `notin` cols_r ρ ->
  P2 <> pskl_var_f α.
Proof.
  intros * Hrel; induction Hrel; intros Hne Hc; try discriminate.
  match goal with
  | Ha : rel_atom _ _ ?x ?y |- _ => inversion Ha; subst
  end.
  - intros Heq; inversion Heq; subst.
    apply Hc. eapply cols_r_in; eassumption.
  - exact Hne.
Qed.

Lemma rel_pskl_neq_ghost : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  P1 <> pskl_ghost ->
  P2 <> pskl_ghost.
Proof.
  intros * Hrel; induction Hrel; intros Hne; try discriminate.
  exact Hne.
Qed.

Lemma rel_pskl_all_syn_r_inv : forall ρ V P1 B,
  rel_pskl ρ V P1 (pskl_all_syn B) ->
  exists P, P1 = pskl_all_syn P /\ rel_pskl ρ V P B.
Proof.
  intros ρ V P1 B Hrel.
  remember (pskl_all_syn B) as T eqn:HT.
  destruct Hrel; try discriminate HT.
  injection HT as HT0; subst.
  eexists; split; [ reflexivity | eassumption ].
Qed.

Lemma rel_pskl_forall_r_off : forall ρ V m P1 P2,
  rel_pskl ρ V P1 P2 ->
  forall_r_off m P1 ->
  forall_r_off m P2.
Proof.
  intros ρ V m P1 P2 Hrel Hoff B Heq Hm.
  rewrite Heq in Hrel.
  destruct (rel_pskl_all_syn_r_inv Hrel) as (P & -> & Hr).
  intro Hgf. apply (Hoff P eq_refl Hm). simpl in Hgf |- *.
  eapply rel_pskl_ghost_free_rev; [ exact Hr | exact Hgf ].
Qed.

Lemma rel_pskl_in_id : forall ρ V P1 P2 α,
  rel_pskl ρ V P1 P2 ->
  α `in` ftvar_in_pskl P1 ->
  α `notin` cols_l ρ ->
  α `in` ftvar_in_pskl P2.
Proof.
  intros * Hrel; induction Hrel; simpl; intros Hn Hc; try fsetdec.
  match goal with
  | Ha : rel_atom _ _ ?x ?y |- _ => inversion Ha; subst
  end.
  - pose proof (cols_l_in _ _ _ ltac:(eassumption)).
    assert (α = β) by fsetdec. subst. exfalso. fsetdec.
  - fsetdec.
Qed.

Definition flex_agree_rel (ρ : list (atom * atom)) (V : atoms)
    (Θ1 Θ2 : aenv) : Prop :=
  (forall α, α `in` V -> (a_flex_tvar Θ1 α <-> a_flex_tvar Θ2 α)) /\
  (forall a b, In (a, b) ρ -> (a_flex_tvar Θ1 a <-> a_flex_tvar Θ2 b)).

Lemma flex_agree_rel_weaken : forall ρ ρ' V V' Θ1 Θ2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  (forall a b, In (a, b) ρ' -> In (a, b) ρ) ->
  V' [<=] V ->
  flex_agree_rel ρ' V' Θ1 Θ2.
Proof.
  intros * [HagV Hagp] Hincl Hsub. split.
  - intros α Hα. apply HagV. fsetdec.
  - intros a b Hin. apply Hagp. apply Hincl. exact Hin.
Qed.

Lemma flex_agree_rel_extend_nonflex : forall ρx ρ V Θ1 Θ2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  (forall a b, In (a, b) ρx -> ~ a_flex_tvar Θ1 a /\ ~ a_flex_tvar Θ2 b) ->
  flex_agree_rel (ρx ++ ρ) V Θ1 Θ2.
Proof.
  intros ρx ρ V Θ1 Θ2 [HagV Hagp] Hnf. split; [ exact HagV | ].
  intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (Hnf a b Hin) as [H1 H2]; split; intro Hf;
      [ exfalso; exact (H1 Hf) | exfalso; exact (H2 Hf) ].
  - exact (Hagp a b Hin).
Qed.

Lemma flex_agree_rel_push_look : forall ρ V Θ1 Θ2 β β2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  β `notin` dom Θ1 ->
  β2 `notin` dom Θ2 ->
  flex_agree_rel ((β, β2) :: ρ) V
    ((β ~ abind_tvar) ++ Θ1) ((β2 ~ abind_tvar) ++ Θ2).
Proof.
  intros ρ V Θ1 Θ2 β β2 [HagV Hagp] Hβ1 Hβ2.
  pose proof a_flex_tvar_in_dom as Hdom.
  split.
  - intros α Hα. rewrite ! a_flex_tvar_cons_tvar_any. exact (HagV _ Hα).
  - intros a b Hin. destruct Hin as [E | Hin].
    + inversion E; subst. rewrite ! a_flex_tvar_cons_tvar_any.
      split; intro Hf; exfalso; apply Hdom in Hf;
        [ clear - Hβ1 Hf | clear - Hβ2 Hf ]; fsetdec.
    + rewrite ! a_flex_tvar_cons_tvar_any. exact (Hagp _ _ Hin).
Qed.

Lemma binds_flex_pairs_l : forall ρ a b,
  In (a, b) ρ -> binds a abind_flex_mono (flex_pairs_l ρ).
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros * Hin; simpl in *;
    [ contradiction | ].
  destruct Hin as [E | Hin].
  - inversion E; subst. unfold binds. simpl. auto.
  - unfold binds. simpl. right. apply (IH _ _ Hin).
Qed.

Lemma binds_flex_pairs_r : forall ρ a b,
  In (a, b) ρ -> binds b abind_flex_mono (flex_pairs_r ρ).
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros * Hin; simpl in *;
    [ contradiction | ].
  destruct Hin as [E | Hin].
  - inversion E; subst. unfold binds. simpl. auto.
  - unfold binds. simpl. right. apply (IH _ _ Hin).
Qed.

Lemma flex_agree_rel_push_pairs : forall ρn ρ V Θ1 Θ2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  cols_l ρn ∩ (V ∪ cols_l ρ) [=] empty ->
  cols_r ρn ∩ (V ∪ cols_r ρ) [=] empty ->
  flex_agree_rel (ρn ++ ρ) V
    (flex_pairs_l ρn ++ Θ1) (flex_pairs_r ρn ++ Θ2).
Proof.
  intros * [HagV Hagp] Hdl Hdr. split.
  - intros α Hα.
    rewrite (a_flex_tvar_app_notin (flex_pairs_l ρn))
      by (rewrite dom_flex_pairs_l; clear - Hdl Hα; fsetdec).
    rewrite (a_flex_tvar_app_notin (flex_pairs_r ρn))
      by (rewrite dom_flex_pairs_r; clear - Hdr Hα; fsetdec).
    apply HagV; exact Hα.
  - intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + split; intros _; left;
        [ pose proof (@binds_flex_pairs_r ρn a b Hin) as Hb
        | pose proof (@binds_flex_pairs_l ρn a b Hin) as Hb ];
        unfold binds in *; apply in_or_app; left; exact Hb.
    + pose proof (cols_l_in _ _ _ Hin) as Hcl.
      pose proof (cols_r_in _ _ _ Hin) as Hcr.
      rewrite (a_flex_tvar_app_notin (flex_pairs_l ρn))
        by (rewrite dom_flex_pairs_l; clear - Hdl Hcl; fsetdec).
      rewrite (a_flex_tvar_app_notin (flex_pairs_r ρn))
        by (rewrite dom_flex_pairs_r; clear - Hdr Hcr; fsetdec).
      apply Hagp. exact Hin.
Qed.

Lemma rel_pskl_non_flex : forall ρ V Θ1 Θ2 P1 P2,
  rel_pskl ρ V P1 P2 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  a_non_flex Θ1 P1 -> a_non_flex Θ2 P2.
Proof.
  intros * Hrel Hagr [Hlc Hnf].
  split; [ eauto using rel_pskl_lc | ].
  intros Hf. apply Hnf.
  inversion Hf; subst;
    match goal with
    | Hb : binds ?b _ Θ2 |- _ =>
        inversion Hrel; subst;
        match goal with
        | Ha : rel_atom _ _ ?a b |- _ =>
            apply a_flex_var_iff_tvar;
            assert (Hf2 : a_flex_tvar Θ2 b)
              by (first [ left; assumption
                        | right; eexists; eassumption ]);
            inversion Ha; subst;
            [ apply (proj2 (Hagr) _ _ ltac:(eassumption)); exact Hf2
            | apply (proj1 (Hagr) _ ltac:(eassumption)); exact Hf2 ]
        end
    end.
Qed.

Lemma rel_pskl_bubble_pair : forall ρn ρ V β1 β2 P1 P2,
  rel_pskl (ρn ++ (β1, β2) :: ρ) V P1 P2 ->
  rel_pskl ((β1, β2) :: ρn ++ ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - right. apply in_or_app. left. exact Hin.
  - destruct Hin as [E | Hin];
      [ left; exact E | right; apply in_or_app; right; exact Hin ].
Qed.

Lemma rel_pskl_widen_hd : forall ρb ρa ρ V P1 P2,
  rel_pskl (ρa ++ ρ) V P1 P2 ->
  rel_pskl ((ρb ++ ρa) ++ ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. apply in_app_or in Hin. apply in_or_app.
  destruct Hin as [Hin | Hin];
    [ left; apply in_or_app; right; exact Hin | right; exact Hin ].
Qed.

Lemma rel_pskl_app_assoc : forall ρa ρb ρ V P1 P2,
  rel_pskl (ρa ++ ρb ++ ρ) V P1 P2 ->
  rel_pskl ((ρa ++ ρb) ++ ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. apply in_app_or in Hin. apply in_or_app.
  destruct Hin as [Hin | Hin].
  - left. apply in_or_app. left. exact Hin.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin];
      [ left; apply in_or_app; right; exact Hin | right; exact Hin ].
Qed.

Lemma rel_pskl_widen : forall ρn ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  rel_pskl (ρn ++ ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. apply in_or_app. right. exact Hin.
Qed.

Lemma rel_pskl_extend_pair : forall β1 β2 ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ((β1, β2) :: ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. right. exact Hin.
Qed.

Lemma cols_l_fresh : forall (ρx : list (atom * atom)) x,
  (forall a b, In (a, b) ρx -> a <> x) ->
  x `notin` cols_l ρx.
Proof.
  induction ρx as [ | [a b] ρx IH ]; intros x H; simpl;
    [ clear; fsetdec | ].
  pose proof (H a b (or_introl eq_refl)) as Hne.
  pose proof (IH x ltac:(intros a' b' Hin'; apply (H a' b');
                         right; exact Hin')) as Htl.
  clear - Hne Htl. fsetdec.
Qed.

Lemma cols_r_fresh : forall (ρx : list (atom * atom)) x,
  (forall a b, In (a, b) ρx -> b <> x) ->
  x `notin` cols_r ρx.
Proof.
  induction ρx as [ | [a b] ρx IH ]; intros x H; simpl;
    [ clear; fsetdec | ].
  pose proof (H a b (or_introl eq_refl)) as Hne.
  pose proof (IH x ltac:(intros a' b' Hin'; apply (H a' b');
                         right; exact Hin')) as Htl.
  clear - Hne Htl. fsetdec.
Qed.

Inductive rel_a_cstr (ρ : list (atom * atom)) (V : atoms)
    : a_cstr -> a_cstr -> Prop :=
| rel_a_cstr__sub : forall m Q1 Q2,
    rel_pskl ρ V Q1 Q2 ->
    rel_a_cstr ρ V (a_cstr_sub m Q1) (a_cstr_sub m Q2)
| rel_a_cstr__eq : forall Q1 Q2,
    rel_pskl ρ V Q1 Q2 ->
    rel_a_cstr ρ V (a_cstr_eq Q1) (a_cstr_eq Q2).

Definition rel_a_cstrs (ρ : list (atom * atom)) (V : atoms)
    : a_cstrs -> a_cstrs -> Prop :=
  List.Forall2 (rel_a_cstr ρ V).

Lemma rel_a_cstr_widen : forall ρn ρ V c1 c2,
  rel_a_cstr ρ V c1 c2 -> rel_a_cstr (ρn ++ ρ) V c1 c2.
Proof.
  intros * H; inversion H; subst; constructor;
    apply rel_pskl_widen; assumption.
Qed.

Lemma rel_a_cstrs_widen : forall ρn ρ V C1 C2,
  rel_a_cstrs ρ V C1 C2 -> rel_a_cstrs (ρn ++ ρ) V C1 C2.
Proof.
  intros * H; induction H; constructor;
    eauto using rel_a_cstr_widen.
Qed.

Lemma rel_a_cstr_mono : forall ρ ρ' V V' c1 c2,
  rel_a_cstr ρ V c1 c2 ->
  (forall a b, In (a, b) ρ -> In (a, b) ρ') ->
  V [<=] V' ->
  rel_a_cstr ρ' V' c1 c2.
Proof.
  intros * H Hincl Hs; inversion H; subst; constructor;
    eapply rel_pskl_mono; eauto.
Qed.

Lemma rel_atom_drop_head : forall a b ρ V x y,
  rel_atom ((a, b) :: ρ) V x y -> x <> a -> rel_atom ρ V x y.
Proof.
  intros a b ρ V x y H Hne.
  inversion H; subst.
  - match goal with
    | Hin : In _ ((a, b) :: ρ) |- _ =>
        destruct Hin as [E | Hin'];
          [ inversion E; subst; congruence
          | apply rel_atom__pair; exact Hin' ]
    end.
  - apply rel_atom__id; assumption.
Qed.

Lemma rel_pskl_drop_head : forall a b ρ V P1 P2,
  rel_pskl ((a, b) :: ρ) V P1 P2 ->
  a `notin` ftvar_in_pskl P1 ->
  rel_pskl ρ V P1 P2.
Proof.
  intros a b ρ V P1 P2 H; induction H; intros Ha; simpl in Ha;
    constructor; try (apply IHrel_pskl || (apply IHrel_pskl1 + apply IHrel_pskl2));
    try (clear - Ha; fsetdec).
  eapply rel_atom_drop_head; [ eassumption | clear - Ha; fsetdec ].
Qed.

Lemma rel_a_cstr_drop_head : forall a b ρ V c1 c2,
  rel_a_cstr ((a, b) :: ρ) V c1 c2 ->
  a `notin` ftvar_in_a_cstr c1 ->
  rel_a_cstr ρ V c1 c2.
Proof.
  intros a b ρ V c1 c2 H Ha; inversion H; subst; simpl in Ha.
  - constructor. eapply rel_pskl_drop_head; [ eassumption | exact Ha ].
  - constructor. eapply rel_pskl_drop_head; [ eassumption | exact Ha ].
Qed.

Lemma rel_a_cstrs_drop_head : forall a b ρ V C1 C2,
  rel_a_cstrs ((a, b) :: ρ) V C1 C2 ->
  a `notin` ftvar_in_a_cstrs C1 ->
  rel_a_cstrs ρ V C1 C2.
Proof.
  intros a b ρ V C1 C2 H; induction H as [ | c1 c2 C1' C2' Hc HC IH ];
    intros Ha; [ constructor | ].
  simpl in Ha. constructor.
  - eapply rel_a_cstr_drop_head; [ exact Hc | clear - Ha; fsetdec ].
  - apply IH. clear - Ha. fsetdec.
Qed.

Definition restrict_pairs (β1 β2 : atom) (ρ : list (atom * atom))
  : list (atom * atom) :=
  List.filter (fun p => if (fst p == β1) then false
                        else if (snd p == β2) then false else true) ρ.

Arguments restrict_pairs : simpl never.

Lemma restrict_pairs_incl : forall β1 β2 ρ a b,
  In (a, b) (restrict_pairs β1 β2 ρ) -> In (a, b) ρ.
Proof.
  intros * Hin. apply List.filter_In in Hin. tauto.
Qed.

Lemma restrict_pairs_notin_l : forall β1 β2 ρ,
  β1 `notin` cols_l (restrict_pairs β1 β2 ρ).
Proof.
  intros. apply cols_l_fresh. intros a b Hin.
  apply List.filter_In in Hin. destruct Hin as [_ Hf]. simpl in Hf.
  destruct (a == β1) as [ | Hne ]; [ discriminate | exact Hne ].
Qed.

Lemma restrict_pairs_notin_r : forall β1 β2 ρ,
  β2 `notin` cols_r (restrict_pairs β1 β2 ρ).
Proof.
  intros. apply cols_r_fresh. intros a b Hin.
  apply List.filter_In in Hin. destruct Hin as [_ Hf]. simpl in Hf.
  destruct (a == β1); [ discriminate | ].
  destruct (b == β2) as [ | Hne ]; [ discriminate | exact Hne ].
Qed.

Lemma cols_l_restrict_pairs : forall β1 β2 ρ,
  cols_l (restrict_pairs β1 β2 ρ) [<=] cols_l ρ.
Proof.
  intros β1 β2 ρ. induction ρ as [ | [a b] ρ IH ];
    unfold restrict_pairs in *; simpl; [ clear; fsetdec | ].
  destruct (a == β1); simpl; [ clear - IH; fsetdec | ].
  destruct (b == β2); simpl; [ clear - IH; fsetdec | ].
  clear - IH. fsetdec.
Qed.

Lemma cols_r_restrict_pairs : forall β1 β2 ρ,
  cols_r (restrict_pairs β1 β2 ρ) [<=] cols_r ρ.
Proof.
  intros β1 β2 ρ. induction ρ as [ | [a b] ρ IH ];
    unfold restrict_pairs in *; simpl; [ clear; fsetdec | ].
  destruct (a == β1); simpl; [ clear - IH; fsetdec | ].
  destruct (b == β2); simpl; [ clear - IH; fsetdec | ].
  clear - IH. fsetdec.
Qed.

Lemma rel_pskl_restrict : forall ρ V P1 P2 β1 β2,
  rel_pskl ρ V P1 P2 ->
  β1 `notin` ftvar_in_pskl P1 ->
  β2 `notin` ftvar_in_pskl P2 ->
  rel_pskl (restrict_pairs β1 β2 ρ) V P1 P2.
Proof.
  intros ρ V P1 P2 β1 β2 H; induction H; intros H1 H2; simpl in H1, H2;
    constructor;
    try (apply IHrel_pskl || (apply IHrel_pskl1 + apply IHrel_pskl2));
    try (clear - H1; fsetdec); try (clear - H2; fsetdec).
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
  end.
  - apply rel_atom__pair. apply List.filter_In. split; [ assumption | ].
    simpl.
    destruct (α == β1) as [ -> | ];
      [ exfalso; clear - H1; fsetdec | ].
    destruct (β == β2) as [ -> | ];
      [ exfalso; clear - H2; fsetdec | ].
    reflexivity.
  - apply rel_atom__id. assumption.
Qed.

Lemma rel_pskl_close_pair_restrict : forall ρ ρ' V P1 P2 β1 β2 ρa,
  rel_pskl (ρa ++ (β1, β2) :: restrict_pairs β1 β2 ρ) V P1 P2 ->
  β1 `notin` V -> β1 `notin` cols_l ρa ->
  β2 `notin` V -> β2 `notin` cols_r ρa ->
  (forall a b, In (a, b) ρa -> In (a, b) ρ') ->
  (forall a b, In (a, b) ρ -> In (a, b) ρ') ->
  rel_pskl ρ' V (close_pskl_wrt_pskl β1 P1) (close_pskl_wrt_pskl β2 P2).
Proof.
  intros ρ ρ' V P1 P2 β1 β2 ρa Hrel Hb1V Hb1a Hb2V Hb2a Hia Hir.
  assert (Hcl : rel_pskl (ρa ++ restrict_pairs β1 β2 ρ) V
                  (close_pskl_wrt_pskl β1 P1) (close_pskl_wrt_pskl β2 P2)).
  { apply rel_pskl_close_pair.
    - apply rel_pskl_bubble_pair. exact Hrel.
    - exact Hb1V.
    - rewrite cols_l_app.
      assert (Hnl : β1 `notin` cols_l (restrict_pairs β1 β2 ρ))
        by apply restrict_pairs_notin_l.
      clear - Hb1a Hnl. fsetdec.
    - exact Hb2V.
    - rewrite cols_r_app.
      assert (Hnr : β2 `notin` cols_r (restrict_pairs β1 β2 ρ))
        by apply restrict_pairs_notin_r.
      clear - Hb2a Hnr. fsetdec. }
  eapply rel_pskl_mono; [ exact Hcl | | intros x Hx; exact Hx ].
  intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin];
    [ exact (Hia _ _ Hin) | apply Hir; eapply restrict_pairs_incl; exact Hin ].
Qed.

Lemma rel_a_cstrs_mono : forall ρ ρ' V V' C1 C2,
  rel_a_cstrs ρ V C1 C2 ->
  (forall a b, In (a, b) ρ -> In (a, b) ρ') ->
  V [<=] V' ->
  rel_a_cstrs ρ' V' C1 C2.
Proof.
  intros * H Hincl Hs; induction H; constructor;
    eauto using rel_a_cstr_mono.
Qed.

Lemma a_solve_cstr_generated_fresh_set : forall Θ C P Ξ P',
  {{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ P' }}a ->
  dom Ξ ∩ ftvar_in_aenv Θ [=] empty.
Proof.
  intros * H.
  apply AtomSetProperties.empty_is_empty_1.
  intros x Hx. apply AtomSetFacts.inter_iff in Hx. destruct Hx as [HA HB].
  exact (a_solve_cstr_generated_fresh H HA HB).
Qed.
