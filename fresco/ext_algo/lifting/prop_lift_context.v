Require Import src.fresco.prop_atom_sets.
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

Require Import src.fresco.ext_algo.subtyping.prop_solve_rel.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

Require Export src.fresco.ext_algo.lifting.prop_lift_look.

Definition rel_ptyp (ρ : list (atom * atom)) (V : atoms) (A1 A2 : ptyp)
  : Prop := rel_pskl ρ V (ptyp_to_pskl A1) (ptyp_to_pskl A2).

Inductive rel_abind (ρ : list (atom * atom)) (V : atoms) : abind -> abind -> Prop :=
| rel_abind__tvar : rel_abind ρ V abind_tvar abind_tvar
| rel_abind__flex : rel_abind ρ V abind_flex_mono abind_flex_mono
| rel_abind__flex_def : forall τ1 τ2,
    rel_ptyp ρ V τ1 τ2 ->
    rel_abind ρ V (abind_flex_mono_def τ1) (abind_flex_mono_def τ2)
| rel_abind__var_typ : forall A1 A2,
    rel_ptyp ρ V A1 A2 ->
    rel_abind ρ V (abind_var_typ A1) (abind_var_typ A2)
| rel_abind__var_skl : forall Q1 Q2,
    rel_pskl ρ V Q1 Q2 ->
    rel_abind ρ V (abind_var_skl Q1) (abind_var_skl Q2).

Inductive rel_aenv (ρ : list (atom * atom)) (V : atoms) : aenv -> aenv -> Prop :=
| rel_aenv__nil : rel_aenv ρ V nil nil
| rel_aenv__cons : forall a b b1 b2 Θ1 Θ2,
    rel_atom ρ V a b ->
    rel_abind ρ V b1 b2 ->
    rel_aenv ρ V Θ1 Θ2 ->
    rel_aenv ρ V ((a ~ b1) ++ Θ1) ((b ~ b2) ++ Θ2).

#[export] Hint Constructors rel_abind rel_aenv : core.

Lemma rel_ptyp_mono : forall ρ ρ' V V' A1 A2,
  rel_ptyp ρ V A1 A2 ->
  (forall α β, In (α, β) ρ -> In (α, β) ρ') ->
  V [<=] V' ->
  rel_ptyp ρ' V' A1 A2.
Proof. intros * H Hi Hs; eapply rel_pskl_mono; eauto. Qed.

Lemma rel_abind_mono : forall ρ ρ' V V' b1 b2,
  rel_abind ρ V b1 b2 ->
  (forall α β, In (α, β) ρ -> In (α, β) ρ') ->
  V [<=] V' ->
  rel_abind ρ' V' b1 b2.
Proof.
  intros * H Hi Hs; inversion H; subst; constructor;
    solve [ eapply rel_ptyp_mono; eauto | eapply rel_pskl_mono; eauto ].
Qed.

Lemma rel_aenv_mono : forall ρ ρ' V V' Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 ->
  (forall α β, In (α, β) ρ -> In (α, β) ρ') ->
  V [<=] V' ->
  rel_aenv ρ' V' Θ1 Θ2.
Proof.
  intros * H; induction H; intros Hi Hs; constructor; auto.
  - match goal with
    | Ha : rel_atom _ _ _ _ |- _ =>
        inversion Ha; subst;
        [ apply rel_atom__pair; auto | apply rel_atom__id; fsetdec ]
    end.
  - eapply rel_abind_mono; eauto.
Qed.

Lemma rel_aenv_widen : forall ρn ρ V Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 -> rel_aenv (ρn ++ ρ) V Θ1 Θ2.
Proof.
  intros * H. eapply rel_aenv_mono;
    [ exact H | intros a b Hin; apply in_or_app; right; exact Hin
    | intros x Hx; exact Hx ].
Qed.

Lemma rel_aenv_app : forall ρ V Θ1a Θ1b Θ2a Θ2b,
  rel_aenv ρ V Θ1a Θ2a -> rel_aenv ρ V Θ1b Θ2b ->
  rel_aenv ρ V (Θ1a ++ Θ1b) (Θ2a ++ Θ2b).
Proof.
  intros * Ha Hb; induction Ha; simpl; [ exact Hb | ].
  change (((a, b1) :: Θ1) ++ Θ1b) with ((a ~ b1) ++ (Θ1 ++ Θ1b)).
  change (((b, b2) :: Θ2) ++ Θ2b) with ((b ~ b2) ++ (Θ2 ++ Θ2b)).
  constructor; auto.
Qed.

Lemma rel_aenv_flex_pairs : forall ρn ρ V,
  rel_aenv (ρn ++ ρ) V (flex_pairs_l ρn) (flex_pairs_r ρn).
Proof.
  intros ρn. induction ρn as [ | [a b] ρn IH ]; intros ρ V; simpl;
    [ constructor | ].
  change ((a, abind_flex_mono) :: flex_pairs_l ρn)
    with ((a ~ abind_flex_mono) ++ flex_pairs_l ρn).
  change ((b, abind_flex_mono) :: flex_pairs_r ρn)
    with ((b ~ abind_flex_mono) ++ flex_pairs_r ρn).
  apply rel_aenv__cons;
    [ apply rel_atom__pair; left; reflexivity
    | apply rel_abind__flex
    | eapply rel_aenv_mono;
        [ apply (IH ρ V)
        | intros x y Hin; right; exact Hin
        | intros x Hx; exact Hx ] ].
Qed.

Lemma rel_aenv_binds_l : forall ρ V Θ1 Θ2 a b1,
  rel_aenv ρ V Θ1 Θ2 ->
  binds a b1 Θ1 ->
  exists b b2, rel_atom ρ V a b /\ rel_abind ρ V b1 b2 /\ binds b b2 Θ2.
Proof.
  intros * H; induction H; intros Hb; [ inversion Hb | ].
  unfold binds in Hb; simpl in Hb; destruct Hb as [Heq | Hb].
  - inversion Heq; subst. exists b, b2. repeat split; try assumption.
    unfold binds; simpl; left; reflexivity.
  - destruct (IHrel_aenv Hb) as (b' & b2' & Hat & Hab & Hbd).
    exists b', b2'. repeat split; try assumption.
    unfold binds in Hbd |- *; simpl; right; exact Hbd.
Qed.

Lemma rel_pskl_ftv_corr_r : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  forall b, b `in` ftvar_in_pskl P2 ->
  exists a, a `in` ftvar_in_pskl P1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V P1 P2 H; induction H; intros c Hc; simpl in Hc;
    try solve [ exfalso; clear - Hc; fsetdec ].
  - exists α. simpl. split; [ clear; fsetdec | ].
    assert (c = β) by (clear - Hc; fsetdec). subst c. assumption.
  - destruct (AtomSetProperties.In_dec c (ftvar_in_pskl Q1)) as [Hin | Hni].
    + destruct (IHrel_pskl1 c Hin) as (a & Ha & Hat).
      exists a. simpl. split; [ clear - Ha; fsetdec | exact Hat ].
    + destruct (IHrel_pskl2 c ltac:(clear - Hc Hni; fsetdec)) as (a & Ha & Hat).
      exists a. simpl. split; [ clear - Ha; fsetdec | exact Hat ].
  - destruct (IHrel_pskl c Hc) as (a & Ha & Hat).
    exists a. simpl. split; [ exact Ha | exact Hat ].
  - destruct (IHrel_pskl c Hc) as (a & Ha & Hat).
    exists a. simpl. split; [ exact Ha | exact Hat ].
Qed.

Lemma rel_pskl_ftv_corr_l : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  forall a, a `in` ftvar_in_pskl P1 ->
  exists b, b `in` ftvar_in_pskl P2 /\ rel_atom ρ V a b.
Proof.
  intros ρ V P1 P2 H; induction H; intros c Hc; simpl in Hc;
    try solve [ exfalso; clear - Hc; fsetdec ].
  - exists β. simpl. split; [ clear; fsetdec | ].
    assert (c = α) by (clear - Hc; fsetdec). subst c. assumption.
  - destruct (AtomSetProperties.In_dec c (ftvar_in_pskl P1)) as [Hin | Hni].
    + destruct (IHrel_pskl1 c Hin) as (b & Hb & Hat).
      exists b. simpl. split; [ clear - Hb; fsetdec | exact Hat ].
    + destruct (IHrel_pskl2 c ltac:(clear - Hc Hni; fsetdec)) as (b & Hb & Hat).
      exists b. simpl. split; [ clear - Hb; fsetdec | exact Hat ].
  - destruct (IHrel_pskl c Hc) as (b & Hb & Hat).
    exists b. simpl. split; [ exact Hb | exact Hat ].
  - destruct (IHrel_pskl c Hc) as (b & Hb & Hat).
    exists b. simpl. split; [ exact Hb | exact Hat ].
Qed.

Definition rel_atoms (ρ : list (atom * atom)) (V : atoms) (D1 D2 : atoms)
  : Prop := forall a b, rel_atom ρ V a b -> (a `in` D1 <-> b `in` D2).

Lemma rel_atoms_weaken : forall ρ ρ' V V' D1 D2,
  rel_atoms ρ V D1 D2 ->
  (forall a b, In (a, b) ρ' -> In (a, b) ρ) ->
  V' [<=] V ->
  rel_atoms ρ' V' D1 D2.
Proof.
  intros * H Hincl Hsub a b Hat. apply H.
  inversion Hat; subst;
    [ apply rel_atom__pair; auto | apply rel_atom__id; fsetdec ].
Qed.

Lemma rel_atoms_disjoint : forall ρ V D1 D2 P1 P2,
  rel_atoms ρ V D1 D2 ->
  rel_pskl ρ V P1 P2 ->
  D1 ∩ ftvar_in_pskl P1 [=] empty ->
  D2 ∩ ftvar_in_pskl P2 [=] empty.
Proof.
  intros * Hd Hr Hdisj.
  apply AtomSetProperties.empty_is_empty_1.
  intros x Hx. apply AtomSetFacts.inter_iff in Hx. destruct Hx as [HxD HxP].
  destruct (rel_pskl_ftv_corr_r Hr HxP) as (a & Ha & Hat).
  assert (HaD : a `in` D1) by (apply (Hd a x Hat); exact HxD).
  clear - Hdisj Ha HaD. fsetdec.
Qed.

Lemma rel_atom_cons_inv : forall β1 β2 ρ V a b,
  rel_atom ((β1, β2) :: ρ) V a b ->
  (a = β1 /\ b = β2) \/ rel_atom ρ V a b.
Proof.
  intros * H. inversion H; subst.
  - match goal with
    | Hin : In _ _ |- _ =>
        destruct Hin as [Heq | Hin];
          [ left; inversion Heq; split; reflexivity
          | right; apply rel_atom__pair; exact Hin ]
    end.
  - right. apply rel_atom__id. assumption.
Qed.

Lemma rel_atom_l_in : forall ρ V a b,
  rel_atom ρ V a b -> a `in` V ∪ cols_l ρ.
Proof.
  intros ρ V a b H; inversion H; subst.
  - match goal with
    | Hin : In _ _ |- _ => apply cols_l_in in Hin
    end. fsetdec.
  - fsetdec.
Qed.

Lemma rel_atom_r_in : forall ρ V a b,
  rel_atom ρ V a b -> b `in` V ∪ cols_r ρ.
Proof.
  intros ρ V a b H; inversion H; subst.
  - match goal with
    | Hin : In _ _ |- _ => apply cols_r_in in Hin
    end. fsetdec.
  - fsetdec.
Qed.

Lemma rel_atoms_push : forall ρ V D1 D2 β1 β2,
  rel_atoms ρ V D1 D2 ->
  β1 `notin` V -> β1 `notin` cols_l ρ ->
  β2 `notin` V -> β2 `notin` cols_r ρ ->
  rel_atoms ((β1, β2) :: ρ) V (add β1 D1) (add β2 D2).
Proof.
  intros * Hd Hb1V Hb1c Hb2V Hb2c a b Hat.
  destruct (rel_atom_cons_inv Hat) as [[-> ->] | Hat'].
  - split; intros _; clear; fsetdec.
  - pose proof (rel_atom_l_in Hat') as Hal.
    pose proof (rel_atom_r_in Hat') as Har.
    assert (Hne1 : a <> β1) by (clear - Hal Hb1V Hb1c; fsetdec).
    assert (Hne2 : b <> β2) by (clear - Har Hb2V Hb2c; fsetdec).
    destruct (Hd a b Hat') as [Hf Hg].
    split; intros Hin2.
    + assert (Ha1 : a `in` D1) by (clear - Hin2 Hne1; fsetdec).
      pose proof (Hf Ha1) as Hb2. clear - Hb2. fsetdec.
    + assert (Hb1 : b `in` D2) by (clear - Hin2 Hne2; fsetdec).
      pose proof (Hg Hb1) as Ha2. clear - Ha2. fsetdec.
Qed.

Lemma rel_pskl_shrink_V : forall ρ V V' P1 P2,
  rel_pskl ρ V P1 P2 ->
  (forall a, a `in` V -> a `in` ftvar_in_pskl P1 -> a `in` V') ->
  rel_pskl ρ V' P1 P2.
Proof.
  intros ρ V V' P1 P2 H; induction H; intros Hu; simpl in Hu;
    constructor;
    try (apply IHrel_pskl || (apply IHrel_pskl1 + apply IHrel_pskl2));
    try (intros a Ha Hf; apply Hu; [ exact Ha | simpl; clear - Hf; fsetdec ]).
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
  end.
  - apply rel_atom__pair; assumption.
  - apply rel_atom__id. apply Hu; [ assumption | simpl; clear; fsetdec ].
Qed.

Lemma rel_ptyp_shrink_V : forall ρ V V' A1 A2,
  rel_ptyp ρ V A1 A2 ->
  (forall a, a `in` V -> a `in` ftvar_in_ptyp A1 -> a `in` V') ->
  rel_ptyp ρ V' A1 A2.
Proof.
  intros * H Hu. unfold rel_ptyp in *.
  eapply rel_pskl_shrink_V; [ exact H | ].
  intros a Ha Hf. apply Hu; [ exact Ha | ].
  rewrite ftvar_ptyp_to_pskl in Hf. exact Hf.
Qed.

Lemma rel_abind_shrink_V : forall ρ V V' b1 b2,
  rel_abind ρ V b1 b2 ->
  (forall a, a `in` V -> a `in` ftvar_in_abind b1 -> a `in` V') ->
  rel_abind ρ V' b1 b2.
Proof.
  intros * H Hu; inversion H; subst; constructor;
    solve [ eapply rel_ptyp_shrink_V; [ eassumption | exact Hu ]
          | eapply rel_pskl_shrink_V; [ eassumption | exact Hu ] ].
Qed.

Lemma rel_aenv_shrink_V : forall ρ V V' Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 ->
  (forall a, a `in` V -> a `in` dom Θ1 ∪ ftvar_in_aenv Θ1 -> a `in` V') ->
  rel_aenv ρ V' Θ1 Θ2.
Proof.
  intros ρ V V' Θ1 Θ2 H; induction H; intros Hu; [ constructor | ].
  simpl in Hu. constructor.
  - match goal with
    | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
    end.
    + apply rel_atom__pair; assumption.
    + apply rel_atom__id. apply Hu; [ assumption | simpl; clear; fsetdec ].
  - eapply rel_abind_shrink_V; [ eassumption | ].
    intros x Hx Hf. apply Hu; [ exact Hx | simpl; clear - Hf; fsetdec ].
  - apply IHrel_aenv.
    intros x Hx Hf. apply Hu; [ exact Hx | simpl; clear - Hf; fsetdec ].
Qed.

Definition rel_inj (ρ : list (atom * atom)) (V : atoms) : Prop :=
  forall a1 a2 b, rel_atom ρ V a1 b -> rel_atom ρ V a2 b -> a1 = a2.

Definition rel_fun (ρ : list (atom * atom)) (V : atoms) (D : atoms) : Prop :=
  forall a b1 b2, a `in` D -> rel_atom ρ V a b1 -> rel_atom ρ V a b2 -> b1 = b2.

Lemma rel_atom_incl : forall ρ ρ' V a b,
  rel_atom ρ' V a b ->
  (forall x y, In (x, y) ρ' -> In (x, y) ρ) ->
  rel_atom ρ V a b.
Proof.
  intros ρ ρ' V a b H Hincl. inversion H; subst;
    [ apply rel_atom__pair; apply Hincl; assumption
    | apply rel_atom__id; assumption ].
Qed.

Lemma rel_inj_sub : forall ρ ρ' V,
  rel_inj ρ V ->
  (forall a b, In (a, b) ρ' -> In (a, b) ρ) ->
  rel_inj ρ' V.
Proof.
  intros ρ ρ' V H Hincl a1 a2 b H1 H2.
  exact (H a1 a2 b (rel_atom_incl ρ H1 Hincl) (rel_atom_incl ρ H2 Hincl)).
Qed.

Lemma rel_fun_weaken : forall ρ ρ' V D D',
  rel_fun ρ V D ->
  (forall a b, In (a, b) ρ' -> In (a, b) ρ) ->
  D' [<=] D ->
  rel_fun ρ' V D'.
Proof.
  intros ρ ρ' V D D' H Hincl Hsub a b1 b2 Ha H1 H2.
  exact (H a b1 b2 ltac:(clear - Ha Hsub; fsetdec)
           (rel_atom_incl ρ H1 Hincl) (rel_atom_incl ρ H2 Hincl)).
Qed.

Lemma rel_inj_push : forall β1 β2 ρ V,
  rel_inj ρ V ->
  β2 `notin` V ->
  β2 `notin` cols_r ρ ->
  rel_inj ((β1, β2) :: ρ) V.
Proof.
  intros β1 β2 ρ V H Hb2V Hb2c a1 a2 b H1 H2.
  destruct (rel_atom_cons_inv H1) as [[Ea1 Eb1] | H1'];
    destruct (rel_atom_cons_inv H2) as [[Ea2 Eb2] | H2']; subst.
  - reflexivity.
  - exfalso. pose proof (rel_atom_r_in H2') as Hr. clear - Hr Hb2V Hb2c. fsetdec.
  - exfalso. pose proof (rel_atom_r_in H1') as Hr. clear - Hr Hb2V Hb2c. fsetdec.
  - exact (H _ _ _ H1' H2').
Qed.

Lemma rel_fun_push : forall β1 β2 ρ V D,
  rel_fun ρ V D ->
  β1 `notin` V ->
  β1 `notin` cols_l ρ ->
  rel_fun ((β1, β2) :: ρ) V (add β1 D).
Proof.
  intros β1 β2 ρ V D H Hb1V Hb1c a b1 b2 Ha H1 H2.
  destruct (rel_atom_cons_inv H1) as [[Ea Eb] | H1'];
    destruct (rel_atom_cons_inv H2) as [[Ea2 Eb2] | H2']; subst.
  - reflexivity.
  - exfalso. pose proof (rel_atom_l_in H2') as Hl. clear - Hl Hb1V Hb1c. fsetdec.
  - exfalso. pose proof (rel_atom_l_in H1') as Hl. clear - Hl Hb1V Hb1c. fsetdec.
  - assert (Hne : a <> β1).
    { intros Heq. subst a. pose proof (rel_atom_l_in H1') as Hl.
      clear - Hl Hb1V Hb1c. fsetdec. }
    assert (Ha' : a `in` D) by (clear - Ha Hne; fsetdec).
    exact (H a b1 b2 Ha' H1' H2').
Qed.

Lemma rel_atom_inj_eq_r : forall ρ V β1 β2 a,
  rel_inj ρ V ->
  rel_atom ρ V β1 β2 ->
  rel_atom ρ V a β2 ->
  a = β1.
Proof. intros * Hinj H1 H2. exact (Hinj _ _ _ H2 H1). Qed.

Lemma rel_pskl_subst : forall ρ V P1 P2 T1 T2 β1 β2,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V T1 T2 ->
  rel_atom ρ V β1 β2 ->
  rel_inj ρ V ->
  (forall b, rel_atom ρ V β1 b -> b = β2) ->
  rel_pskl ρ V (subst_pskl_in_pskl T1 β1 P1) (subst_pskl_in_pskl T2 β2 P2).
Proof.
  intros ρ V P1 P2 T1 T2 β1 β2 H HT Hβ Hinj Hfun.
  induction H as [ | n | a b Hat | Pa Pb Qa Qb Ha IHa Hb IHb
                 | Pa Qa Ha IHa | | Pa Qa Ha IHa ]; simpl;
    try solve [ constructor; auto ].
  match goal with
  | |- context [ if ?X then _ else _ ] => destruct X as [Heq1 | Hne1]
  end;
  match goal with
  | |- context [ if ?X then _ else _ ] => destruct X as [Heq2 | Hne2]
  end.
  - exact HT.
  - exfalso. subst a. apply Hne2. exact (Hfun _ Hat).
  - exfalso. subst b. apply Hne1. exact (rel_atom_inj_eq_r Hinj Hβ Hat).
  - constructor. exact Hat.
Qed.

Lemma rel_ptyp_subst : forall ρ V A1 A2 τ1 τ2 β1 β2,
  rel_ptyp ρ V A1 A2 ->
  rel_ptyp ρ V τ1 τ2 ->
  rel_atom ρ V β1 β2 ->
  rel_inj ρ V ->
  (forall b, rel_atom ρ V β1 b -> b = β2) ->
  rel_ptyp ρ V (subst_ptyp_in_ptyp τ1 β1 A1) (subst_ptyp_in_ptyp τ2 β2 A2).
Proof.
  intros ρ V A1 A2 τ1 τ2 β1 β2 H HT Hβ Hinj Hfun. unfold rel_ptyp in *.
  rewrite 2 ptyp_to_pskl_subst.
  apply rel_pskl_subst; assumption.
Qed.

Lemma rel_aenv_cons_inv_l : forall ρ V a b1 Θ1 Θ2,
  rel_aenv ρ V ((a ~ b1) ++ Θ1) Θ2 ->
  exists b b2 Θ2',
    Θ2 = (b ~ b2) ++ Θ2'
    /\ rel_atom ρ V a b /\ rel_abind ρ V b1 b2 /\ rel_aenv ρ V Θ1 Θ2'.
Proof.
  intros ρ V a b1 Θ1 Θ2 H. inversion H; subst.
  do 3 eexists.
  split; [ reflexivity | ].
  split; [ eassumption | ].
  split; eassumption.
Qed.

Lemma rel_ptyp_restrict : forall ρ V A1 A2 β1 β2,
  rel_ptyp ρ V A1 A2 ->
  β1 `notin` ftvar_in_ptyp A1 ->
  β2 `notin` ftvar_in_ptyp A2 ->
  rel_ptyp (restrict_pairs β1 β2 ρ) V A1 A2.
Proof.
  intros ρ V A1 A2 β1 β2 H H1 H2. unfold rel_ptyp in *.
  apply rel_pskl_restrict;
    [ exact H
    | rewrite ftvar_ptyp_to_pskl; exact H1
    | rewrite ftvar_ptyp_to_pskl; exact H2 ].
Qed.

Lemma rel_abind_restrict : forall ρ V b1 b2 β1 β2,
  rel_abind ρ V b1 b2 ->
  β1 `notin` ftvar_in_abind b1 ->
  β2 `notin` ftvar_in_abind b2 ->
  rel_abind (restrict_pairs β1 β2 ρ) V b1 b2.
Proof.
  intros ρ V b1 b2 β1 β2 H Hf1 Hf2; inversion H; subst; simpl in Hf1, Hf2;
    constructor;
    solve [ apply rel_ptyp_restrict; assumption
          | apply rel_pskl_restrict; assumption ].
Qed.

Lemma rel_aenv_restrict : forall ρ V Θ1 Θ2 β1 β2,
  rel_aenv ρ V Θ1 Θ2 ->
  β1 `notin` ftvar_in_aenv Θ1 ->
  β2 `notin` ftvar_in_aenv Θ2 ->
  rel_aenv (restrict_pairs β1 β2 ρ) V Θ1 Θ2.
Proof.
  intros ρ V Θ1 Θ2 β1 β2 H; induction H; intros Hf1 Hf2; [ constructor | ].
  simpl in Hf1, Hf2. constructor.
  - match goal with
    | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
    end.
    + apply rel_atom__pair. apply List.filter_In. split; [ assumption | ].
      simpl.
      match goal with
      | |- context [ if ?X then _ else _ ] => destruct X as [Heq | Hne]
      end; [ exfalso; subst; clear - Hf1; fsetdec | ].
      match goal with
      | |- context [ if ?X then _ else _ ] => destruct X as [Heq' | Hne']
      end; [ exfalso; subst; clear - Hf2; fsetdec | ].
      reflexivity.
    + apply rel_atom__id. assumption.
  - apply rel_abind_restrict; [ assumption | clear - Hf1; fsetdec
                              | clear - Hf2; fsetdec ].
  - apply IHrel_aenv; [ clear - Hf1; fsetdec | clear - Hf2; fsetdec ].
Qed.

Definition rel_ext (ρe : list (atom * atom)) (W S : atoms) : Prop :=
  (forall a b, In (a, b) ρe -> a `notin` W /\ b `notin` S)
  /\ (forall a1 a2 b, In (a1, b) ρe -> In (a2, b) ρe -> a1 = a2)
  /\ (forall a b1 b2, In (a, b1) ρe -> In (a, b2) ρe -> b1 = b2).

Lemma rel_ext_mono : forall ρ ρ' W S W' S',
  rel_ext ρ W S ->
  (forall a b, In (a, b) ρ' -> In (a, b) ρ) ->
  W' [<=] W -> S' [<=] S -> rel_ext ρ' W' S'.
Proof.
  intros * (Hfresh & Hinj & Hfun) Hincl HW HS.
  split; [ | split ].
  - intros a b Hin. destruct (Hfresh _ _ (Hincl _ _ Hin)) as [Ha Hb].
    split; clear - Ha Hb HW HS; fsetdec.
  - intros a1 a2 b H1 H2. eapply Hinj; apply Hincl; eassumption.
  - intros a b1 b2 H1 H2. eapply Hfun; apply Hincl; eassumption.
Qed.

Lemma rel_ext_add_scope_l : forall ρ W S W' x,
  rel_ext ρ W S -> W' [<=] add x W ->
  (forall a b, In (a, b) ρ -> a <> x) -> rel_ext ρ W' S.
Proof.
  intros * (Hfresh & Hinj & Hfun) HW Hx.
  split; [ | split; assumption ].
  intros a b Hin. destruct (Hfresh _ _ Hin) as [Ha Hb].
  split; [ | exact Hb ].
  pose proof (Hx _ _ Hin) as Hne. clear - Ha HW Hne; fsetdec.
Qed.

Lemma rel_atom_app_inv : forall ρe ρ V a b,
  rel_atom (ρe ++ ρ) V a b -> In (a, b) ρe \/ rel_atom ρ V a b.
Proof.
  intros ρe ρ V a b H. inversion H; subst.
  - match goal with
    | Hin : In _ (ρe ++ ρ) |- _ =>
        apply in_app_or in Hin; destruct Hin as [Hin | Hin];
          [ left; exact Hin | right; apply rel_atom__pair; exact Hin ]
    end.
  - right. apply rel_atom__id. assumption.
Qed.

Lemma rel_inj_app : forall ρe ρ V W S,
  rel_inj ρ V ->
  rel_ext ρe W S ->
  V ∪ cols_r ρ [<=] S ->
  rel_inj (ρe ++ ρ) V.
Proof.
  intros ρe ρ V W S Hinj [Hfr [Hri _]] Hcov a1 a2 b H1 H2.
  destruct (rel_atom_app_inv ρe ρ H1) as [Hin1 | Hat1];
    destruct (rel_atom_app_inv ρe ρ H2) as [Hin2 | Hat2].
  - exact (Hri _ _ _ Hin1 Hin2).
  - exfalso. destruct (Hfr _ _ Hin1) as [_ Hb].
    pose proof (rel_atom_r_in Hat2) as Hr. clear - Hb Hr Hcov. fsetdec.
  - exfalso. destruct (Hfr _ _ Hin2) as [_ Hb].
    pose proof (rel_atom_r_in Hat1) as Hr. clear - Hb Hr Hcov. fsetdec.
  - exact (Hinj _ _ _ Hat1 Hat2).
Qed.

Lemma rel_atom_off_l : forall ρ V a,
  a `notin` cols_l ρ -> a `notin` V -> forall b, ~ rel_atom ρ V a b.
Proof.
  intros ρ V a Hc Hv b Hat.
  pose proof (rel_atom_l_in Hat) as Hin. clear - Hin Hc Hv. fsetdec.
Qed.

Lemma rel_fun_app : forall ρe ρ V D0 D1 W S,
  rel_fun ρ V D0 ->
  rel_ext ρe W S ->
  D0 [<=] W ->
  (forall a, a `in` D1 -> a `notin` D0 -> a `notin` cols_l ρ) ->
  (forall a, a `in` D1 -> a `notin` D0 -> a `notin` V) ->
  rel_fun (ρe ++ ρ) V D1.
Proof.
  intros ρe ρ V D0 D1 W S Hfun [Hfr [_ Hlf]] Hsub Hnc Hnv a b1 b2 Ha H1 H2.
  destruct (AtomSetProperties.In_dec a D0) as [HaD | HaD].
  - assert (Hnl : a `notin` cols_l ρe).
    { intros Hc. destruct (cols_l_in_inv _ _ Hc) as [y Hin].
      destruct (Hfr _ _ Hin) as [Hna _]. clear - Hna HaD Hsub. fsetdec. }
    assert (Hr1 : rel_atom ρ V a b1).
    { destruct (rel_atom_app_inv ρe ρ H1) as [Hin | Hat]; [ | exact Hat ].
      exfalso. apply Hnl. eapply cols_l_in; exact Hin. }
    assert (Hr2 : rel_atom ρ V a b2).
    { destruct (rel_atom_app_inv ρe ρ H2) as [Hin | Hat]; [ | exact Hat ].
      exfalso. apply Hnl. eapply cols_l_in; exact Hin. }
    exact (Hfun a b1 b2 HaD Hr1 Hr2).
  - pose proof (rel_atom_off_l (Hnc a Ha HaD) (Hnv a Ha HaD)) as Hoff.
    assert (Hin1 : In (a, b1) ρe).
    { destruct (rel_atom_app_inv ρe ρ H1) as [Hin | Hat]; [ exact Hin | ].
      exfalso. exact (Hoff b1 Hat). }
    assert (Hin2 : In (a, b2) ρe).
    { destruct (rel_atom_app_inv ρe ρ H2) as [Hin | Hat]; [ exact Hin | ].
      exfalso. exact (Hoff b2 Hat). }
    exact (Hlf _ _ _ Hin1 Hin2).
Qed.

Lemma rel_pskl_notin_r_inj : forall ρ V P1 P2 a b,
  rel_pskl ρ V P1 P2 ->
  rel_inj ρ V ->
  rel_atom ρ V a b ->
  a `notin` ftvar_in_pskl P1 ->
  b `notin` ftvar_in_pskl P2.
Proof.
  intros ρ V P1 P2 a b Hr Hinj Hat Ha Hb.
  destruct (rel_pskl_ftv_corr_r Hr Hb) as (a0 & Ha0 & Hat0).
  assert (a0 = a) by (exact (Hinj a0 a b Hat0 Hat)). subst a0. contradiction.
Qed.

Lemma rel_ptyp_mono_ptyp : forall ρ V A1 A2,
  rel_ptyp ρ V A1 A2 -> mono_ptyp A1 -> mono_ptyp A2.
Proof.
  intros ρ V A1 A2 H Hm. unfold rel_ptyp in H.
  generalize dependent A2.
  induction Hm as [ | a | B1 B2 Hm1 IH1 Hm2 IH2 ]; intros C H;
    destruct C; simpl in H;
    try solve [ inversion H ];
    try solve [ constructor ].
  inversion H; subst. constructor;
    [ eapply IH1; eassumption | eapply IH2; eassumption ].
Qed.

Lemma nodup_snd_inj : forall (ρ : list (atom * atom)) a1 a2 b,
  NoDup (List.map snd ρ) -> In (a1, b) ρ -> In (a2, b) ρ -> a1 = a2.
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros a1 a2 b Hnd H1 H2;
    [ contradiction | ].
  simpl in Hnd. inversion Hnd as [ | z l Hni Hnd' ]; subst.
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - injection E1 as Ex1 Ey1. injection E2 as Ex2 Ey2. subst. reflexivity.
  - exfalso. injection E1 as Ex1 Ey1. apply Hni. rewrite Ey1.
    exact (List.in_map snd ρ (a2, b) H2).
  - exfalso. injection E2 as Ex2 Ey2. apply Hni. rewrite Ey2.
    exact (List.in_map snd ρ (a1, b) H1).
  - exact (IH _ _ _ Hnd' H1 H2).
Qed.

Lemma nodup_fst_fun : forall (ρ : list (atom * atom)) a b1 b2,
  NoDup (List.map fst ρ) -> In (a, b1) ρ -> In (a, b2) ρ -> b1 = b2.
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros a b1 b2 Hnd H1 H2;
    [ contradiction | ].
  simpl in Hnd. inversion Hnd as [ | z l Hni Hnd' ]; subst.
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - injection E1 as Ex1 Ey1. injection E2 as Ex2 Ey2. subst. reflexivity.
  - exfalso. injection E1 as Ex1 Ey1. apply Hni. rewrite Ex1.
    exact (List.in_map fst ρ (a, b2) H2).
  - exfalso. injection E2 as Ex2 Ey2. apply Hni. rewrite Ex2.
    exact (List.in_map fst ρ (a, b1) H1).
  - exact (IH _ _ _ Hnd' H1 H2).
Qed.

Lemma a_flex_tvar_decls : forall Ξ x,
  a_decls Ξ -> (a_flex_tvar Ξ x <-> x `in` dom Ξ).
Proof.
  intros Ξ x H; induction H as [ | α1 Ξ H IH ]; split.
  - intros [Hb | [t Hb]]; inversion Hb.
  - simpl; intros Hx; exfalso; clear - Hx; fsetdec.
  - rewrite a_flex_tvar_app_iff. intros [Hh | Ht]; simpl.
    + assert (Hx : x = α1).
      { destruct Hh as [Hb | [t Hb]]; unfold binds in Hb; simpl in Hb;
          destruct Hb as [E | E]; try contradiction; inversion E; reflexivity. }
      subst; clear; fsetdec.
    + apply IH in Ht. clear - Ht. fsetdec.
  - intros Hx; simpl in Hx. rewrite a_flex_tvar_app_iff.
    destruct (x == α1) as [-> | Hne].
    + left. left. unfold binds; simpl; left; reflexivity.
    + right. apply IH. clear - Hx Hne. fsetdec.
Qed.

Lemma a_flex_tvar_solve_m : forall α (τ : ptyp) βs Ξ Θ0 x,
  x `notin` dom βs ->
  (a_flex_tvar ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0) x
   <-> a_flex_tvar (Ξ ++ (α ~ abind_flex_mono) ++ Θ0) x).
Proof.
  intros α τ βs Ξ Θ0 x Hx.
  rewrite ! a_flex_tvar_app_iff.
  rewrite (@a_flex_tvar_one_flex α (abind_flex_mono_def τ) x
             ltac:(right; exists τ; reflexivity)).
  rewrite (@a_flex_tvar_one_flex α abind_flex_mono x
             ltac:(left; reflexivity)).
  assert (Hnb := fun Hf => Hx (a_flex_tvar_in_dom Hf)).
  tauto.
Qed.

Lemma a_decls_flex_pairs_l : forall ρ, a_decls (flex_pairs_l ρ).
Proof.
  induction ρ as [ | [a b] ρ IH ]; simpl; [ constructor | ].
  change ((a, abind_flex_mono) :: flex_pairs_l ρ)
    with ((a ~ abind_flex_mono) ++ flex_pairs_l ρ).
  constructor. exact IH.
Qed.

Lemma a_decls_flex_pairs_r : forall ρ, a_decls (flex_pairs_r ρ).
Proof.
  induction ρ as [ | [a b] ρ IH ]; simpl; [ constructor | ].
  change ((b, abind_flex_mono) :: flex_pairs_r ρ)
    with ((b ~ abind_flex_mono) ++ flex_pairs_r ρ).
  constructor. exact IH.
Qed.

Lemma rel_aenv_dom_r_inv : forall ρ V Θ1 Θ2 b,
  rel_aenv ρ V Θ1 Θ2 -> b `in` dom Θ2 ->
  exists a, a `in` dom Θ1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V Θ1 Θ2 b H; induction H; intros Hb; simpl in Hb;
    [ exfalso; clear - Hb; fsetdec | ].
  destruct (b == b0) as [-> | Hne].
  - exists a. split; [ simpl; clear; fsetdec | assumption ].
  - destruct (IHrel_aenv ltac:(clear - Hb Hne; fsetdec)) as (x & Hx & Hat).
    exists x. split; [ simpl; clear - Hx; fsetdec | exact Hat ].
Qed.

Lemma rel_aenv_dom_l_inv : forall ρ V Θ1 Θ2 a,
  rel_aenv ρ V Θ1 Θ2 -> a `in` dom Θ1 ->
  exists b, b `in` dom Θ2 /\ rel_atom ρ V a b.
Proof.
  intros ρ V Θ1 Θ2 a H; induction H; intros Ha; simpl in Ha;
    [ exfalso; clear - Ha; fsetdec | ].
  destruct (a == a0) as [-> | Hne].
  - exists b. split; [ simpl; clear; fsetdec | assumption ].
  - destruct (IHrel_aenv ltac:(clear - Ha Hne; fsetdec)) as (y & Hy & Hat).
    exists y. split; [ simpl; clear - Hy; fsetdec | exact Hat ].
Qed.

Lemma rel_atom_mono_V : forall ρ V V' a b,
  rel_atom ρ V' a b -> V' [<=] V -> rel_atom ρ V a b.
Proof.
  intros ρ V V' a b H Hs; inversion H; subst;
    [ apply rel_atom__pair; assumption | apply rel_atom__id; fsetdec ].
Qed.

Lemma rel_inj_weaken_V : forall ρ V V',
  rel_inj ρ V -> V' [<=] V -> rel_inj ρ V'.
Proof.
  intros ρ V V' H Hs a1 a2 b H1 H2.
  exact (H a1 a2 b (rel_atom_mono_V H1 Hs) (rel_atom_mono_V H2 Hs)).
Qed.

Lemma rel_fun_weaken_V : forall ρ V V' D,
  rel_fun ρ V D -> V' [<=] V -> rel_fun ρ V' D.
Proof.
  intros ρ V V' D H Hs a b1 b2 Ha H1 H2.
  exact (H a b1 b2 Ha (rel_atom_mono_V H1 Hs) (rel_atom_mono_V H2 Hs)).
Qed.

Lemma flex_agree_rel_use : forall ρ V Θ1 Θ2 a b,
  flex_agree_rel ρ V Θ1 Θ2 ->
  rel_atom ρ V a b ->
  (a_flex_tvar Θ1 a <-> a_flex_tvar Θ2 b).
Proof.
  intros ρ V Θ1 Θ2 a b [HV Hp] Hat.
  inversion Hat as [x y Hin | x Hv]; subst.
  - exact (Hp _ _ Hin).
  - exact (HV _ Hv).
Qed.

Lemma a_flex_tvar_head_flexish : forall (c : atom) (bd : abind) (Θ : aenv),
  (bd = abind_flex_mono \/ exists t, bd = abind_flex_mono_def t) ->
  a_flex_tvar ((c ~ bd) ++ Θ) c.
Proof.
  intros c bd Θ [-> | [t ->]];
    [ left | right; exists t ]; unfold binds; simpl; left; reflexivity.
Qed.

Lemma a_decls_one : forall (α : atom), a_decls (α ~ abind_flex_mono).
Proof. intros α. simpl_env. constructor. constructor. Qed.

Lemma flex_agree_peel : forall ρ V V' Ξ Ξ' Θ0 Θ0'' (β b : atom) bd bd',
  flex_agree_rel ρ V (Ξ ++ (β ~ bd) ++ Θ0) (Ξ' ++ (b ~ bd') ++ Θ0'') ->
  rel_atom ρ V β b ->
  rel_inj ρ V ->
  (forall y, rel_atom ρ V β y -> y = b) ->
  β `notin` dom (Ξ ++ Θ0) ->
  b `notin` dom (Ξ' ++ Θ0'') ->
  V' [<=] V ->
  (forall x, x `in` V' -> x <> β) ->
  flex_agree_rel ρ V' (Ξ ++ Θ0) (Ξ' ++ Θ0'').
Proof.
  intros ρ V V' Ξ Ξ' Θ0 Θ0'' β b bd bd' Hagr Hab Hinj Hβfun Hβnd Hbnd HV Hne.
  split.
  - intros x HxV'.
    assert (HxV : x `in` V) by (clear - HxV' HV; fsetdec).
    pose proof (Hne x HxV') as Hnb.
    assert (Hnb2 : x <> b).
    { intros Ey. apply Hnb. rewrite Ey in HxV |- *. symmetry.
      exact (Hinj β b b Hab (@rel_atom__id ρ V b HxV)). }
    pose proof (proj1 Hagr x HxV) as Hx0.
    rewrite (@a_flex_tvar_mid_other Ξ β bd Θ0 x Hnb) in Hx0.
    rewrite (@a_flex_tvar_mid_other Ξ' b bd' Θ0'' x Hnb2) in Hx0.
    exact Hx0.
  - intros x y Hin.
    pose proof (proj2 Hagr x y Hin) as Hxy.
    destruct (x == β) as [Exβ | Hnb].
    + assert (Ey : y = b)
        by (apply Hβfun; rewrite <- Exβ; apply rel_atom__pair; exact Hin).
      rewrite Exβ, Ey.
      split; intros Hf; exfalso;
        [ exact (Hβnd (a_flex_tvar_in_dom Hf))
        | exact (Hbnd (a_flex_tvar_in_dom Hf)) ].
    + assert (Hnb2 : y <> b).
      { intros Ey. apply Hnb. rewrite Ey in Hin.
        exact (Hinj x β b (@rel_atom__pair ρ V x b Hin) Hab). }
      rewrite (@a_flex_tvar_mid_other Ξ β bd Θ0 x Hnb) in Hxy.
      rewrite (@a_flex_tvar_mid_other Ξ' b bd' Θ0'' y Hnb2) in Hxy.
      exact Hxy.
Qed.

Lemma flex_agree_reattach : forall ρ' V V' Θ1 Θ1' (β b : atom) bd bd',
  flex_agree_rel ρ' V' Θ1 Θ1' ->
  rel_atom ρ' V β b ->
  rel_inj ρ' V ->
  (forall y, rel_atom ρ' V β y -> y = b) ->
  (forall x, x `in` V -> x <> β -> x `in` V') ->
  (β `in` V -> b = β) ->
  (a_flex_tvar ((β ~ bd) ++ Θ1) β <-> a_flex_tvar ((b ~ bd') ++ Θ1') b) ->
  flex_agree_rel ρ' V ((β ~ bd) ++ Θ1) ((b ~ bd') ++ Θ1').
Proof.
  intros ρ' V V' Θ1 Θ1' β b bd bd' Hagr Hab Hinj Hβfun Hsplit Hβb Hhead.
  split.
  - intros x HxV. destruct (x == β) as [Ex | Hnb].
    + rewrite Ex in HxV |- *. pose proof (Hβb HxV) as Eb.
      rewrite Eb in Hhead. rewrite Eb. exact Hhead.
    + assert (Hnb2 : x <> b).
      { intros Ey. apply Hnb. rewrite Ey in HxV |- *. symmetry.
        exact (Hinj β b b Hab (@rel_atom__id ρ' V b HxV)). }
      rewrite (@a_flex_tvar_cons_other β bd Θ1 x Hnb).
      rewrite (@a_flex_tvar_cons_other b bd' Θ1' x Hnb2).
      apply (proj1 Hagr x). apply Hsplit; assumption.
  - intros x y Hin.
    destruct (x == β) as [Exβ | Hnb].
    + assert (Ey : y = b)
        by (apply Hβfun; rewrite <- Exβ; apply rel_atom__pair; exact Hin).
      rewrite Exβ, Ey. exact Hhead.
    + assert (Hnb2 : y <> b).
      { intros Ey. apply Hnb. rewrite Ey in Hin.
        exact (Hinj x β b (@rel_atom__pair ρ' V x b Hin) Hab). }
      rewrite (@a_flex_tvar_cons_other β bd Θ1 x Hnb).
      rewrite (@a_flex_tvar_cons_other b bd' Θ1' y Hnb2).
      exact (proj2 Hagr x y Hin).
Qed.

Lemma rel_pskl_shrink_V_id : forall ρ V V' P1 P2 x,
  rel_pskl ρ V P1 P2 ->
  (forall a, a `in` V -> a `in` ftvar_in_pskl P1 -> a = x \/ a `in` V') ->
  rel_pskl ((x, x) :: ρ) V' P1 P2.
Proof.
  intros ρ V V' P1 P2 x H; induction H; intros Hu; simpl in Hu;
    constructor;
    try (apply IHrel_pskl || (apply IHrel_pskl1 + apply IHrel_pskl2));
    try (intros a Ha Hf; apply Hu; [ exact Ha | simpl; clear - Hf; fsetdec ]).
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
  end.
  - apply rel_atom__pair. right. assumption.
  - match goal with
    | Hv : ?a `in` V |- _ =>
        destruct (Hu a Hv ltac:(simpl; clear; fsetdec)) as [Ex | HV']
    end.
    + subst. apply rel_atom__pair. left. reflexivity.
    + apply rel_atom__id. exact HV'.
Qed.

Lemma rel_atom_drop_id : forall ρa ρb V x a b,
  rel_atom (ρa ++ (x, x) :: ρb) V a b ->
  x `in` V ->
  rel_atom (ρa ++ ρb) V a b.
Proof.
  intros ρa ρb V x a b H Hx.
  inversion H as [x0 y0 Hin | x0 Hv]; subst.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply rel_atom__pair. apply in_or_app. left. exact Hin.
    + destruct Hin as [E | Hin].
      * inversion E; subst. apply rel_atom__id. exact Hx.
      * apply rel_atom__pair. apply in_or_app. right. exact Hin.
  - apply rel_atom__id. assumption.
Qed.

Lemma rel_pskl_drop_id : forall ρa ρb V x P1 P2,
  rel_pskl (ρa ++ (x, x) :: ρb) V P1 P2 ->
  x `in` V ->
  rel_pskl (ρa ++ ρb) V P1 P2.
Proof.
  intros ρa ρb V x P1 P2 H Hx.
  remember (ρa ++ (x, x) :: ρb) as ρ eqn:Eρ.
  induction H; subst; constructor; auto.
  eapply rel_atom_drop_id; [ eassumption | exact Hx ].
Qed.

Lemma rel_ptyp_drop_id : forall ρa ρb V x A1 A2,
  rel_ptyp (ρa ++ (x, x) :: ρb) V A1 A2 ->
  x `in` V ->
  rel_ptyp (ρa ++ ρb) V A1 A2.
Proof.
  intros * H Hx. unfold rel_ptyp in *. eapply rel_pskl_drop_id; eauto.
Qed.

Lemma rel_abind_drop_id : forall ρa ρb V x b1 b2,
  rel_abind (ρa ++ (x, x) :: ρb) V b1 b2 ->
  x `in` V ->
  rel_abind (ρa ++ ρb) V b1 b2.
Proof.
  intros * H Hx; inversion H; subst; constructor;
    solve [ eapply rel_ptyp_drop_id; eauto | eapply rel_pskl_drop_id; eauto ].
Qed.

Lemma rel_aenv_drop_id : forall ρa ρb V x Θ1 Θ2,
  rel_aenv (ρa ++ (x, x) :: ρb) V Θ1 Θ2 ->
  x `in` V ->
  rel_aenv (ρa ++ ρb) V Θ1 Θ2.
Proof.
  intros ρa ρb V x Θ1 Θ2 H Hx.
  remember (ρa ++ (x, x) :: ρb) as ρ eqn:Eρ.
  induction H; subst; constructor; auto.
  - eapply rel_atom_drop_id; [ eassumption | exact Hx ].
  - eapply rel_abind_drop_id; [ eassumption | exact Hx ].
Qed.

Lemma flex_agree_rel_push_id_absent : forall ρ V x Θ1 Θ2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  x `notin` dom Θ1 -> x `notin` dom Θ2 ->
  flex_agree_rel ((x, x) :: ρ) V Θ1 Θ2.
Proof.
  intros ρ V x Θ1 Θ2 [HV Hp] H1 H2. split; [ exact HV | ].
  intros a b Hin. destruct Hin as [E | Hin].
  - inversion E; subst. split; intros Hf; exfalso;
      [ exact (H1 (a_flex_tvar_in_dom Hf))
      | exact (H2 (a_flex_tvar_in_dom Hf)) ].
  - exact (Hp a b Hin).
Qed.

Lemma rel_inj_push_id : forall ρ V V' x,
  rel_inj ρ V -> x `in` V -> V' [<=] V -> rel_inj ((x, x) :: ρ) V'.
Proof.
  intros ρ V V' x Hinj Hx HV a1 a2 b H1 H2.
  destruct (rel_atom_cons_inv H1) as [[E1a E1b] | H1'];
    destruct (rel_atom_cons_inv H2) as [[E2a E2b] | H2']; subst.
  - reflexivity.
  - symmetry. exact (Hinj a2 x x (rel_atom_mono_V H2' HV)
                       (@rel_atom__id ρ V x Hx)).
  - exact (Hinj a1 x x (rel_atom_mono_V H1' HV) (@rel_atom__id ρ V x Hx)).
  - exact (Hinj a1 a2 b (rel_atom_mono_V H1' HV) (rel_atom_mono_V H2' HV)).
Qed.

Lemma rel_fun_push_absent : forall ρ V V' D x,
  rel_fun ρ V D -> V' [<=] V -> x `notin` D -> rel_fun ((x, x) :: ρ) V' D.
Proof.
  intros ρ V V' D x Hfun HV Hx a b1 b2 Ha H1 H2.
  destruct (rel_atom_cons_inv H1) as [[E1a E1b] | H1'];
    destruct (rel_atom_cons_inv H2) as [[E2a E2b] | H2']; subst;
    try (exfalso; contradiction).
  exact (Hfun a b1 b2 Ha (rel_atom_mono_V H1' HV) (rel_atom_mono_V H2' HV)).
Qed.

Lemma a_flex_tvar_mid_nonflex_absurd : forall Ξ (c : atom) (bd : abind) Θ,
  uniq (Ξ ++ (c ~ bd) ++ Θ) ->
  bd <> abind_flex_mono ->
  (forall t, bd <> abind_flex_mono_def t) ->
  ~ a_flex_tvar (Ξ ++ (c ~ bd) ++ Θ) c.
Proof.
  intros Ξ c bd Θ Huq H1 H2 Hf.
  assert (HcΞ : c `notin` dom Ξ).
  { assert (Hd : disjoint Ξ ((c ~ bd) ++ Θ)) by (clear - Huq; solve_uniq).
    unfold disjoint in Hd. repeat rewrite dom_app in Hd. simpl in Hd.
    clear - Hd. fsetdec. }
  assert (HcΘ : c `notin` dom Θ).
  { assert (Hd : uniq ((c ~ bd) ++ Θ)) by (clear - Huq; solve_uniq).
    clear - Hd. destruct_uniq. fsetdec. }
  rewrite ! a_flex_tvar_app_iff in Hf.
  destruct Hf as [Hf | [Hf | Hf]].
  - exact (HcΞ (a_flex_tvar_in_dom Hf)).
  - exact (@a_flex_tvar_one_nonflex c bd c H1 H2 Hf).
  - exact (HcΘ (a_flex_tvar_in_dom Hf)).
Qed.

Lemma a_wf_aenv_mid_var_typ_inv : forall Ξ x A Θ,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ (x ~ abind_var_typ A) ++ Θ) }}a ->
  a_wf_ptyp Θ A.
Proof.
  intros Ξ x A Θ Hdecl; revert x A Θ; induction Hdecl; intros * Hwf;
    simpl_env in *.
  - inversion Hwf; subst. assumption.
  - inversion Hwf; subst.
    match goal with
    | Hw : {{ ⊢ _ }}a |- _ => eapply IHHdecl; exact Hw
    end.
Qed.

Lemma a_wf_aenv_mid_var_skl_inv : forall Ξ x Q Θ,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ (x ~ abind_var_skl Q) ++ Θ) }}a ->
  {{ Θ ⨟ empty ⊢ₚₛ Q }}a.
Proof.
  intros Ξ x Q Θ Hdecl; revert x Q Θ; induction Hdecl; intros * Hwf;
    simpl_env in *.
  - inversion Hwf; subst. assumption.
  - inversion Hwf; subst.
    match goal with
    | Hw : {{ ⊢ _ }}a |- _ => eapply IHHdecl; exact Hw
    end.
Qed.

Lemma a_flex_tvar_head_swap_flexish : forall (c : atom) bd bd2 (Θ : aenv) y,
  (bd = abind_flex_mono \/ exists t, bd = abind_flex_mono_def t) ->
  (bd2 = abind_flex_mono \/ exists t, bd2 = abind_flex_mono_def t) ->
  (a_flex_tvar ((c ~ bd) ++ Θ) y <-> a_flex_tvar ((c ~ bd2) ++ Θ) y).
Proof.
  intros c bd bd2 Θ y H1 H2.
  rewrite ! a_flex_tvar_app_iff.
  rewrite (@a_flex_tvar_one_flex c bd y H1).
  rewrite (@a_flex_tvar_one_flex c bd2 y H2).
  tauto.
Qed.

Lemma flex_agree_peel_cons : forall ρ V V' Θ0 Θ0'' (β b : atom) bd bd',
  flex_agree_rel ρ V ((β ~ bd) ++ Θ0) ((b ~ bd') ++ Θ0'') ->
  rel_atom ρ V β b ->
  rel_inj ρ V ->
  (forall y, rel_atom ρ V β y -> y = b) ->
  β `notin` dom Θ0 ->
  b `notin` dom Θ0'' ->
  V' [<=] V ->
  (forall y, y `in` V' -> y <> β) ->
  flex_agree_rel ρ V' Θ0 Θ0''.
Proof.
  intros ρ V V' Θ0 Θ0'' β b bd bd' Hagr Hab Hinj Hfun Hβn Hbn HV Hne.
  eapply (@flex_agree_peel ρ V V' nil nil Θ0 Θ0'' β b bd bd');
    simpl_env; eassumption.
Qed.

Lemma flex_agree_rel_head_swap : forall ρ V (c d : atom) bd bd' bd2 bd2' Θ1 Θ2,
  flex_agree_rel ρ V ((c ~ bd) ++ Θ1) ((d ~ bd') ++ Θ2) ->
  (bd = abind_flex_mono \/ exists t, bd = abind_flex_mono_def t) ->
  (bd2 = abind_flex_mono \/ exists t, bd2 = abind_flex_mono_def t) ->
  (bd' = abind_flex_mono \/ exists t, bd' = abind_flex_mono_def t) ->
  (bd2' = abind_flex_mono \/ exists t, bd2' = abind_flex_mono_def t) ->
  flex_agree_rel ρ V ((c ~ bd2) ++ Θ1) ((d ~ bd2') ++ Θ2).
Proof.
  intros ρ V c d bd bd' bd2 bd2' Θ1 Θ2 [HV Hp] F1 F2 F3 F4. split.
  - intros y Hy.
    rewrite <- (@a_flex_tvar_head_swap_flexish c bd bd2 Θ1 y F1 F2).
    rewrite <- (@a_flex_tvar_head_swap_flexish d bd' bd2' Θ2 y F3 F4).
    exact (HV y Hy).
  - intros a b0 Hin.
    rewrite <- (@a_flex_tvar_head_swap_flexish c bd bd2 Θ1 a F1 F2).
    rewrite <- (@a_flex_tvar_head_swap_flexish d bd' bd2' Θ2 b0 F3 F4).
    exact (Hp a b0 Hin).
Qed.

Lemma a_wf_aenv_cons_payload_ftv : forall (c : atom) bd (Θ : aenv),
  {{ ⊢ ((c ~ bd) ++ Θ) }}a -> ftvar_in_abind bd [<=] dom Θ.
Proof.
  intros c bd Θ H; inversion H; subst; simpl;
    try solve [ clear; fsetdec ].
  - apply a_wf_ptyp_ftv_dom; assumption.
  - pose proof (a_wf_pskl_ftv_dom ltac:(eassumption)) as Hs.
    clear - Hs. fsetdec.
  - apply a_wf_ptyp_ftv_dom; assumption.
Qed.

Lemma a_binds_tvar_not_var_typ : forall (Θ : aenv) x A,
  uniq Θ -> binds x (abind_var_typ A) Θ -> ~ a_binds_tvar x Θ.
Proof.
  intros Θ x A Hu Hb [Hb2 | [Hb2 | [t Hb2]]];
    pose proof (binds_unique _ _ _ _ _ Hb Hb2 Hu) as E; discriminate.
Qed.

Lemma a_binds_tvar_not_var_skl : forall (Θ : aenv) x Q,
  uniq Θ -> binds x (abind_var_skl Q) Θ -> ~ a_binds_tvar x Θ.
Proof.
  intros Θ x Q Hu Hb [Hb2 | [Hb2 | [t Hb2]]];
    pose proof (binds_unique _ _ _ _ _ Hb Hb2 Hu) as E; discriminate.
Qed.

Lemma rel_atoms_app : forall ρe ρ V D1 D2 W S,
  rel_atoms ρ V D1 D2 ->
  rel_ext ρe W S ->
  D1 [<=] W -> D2 [<=] S ->
  rel_atoms (ρe ++ ρ) V D1 D2.
Proof.
  intros ρe ρ V D1 D2 W S Hd [Hfr _] H1 H2 a b Hat.
  destruct (rel_atom_app_inv ρe ρ Hat) as [Hin | Hat'].
  - destruct (Hfr _ _ Hin) as [Ha Hb].
    split; intros Hc; exfalso; [ clear - Ha H1 Hc | clear - Hb H2 Hc ];
      fsetdec.
  - exact (Hd a b Hat').
Qed.

Lemma a_isub_wf_pskl : forall Θ Θ' Δ P,
  a_isub Θ Θ' -> {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros Θ Θ' Δ P [[κ [Hid Hinc]] _] Hwf.
  eapply a_wf_pskl_tvar_mono; [ exact Hwf | ].
  intros α Htv. eapply a_inc_binds_tvarish; eassumption.
Qed.

Lemma rel_ext_app : forall ρe2 ρe1 W1 W2 S1 S2,
  rel_ext ρe1 W1 S1 ->
  rel_ext ρe2 W2 S2 ->
  W1 [<=] W2 -> S1 [<=] S2 ->
  (forall a b, In (a, b) ρe1 -> a `in` W2 /\ b `in` S2) ->
  rel_ext (ρe2 ++ ρe1) W1 S1.
Proof.
  intros ρe2 ρe1 W1 W2 S1 S2 [Hfr1 [Hri1 Hlf1]] [Hfr2 [Hri2 Hlf2]] HW HS Hin1.
  unfold rel_ext. split; [ | split ].
  - intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (Hfr2 _ _ Hin) as [Ha Hb].
      split; [ clear - Ha HW; fsetdec | clear - Hb HS; fsetdec ].
    + exact (Hfr1 _ _ Hin).
  - intros a1 a2 b Hi1 Hi2. apply in_app_or in Hi1. apply in_app_or in Hi2.
    destruct Hi1 as [Hi1 | Hi1]; destruct Hi2 as [Hi2 | Hi2].
    + exact (Hri2 _ _ _ Hi1 Hi2).
    + exfalso. destruct (Hfr2 _ _ Hi1) as [_ Hb].
      destruct (Hin1 _ _ Hi2) as [_ Hb2]. contradiction.
    + exfalso. destruct (Hfr2 _ _ Hi2) as [_ Hb].
      destruct (Hin1 _ _ Hi1) as [_ Hb2]. contradiction.
    + exact (Hri1 _ _ _ Hi1 Hi2).
  - intros a b1 b2 Hi1 Hi2. apply in_app_or in Hi1. apply in_app_or in Hi2.
    destruct Hi1 as [Hi1 | Hi1]; destruct Hi2 as [Hi2 | Hi2].
    + exact (Hlf2 _ _ _ Hi1 Hi2).
    + exfalso. destruct (Hfr2 _ _ Hi1) as [Ha _].
      destruct (Hin1 _ _ Hi2) as [Ha2 _]. contradiction.
    + exfalso. destruct (Hfr2 _ _ Hi2) as [Ha _].
      destruct (Hin1 _ _ Hi1) as [Ha2 _]. contradiction.
    + exact (Hlf1 _ _ _ Hi1 Hi2).
Qed.

Lemma rel_ptyp_ftv_corr_r : forall ρ V A1 A2,
  rel_ptyp ρ V A1 A2 ->
  forall b, b `in` ftvar_in_ptyp A2 ->
  exists a, a `in` ftvar_in_ptyp A1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V A1 A2 H b Hb. unfold rel_ptyp in H.
  rewrite <- ftvar_ptyp_to_pskl in Hb.
  destruct (rel_pskl_ftv_corr_r H Hb) as (a & Ha & Hat).
  exists a. rewrite ftvar_ptyp_to_pskl in Ha. split; assumption.
Qed.

Lemma rel_abind_ftv_corr_r : forall ρ V b1 b2,
  rel_abind ρ V b1 b2 ->
  forall b, b `in` ftvar_in_abind b2 ->
  exists a, a `in` ftvar_in_abind b1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V b1 b2 H b Hb; inversion H; subst; simpl in Hb |- *;
    try solve [ exfalso; clear - Hb; fsetdec ];
    solve [ eapply rel_ptyp_ftv_corr_r; eassumption
          | eapply rel_pskl_ftv_corr_r; eassumption ].
Qed.

Lemma rel_aenv_ftv_corr_r : forall ρ V Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 ->
  forall b, b `in` ftvar_in_aenv Θ2 ->
  exists a, a `in` ftvar_in_aenv Θ1 /\ rel_atom ρ V a b.
Proof.
  intros ρ V Θ1 Θ2 H; induction H; intros y Hy; simpl in Hy;
    [ exfalso; clear - Hy; fsetdec | ].
  simpl.
  destruct (y == b) as [-> | Hne].
  - exists a. split; [ clear; fsetdec | assumption ].
  - destruct (AtomSetProperties.In_dec y (ftvar_in_abind b2)) as [Hin | Hni].
    + destruct (rel_abind_ftv_corr_r H0 Hin) as (x & Hx & Hat).
      exists x. split; [ clear - Hx; fsetdec | exact Hat ].
    + destruct (IHrel_aenv y ltac:(clear - Hy Hne Hni; fsetdec))
        as (x & Hx & Hat).
      exists x. split; [ clear - Hx; fsetdec | exact Hat ].
Qed.

Lemma restrict_pairs_in : forall b1 b2 rho a b,
  In (a, b) rho -> a <> b1 -> b <> b2 -> In (a, b) (restrict_pairs b1 b2 rho).
Proof.
  intros b1 b2 rho a b Hin H1 H2. unfold restrict_pairs.
  apply List.filter_In. split; [ exact Hin | ]. simpl.
  match goal with |- context [ if ?X then _ else _ ] => destruct X end;
    [ contradiction | ].
  match goal with |- context [ if ?X then _ else _ ] => destruct X end;
    [ contradiction | reflexivity ].
Qed.

Lemma rel_atoms_push_absent : forall ρ V D1 D2 β1 β2,
  rel_atoms ρ V D1 D2 ->
  β1 `notin` V -> β1 `notin` cols_l ρ ->
  β2 `notin` V -> β2 `notin` cols_r ρ ->
  β1 `notin` D1 -> β2 `notin` D2 ->
  rel_atoms ((β1, β2) :: ρ) V D1 D2.
Proof.
  intros ρ V D1 D2 β1 β2 Hd Hb1V Hb1c Hb2V Hb2c Hb1D Hb2D a b Hat.
  destruct (rel_atom_cons_inv Hat) as [[-> ->] | Hat'].
  - split; intros Hin; exfalso; [ exact (Hb1D Hin) | exact (Hb2D Hin) ].
  - exact (Hd a b Hat').
Qed.

Definition restrict_l (D : atoms) (ρ : list (atom * atom))
  : list (atom * atom) :=
  List.filter (fun p => negb (AtomSetImpl.mem (fst p) D)) ρ.

Arguments restrict_l : simpl never.

Lemma restrict_l_incl : forall D ρ a b,
  In (a, b) (restrict_l D ρ) -> In (a, b) ρ.
Proof. intros * Hin. apply List.filter_In in Hin. tauto. Qed.

Lemma restrict_l_in : forall D ρ a b,
  In (a, b) ρ -> a `notin` D -> In (a, b) (restrict_l D ρ).
Proof.
  intros D ρ a b Hin Hn. unfold restrict_l. apply List.filter_In.
  split; [ exact Hin | ]. simpl.
  destruct (AtomSetImpl.mem a D) eqn:E; [ | reflexivity ].
  exfalso. apply Hn. apply AtomSetFacts.mem_iff. exact E.
Qed.

Lemma restrict_l_notin : forall D ρ a,
  a `in` D -> a `notin` cols_l (restrict_l D ρ).
Proof.
  intros D ρ a Ha. apply cols_l_fresh. intros x y Hin Ex. subst x.
  apply List.filter_In in Hin. destruct Hin as [_ Hb]. simpl in Hb.
  destruct (AtomSetImpl.mem a D) eqn:E; [ discriminate | ].
  rewrite <- AtomSetFacts.not_mem_iff in E. contradiction.
Qed.

Lemma restrict_l_app_restore : forall D ρe ρ0 ρ,
  (forall a b, In (a, b) ρ0 -> In (a, b) ρ) ->
  forall a b, In (a, b) (restrict_l D (ρe ++ ρ0)) ->
    In (a, b) (restrict_l D ρe ++ ρ).
Proof.
  intros * Hbase a b Hin.
  assert (Ha : a `notin` D).
  { intros Ha. apply (restrict_l_notin (ρe ++ ρ0) Ha).
    eapply cols_l_in; exact Hin. }
  apply restrict_l_incl in Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | Hin]; apply in_or_app;
    [ left; apply restrict_l_in; auto | right; apply Hbase; exact Hin ].
Qed.

Lemma rel_ext_restrict_l : forall D ρ W S,
  rel_ext ρ W S -> rel_ext (restrict_l D ρ) W S.
Proof.
  intros * Hext. eapply rel_ext_mono;
    [ exact Hext | intros a b Hin; eapply restrict_l_incl; exact Hin
    | intros a Ha; exact Ha | intros a Ha; exact Ha ].
Qed.

Lemma rel_aenv_restrict_l_dom : forall ρ V Ξ Ξ' Θ Θ' ρe,
  rel_aenv ρ V Ξ Ξ' -> rel_inj ρ V ->
  (forall a b, In (a, b) ρe -> In (a, b) ρ) ->
  (forall a b, In (a, b) ρe ->
    a `in` dom (Ξ ++ Θ) /\ b `in` dom (Ξ' ++ Θ')) ->
  forall a b, In (a, b) (restrict_l (dom Ξ) ρe) ->
    a `in` dom Θ /\ b `in` dom Θ'.
Proof.
  intros * Hrel Hinj Hincl Hdom a b Hin.
  assert (Ha : a `notin` dom Ξ).
  { intros Ha. apply (restrict_l_notin ρe Ha). eapply cols_l_in; exact Hin. }
  apply restrict_l_incl in Hin.
  assert (Hb : b `notin` dom Ξ').
  { intros Hb. destruct (rel_aenv_dom_r_inv Hrel Hb) as (a' & Ha' & Hat).
    assert (Heq : a' = a).
    { eapply Hinj; [ exact Hat | constructor; apply Hincl; exact Hin ]. }
    subst a'. exact (Ha Ha'). }
  destruct (Hdom _ _ Hin) as [Hd1 Hd2].
  rewrite dom_app in Hd1, Hd2.
  split; [ clear - Hd1 Ha; fsetdec | clear - Hd2 Hb; fsetdec ].
Qed.

Lemma cols_l_restrict_l : forall D ρ, cols_l (restrict_l D ρ) [<=] cols_l ρ.
Proof.
  intros D ρ x Hx. destruct (cols_l_in_inv _ _ Hx) as [y Hin].
  eapply cols_l_in. eapply restrict_l_incl. exact Hin.
Qed.

Lemma cols_r_restrict_l : forall D ρ, cols_r (restrict_l D ρ) [<=] cols_r ρ.
Proof.
  intros D ρ x Hx. destruct (cols_r_in_inv _ _ Hx) as [y Hin].
  eapply cols_r_in. eapply restrict_l_incl. exact Hin.
Qed.

Lemma rel_atom_restrict_l : forall D ρ V a b,
  rel_atom ρ V a b -> a `notin` D -> rel_atom (restrict_l D ρ) V a b.
Proof.
  intros D ρ V a b Hat Hn. inversion Hat; subst;
    [ apply rel_atom__pair; apply restrict_l_in; assumption
    | apply rel_atom__id; assumption ].
Qed.

Lemma rel_pskl_restrict_l : forall D ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> D ∩ ftvar_in_pskl P1 [=] empty ->
  rel_pskl (restrict_l D ρ) V P1 P2.
Proof.
  intros D ρ V P1 P2 H; induction H; intros Hd; simpl in Hd;
    try solve [ constructor ].
  - apply rel_pskl__var_f. apply rel_atom_restrict_l;
      [ assumption | clear - Hd; fsetdec ].
  - constructor; [ apply IHrel_pskl1 | apply IHrel_pskl2 ];
      clear - Hd; fsetdec.
  - constructor; apply IHrel_pskl; clear - Hd; fsetdec.
  - constructor; apply IHrel_pskl; clear - Hd; fsetdec.
Qed.

Lemma rel_ptyp_restrict_l : forall D ρ V A1 A2,
  rel_ptyp ρ V A1 A2 -> D ∩ ftvar_in_ptyp A1 [=] empty ->
  rel_ptyp (restrict_l D ρ) V A1 A2.
Proof.
  intros D ρ V A1 A2 H Hd. unfold rel_ptyp in H |- *.
  apply rel_pskl_restrict_l; [ exact H | ].
  rewrite ftvar_ptyp_to_pskl. exact Hd.
Qed.

Lemma rel_abind_restrict_l : forall D ρ V b1 b2,
  rel_abind ρ V b1 b2 -> D ∩ ftvar_in_abind b1 [=] empty ->
  rel_abind (restrict_l D ρ) V b1 b2.
Proof.
  intros D ρ V b1 b2 H Hd; inversion H; subst; simpl in Hd; constructor;
    solve [ apply rel_ptyp_restrict_l; assumption
          | apply rel_pskl_restrict_l; assumption ].
Qed.

Lemma rel_aenv_restrict_l : forall D ρ V Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 -> D ∩ ftvar_in_aenv Θ1 [=] empty ->
  rel_aenv (restrict_l D ρ) V Θ1 Θ2.
Proof.
  intros D ρ V Θ1 Θ2 H; induction H; intros Hd; [ constructor | ].
  simpl in Hd. constructor.
  - apply rel_atom_restrict_l; [ assumption | clear - Hd; fsetdec ].
  - apply rel_abind_restrict_l; [ assumption | clear - Hd; fsetdec ].
  - apply IHrel_aenv. clear - Hd. fsetdec.
Qed.

Lemma restrict_l_drop_mid_incl : forall ρa ρb x y a b,
  In (a, b) (restrict_l {{x}} (ρa ++ (x, y) :: ρb)) ->
  In (a, b) (ρa ++ ρb).
Proof.
  intros ρa ρb x y a b Hin.
  assert (Hne : a <> x).
  { intros ->. apply (@restrict_l_notin {{x}} (ρa ++ (x, y) :: ρb) x).
    - clear; fsetdec.
    - eapply cols_l_in; exact Hin. }
  apply restrict_l_incl in Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | [Heq | Hin]];
    [apply in_or_app; left; exact Hin | inversion Heq; subst; contradiction
    |apply in_or_app; right; exact Hin].
Qed.

Lemma rel_pskl_drop_mid : forall ρa ρb V x y P Q,
  rel_pskl (ρa ++ (x, y) :: ρb) V P Q ->
  x `notin` ftvar_in_pskl P -> rel_pskl (ρa ++ ρb) V P Q.
Proof.
  intros * Hr Hfresh. eapply rel_pskl_mono.
  - eapply rel_pskl_restrict_l with (D := {{x}});
      [exact Hr | clear - Hfresh; fsetdec].
  - intros a b Hin. eapply restrict_l_drop_mid_incl; exact Hin.
  - intros a Ha; exact Ha.
Qed.

Lemma rel_aenv_drop_mid : forall ρa ρb V x y Θ Θ',
  rel_aenv (ρa ++ (x, y) :: ρb) V Θ Θ' ->
  x `notin` ftvar_in_aenv Θ -> rel_aenv (ρa ++ ρb) V Θ Θ'.
Proof.
  intros * Hr Hfresh. eapply rel_aenv_mono.
  - eapply rel_aenv_restrict_l with (D := {{x}});
      [exact Hr | clear - Hfresh; fsetdec].
  - intros a b Hin. eapply restrict_l_drop_mid_incl; exact Hin.
  - intros a Ha; exact Ha.
Qed.

Lemma rel_aenv_app_inv_l : forall Ξ ρ V Θ1 Θ2,
  rel_aenv ρ V (Ξ ++ Θ1) Θ2 ->
  exists Ξ2 Θ2', Θ2 = Ξ2 ++ Θ2'
    /\ rel_aenv ρ V Ξ Ξ2 /\ rel_aenv ρ V Θ1 Θ2'.
Proof.
  induction Ξ as [ | [c bd] Ξ IH ]; intros ρ V Θ1 Θ2 H.
  - exists (@nil (atom * abind)), Θ2. simpl_env.
    split; [ reflexivity | split; [ constructor | exact H ] ].
  - simpl_env in H.
    destruct (rel_aenv_cons_inv_l H) as (b & b2 & Θ2b & E & Hab & Hbd & Hrest).
    subst Θ2.
    destruct (IH _ _ _ _ Hrest) as (Ξ2 & Θ2' & E2 & HΞ & HΘ).
    subst Θ2b.
    exists ((b ~ b2) ++ Ξ2), Θ2'. simpl_env.
    split; [ reflexivity
           | split; [ apply rel_aenv__cons; assumption | exact HΘ ] ].
Qed.

Lemma rel_aenv_suffix : forall ρ V Ξ Ξ2,
  rel_aenv ρ V Ξ Ξ2 -> a_suffix Ξ -> a_suffix Ξ2.
Proof.
  intros ρ V Ξ Ξ2 H; induction H; intros Hs; [ constructor | ].
  inversion Hs; subst.
  apply a_suffix__cons; [ apply IHrel_aenv; assumption | ].
  match goal with Hsb : a_suffix_binding _ |- _ => inversion Hsb; subst end;
    match goal with Hb : rel_abind _ _ _ _ |- _ => inversion Hb; subst end;
    constructor.
Qed.

Lemma rel_pskl_open_rec_skl : forall ρ V P1 P2 Q1 Q2 k,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V Q1 Q2 ->
  rel_pskl ρ V (open_pskl_wrt_pskl_rec k Q1 P1)
               (open_pskl_wrt_pskl_rec k Q2 P2).
Proof.
  intros ρ V P1 P2 Q1 Q2 k Hrel HQ; revert k;
    induction Hrel; intros k; simpl; try (constructor; auto; fail).
  destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt];
    [ constructor | exact HQ | constructor ].
Qed.

Lemma rel_pskl_open_skl : forall ρ V P1 P2 Q1 Q2,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V Q1 Q2 ->
  rel_pskl ρ V (open_pskl_wrt_pskl P1 Q1) (open_pskl_wrt_pskl P2 Q2).
Proof.
  intros. unfold open_pskl_wrt_pskl. apply rel_pskl_open_rec_skl; assumption.
Qed.

Lemma rel_ext_flex_pairs : forall ρn W S,
  uniq (flex_pairs_l ρn) ->
  uniq (flex_pairs_r ρn) ->
  cols_l ρn ∩ W [=] empty ->
  cols_r ρn ∩ S [=] empty ->
  rel_ext ρn W S.
Proof.
  intros ρn W S Hul Hur Hcl Hcr. unfold rel_ext. split; [ | split ].
  - intros a b Hin.
    assert (Hal : a `in` cols_l ρn) by (eapply cols_l_in; exact Hin).
    assert (Har : b `in` cols_r ρn) by (eapply cols_r_in; exact Hin).
    split; [ clear - Hal Hcl; fsetdec | clear - Har Hcr; fsetdec ].
  - intros a1 a2 b H1 H2.
    exact (nodup_snd_inj _ _ _ _ (uniq_flex_pairs_r_nodup _ Hur) H1 H2).
  - intros a b1 b2 H1 H2.
    exact (nodup_fst_fun _ _ _ _ (uniq_flex_pairs_l_nodup _ Hul) H1 H2).
Qed.

Lemma rel_atom_shrink_add : forall ρ V a0 a b,
  rel_atom ρ (add a0 V) a b -> a <> a0 -> rel_atom ρ V a b.
Proof.
  intros ρ V a0 a b H Hne. inversion H; subst;
    [ apply rel_atom__pair; assumption | ].
  apply rel_atom__id.
  match goal with
  | Hin : _ `in` add a0 V |- _ => clear - Hin Hne; fsetdec
  end.
Qed.

Lemma a_binds_tvar_rel : forall ρ V Θ1 Θ2 a b,
  rel_aenv ρ V Θ1 Θ2 ->
  rel_fun ρ V (dom Θ1) ->
  a_binds_tvar a Θ1 ->
  rel_atom ρ V a b ->
  a_binds_tvar b Θ2.
Proof.
  intros ρ V Θ1 Θ2 a b Hrel Hfun Hbt Hat.
  assert (Had : a `in` dom Θ1) by (apply a_binds_tvar_in_dom; exact Hbt).
  assert (Hstep : forall bd, binds a bd Θ1 ->
            exists bd2, rel_abind ρ V bd bd2 /\ binds b bd2 Θ2).
  { intros bd Hb.
    destruct (@rel_aenv_binds_l ρ V Θ1 Θ2 a bd Hrel Hb)
      as (b' & bd2 & Hat' & Habd & Hb2).
    assert (Eb : b' = b) by (exact (Hfun a b' b Had Hat' Hat)).
    subst b'. exists bd2. split; [ exact Habd | exact Hb2 ]. }
  destruct Hbt as [Hb | [Hb | [τ Hb]]];
    destruct (Hstep _ Hb) as (bd2 & Habd & Hb2);
    inversion Habd; subst.
  - left. exact Hb2.
  - right. left. exact Hb2.
  - right. right. eexists. exact Hb2.
Qed.

Lemma a_wf_pskl_rel_gen : forall Θ1 Δ P1,
  {{ Θ1 ⨟ Δ ⊢ₚₛ P1 }}a ->
  forall ρ V Θ2 P2,
  (forall a b, a_binds_tvar a Θ1 -> rel_atom ρ V a b -> a_binds_tvar b Θ2) ->
  Δ ∩ cols_r ρ [=] empty ->
  rel_pskl ρ V P1 P2 ->
  {{ Θ2 ⨟ Δ ⊢ₚₛ P2 }}a.
Proof.
  intros Θ1 Δ P1 Hwf.
  induction Hwf as [ Θ Δ | Θ Δ a0 Hd | Θ Δ Pa Pb Hwfa IHa Hwfb IHb
                   | L Θ Δ Pa Hbody IHbody | Θ Δ | Θ Δ Pa Hg Hwfa IHa ];
    intros ρ V Θ2 P2 Htv HΔ Hp.
  -  inversion Hp; subst. apply a_wf_pskl__unit.
  -
    inversion Hp as [ | | x y Hat | | | | ]; subst.
    apply a_wf_pskl__var. exact (Htv _ _ Hd Hat).
  -
    inversion Hp as [ | | | Q1 Q2 Q3 Q4 Hpa Hpb | | | ]; subst.
    apply a_wf_pskl__arrow;
      [ eapply IHa; [ exact Htv | exact HΔ | exact Hpa ]
      | eapply IHb; [ exact Htv | exact HΔ | exact Hpb ] ].
  -
    inversion Hp as [ | | | | Q1 Q2 Hpb | | ]; subst.
    apply a_wf_pskl__all with (L := L ∪ cols_l ρ ∪ cols_r ρ).
    intros a0 Ha0.
    eapply IHbody with (ρ := ρ) (V := add a0 V);
      [ clear - Ha0; solve_notin_auto
      | | clear - HΔ Ha0; fsetdec
      | apply rel_pskl_open_var; exact Hpb ].
    intros a b Ha Hab. apply a_binds_tvar_cons_tvar.
    destruct (a == a0) as [-> | Hne].
    + left. inversion Hab as [ x1 y1 Hin | x1 Hin ]; subst; [ | reflexivity ].
      exfalso. apply cols_l_in in Hin. clear - Hin Ha0. solve_notin_auto.
    + right. destruct (a_binds_tvar_cons_tvar_inv Ha) as [E | Ha'];
        [ contradiction | ].
      eapply Htv; [ exact Ha' | eapply rel_atom_shrink_add; eassumption ].
  -  inversion Hp; subst. apply a_wf_pskl__ghost.
  -
    inversion Hp as [ | | | | | | Q1 Q2 Hpb ]; subst.
    apply a_wf_pskl__univ_ghost;
      [ eapply rel_pskl_guarded; [ exact Hpb | exact Hg ]
      | eapply IHa; [ | clear; fsetdec | exact Hpb ] ].
    intros a b Ha Hab.
    apply a_binds_tvar_aenv_minus in Ha. destruct Ha as [Ha HaΔ].
    apply a_binds_tvar_aenv_minus. split; [ exact (Htv _ _ Ha Hab) | ].
    inversion Hab as [ x1 y1 Hin | x1 Hin ]; subst; [ | exact HaΔ ].
    apply cols_r_in in Hin. clear - Hin HΔ. fsetdec.
Qed.

Lemma a_wf_pskl_rel : forall Θ1 Δ P1,
  {{ Θ1 ⨟ Δ ⊢ₚₛ P1 }}a ->
  forall ρ V Θ2 P2,
  rel_aenv ρ V Θ1 Θ2 ->
  rel_fun ρ V (dom Θ1) ->
  Δ ∩ cols_r ρ [=] empty ->
  rel_pskl ρ V P1 P2 ->
  {{ Θ2 ⨟ Δ ⊢ₚₛ P2 }}a.
Proof.
  intros Θ1 Δ P1 Hwf ρ V Θ2 P2 Hrel Hfun HΔ Hp.
  eapply a_wf_pskl_rel_gen; [ exact Hwf | | exact HΔ | exact Hp ].
  intros a b Hbt Hat.
  eapply a_binds_tvar_rel; [ exact Hrel | exact Hfun | exact Hbt | exact Hat ].
Qed.

Inductive rel_exp (ρ : list (atom * atom)) (V : atoms) : exp -> exp -> Prop :=
| rel_exp__unit : rel_exp ρ V exp_unit exp_unit
| rel_exp__var_b : forall n, rel_exp ρ V (exp_var_b n) (exp_var_b n)
| rel_exp__var_f : forall x y,
    rel_atom ρ V x y -> rel_exp ρ V (exp_var_f x) (exp_var_f y)
| rel_exp__abs : forall e1 e2,
    rel_exp ρ V e1 e2 -> rel_exp ρ V (exp_abs e1) (exp_abs e2)
| rel_exp__abs_anno : forall A1 A2 e1 e2,
    rel_ptyp ρ V A1 A2 -> rel_exp ρ V e1 e2 ->
    rel_exp ρ V (exp_abs_anno A1 e1) (exp_abs_anno A2 e2)
| rel_exp__app : forall a1 a2 b1 b2,
    rel_exp ρ V a1 b1 -> rel_exp ρ V a2 b2 ->
    rel_exp ρ V (exp_app a1 a2) (exp_app b1 b2)
| rel_exp__anno : forall e1 e2 A1 A2,
    rel_exp ρ V e1 e2 -> rel_ptyp ρ V A1 A2 ->
    rel_exp ρ V (exp_anno e1 A1) (exp_anno e2 A2)
| rel_exp__freeze : forall e1 e2,
    rel_exp ρ V e1 e2 -> rel_exp ρ V (exp_freeze e1) (exp_freeze e2).

#[export] Hint Constructors rel_exp : core.

Lemma rel_exp_mono : forall ρ ρ' V V' e1 e2,
  rel_exp ρ V e1 e2 ->
  (forall a b, In (a, b) ρ -> In (a, b) ρ') ->
  V [<=] V' ->
  rel_exp ρ' V' e1 e2.
Proof.
  intros ρ ρ' V V' e1 e2 H Hin Hs; induction H; constructor; auto;
    try (unfold rel_ptyp in *; eapply rel_pskl_mono; eauto; fail).
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ =>
      inversion Ha; subst;
        [ apply rel_atom__pair; auto | apply rel_atom__id; fsetdec ]
  end.
Qed.

Lemma rel_exp_refl : forall ρ V e,
  fvar_in_exp e ∪ ftvar_in_exp e [<=] V ->
  rel_exp ρ V e e.
Proof.
  intros ρ V e; induction e; intros Hsub; simpl in Hsub;
    constructor;
    try (apply rel_atom__id; clear - Hsub; fsetdec);
    try (unfold rel_ptyp; apply rel_pskl_refl;
         match goal with
         | |- ftvar_in_pskl (ptyp_to_pskl ?A0) [<=] _ =>
             pose proof (ftvar_ptyp_to_pskl A0) as He
         end; clear - Hsub He; fsetdec);
    try (match goal with
         | IH : _ -> rel_exp _ _ ?x ?x |- rel_exp _ _ ?x ?x => apply IH
         end; clear - Hsub; fsetdec).
Qed.

Lemma rel_exp_open_rec_pair : forall ρ V e1 e2 x y k,
  rel_exp ρ V e1 e2 ->
  rel_exp ((x, y) :: ρ) V
    (open_exp_wrt_exp_rec k (exp_var_f x) e1)
    (open_exp_wrt_exp_rec k (exp_var_f y) e2).
Proof.
  intros ρ V e1 e2 x y k H; revert k; induction H; intros k; simpl;
    try (constructor; auto;
         (unfold rel_ptyp in *; eapply rel_pskl_mono;
          [ eassumption | intros ?a ?b Hi; right; exact Hi
          | intros ?z Hz; exact Hz ]); fail).
  -
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt];
      [ constructor | | constructor ].
    apply rel_exp__var_f. apply rel_atom__pair. left. reflexivity.
  -
    apply rel_exp__var_f.
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ =>
        inversion Ha; subst;
          [ apply rel_atom__pair; right; assumption
          | apply rel_atom__id; assumption ]
    end.
Qed.

Lemma rel_exp_open_pair : forall ρ V e1 e2 x y,
  rel_exp ρ V e1 e2 ->
  rel_exp ((x, y) :: ρ) V
    (open_exp_wrt_exp e1 (exp_var_f x)) (open_exp_wrt_exp e2 (exp_var_f y)).
Proof.
  intros. unfold open_exp_wrt_exp. apply rel_exp_open_rec_pair. assumption.
Qed.

Lemma rel_exp_restrict : forall x y ρ V e1 e2,
  rel_exp ρ V e1 e2 ->
  x `notin` fvar_in_exp e1 ∪ ftvar_in_exp e1 ->
  y `notin` fvar_in_exp e2 ∪ ftvar_in_exp e2 ->
  rel_exp (restrict_pairs x y ρ) V e1 e2.
Proof.
  intros x y ρ V e1 e2 H; induction H; intros Hx Hy; simpl in Hx, Hy.
  - apply rel_exp__unit.
  - apply rel_exp__var_b.
  - apply rel_exp__var_f.
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ =>
        inversion Ha; subst;
          [ apply rel_atom__pair; apply restrict_pairs_in;
              [ assumption | clear - Hx; fsetdec | clear - Hy; fsetdec ]
          | apply rel_atom__id; assumption ]
    end.
  - apply rel_exp__abs. apply IHrel_exp;
      [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  - apply rel_exp__abs_anno.
    + unfold rel_ptyp in *. apply rel_pskl_restrict;
        [ assumption
        | rewrite ftvar_ptyp_to_pskl; clear - Hx; fsetdec
        | rewrite ftvar_ptyp_to_pskl; clear - Hy; fsetdec ].
    + apply IHrel_exp; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  - apply rel_exp__app;
      [ apply IHrel_exp1 | apply IHrel_exp2 ];
      solve [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
  - apply rel_exp__anno.
    + apply IHrel_exp; [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
    + unfold rel_ptyp in *. apply rel_pskl_restrict;
        [ assumption
        | rewrite ftvar_ptyp_to_pskl; clear - Hx; fsetdec
        | rewrite ftvar_ptyp_to_pskl; clear - Hy; fsetdec ].
  - apply rel_exp__freeze. apply IHrel_exp;
      [ clear - Hx; fsetdec | clear - Hy; fsetdec ].
Qed.

Lemma rel_exp_restrict_l : forall D ρ V e1 e2,
  rel_exp ρ V e1 e2 ->
  D ∩ (fvar_in_exp e1 ∪ ftvar_in_exp e1) [=] empty ->
  rel_exp (restrict_l D ρ) V e1 e2.
Proof.
  intros D ρ V e1 e2 H; induction H; intros Hd; simpl in Hd.
  - apply rel_exp__unit.
  - apply rel_exp__var_b.
  - apply rel_exp__var_f.
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ =>
        inversion Ha; subst;
          [ apply rel_atom__pair; apply restrict_l_in;
              [ assumption | clear - Hd; fsetdec ]
          | apply rel_atom__id; assumption ]
    end.
  - apply rel_exp__abs. apply IHrel_exp. clear - Hd. fsetdec.
  - apply rel_exp__abs_anno.
    + apply rel_ptyp_restrict_l; [ assumption | clear - Hd; fsetdec ].
    + apply IHrel_exp. clear - Hd. fsetdec.
  - apply rel_exp__app;
      [ apply IHrel_exp1 | apply IHrel_exp2 ]; clear - Hd; fsetdec.
  - apply rel_exp__anno.
    + apply IHrel_exp. clear - Hd. fsetdec.
    + apply rel_ptyp_restrict_l; [ assumption | clear - Hd; fsetdec ].
  - apply rel_exp__freeze. apply IHrel_exp. clear - Hd. fsetdec.
Qed.

Lemma rel_aenv_binds_pin : forall ρ V Θ1 Θ2 a b bd,
  rel_aenv ρ V Θ1 Θ2 ->
  rel_fun ρ V (dom Θ1) ->
  binds a bd Θ1 ->
  rel_atom ρ V a b ->
  exists bd2, rel_abind ρ V bd bd2 /\ binds b bd2 Θ2.
Proof.
  intros ρ V Θ1 Θ2 a b bd Hrel Hfun Hb Hat.
  assert (Had : a `in` dom Θ1) by (eapply binds_In; exact Hb).
  destruct (@rel_aenv_binds_l ρ V Θ1 Θ2 a bd Hrel Hb)
    as (b' & bd2 & Hat' & Habd & Hb2).
  assert (Eb : b' = b) by (exact (Hfun a b' b Had Hat' Hat)).
  subst b'. exists bd2. split; [ exact Habd | exact Hb2 ].
Qed.

Lemma flex_agree_rel_push_tm : forall ρ V Θ1 Θ2 x x2 (bd bd' : abind),
  flex_agree_rel ρ V Θ1 Θ2 ->
  abind_nonflex bd ->
  abind_nonflex bd' ->
  x `notin` dom Θ1 ->
  x2 `notin` dom Θ2 ->
  flex_agree_rel ((x, x2) :: ρ) V ((x ~ bd) ++ Θ1) ((x2 ~ bd') ++ Θ2).
Proof.
  intros ρ V Θ1 Θ2 x x2 bd bd' [HagV Hagp] Hnf1 Hnf2 Hx1 Hx2.
  split.
  - intros v Hv.
    rewrite (a_flex_tvar_cons_nonflex _ _ _ Hnf1).
    rewrite (a_flex_tvar_cons_nonflex _ _ _ Hnf2).
    exact (HagV v Hv).
  - intros a b Hin.
    rewrite (a_flex_tvar_cons_nonflex _ _ _ Hnf1).
    rewrite (a_flex_tvar_cons_nonflex _ _ _ Hnf2).
    destruct Hin as [E | Hin].
    + injection E as -> ->.
      split; intros Hf; exfalso;
        [ apply Hx1 | apply Hx2 ]; apply a_flex_tvar_in_dom; exact Hf.
    + exact (Hagp a b Hin).
Qed.

Lemma rel_aenv_binds_r : forall ρ V Θ1 Θ2 b b2,
  rel_aenv ρ V Θ1 Θ2 -> binds b b2 Θ2 ->
  exists a b1, rel_atom ρ V a b /\ rel_abind ρ V b1 b2 /\ binds a b1 Θ1.
Proof.
  intros * H; induction H; intros Hb; [ inversion Hb | ].
  unfold binds in Hb; simpl in Hb; destruct Hb as [Heq | Hb].
  - inversion Heq; subst. exists a, b1. repeat split; try assumption.
    unfold binds; simpl; left; reflexivity.
  - destruct (IHrel_aenv Hb) as (a' & b1' & Hat & Hab & Hbd).
    exists a', b1'. repeat split; try assumption.
    unfold binds in Hbd |- *; simpl; right; exact Hbd.
Qed.

Lemma rel_aenv_flex : forall ρ V Θ1 Θ2 a b,
  rel_aenv ρ V Θ1 Θ2 -> rel_inj ρ V -> rel_fun ρ V (dom Θ1) ->
  rel_atom ρ V a b -> (a_flex_tvar Θ1 a <-> a_flex_tvar Θ2 b).
Proof.
  intros * Hr Hinj Hfun Hat. split; intros [Hb | [τ Hb]].
  - destruct (rel_aenv_binds_pin abind_flex_mono Hr Hfun Hb Hat) as (bd & Hbd & Hb').
    inversion Hbd; subst. left; exact Hb'.
  - destruct (rel_aenv_binds_pin (abind_flex_mono_def τ) Hr Hfun Hb Hat) as (bd & Hbd & Hb').
    inversion Hbd; subst. right; eexists; exact Hb'.
  - destruct (@rel_aenv_binds_r ρ V Θ1 Θ2 b abind_flex_mono Hr Hb) as (a' & bd & Hat' & Hbd & Hb').
    assert (a' = a) by (exact (Hinj _ _ _ Hat' Hat)). subst a'.
    inversion Hbd; subst. left; exact Hb'.
  - destruct (@rel_aenv_binds_r ρ V Θ1 Θ2 b (abind_flex_mono_def τ) Hr Hb) as (a' & bd & Hat' & Hbd & Hb').
    assert (a' = a) by (exact (Hinj _ _ _ Hat' Hat)). subst a'.
    inversion Hbd; subst. right; eexists; exact Hb'.
Qed.

Lemma rel_aenv_flex_agree : forall ρ V Θ1 Θ2,
  rel_aenv ρ V Θ1 Θ2 -> rel_inj ρ V -> rel_fun ρ V (dom Θ1) ->
  flex_agree_rel ρ V Θ1 Θ2.
Proof.
  intros * Hr Hinj Hfun. split; intros.
  - eapply rel_aenv_flex; eauto using rel_atom__id.
  - eapply rel_aenv_flex; eauto using rel_atom__pair.
Qed.

Lemma rel_aenv_flex_agree_ext : forall ρe ρ V Θ1 Θ2 D W S,
  rel_aenv (ρe ++ ρ) V Θ1 Θ2 ->
  rel_inj ρ V -> rel_fun ρ V D -> rel_ext ρe W S ->
  D [<=] W -> V [<=] D -> V ∪ cols_r ρ [<=] S ->
  (forall a, a `in` dom Θ1 -> a `notin` D -> a `notin` cols_l ρ) ->
  flex_agree_rel (ρe ++ ρ) V Θ1 Θ2.
Proof.
  intros * Hr Hinj Hfun Hext HD HV Hcov Hblk.
  eapply rel_aenv_flex_agree; [ exact Hr | | ].
  - eapply rel_inj_app; eassumption.
  - eapply rel_fun_app;
      [ exact Hfun | exact Hext | exact HD | exact Hblk | ].
    intros a Ha Hn. clear - Hn HV. fsetdec.
Qed.

Lemma rel_pskl_restore_pairs : forall ρe ρ V x y P Q,
  rel_pskl (ρe ++ (x, y) :: restrict_pairs x y ρ) V P Q ->
  x `notin` ftvar_in_pskl P -> rel_pskl (ρe ++ ρ) V P Q.
Proof.
  intros * Hr Hfresh. eapply rel_pskl_mono.
  - eapply rel_pskl_drop_mid; eassumption.
  - intros a b Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [Hin | Hin];
      [left; exact Hin | right; eapply restrict_pairs_incl; exact Hin].
  - intros z Hz; exact Hz.
Qed.

Lemma rel_aenv_restore_pairs : forall ρe ρ V x y Θ Θ',
  rel_aenv (ρe ++ (x, y) :: restrict_pairs x y ρ) V Θ Θ' ->
  x `notin` ftvar_in_aenv Θ -> rel_aenv (ρe ++ ρ) V Θ Θ'.
Proof.
  intros * Hr Hfresh. eapply rel_aenv_mono.
  - eapply rel_aenv_drop_mid; eassumption.
  - intros a b Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [Hin | Hin];
      [left; exact Hin | right; eapply restrict_pairs_incl; exact Hin].
  - intros z Hz; exact Hz.
Qed.

Lemma rel_aenv_split_preserved_binding : forall ρe ρ V x y bd bd' Ξ Θ Θout,
  rel_aenv (ρe ++ (x, y) :: restrict_pairs x y ρ) V
    (Ξ ++ (x ~ bd) ++ Θ) Θout ->
  (forall b, ~ In (x, b) ρe) -> x `notin` V ->
  binds y bd' Θout -> uniq Θout ->
  exists Ξ' Θ', Θout = Ξ' ++ (y ~ bd') ++ Θ' /\
    rel_aenv (ρe ++ (x, y) :: restrict_pairs x y ρ) V Ξ Ξ' /\
    rel_aenv (ρe ++ (x, y) :: restrict_pairs x y ρ) V Θ Θ'.
Proof.
  intros * Hr Hfresh HxV Hb Huq.
  assert (Honly : forall z,
    rel_atom (ρe ++ (x, y) :: restrict_pairs x y ρ) V x z -> z = y).
  { intros z Hz. inversion Hz as [a b Hin | a HinV]; subst.
    - apply in_app_or in Hin. destruct Hin as [Hin | [Heq | Hin]].
      + exfalso; exact (Hfresh _ Hin).
      + inversion Heq; reflexivity.
      + exfalso. apply (@restrict_pairs_notin_l x y ρ).
        eapply cols_l_in; exact Hin.
    - exfalso; exact (HxV HinV). }
  destruct (@rel_aenv_app_inv_l Ξ _ _ _ _ Hr) as (Ξ' & Θrest & Eout & HrΞ & HrTail).
  subst Θout.
  destruct (rel_aenv_cons_inv_l HrTail)
    as (z & bd2 & Θ' & Erest & Hz & Hbd & HrΘ).
  subst Θrest. assert (Ez : z = y) by auto. subst z.
  assert (Hmid : binds y bd2 (Ξ' ++ (y ~ bd2) ++ Θ'))
    by (unfold binds; apply in_or_app; right; left; reflexivity).
  assert (Ebd : bd2 = bd') by (eapply binds_unique; eauto).
  subst bd2. exists Ξ', Θ'; auto.
Qed.

Lemma lift_seq_widen : forall {ρe1 ρ V} {Θa Θb Θc Θb' : aenv} {S0 S1},
  rel_inj ρ V ->
  rel_fun ρ V (dom Θa) ->
  rel_ext ρe1 (ftvar_in_aenv Θa) S0 ->
  (forall a b, In (a, b) ρe1 -> a `in` dom Θb /\ b `in` dom Θb') ->
  {{ ⊢ Θa }}a ->
  V [<=] ftvar_in_aenv Θa ->
  V ∪ cols_r ρ [<=] S0 ->
  (forall a, a `in` dom Θc -> a `notin` dom Θa -> a `notin` cols_l ρ) ->
  dom Θa [<=] dom Θb ->
  dom Θb [<=] dom Θc ->
  S0 [<=] S1 ->
  dom Θb' [<=] S1 ->
  rel_inj (ρe1 ++ ρ) V
  /\ rel_fun (ρe1 ++ ρ) V (dom Θb)
  /\ V [<=] ftvar_in_aenv Θb
  /\ V ∪ cols_r (ρe1 ++ ρ) [<=] S1
  /\ (forall a, a `in` dom Θc -> a `notin` dom Θb ->
        a `notin` cols_l (ρe1 ++ ρ)).
Proof.
  intros ρe1 ρ V Θa Θb Θc Θb' S0 S1 Hinj Hfun Hext1 Hdom1 Hwf Hscp Hcov
    Hblk Hdm0 Hdm1 Hgr1 HdΘ1.
  assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (Hd1s : dom Θb [<=] ftvar_in_aenv Θb)
    by (apply dom_subset_ftvar_in_aenv).
  assert (HVdom0 : V [<=] dom Θa) by (clear - Hscp Hsc0; fsetdec).
  split; [ eapply rel_inj_app; [ exact Hinj | exact Hext1 | exact Hcov ] | ].
  split.
  { eapply rel_fun_app;
      [ exact Hfun | exact Hext1 | apply dom_subset_ftvar_in_aenv
      | intros a Ha Hn; apply Hblk; [ clear - Ha Hdm1; fsetdec | exact Hn ]
      | intros a Ha Hn; clear - HVdom0 Hn; fsetdec ]. }
  split; [ clear - Hscp Hsc0 Hdm0 Hd1s; fsetdec | ].
  split.
  { assert (Hc1r : cols_r ρe1 [<=] S1).
    { intros y Hy. destruct (cols_r_in_inv _ _ Hy) as (a & Hin).
      destruct (Hdom1 _ _ Hin) as [_ Hd2]. clear - Hd2 HdΘ1. fsetdec. }
    rewrite cols_r_app. clear - Hcov Hc1r Hgr1. fsetdec. }
  intros a Ha Hn. rewrite cols_l_app.
  assert (Hc1 : a `notin` cols_l ρe1).
  { intros Hy. destruct (cols_l_in_inv _ _ Hy) as (y & Hin).
    destruct (Hdom1 _ _ Hin) as [Hd1 _]. contradiction. }
  assert (Hc2 : a `notin` cols_l ρ)
    by (apply Hblk; [ exact Ha | clear - Hn Hdm0; fsetdec ]).
  clear - Hc1 Hc2. fsetdec.
Qed.

Lemma lift_seq_ext : forall {ρe1 ρe2} {Θa Θb Θc Θb' Θc' : aenv} {S0 S1},
  rel_ext ρe1 (ftvar_in_aenv Θa) S0 ->
  rel_ext ρe2 (ftvar_in_aenv Θb) S1 ->
  (forall a b, In (a, b) ρe1 -> a `in` dom Θb /\ b `in` dom Θb') ->
  (forall a b, In (a, b) ρe2 -> a `in` dom Θc /\ b `in` dom Θc') ->
  {{ ⊢ Θa }}a ->
  dom Θa [<=] dom Θb ->
  dom Θb [<=] dom Θc ->
  S0 [<=] S1 ->
  dom Θb' [<=] S1 ->
  dom Θb' [<=] dom Θc' ->
  rel_ext (ρe2 ++ ρe1) (ftvar_in_aenv Θa) S0
  /\ (forall a b, In (a, b) (ρe2 ++ ρe1) -> a `in` dom Θc /\ b `in` dom Θc').
Proof.
  intros ρe1 ρe2 Θa Θb Θc Θb' Θc' S0 S1 Hext1 Hext2 Hdom1 Hdom2 Hwf Hdm0
    Hdm1 Hgr1 HdΘ1 Hdm2.
  assert (Hsc0 : ftvar_in_aenv Θa [<=] dom Θa)
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (Hd1s : dom Θb [<=] ftvar_in_aenv Θb)
    by (apply dom_subset_ftvar_in_aenv).
  split.
  { eapply rel_ext_app;
      [ exact Hext1 | exact Hext2
      | clear - Hsc0 Hdm0 Hd1s; fsetdec
      | exact Hgr1
      | intros a b Hin; destruct (Hdom1 _ _ Hin) as [Hd1 Hd2];
        split; [ clear - Hd1 Hd1s; fsetdec | clear - Hd2 HdΘ1; fsetdec ] ]. }
  intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - exact (Hdom2 _ _ Hin).
  - destruct (Hdom1 _ _ Hin) as [Hd1 Hd2].
    split; [ clear - Hd1 Hdm1; fsetdec | clear - Hd2 Hdm2; fsetdec ].
Qed.

Definition binder_head (opens : bool) (P : pskl) : pskl :=
  if opens then pskl_all_syn P else pskl_univ_ghost P.

Definition binder_body (opens : bool) (P : pskl) (α : atom) : pskl :=
  if opens then open_pskl_wrt_pskl P (pskl_var_f α) else pskl_univ_ghost P.

Definition binder_delta (grows : bool) (α : atom) (Δ : atoms) : atoms :=
  if grows then add α Δ else Δ.

Lemma rel_pskl_binder_head_inv : forall {ρ V opens P P'},
  rel_pskl ρ V (binder_head opens P) P' ->
  exists P2, P' = binder_head opens P2 /\ rel_pskl ρ V P P2.
Proof.
  intros ρ V [] P P' Hr; inversion Hr; subst; eexists; split;
    solve [ reflexivity | eassumption ].
Qed.

Lemma ftvar_in_pskl_binder_head : forall opens P,
  ftvar_in_pskl (binder_head opens P) = ftvar_in_pskl P.
Proof. intros [] P; reflexivity. Qed.

Lemma ftvar_in_pskl_binder_body_upper : forall opens P α,
  ftvar_in_pskl (binder_body opens P α) [<=] add α (ftvar_in_pskl P).
Proof.
  intros [] P α; simpl.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α))
      as Hu.
    simpl in Hu. clear - Hu. fsetdec.
  - clear. fsetdec.
Qed.

Lemma binder_delta_upper : forall grows α Δ,
  Δ [<=] binder_delta grows α Δ /\ binder_delta grows α Δ [<=] add α Δ.
Proof. intros [] α Δ; simpl; split; clear; fsetdec. Qed.

Lemma rel_pskl_binder_body : forall ρ V opens P P2 α α2,
  rel_pskl ρ V P P2 ->
  rel_pskl ((α, α2) :: ρ) V (binder_body opens P α) (binder_body opens P2 α2).
Proof.
  intros ρ V [] P P2 α α2 Hr; simpl.
  - apply rel_pskl_open_pair; exact Hr.
  - apply rel_pskl__univ_ghost; eapply rel_pskl_mono;
      [ exact Hr | intros x y Hx; right; exact Hx | intros x Hx; exact Hx ].
Qed.

Lemma lift_restrict_junk : forall {D ρ V Θ Θ' S0},
  D ∩ ftvar_in_aenv Θ [=] empty ->
  rel_aenv ρ V Θ Θ' ->
  flex_agree_rel ρ V Θ Θ' ->
  rel_inj ρ V ->
  rel_fun ρ V (dom Θ) ->
  V ∪ cols_r ρ [<=] S0 ->
  (forall a b, In (a, b) (restrict_l D ρ) -> In (a, b) ρ)
  /\ (forall a b, In (a, b) ρ -> a `notin` D -> In (a, b) (restrict_l D ρ))
  /\ cols_l (restrict_l D ρ) [<=] cols_l ρ
  /\ cols_r (restrict_l D ρ) [<=] cols_r ρ
  /\ (forall a, a `in` D -> a `notin` cols_l (restrict_l D ρ))
  /\ rel_aenv (restrict_l D ρ) V Θ Θ'
  /\ flex_agree_rel (restrict_l D ρ) V Θ Θ'
  /\ rel_inj (restrict_l D ρ) V
  /\ rel_fun (restrict_l D ρ) V (dom Θ)
  /\ V ∪ cols_r (restrict_l D ρ) [<=] S0.
Proof.
  intros D ρ V Θ Θ' S0 HDΘ HrΘ Hagr Hinj Hfun Hcov.
  assert (Hincl : forall a b, In (a, b) (restrict_l D ρ) -> In (a, b) ρ)
    by (intros a b Hin; eapply restrict_l_incl; exact Hin).
  pose proof (cols_r_restrict_l D ρ) as Hcr.
  split; [ exact Hincl | ].
  split; [ intros a b Hin Hn; apply restrict_l_in; assumption | ].
  split; [ apply cols_l_restrict_l | ].
  split; [ exact Hcr | ].
  split; [ intros a Ha; apply restrict_l_notin; exact Ha | ].
  split; [ apply rel_aenv_restrict_l; [ exact HrΘ | exact HDΘ ] | ].
  split.
  { eapply flex_agree_rel_weaken;
      [ exact Hagr | exact Hincl | intros z Hz; exact Hz ]. }
  split; [ eapply rel_inj_sub; [ exact Hinj | exact Hincl ] | ].
  split.
  { eapply rel_fun_weaken;
      [ exact Hfun | exact Hincl | intros z Hz; exact Hz ]. }
  clear - Hcov Hcr; fsetdec.
Qed.

Lemma lift_flex_block_push : forall {ρn ρ V Ξ Ξ2 Θ Θ'} {Θout : aenv} {S0 S1},
  Ξ = flex_pairs_l ρn ->
  Ξ2 = flex_pairs_r ρn ->
  uniq (Ξ ++ Θ) ->
  uniq Ξ2 ->
  dom Ξ2 ∩ S0 [=] empty ->
  dom Ξ2 [<=] S1 ->
  S0 [<=] S1 ->
  dom Ξ ∩ cols_l ρ [=] empty ->
  rel_aenv ρ V Θ Θ' ->
  flex_agree_rel ρ V Θ Θ' ->
  rel_inj ρ V ->
  rel_fun ρ V (dom Θ) ->
  {{ ⊢ Θ }}a ->
  uniq Θ' ->
  ftvar_in_aenv Θ' [<=] S0 ->
  V [<=] ftvar_in_aenv Θ ->
  (forall a, a `in` dom Θout -> a `notin` dom Θ -> a `notin` cols_l ρ) ->
  dom Θ' [<=] S0 ->
  V ∪ cols_r ρ [<=] S0 ->
  rel_aenv (ρn ++ ρ) V (Ξ ++ Θ) (Ξ2 ++ Θ')
  /\ flex_agree_rel (ρn ++ ρ) V (Ξ ++ Θ) (Ξ2 ++ Θ')
  /\ rel_ext ρn (ftvar_in_aenv Θ) S0
  /\ rel_inj (ρn ++ ρ) V
  /\ rel_fun (ρn ++ ρ) V (dom (Ξ ++ Θ))
  /\ {{ ⊢ (Ξ ++ Θ) }}a
  /\ uniq (Ξ2 ++ Θ')
  /\ ftvar_in_aenv (Ξ2 ++ Θ') [<=] S1
  /\ V [<=] ftvar_in_aenv (Ξ ++ Θ)
  /\ (forall a, a `in` dom Θout -> a `notin` dom (Ξ ++ Θ) ->
        a `notin` cols_l (ρn ++ ρ))
  /\ dom (Ξ2 ++ Θ') [<=] S1
  /\ V ∪ cols_r (ρn ++ ρ) [<=] S1.
Proof.
  intros ρn ρ V Ξ Ξ2 Θ Θ' Θout S0 S1 E1 E2 Huq HuqΞ2 HfrΞ2 HinΞ2 Hgr HΞcl
    HrΘ Hagr Hinj Hfun Hwf Huq2p Hftv2 Hscp Hblk HdΘ Hcov.
  assert (Hdfl : dom Ξ [=] cols_l ρn) by (rewrite E1; apply dom_flex_pairs_l).
  assert (Hdfr : dom Ξ2 [=] cols_r ρn) by (rewrite E2; apply dom_flex_pairs_r).
  assert (Hsc0 : ftvar_in_aenv Θ [<=] dom Θ)
    by (apply a_wf_aenv_ftv_dom; exact Hwf).
  assert (HdisjΞ : disjoint Ξ Θ) by (clear - Huq; solve_uniq).
  unfold disjoint in HdisjΞ.
  assert (HΞV : dom Ξ ∩ V [=] empty) by (clear - HdisjΞ Hscp Hsc0; fsetdec).
  assert (Hext : rel_ext ρn (ftvar_in_aenv Θ) S0).
  { apply rel_ext_flex_pairs;
      [ rewrite <- E1; clear - Huq; solve_uniq
      | rewrite <- E2; exact HuqΞ2
      | clear - Hdfl HdisjΞ Hsc0; fsetdec
      | clear - Hdfr HfrΞ2; fsetdec ]. }
  split.
  { apply rel_aenv_app.
    - rewrite E1, E2. apply rel_aenv_flex_pairs.
    - eapply rel_aenv_mono;
        [ exact HrΘ | intros a b Hin; apply in_or_app; right; exact Hin
        | intros z Hz; exact Hz ]. }
  split.
  { rewrite E1, E2. apply flex_agree_rel_push_pairs;
      [ exact Hagr | clear - Hdfl HΞV HΞcl; fsetdec
      | clear - Hdfr HfrΞ2 Hcov; fsetdec ]. }
  split; [ exact Hext | ].
  split; [ eapply rel_inj_app; [ exact Hinj | exact Hext | exact Hcov ] | ].
  split.
  { eapply rel_fun_app;
      [ exact Hfun | exact Hext | apply dom_subset_ftvar_in_aenv
      | intros a Ha Hn; rewrite dom_app in Ha;
        assert (HaΞ : a `in` dom Ξ) by (clear - Ha Hn; fsetdec);
        clear - HaΞ HΞcl; fsetdec
      | intros a Ha Hn; rewrite dom_app in Ha;
        assert (HaΞ : a `in` dom Ξ) by (clear - Ha Hn; fsetdec);
        clear - HaΞ HΞV; fsetdec ]. }
  split.
  { apply a_wf_aenv_decls_app;
      [ rewrite E1; apply a_decls_flex_pairs_l | exact Huq | exact Hwf ]. }
  split.
  { apply uniq_app_4;
      [ exact HuqΞ2 | exact Huq2p
      | intros z Hz;
        assert (Hz1 : z `in` dom Ξ2) by (clear - Hz; fsetdec);
        assert (Hz2 : z `in` dom Θ') by (clear - Hz; fsetdec);
        clear - Hz1 Hz2 HfrΞ2 HdΘ; fsetdec ]. }
  split.
  { rewrite ftvar_in_aenv_app.
    assert (H1 : ftvar_in_aenv Ξ2 [<=] S1).
    { rewrite E2. pose proof (ftvar_in_aenv_flex_pairs_r ρn) as He.
      rewrite He. clear - Hdfr HinΞ2. fsetdec. }
    clear - H1 Hftv2 Hgr. fsetdec. }
  split; [ rewrite ftvar_in_aenv_app; clear - Hscp; fsetdec | ].
  split.
  { intros a Ha Hn. rewrite dom_app in Hn. rewrite cols_l_app.
    assert (H1 : a `notin` cols_l ρn) by (clear - Hn Hdfl; fsetdec).
    assert (H2 : a `notin` cols_l ρ)
      by (apply Hblk; [ exact Ha | clear - Hn; fsetdec ]).
    clear - H1 H2. fsetdec. }
  split; [ rewrite dom_app; clear - HinΞ2 HdΘ Hgr; fsetdec | ].
  rewrite cols_r_app. clear - Hcov Hdfr HinΞ2 Hgr. fsetdec.
Qed.
