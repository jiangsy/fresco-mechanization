Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_tag.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_ctx_mono.
Require Import src.fresco.decl.prop_renaming.
Require Import src.fresco.decl.prop_tag_swap.

Set Implicit Arguments.

Fixpoint compose_tags (C : utyp) (B : btyp) {struct C} : atoms :=
  match C with
  | utyp_arrow C1 C2 =>
      match B with
      | btyp_arrow B1 B2 => compose_tags C1 B1 `union` compose_tags C2 B2
      | _ => empty
      end
  | utyp_all_tag ε C0 =>
      match B with
      | btyp_all_inh B0 => add ε (compose_tags C0 B0)
      | btyp_all_syn B0 => compose_tags C0 B0
      | _ => empty
      end
  | utyp_all_syn C0 =>
      match B with
      | btyp_all_inh B0 => compose_tags C0 B0
      | btyp_all_syn B0 => compose_tags C0 B0
      | _ => empty
      end
  | _ => empty
  end.

Lemma compose_tags_open_rec : forall C B α' β k,
    compose_tags (open_utyp_wrt_utyp_rec k (utyp_var_f α') C)
                 (open_btyp_wrt_btyp_rec k (btyp_var_f β) B) = compose_tags C B.
Proof.
  induction C; intros B α' β k; destruct B; simpl;
    repeat match goal with
           | [ |- context[lt_eq_lt_dec ?a ?b] ] =>
               destruct (lt_eq_lt_dec a b) as [[|]|]
           end; simpl; try reflexivity;
    repeat match goal with
           | [ IH : forall _ _ _ _, compose_tags _ _ = compose_tags _ _ |- _ ] =>
               rewrite IH
           end; reflexivity.
Qed.

Lemma compose_tags_open : forall C B α β,
    compose_tags (open_utyp_wrt_utyp C (utyp_var_f α))
                 (open_btyp_wrt_btyp B (btyp_var_f β)) = compose_tags C B.
Proof.
  intros C B α β. unfold open_utyp_wrt_utyp, open_btyp_wrt_btyp.
  apply compose_tags_open_rec.
Qed.

Lemma compose_tags_is_styp_nil : forall B C,
    is_styp B -> compose_tags C B [=] empty.
Proof.
  intros B C Hsyn. generalize dependent C.
  induction Hsyn; intros C0.
  - destruct C0; simpl; reflexivity.
  - destruct C0; simpl; reflexivity.
  - destruct C0; simpl; try reflexivity. rewrite IHHsyn1, IHHsyn2. fsetdec.
  - destruct C0; simpl; try reflexivity;
      (pick fresh α for L;
       rewrite <- (compose_tags_open _ B α α);
       apply (H0 α); fsetdec).
Qed.

Ltac binder_ih IHn HszA HH HH0 AA α :=
  let HcX := fresh "HcX" in
  let HdX := fresh "HdX" in
  pose proof (HH α ltac:(solve_notin_auto)) as HcX;
  pose proof (HH0 α ltac:(solve_notin_auto)) as HdX;
  change (btyp_var_f α) with (ptyp_to_btyp_syn (ptyp_var_f α)) in HcX;
  rewrite <- ptyp_to_btyp_syn_open in HcX;
  change (utyp_var_f α) with (ptyp_to_utyp_syn (ptyp_var_f α)) in HdX;
  rewrite <- ptyp_to_utyp_syn_open in HdX;
  edestruct (IHn (open_ptyp_wrt_ptyp AA (ptyp_var_f α))
                 ltac:(rewrite size_ptyp_open_ptyp_wrt_ptyp_var; exact HszA)
                 _ _ _ _ _ HcX HdX) as [Hincl Hcons];
  rewrite compose_tags_open in Hincl;
  rewrite compose_tags_open in Hcons.

Lemma d_consis_compose_strong : forall n A,
    size_ptyp A < n ->
    forall Ψa Ψb Γ C B,
    {{ Ψa ⨟ Γ ⊢ C ∼ ptyp_to_btyp_syn A }}d ->
    {{ Ψb ⨟ Γ ⊢ ptyp_to_utyp_syn A ∼ B }}d ->
    (Ψa `union` Ψb) [<=] (compose_tags C B) /\ {{ (compose_tags C B) ⨟ Γ ⊢ C ∼ B }}d.
Proof.
  induction n; intros A Hsz Ψa Ψb Γ C B H1 H2.
  - lia.
  - destruct A; simpl in H1, H2.
    +
      dependent destruction H1. dependent destruction H2. simpl.
      split; [ fsetdec | apply d_consis__unit; reflexivity ].
    +
      inversion H1.
    +
      dependent destruction H1. dependent destruction H2. simpl.
      split; [ fsetdec | apply d_consis__var; [ assumption | reflexivity ] ].
    +
      dependent destruction H1. dependent destruction H2. simpl.
      simpl in Hsz. pose proof (size_ptyp_min A1). pose proof (size_ptyp_min A2).
      assert (HszA1 : size_ptyp A1 < n) by lia.
      assert (HszA2 : size_ptyp A2 < n) by lia.
      edestruct (IHn A1 HszA1 _ _ _ _ _ H1_ H2_) as [Hincl1 Hcons1].
      edestruct (IHn A2 HszA2 _ _ _ _ _ H1_0 H2_0) as [Hincl2 Hcons2].
      split;
        [ fsetdec
        | eapply d_consis__arrow; [ exact Hcons1 | exact Hcons2 | reflexivity ] ].
    +
      assert (HszA : size_ptyp A < n) by (simpl in Hsz; lia).
      dependent destruction H1; dependent destruction H2.
      {
        split.
        { destruct (atom_fresh (L `union` L0)) as [α0 HX0].
          binder_ih IHn HszA H H0 A α0. simpl. fsetdec. }
        { simpl. eapply d_consis__forall_inh_tagged with (L := L `union` L0);
            [ | reflexivity ].
          intros α Hα. binder_ih IHn HszA H H0 A α. exact Hcons. } }
      {
        split.
        { destruct (atom_fresh (L `union` L0)) as [α0 HX0].
          binder_ih IHn HszA H H0 A α0. simpl. fsetdec. }
        { simpl. apply d_consis__forall_syn_tagged with (L := L `union` L0).
          intros α Hα. binder_ih IHn HszA H H0 A α. exact Hcons. } }
      {
        split.
        { destruct (atom_fresh (L `union` L0)) as [α0 HX0].
          binder_ih IHn HszA H H0 A α0. simpl. fsetdec. }
        { simpl. apply d_consis__forall_inh_untagged with (L := L `union` L0).
          intros α Hα. binder_ih IHn HszA H H0 A α. exact Hcons. } }
      {
        split.
        { destruct (atom_fresh (L `union` L0)) as [α0 HX0].
          binder_ih IHn HszA H H0 A α0. simpl. fsetdec. }
        { simpl. apply d_consis__forall_syn with (L := L `union` L0).
          intros α Hα. binder_ih IHn HszA H H0 A α. exact Hcons. } }
Qed.

Lemma d_consis_compose : forall Ψa Ψb Γ C A B,
    {{ Ψa ⨟ Γ ⊢ C ∼ ptyp_to_btyp_syn A }}d ->
    {{ Ψb ⨟ Γ ⊢ ptyp_to_utyp_syn A ∼ B }}d ->
    exists Ψc, (Ψa `union` Ψb) [<=] Ψc /\ {{ Ψc ⨟ Γ ⊢ C ∼ B }}d.
Proof.
  intros Ψa Ψb Γ C A B H1 H2.
  exists (compose_tags C B).
  exact (@d_consis_compose_strong (S (size_ptyp A)) A ltac:(lia) Ψa Ψb Γ C B H1 H2).
Qed.

Lemma d_consis_compose_syn_nil_l : forall Ψa Ψb Γ C B2 B,
    is_styp B2 -> is_styp B ->
    {{ Ψa ⨟ Γ ⊢ C ∼ B2 }}d ->
    {{ Ψb ⨟ Γ ⊢ (btyp_to_utyp_syn B2) ∼ B }}d ->
    {{ empty ⨟ Γ ⊢ C ∼ B }}d.
Proof.
  intros Ψa Ψb Γ C B2 B Hsyn2 HsynB Hc Hd.
  rewrite <- (ptyp_to_btyp_syn_btyp_to_ptyp Hsyn2) in Hc.
  rewrite <- (ptyp_to_utyp_syn_btyp_to_ptyp B2) in Hd.
  pose proof (@d_consis_compose_strong (S (size_ptyp (btyp_to_ptyp B2)))
                (btyp_to_ptyp B2) ltac:(lia) Ψa Ψb Γ C B Hc Hd) as [_ Hcons].
  exact (d_consis_equiv (@compose_tags_is_styp_nil B C HsynB) Hcons).
Qed.

Lemma d_consis_lc_utyp : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d -> lc_utyp C.
Proof.
  intros Ψ Γ C B H. induction H.
  - apply lc_utyp_unit.
  - apply lc_utyp_var_f.
  - pick fresh α. apply lc_utyp_all_tag_exists with (α1 := α). apply H0. fsetdec.
  - pick fresh α. apply lc_utyp_all_syn_exists with (α1 := α). apply H0. fsetdec.
  - pick fresh α. apply lc_utyp_all_tag_exists with (α1 := α). apply H0. fsetdec.
  - pick fresh α. apply lc_utyp_all_syn_exists with (α1 := α). apply H0. fsetdec.
  - apply lc_utyp_arrow; assumption.
Qed.

Lemma d_consis_lc_btyp : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d -> lc_utyp C -> lc_btyp B.
Proof.
  intros Ψ Γ C B H. induction H; intros Hlc.
  - apply lc_btyp_unit.
  - apply lc_btyp_var_f.
  - inversion Hlc; subst. pick fresh α.
    apply lc_btyp_all_inh_exists with (α1 := α). apply H0; auto.
  - inversion Hlc; subst. pick fresh α.
    apply lc_btyp_all_inh_exists with (α1 := α). apply H0; auto.
  - inversion Hlc; subst. pick fresh α.
    apply lc_btyp_all_syn_exists with (α1 := α). apply H0; auto.
  - inversion Hlc; subst. pick fresh α.
    apply lc_btyp_all_syn_exists with (α1 := α). apply H0; auto.
  - inversion Hlc; subst. apply lc_btyp_arrow; auto.
Qed.

Lemma d_sub_lc_btyp : forall m Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d -> lc_utyp C -> lc_btyp B.
Proof.
  intros m Ψ Γ C B H. induction H; intros Hlc.
  - eapply d_consis_lc_btyp; eassumption.
  - eapply d_consis_lc_btyp; eassumption.
  - pick fresh α. apply lc_btyp_all_inh_exists with (α1 := α).
    apply H0; [ solve_notin_auto | exact Hlc ].
  - inversion Hlc; subst. apply lc_btyp_arrow;
      [ eapply d_consis_lc_btyp; eassumption | auto ].
  -
    inversion Hlc; subst. apply IHd_sub.
    apply lc_body_utyp_wrt_utyp;
      [ intro α; auto | eapply d_wf_utyp_lc; eassumption ].
  - inversion Hlc; subst. apply IHd_sub.
    apply lc_body_utyp_wrt_utyp;
      [ intro α; auto | eapply d_wf_utyp_lc; eassumption ].
Qed.

Lemma d_consis_guarded_lhs : forall Ψ Γ Csrc C,
    guarded_utyp C ->
    {{ Ψ ⨟ Γ ⊢ Csrc ∼ (utyp_to_btyp C) }}d ->
    guarded_utyp Csrc.
Proof.
  intros Ψ Γ Csrc C Hg Hc.
  inversion Hg; subst; simpl in Hc.
  - inversion Hc; subst. apply guarded_utyp__unit.
  - inversion Hc; subst. apply guarded_utyp__var.
  - inversion Hc; subst. apply guarded_utyp__arrow.
    + eapply d_consis_lc_utyp; eauto.
    + eapply d_consis_lc_utyp; eauto.
Qed.

Fixpoint mode_fn_n_subst (m_orig m_new : mode) : mode :=
  match m_orig with
  | mode_ti => m_new
  | mode_tc => mode_tc
  | mode_fn m => mode_fn (mode_fn_n_subst m m_new)
  end.

Lemma is_styp_ptyp_to_btyp_inh_mono : forall A,
    is_styp (ptyp_to_btyp_inh A) -> mono_ptyp A.
Proof.
  induction A; simpl; intros Hst.
  - constructor.
  - inversion Hst.
  - constructor.
  - dependent destruction Hst. constructor; auto.
  - inversion Hst.
Qed.

Lemma d_consis_mono_determines : forall Ψ Γ A B,
    {{ Ψ ⨟ Γ ⊢ (ptyp_to_utyp_syn A) ∼ B }}d ->
    mono_ptyp A ->
    B = ptyp_to_btyp_syn A.
Proof.
  intros Ψ Γ A B Hcons Hmono. generalize dependent B. generalize dependent Ψ.
  induction Hmono; intros Ψ B Hcons; simpl in *.
  - dependent destruction Hcons. reflexivity.
  - dependent destruction Hcons. reflexivity.
  - dependent destruction Hcons.
    f_equal; [ eapply IHHmono1 | eapply IHHmono2 ]; eassumption.
Qed.

Lemma is_styp_arrow_r : forall B1 B2, is_styp (btyp_arrow B1 B2) -> is_styp B2.
Proof. intros B1 B2 H. inversion H; subst; assumption. Qed.

Lemma is_styp_arrow_l : forall B1 B2, is_styp (btyp_arrow B1 B2) -> is_styp B1.
Proof. intros B1 B2 H. inversion H; subst; assumption. Qed.

Lemma d_sub_lc_l : forall m Ψ Γ C B, {{ Ψ ⨟ Γ ⊢[ m ] C ⩽ B }}d -> lc_utyp C.
Proof.
  intros m Ψ Γ C B H. induction H.
  - eapply d_consis_lc_utyp; eassumption.
  - eapply d_consis_lc_utyp; eassumption.
  - pick fresh α.
    match goal with H : forall _ : atom, _ -> lc_utyp _ |- _ => apply (H α); fsetdec end.
  - apply lc_utyp_arrow; [ eapply d_consis_lc_utyp; eassumption | assumption ].
  - apply lc_utyp_of_degree. constructor.
    eapply degree_utyp_wrt_utyp_open_utyp_wrt_utyp_inv.
    apply degree_utyp_wrt_utyp_of_lc_utyp. eassumption.
  - apply lc_utyp_of_degree. constructor.
    eapply degree_utyp_wrt_utyp_open_utyp_wrt_utyp_inv.
    apply degree_utyp_wrt_utyp_of_lc_utyp. eassumption.
Qed.

Lemma consis_mono_arg : forall Ψ Γ A B,
    {{ Ψ ⨟ Γ ⊢ (btyp_to_utyp_syn (ptyp_to_btyp_inh A)) ∼ B }}d ->
    mono_ptyp A ->
    B = ptyp_to_btyp_inh A.
Proof.
  intros Ψ Γ A B Hc Hmono.
  rewrite (ptyp_to_btyp_inh_mono_syn Hmono) in Hc.
  rewrite btyp_to_utyp_syn_ptyp_to_btyp_syn in Hc.
  rewrite (ptyp_to_btyp_inh_mono_syn Hmono).
  eapply d_consis_mono_determines; eassumption.
Qed.

Lemma d_consis_btyp_erase : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d -> btyp_to_ptyp (utyp_to_btyp C) = btyp_to_ptyp B.
Proof.
  intros Ψ Γ C B H.
  induction H; simpl; try reflexivity; try (f_equal; assumption).
  all: f_equal;
    match goal with
    | |- btyp_to_ptyp (utyp_to_btyp ?c) = btyp_to_ptyp ?b =>
        pick fresh α for (L `union` ftvar_in_ptyp (btyp_to_ptyp (utyp_to_btyp c))
                          `union` ftvar_in_ptyp (btyp_to_ptyp b))
    end;
    apply open_ptyp_wrt_ptyp_inj with (α1 := α);
      [ fsetdec
      | fsetdec
      | match goal with
        | H0 : forall _ : atom, _ -> _ = _ |- _ =>
            specialize (H0 α ltac:(solve_notin_auto));
            rewrite utyp_to_btyp_open, !btyp_to_ptyp_open in H0; simpl in H0; exact H0
        end ].
Qed.

Lemma d_consis_erase_tags : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    exists Ψ', {{ Ψ' ⨟ Γ ⊢ (btyp_to_utyp_syn (utyp_to_btyp C)) ∼ B }}d.
Proof.
  intros Ψ Γ C B H. induction H.
  -  exists empty. apply d_consis__unit. reflexivity.
  -  exists empty. simpl. apply d_consis__var; [ assumption | reflexivity ].
  -
    pick fresh α0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 α0 ltac:(solve_notin_auto)) as [Ψ'0 HΨ'0].
    rewrite btyp_to_utyp_syn_utyp_to_btyp_open_var in HΨ'0.
    exists Ψ'0. simpl.
    apply d_consis__forall_inh_untagged with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton α0).
    intros α Hα.
    rewrite (subst_utyp_in_utyp_intro α0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro α0) by fsetdec.
    apply (@d_consis_rename_tvar _ _ _ _ HΨ'0 nil Γ α0 α); [ reflexivity | simpl; fsetdec ].
  -
    pick fresh α0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 α0 ltac:(solve_notin_auto)) as [Ψ'0 HΨ'0].
    rewrite btyp_to_utyp_syn_utyp_to_btyp_open_var in HΨ'0.
    exists Ψ'0. simpl.
    apply d_consis__forall_inh_untagged with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton α0).
    intros α Hα.
    rewrite (subst_utyp_in_utyp_intro α0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro α0) by fsetdec.
    apply (@d_consis_rename_tvar _ _ _ _ HΨ'0 nil Γ α0 α); [ reflexivity | simpl; fsetdec ].
  -
    pick fresh α0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 α0 ltac:(solve_notin_auto)) as [Ψ'0 HΨ'0].
    rewrite btyp_to_utyp_syn_utyp_to_btyp_open_var in HΨ'0.
    exists Ψ'0. simpl.
    apply d_consis__forall_syn with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton α0).
    intros α Hα.
    rewrite (subst_utyp_in_utyp_intro α0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro α0) by fsetdec.
    apply (@d_consis_rename_tvar _ _ _ _ HΨ'0 nil Γ α0 α); [ reflexivity | simpl; fsetdec ].
  -
    pick fresh α0 for (L `union` dom Γ
       `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
       `union` ftvar_in_btyp B).
    destruct (H0 α0 ltac:(solve_notin_auto)) as [Ψ'0 HΨ'0].
    rewrite btyp_to_utyp_syn_utyp_to_btyp_open_var in HΨ'0.
    exists Ψ'0. simpl.
    apply d_consis__forall_syn with
      (L := dom Γ `union` ftvar_in_utyp (btyp_to_utyp_syn (utyp_to_btyp C))
            `union` ftvar_in_btyp B `union` singleton α0).
    intros α Hα.
    rewrite (subst_utyp_in_utyp_intro α0) by fsetdec.
    rewrite (subst_btyp_in_btyp_intro α0) by fsetdec.
    apply (@d_consis_rename_tvar _ _ _ _ HΨ'0 nil Γ α0 α); [ reflexivity | simpl; fsetdec ].
  -
    destruct IHd_consis1 as [Ψ1' H1']. destruct IHd_consis2 as [Ψ2' H2'].
    exists (Ψ1' `union` Ψ2'). simpl.
    eapply d_consis__arrow; [ eassumption | eassumption | reflexivity ].
Qed.

Lemma d_consis_trans_mid_nil : forall Ψ1 Ψ2 Γ C Cmid B,
    lc_utyp Cmid ->
    is_styp B ->
    {{ Ψ1 ⨟ Γ ⊢ C ∼ (utyp_to_btyp Cmid) }}d ->
    {{ Ψ2 ⨟ Γ ⊢ Cmid ∼ B }}d ->
    {{ empty ⨟ Γ ⊢ C ∼ B }}d.
Proof.
  intros Ψ1 Ψ2 Γ C Cmid B Hlc Hsyn HT HCmid.
  destruct (d_consis_erase_tags HCmid) as [Ψ2' Herase].
  eapply (d_consis_compose_syn_nil_l (B2 := utyp_to_btyp Cmid)).
  - apply is_styp_utyp_to_btyp; exact Hlc.
  - exact Hsyn.
  - exact HT.
  - exact Herase.
Qed.

Inductive utyp_tag_refines_in : atoms -> utyp -> utyp -> Prop :=
| utri_unit  : forall V, utyp_tag_refines_in V utyp_unit utyp_unit
| utri_var_b : forall V n, utyp_tag_refines_in V (utyp_var_b n) (utyp_var_b n)
| utri_var_f : forall V α, utyp_tag_refines_in V (utyp_var_f α) (utyp_var_f α)
| utri_arrow : forall V T1 T2 C1 C2,
    utyp_tag_refines_in V T1 C1 -> utyp_tag_refines_in V T2 C2 ->
    utyp_tag_refines_in V (utyp_arrow T1 T2) (utyp_arrow C1 C2)
| utri_tag_tag : forall V ε T0 C0,
    utyp_tag_refines_in V T0 C0 ->
    utyp_tag_refines_in V (utyp_all_tag ε T0) (utyp_all_tag ε C0)
| utri_tag_syn : forall V ε T0 C0,

    ε `in` V ->
    utyp_tag_refines_in V T0 C0 ->
    utyp_tag_refines_in V (utyp_all_tag ε T0) (utyp_all_syn C0)
| utri_syn_syn : forall V T0 C0,
    utyp_tag_refines_in V T0 C0 ->
    utyp_tag_refines_in V (utyp_all_syn T0) (utyp_all_syn C0).

#[local] Hint Constructors utyp_tag_refines_in : core.

Lemma utyp_tag_refines_in_ftag : forall V C' C,
    utyp_tag_refines_in V C' C ->
    ftag_in_utyp C' [<=] (ftag_in_utyp C) `union` V.
Proof. induction 1; simpl; fsetdec. Qed.

Lemma utyp_tag_refines_in_ftvar : forall V C' C,
    utyp_tag_refines_in V C' C -> ftvar_in_utyp C' [=] ftvar_in_utyp C.
Proof. induction 1; simpl; fsetdec. Qed.

Lemma utyp_tag_refines_in_refl : forall V C, utyp_tag_refines_in V C C.
Proof. intros V C. induction C; constructor; assumption. Qed.

Lemma utyp_tag_refines_in_open_rec_gen : forall V C' C,
    utyp_tag_refines_in V C' C ->
    forall k C0',
      utyp_tag_refines_in V (open_utyp_wrt_utyp_rec k C0' C')
                            (open_utyp_wrt_utyp_rec k C0' C).
Proof.
  induction 1; intros k C0'; simpl; try solve [ constructor; auto ].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?];
    solve [ apply utri_var_b | apply utyp_tag_refines_in_refl ].
Qed.

Lemma utyp_tag_refines_in_open_gen : forall V C' C C0,
    utyp_tag_refines_in V C' C ->
    utyp_tag_refines_in V (open_utyp_wrt_utyp C' C0) (open_utyp_wrt_utyp C C0).
Proof.
  intros V C' C C0 H. unfold open_utyp_wrt_utyp.
  apply utyp_tag_refines_in_open_rec_gen; exact H.
Qed.

Lemma utyp_tag_refines_in_close_rec : forall V C' C,
    utyp_tag_refines_in V C' C ->
    forall k β,
      utyp_tag_refines_in V (close_utyp_wrt_utyp_rec k β C')
                            (close_utyp_wrt_utyp_rec k β C).
Proof.
  induction 1; intros k β; simpl; auto using utyp_tag_refines_in_refl.
Qed.

Lemma consis_refines_paint_body : forall V L C B,
    (forall α, α `notin` L ->
       utyp_tag_refines_in V (open_utyp_wrt_utyp C (utyp_var_f α))
                        (btyp_to_utyp_syn (open_btyp_wrt_btyp B (btyp_var_f α)))) ->
    utyp_tag_refines_in V C (btyp_to_utyp_syn B).
Proof.
  intros V L C B H.
  pick fresh α for (L `union` ftvar_in_utyp C `union` ftvar_in_btyp B).
  specialize (H α ltac:(solve_notin_auto)).
  rewrite btyp_to_utyp_syn_open in H.
  pose proof (utyp_tag_refines_in_close_rec H 0 α) as H'.
  unfold open_utyp_wrt_utyp in H'.
  rewrite !close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec in H'
    by (try rewrite ftvar_btyp_to_utyp_syn; fsetdec).
  exact H'.
Qed.

Lemma consis_refines_paint : forall Ψ Γ C B_A,
    {{ Ψ ⨟ Γ ⊢ C ∼ B_A }}d ->
    forall V, ftag_in_utyp C [<=] V ->
    utyp_tag_refines_in V C (btyp_to_utyp_syn B_A).
Proof.
  intros Ψ Γ C B_A H. induction H; intros V HV; simpl in *.
  - apply utri_unit.
  - apply utri_var_f.
  - apply utri_tag_syn; [ fsetdec | ].
    apply consis_refines_paint_body with (L := L). intros α Hα.
    apply H0; [ exact Hα | rewrite ftag_in_utyp_open_var; fsetdec ].
  - apply utri_syn_syn.
    apply consis_refines_paint_body with (L := L). intros α Hα.
    apply H0; [ exact Hα | rewrite ftag_in_utyp_open_var; fsetdec ].
  - apply utri_tag_syn; [ fsetdec | ].
    apply consis_refines_paint_body with (L := L). intros α Hα.
    apply H0; [ exact Hα | rewrite ftag_in_utyp_open_var; fsetdec ].
  - apply utri_syn_syn.
    apply consis_refines_paint_body with (L := L). intros α Hα.
    apply H0; [ exact Hα | rewrite ftag_in_utyp_open_var; fsetdec ].
  - apply utri_arrow; [ apply IHd_consis1 | apply IHd_consis2 ]; fsetdec.
Qed.

Lemma utyp_tag_refines_compose_mono : forall V C' C,
    utyp_tag_refines_in V C' C ->
    forall B, compose_tags C B [<=] compose_tags C' B.
Proof.
  induction 1; intros B0; destruct B0; simpl; try fsetdec;
    try (specialize (IHutyp_tag_refines_in1 B0_1);
         specialize (IHutyp_tag_refines_in2 B0_2); fsetdec);
    specialize (IHutyp_tag_refines_in B0); fsetdec.
Qed.

Lemma d_consis_ctx_subset_compose : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d ->
    Ψ [<=] compose_tags C B.
Proof.
  intros Ψ Γ C B H. induction H; simpl;
    try (pick fresh α; match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
           specialize (IH α ltac:(solve_notin_auto)) end;
         rewrite compose_tags_open in *); fsetdec.
Qed.

Local Ltac swap_body H0 :=
  intros α Hα;
  match goal with |- {{ compose_tags ?Tb ?Bb ⨟ _ ⊢ _ ∼ _ }}d =>
    rewrite <- (compose_tags_open Tb Bb α α) end;
  eapply (H0 α Hα); apply utyp_tag_refines_in_open_gen; eassumption.

Lemma refines_consis_swap : forall Ψ Γ Cmid B,
    {{ Ψ ⨟ Γ ⊢ Cmid ∼ B }}d ->

    forall V C', utyp_tag_refines_in V C' Cmid ->
      {{ (compose_tags C' B) ⨟ Γ ⊢ C' ∼ B }}d.
Proof.
  intros Ψ Γ Cmid B H. induction H; intros V C' Href;
    inversion Href; subst; simpl.
  - apply d_consis__unit. reflexivity.
  - apply d_consis__var; [ assumption | reflexivity ].
  - eapply d_consis__forall_inh_tagged with (L := L); [ | reflexivity ]; swap_body H0.
  - eapply d_consis__forall_inh_tagged with (L := L); [ | reflexivity ]; swap_body H0.
  - apply d_consis__forall_inh_untagged with (L := L). swap_body H0.
  - apply d_consis__forall_syn_tagged with (L := L). swap_body H0.
  - apply d_consis__forall_syn_tagged with (L := L). swap_body H0.
  - apply d_consis__forall_syn with (L := L). swap_body H0.
  - eapply d_consis__arrow; [ eapply IHd_consis1 | eapply IHd_consis2 | reflexivity ];
      eassumption.
Qed.

Lemma d_consis_sub_trans_mid_tagsin : forall U M Ψ2 Γ Cmid B,
    d_sub_tagsin U M Ψ2 Γ Cmid B ->
    forall Ψ1 C' V,
      {{ Ψ1 ⨟ Γ ⊢ C' ∼ (utyp_to_btyp Cmid) }}d ->
      utyp_tag_refines_in V C' Cmid ->
      U ∩ V [=] empty ->
      exists Δ, Ψ2 [<=] Δ /\ {{ Δ ⨟ Γ ⊢[ M ] C' ⩽ B }}d.
Proof.
  intros U M Ψ2 Γ Cmid B Hsub.
  induction Hsub; intros Ψ0 C' V Hcons Href Hdisj.
  -
    exists empty. split; [ fsetdec | ].
    apply d_sub__infer.
    + apply (d_consis_trans_mid_nil (Cmid := C) (Ψ1 := Ψ0) (Ψ2 := empty)).
      * exact (d_consis_lc_utyp H).
      * exact H0.
      * exact Hcons.
      * exact H.
    + exact H0.
    + reflexivity.
  -
    assert (HgT : guarded_utyp C') by (eapply d_consis_guarded_lhs; [ exact H | exact Hcons ]).
    exists (compose_tags C' B). split.
    + pose proof (d_consis_ctx_subset_compose H1) as Hc1.
      pose proof (utyp_tag_refines_compose_mono Href B) as Hc2. fsetdec.
    + apply d_sub__check;
        [ exact HgT | exact H0
        | apply (refines_consis_swap H1 Href)
        | exact H2 ].
  -
    assert (Hftv : ftvar_in_utyp C' [=] ftvar_in_utyp C)
      by (eapply utyp_tag_refines_in_ftvar; exact Href).
    destruct (IHHsub Ψ0 C' V
                ltac:(apply d_consis_weakening_head; exact Hcons) Href Hdisj)
      as [Ψ' [Hbnd HΨ']].
    exists Ψ'. split; [ exact Hbnd | ].
    apply d_sub__forall_r with
      (L := dom Γ `union` ftvar_in_utyp C' `union` ftvar_in_btyp B
            `union` singleton α).
    intros α2 Hα2.
    rewrite (subst_btyp_in_btyp_intro α) by (clear - H; fsetdec).
    rewrite <- (subst_utyp_in_utyp_fresh_eq C' (utyp_var_f α2) α)
      by (clear - H Hftv; fsetdec).
    apply (@d_sub_rename_tvar _ _ _ _ _ HΨ' nil Γ α α2);
      [ reflexivity | simpl; clear - H Hα2; fsetdec ].
  -
    simpl in Hcons. dependent destruction Hcons.
    dependent destruction Href.
    destruct (IHHsub _ _ V ltac:(eassumption) ltac:(eassumption) Hdisj)
      as [Δc2 [Hbnd2 Hres]].
    match goal with Hr : utyp_tag_refines_in _ ?t C1 |- _ =>
      exists (compose_tags t B1 `union` Δc2) end. split.
    + pose proof (d_consis_ctx_subset_compose H) as Hc1.
      match goal with Hr : utyp_tag_refines_in _ _ C1 |- _ =>
        pose proof (utyp_tag_refines_compose_mono Hr B1) as Hc2 end.
      fsetdec.
    + eapply d_sub__arrow;
        [ match goal with Hr : utyp_tag_refines_in _ _ C1 |- _ =>
            apply (refines_consis_swap H Hr) end
        | exact Hres | reflexivity ].
  -
    dependent destruction Href.
    simpl in Hcons. dependent destruction Hcons.
    pick fresh α for (L `union` dom Γ `union` ftvar_in_utyp T0
                      `union` ftvar_in_utyp C `union` ftvar_in_btyp B
                      `union` Ψ `union` Ψ').
    pose proof (@d_consis_subst_tvar _ _ _ _ (H6 α ltac:(solve_notin_auto)) nil Γ α ph
                  eq_refl ltac:(simpl; exact H4) H5) as Hinst.
    rewrite <- (subst_utyp_in_utyp_intro α T0 ph) in Hinst by fsetdec.
    rewrite <- (subst_btyp_in_btyp_intro α (utyp_to_btyp C) (utyp_to_btyp ph)) in Hinst
      by (rewrite ftvar_utyp_to_btyp; fsetdec).
    rewrite <- utyp_to_btyp_open in Hinst.
    simpl in Hinst.
    pose proof (utyp_tag_refines_in_ftag Href) as Hft.
    destruct (IHHsub _ _ V Hinst
                (utyp_tag_refines_in_open_gen ph Href) Hdisj)
      as [Δ_IH [Hbnd HΔ_IH]].
    exists (Δ_IH ∖ Ψ'). split.
    + clear - Hbnd H0; fsetdec.
    + eapply d_sub__forall_l_tagged with (Ψ' := Ψ').
      * exact H.
      * clear - Hbnd H0; fsetdec.
      *
        simpl in H1 |- *. clear - H1 H2 Hdisj Hft; fsetdec.
      * exact H3.
      * exact H4.
      * exact H5.
      * eapply d_sub_equiv; [ | exact HΔ_IH ]. clear - Hbnd H0; fsetdec.
  -
    simpl in Hcons.
    dependent destruction Hcons.
    +
      dependent destruction Href.
      pick fresh α for (L `union` dom Γ `union` ftvar_in_utyp C0
                        `union` ftvar_in_utyp C `union` ftvar_in_btyp B
                        `union` Ψ0 `union` Ψ `union` Ψ').
      pose proof (@d_consis_subst_tvar _ _ _ _ (H6 α ltac:(solve_notin_auto)) nil Γ α ph
                    eq_refl ltac:(simpl; exact H4) H5) as Hinst.
      rewrite <- (subst_utyp_in_utyp_intro α C0 ph) in Hinst by fsetdec.
      rewrite <- (subst_btyp_in_btyp_intro α (utyp_to_btyp C) (utyp_to_btyp ph)) in Hinst
        by (rewrite ftvar_utyp_to_btyp; fsetdec).
      rewrite <- utyp_to_btyp_open in Hinst.
      simpl in Hinst.
      pose proof (utyp_tag_refines_in_ftag Href) as Hft.
      destruct (IHHsub _ _ V Hinst
                  (utyp_tag_refines_in_open_gen ph Href) Hdisj)
        as [Δ_IH [Hbnd HΔ_IH]].
      exists (Δ_IH ∖ Ψ'). split.
      * clear - Hbnd H0; fsetdec.
      * eapply d_sub__forall_l_tagged with (Ψ' := Ψ').
        -- exact H.
        -- clear - Hbnd H0; fsetdec.
        --
           simpl in H1 |- *. clear - H1 H2 Hdisj Hft H7; fsetdec.
        -- exact H3.
        -- exact H4.
        -- exact H5.
        -- eapply d_sub_equiv; [ | exact HΔ_IH ]. clear - Hbnd H0; fsetdec.
    +
      dependent destruction Href.
      pick fresh α for (L `union` dom Γ `union` ftvar_in_utyp C0
                        `union` ftvar_in_utyp C `union` ftvar_in_btyp B
                        `union` Ψ0 `union` Ψ `union` Ψ').
      pose proof (@d_consis_subst_tvar _ _ _ _ (H6 α ltac:(solve_notin_auto)) nil Γ α ph
                    eq_refl ltac:(simpl; exact H4) H5) as Hinst.
      rewrite <- (subst_utyp_in_utyp_intro α C0 ph) in Hinst by fsetdec.
      rewrite <- (subst_btyp_in_btyp_intro α (utyp_to_btyp C) (utyp_to_btyp ph)) in Hinst
        by (rewrite ftvar_utyp_to_btyp; fsetdec).
      rewrite <- utyp_to_btyp_open in Hinst.
      simpl in Hinst.
      pose proof (utyp_tag_refines_in_ftag Href) as Hft.
      destruct (IHHsub _ _ V Hinst
                  (utyp_tag_refines_in_open_gen ph Href) Hdisj)
        as [Δ_IH [Hbnd HΔ_IH]].
      exists (Δ_IH ∖ Ψ'). split.
      * clear - Hbnd H0; fsetdec.
      * eapply d_sub__forall_l_untagged with (Ψ' := Ψ').
        -- exact H.
        -- clear - Hbnd H0; fsetdec.
        -- simpl in H1 |- *. clear - H1 H2 Hdisj Hft; fsetdec.
        -- exact H3.
        -- exact H4.
        -- exact H5.
        -- eapply d_sub_equiv; [ | exact HΔ_IH ]. clear - Hbnd H0; fsetdec.
Qed.

Lemma d_consis_sub_trans_mid : forall M Ψ2 Γ Cmid B,
    {{ Ψ2 ⨟ Γ ⊢[ M ] Cmid ⩽ B }}d ->
    Ψ2 [=] empty ->
    ftag_in_utyp Cmid [=] empty ->
    forall Ψ1 C',
      {{ Ψ1 ⨟ Γ ⊢ C' ∼ (utyp_to_btyp Cmid) }}d ->
      utyp_tag_refines_in (ftag_in_utyp C') C' Cmid ->
      exists Ψ, Ψ2 [<=] Ψ /\ {{ Ψ ⨟ Γ ⊢[ M ] C' ⩽ B }}d.
Proof.
  intros M Ψ2 Γ Cmid B Hsub HΨ HC Ψ1 C' Hcons Href.
  destruct (d_sub_freshen M Ψ2 Γ Cmid B (ftag_in_utyp C') Hsub
              ltac:(rewrite HΨ; clear; fsetdec)
              ltac:(rewrite HC; clear; fsetdec))
    as [ U [ Hfresh Htagsin ] ].
  eapply d_consis_sub_trans_mid_tagsin;
    [ exact Htagsin | exact Hcons | exact Href
    | clear - Hfresh; fsetdec ].
Qed.

Lemma d_consis_sub_trans : forall M Ψb Γ C B,
    {{ Ψb ⨟ Γ ⊢[ M ] C ⩽ B }}d ->
    Ψb [=] empty ->
    forall B_A C' Ψt,
      C = btyp_to_utyp_syn B_A ->
      is_styp B_A ->
      {{ Ψt ⨟ Γ ⊢ C' ∼ B_A }}d ->
      exists Ψ, Ψb [<=] Ψ /\ {{ Ψ ⨟ Γ ⊢[ M ] C' ⩽ B }}d.
Proof.
  intros M Ψb Γ C B Hsub HΔ B_A C' Ψt Heq Hsyn Hcons. subst C.
  eapply d_consis_sub_trans_mid;
    [ exact Hsub | exact HΔ | apply ftag_btyp_to_utyp_syn | | ].
  - rewrite utyp_to_btyp_btyp_to_utyp_syn by assumption. exact Hcons.
  - eapply consis_refines_paint; [ exact Hcons | reflexivity ].
Qed.

Inductive is_fn_n : nat -> mode -> Prop :=
| is_fn_n__ti : is_fn_n 0 mode_ti
| is_fn_n__fn : forall n m, is_fn_n n m -> is_fn_n (S n) (mode_fn m).

Inductive btyp_spine : nat -> btyp -> btyp -> btyp -> btyp -> Prop :=
| btyp_spine__tail : forall A Bnew,
    is_styp A ->
    btyp_spine 0 A A Bnew Bnew
| btyp_spine__arrow : forall n B1 B2 A Bnew B2',
    btyp_spine n B2 A Bnew B2' ->
    btyp_spine (S n) (btyp_arrow B1 B2) A Bnew (btyp_arrow B1 B2').

Lemma d_sub_trans_spine : forall m1 Ψ Γ C Bfull,
    {{ Ψ ⨟ Γ ⊢[ m1 ] C ⩽ Bfull }}d ->
    forall n B' M B Bres,
      is_fn_n n m1 ->
      btyp_spine n Bfull B' B Bres ->
      {{ empty ⨟ Γ ⊢[ M ] (btyp_to_utyp_syn B') ⩽ B }}d ->
      exists Ψ', Ψ [<=] Ψ' /\ {{ Ψ' ⨟ Γ ⊢[ mode_fn_n_subst m1 M ] C ⩽ Bres }}d.
Proof.
  intros m1 Ψ Γ C Bfull Hsub.
  induction Hsub; intros n A0 M0 B0 Bres Hfn Hspine Htail.
  -
    inversion Hfn; subst.
    dependent destruction Hspine.
    edestruct (d_consis_sub_trans_mid Htail) as [Ψ' [_ HΨ']].
    +
      clear; fsetdec.
    +
      apply ftag_btyp_to_utyp_syn.
    + rewrite utyp_to_btyp_btyp_to_utyp_syn by eassumption.
      eassumption.
    + eapply consis_refines_paint; [ eassumption | reflexivity ].
    + exists Ψ'. split; [ fsetdec | simpl; exact HΨ' ].
  -
    inversion Hfn.
  -
    inversion Hfn.
  -
    inversion Hfn; subst.
    dependent destruction Hspine.
    edestruct IHHsub as [Ψ2' [Hb2 Hres]];
      [ eassumption | eassumption | eassumption | ].
    exists (Ψ1 `union` Ψ2'). split.
    + fsetdec.
    + simpl. eapply d_sub__arrow; [ eassumption | exact Hres | reflexivity ].
  -
    edestruct IHHsub as [Ψr [Hb Hr]];
      [ eassumption | eassumption | eassumption | ].
    exists (Ψr ∖ Ψ'). split.
    + fsetdec.
    + eapply d_sub__forall_l_tagged with (Ψ' := Ψ').
      * destruct m as [ | | m']; simpl;
          [ exfalso; apply H; reflexivity | discriminate | discriminate ].
      * fsetdec.
      * eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
      * eapply d_sub_equiv; [ | exact Hr ]. fsetdec.
  -
    edestruct IHHsub as [Ψr [Hb Hr]];
      [ eassumption | eassumption | eassumption | ].
    exists (Ψr ∖ Ψ'). split.
    + fsetdec.
    + eapply d_sub__forall_l_untagged with (Ψ' := Ψ').
      * destruct m as [ | | m']; simpl;
          [ exfalso; apply H; reflexivity | discriminate | discriminate ].
      * fsetdec.
      * eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
      * eapply d_sub_equiv; [ | exact Hr ]. fsetdec.
Qed.

Lemma consis_guarded_btyp_lhs : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d -> guarded_btyp B -> guarded_utyp C.
Proof.
  intros Ψ Γ C B Hc Hg.
  inversion Hc; subst; try (inversion Hg; fail).
  - auto with fresco.
  - auto with fresco.
  - apply guarded_utyp__arrow; eapply d_consis_lc_utyp; eassumption.
Qed.

Lemma d_consis_syn_sub_tc : forall Bn, is_ityp Bn ->
    forall Δ Γ B',
      {{ Δ ⨟ Γ ⊢ (btyp_to_utyp_syn B') ∼ Bn }}d ->
      {{ Δ ⨟ Γ ⊢[ mode_tc ] (btyp_to_utyp_syn B') ⩽ Bn }}d.
Proof.
  intros Bn Hityp.
  induction Hityp; intros Δ Γ B' Hcons.
  -
    apply d_sub__check;
      [ eapply consis_guarded_btyp_lhs; [ exact Hcons | apply guarded_btyp__unit ]
      | apply guarded_btyp__unit | exact Hcons | apply is_ityp__unit ].
  -
    apply d_sub__check;
      [ eapply consis_guarded_btyp_lhs; [ exact Hcons | apply guarded_btyp__var ]
      | apply guarded_btyp__var | exact Hcons | apply is_ityp__var ].
  -
    apply d_sub__check;
      [ eapply consis_guarded_btyp_lhs;
          [ exact Hcons | apply guarded_btyp__arrow; apply is_ityp_lc; assumption ]
      | apply guarded_btyp__arrow; apply is_ityp_lc; assumption
      | exact Hcons | apply is_ityp__arrow; assumption ].
  -
    destruct B'; simpl in Hcons; try solve [ inversion Hcons ];
      dependent destruction Hcons;
      match goal with
      | Hc : forall α0, α0 `notin` ?L1 -> {{ _ ⨟ _ ⊢ _ ∼ _ }}d |- _ =>
          apply d_sub__forall_r with (L := L `union` L1 `union` dom Γ);
          intros α Hα;
          apply d_sub__forall_l_untagged with (Ψ' := (@empty : atoms)) (ph := utyp_var_f α);
          [ intro Hco; discriminate
          | fsetdec
          | clear; fsetdec
          | apply d_tags__var; reflexivity
          | apply d_wf_utyp__var; simpl; auto
          | apply is_dtyp__var
          | specialize (Hc α ltac:(clear -Hα; solve_notin_auto));
            change (utyp_var_f α) with (btyp_to_utyp_syn (btyp_var_f α)) in Hc |- *;
            rewrite <- btyp_to_utyp_syn_open in Hc |- *;
            apply d_sub_equiv with (Ψ := Ψ); [ clear; fsetdec | ];
            apply H0; [ clear -Hα; fsetdec | exact Hc ] ]
      end.
Qed.

Lemma btyp_spine_skmod : forall n Bfull B Bnew Bres m M,
    btyp_spine n Bfull B Bnew Bres ->
    is_fn_n n m ->
    mod_comp_ty Bnew M ->
    mod_comp_ty Bres (mode_fn_n_subst m M).
Proof.
  intros n Bfull B Bnew Bres m M Hsp. revert m M.
  induction Hsp; intros m M Hfn Hsk.
  - inversion Hfn; subst. simpl. exact Hsk.
  - inversion Hfn; subst. simpl. apply mod_comp_ty__fn. eapply IHHsp; eassumption.
Qed.

Lemma d_sd_typing_abs_tail_gen : forall L0 e A Bbody M Bnew Γ',
    mono_ptyp A ->
    is_styp Bbody ->
    d_wf_ptyp Γ' A ->
    (forall Γ'' x M' B'',
       denv_binds_le Γ' Γ'' ->
       x `notin` (L0 `union` dom Γ'') ->
       {{ empty ⨟ ((x ~ dbind_typ A) ++ Γ'') ⊢[ M' ] (btyp_to_utyp_syn Bbody) ⩽ B'' }}d ->
       {{ ((x ~ dbind_typ A) ++ Γ'') ⊢ˢᵈ[ M' ] open_exp_wrt_exp e (exp_var_f x) ⦂ B'' }}d) ->
    {{ empty ⨟ Γ' ⊢[ M ]
      (utyp_arrow (btyp_to_utyp_syn (ptyp_to_btyp_inh A)) (btyp_to_utyp_syn Bbody)) ⩽ Bnew }}d ->
    {{ Γ' ⊢ˢᵈ[ M ] exp_abs e ⦂ Bnew }}d.
Proof.
  intros L0 e A Bbody M Bnew Γ' Hmono Hstyp Hwf Hbody Hsub.
  remember (utyp_arrow (btyp_to_utyp_syn (ptyp_to_btyp_inh A))
              (btyp_to_utyp_syn Bbody)) as Clhs eqn:HC.
  remember (@empty) as Ψ0 eqn:HD.
  revert Hwf Hbody.
  induction Hsub; intros Hwf Hbody; try (exfalso; discriminate HC).
  -
    subst. dependent destruction H.
    rename B1 into Bn1. rename B2 into Bn2.
    pose proof (consis_mono_arg H Hmono) as HBn1. subst Bn1.
    apply d_sd_typing__abs with (L := L0 `union` dom Γ) (A := A).
    + discriminate.
    + assumption.
    + apply mod_comp_ty__ti. assumption.
    + intros xv Hxv.
      eapply (Hbody Γ xv mode_ti Bn2 (denv_binds_le_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      apply d_sub__infer; [ | exact (is_styp_arrow_r H2) | reflexivity ].
      eapply d_consis_equiv; [ | eassumption ]. fsetdec.
  -
    subst. dependent destruction H1.
    rename B1 into Bn1. rename B2 into Bn2.
    match goal with
    | Harg : {{ _ ⨟ _ ⊢ btyp_to_utyp_syn (ptyp_to_btyp_inh A) ∼ Bn1 }}d |- _ =>
        pose proof (consis_mono_arg Harg Hmono) as HBn1
    end. subst Bn1.
    match goal with Hit : is_ityp (btyp_arrow _ Bn2) |- _ => inversion Hit; subst end.
    apply d_sd_typing__abs_check_base with (L := L0 `union` dom Γ).
    + assumption.
    + assumption.
    + intros xv Hxv.
      eapply (Hbody Γ xv mode_tc Bn2 (denv_binds_le_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      eapply d_consis_syn_sub_tc;
        [ match goal with Hit : is_ityp Bn2 |- _ => exact Hit end
        | match goal with Hbc : {{ _ ⨟ _ ⊢ btyp_to_utyp_syn Bbody ∼ Bn2 }}d |- _ =>
            eapply d_consis_equiv; [ | exact Hbc ]; fsetdec end ].
  -
    subst.
    apply d_sd_typing__abs_check_step with (L := L `union` L0 `union` dom Γ).
    + intros α Hα.
      eapply (H0 α ltac:(solve_notin_auto)); [ reflexivity | reflexivity | | ].
      * apply d_wf_ptyp_tvar_mono with (Γ := Γ);
          [ assumption | apply denv_tbinds_le_of_binds_le, denv_binds_le_weaken_l ].
      * intros Γ'' xv M' B'' Hcw Hfr Hsb.
        eapply (Hbody Γ'' xv M' B''); [ | exact Hfr | exact Hsb ].
        eapply denv_binds_le_trans; [ apply denv_binds_le_weaken_l | exact Hcw ].
  -
    subst. injection HC; intros; subst.
    pose proof (consis_mono_arg H Hmono) as HBn1. subst B1.
    apply d_sd_typing__abs with (L := L0 `union` dom Γ) (A := A).
    + discriminate.
    + assumption.
    + apply mod_comp_ty__fn.
      match goal with Hs : {{ _ ⨟ _ ⊢[ _ ] btyp_to_utyp_syn Bbody ⩽ B2 }}d |- _ =>
        exact (d_sub_skmod Hs) end.
    + intros xv Hxv.
      eapply (Hbody Γ xv m B2 (denv_binds_le_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      match goal with Hs : {{ _ ⨟ _ ⊢[ _ ] btyp_to_utyp_syn Bbody ⩽ B2 }}d |- _ =>
        eapply d_sub_equiv; [ | exact Hs ] end.
      fsetdec.
Qed.

Lemma d_sd_typing_abs_anno_tail_gen : forall L0 e A Barg Bbody M Bnew Γ',
    is_styp Barg ->
    btyp_to_ptyp Barg = A ->
    is_styp Bbody ->
    d_wf_ptyp Γ' A ->
    (forall Γ'' x M' B'',
       denv_binds_le Γ' Γ'' ->
       x `notin` (L0 `union` dom Γ'') ->
       {{ empty ⨟ ((x ~ dbind_typ A) ++ Γ'') ⊢[ M' ] (btyp_to_utyp_syn Bbody) ⩽ B'' }}d ->
       {{ ((x ~ dbind_typ A) ++ Γ'') ⊢ˢᵈ[ M' ] open_exp_wrt_exp e (exp_var_f x) ⦂ B'' }}d) ->
    {{ empty ⨟ Γ' ⊢[ M ]
      (utyp_arrow (btyp_to_utyp_syn Barg) (btyp_to_utyp_syn Bbody)) ⩽ Bnew }}d ->
    {{ Γ' ⊢ˢᵈ[ M ] exp_abs_anno A e ⦂ Bnew }}d.
Proof.
  intros L0 e A Barg Bbody M Bnew Γ' HsBarg HBargA Hstyp Hwf Hbody Hsub. subst A.
  remember (utyp_arrow (btyp_to_utyp_syn Barg) (btyp_to_utyp_syn Bbody)) as Clhs eqn:HC.
  remember (@empty) as Ψ0 eqn:HD.
  revert Hwf Hbody.
  induction Hsub; intros Hwf Hbody; try (exfalso; discriminate HC).
  -
    subst. dependent destruction H. rename B1 into Bn1. rename B2 into Bn2.
    assert (Herase : btyp_to_ptyp Bn1 = btyp_to_ptyp Barg).
    { pose proof (d_consis_btyp_erase H) as He.
      rewrite (utyp_to_btyp_btyp_to_utyp_syn HsBarg) in He.
      symmetry. exact He. }
    apply d_sd_typing__abs_anno with (L := L0 `union` dom Γ) (B1 := Bn1).
    + discriminate.
    + assumption.
    + exact Herase.
    + apply mod_comp_ty__ti; assumption.
    + intros xv Hxv.
      eapply (Hbody Γ xv mode_ti Bn2 (denv_binds_le_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      apply d_sub__infer; [ | exact (is_styp_arrow_r H2) | reflexivity ].
      eapply d_consis_equiv; [ | eassumption ]. fsetdec.
  -
    subst. dependent destruction H1.
    rename B1 into Bn1. rename B2 into Bn2.
    assert (Herase : btyp_to_ptyp Bn1 = btyp_to_ptyp Barg).
    { match goal with Harg : {{ _ ⨟ _ ⊢ btyp_to_utyp_syn Barg ∼ Bn1 }}d |- _ =>
        pose proof (d_consis_btyp_erase Harg) as He end.
      rewrite (utyp_to_btyp_btyp_to_utyp_syn HsBarg) in He.
      symmetry. exact He. }
    match goal with Hit : is_ityp (btyp_arrow _ Bn2) |- _ => inversion Hit; subst end.
    assert (HBn1 : Bn1 = ptyp_to_btyp_inh (btyp_to_ptyp Barg)).
    { rewrite <- Herase. symmetry. apply ptyp_to_btyp_inh_btyp_to_ptyp. assumption. }
    rewrite HBn1.
    apply d_sd_typing__abs_anno_check_base with (L := L0 `union` dom Γ).
    + assumption.
    + assumption.
    + intros xv Hxv.
      eapply (Hbody Γ xv mode_tc Bn2 (denv_binds_le_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      eapply d_consis_syn_sub_tc;
        [ match goal with Hit : is_ityp Bn2 |- _ => exact Hit end
        | match goal with Hbc : {{ _ ⨟ _ ⊢ btyp_to_utyp_syn Bbody ∼ Bn2 }}d |- _ =>
            eapply d_consis_equiv; [ | exact Hbc ]; fsetdec end ].
  -
    subst.
    apply d_sd_typing__abs_anno_check_step with (L := L `union` L0 `union` dom Γ).
    + intros α Hα.
      eapply (H0 α ltac:(solve_notin_auto)); [ reflexivity | reflexivity | | ].
      * apply d_wf_ptyp_tvar_mono with (Γ := Γ);
          [ assumption | apply denv_tbinds_le_of_binds_le, denv_binds_le_weaken_l ].
      * intros Γ'' xv M' B'' Hcw Hfr Hsb.
        eapply (Hbody Γ'' xv M' B''); [ | exact Hfr | exact Hsb ].
        eapply denv_binds_le_trans; [ apply denv_binds_le_weaken_l | exact Hcw ].
  -
    subst. injection HC; intros; subst.
    assert (Herase : btyp_to_ptyp B1 = btyp_to_ptyp Barg).
    { pose proof (d_consis_btyp_erase H) as He.
      rewrite (utyp_to_btyp_btyp_to_utyp_syn HsBarg) in He.
      symmetry. exact He. }
    apply d_sd_typing__abs_anno with (L := L0 `union` dom Γ) (B1 := B1).
    + discriminate.
    + assumption.
    + exact Herase.
    + apply mod_comp_ty__fn.
      match goal with Hs : {{ _ ⨟ _ ⊢[ _ ] btyp_to_utyp_syn Bbody ⩽ B2 }}d |- _ =>
        exact (d_sub_skmod Hs) end.
    + intros xv Hxv.
      eapply (Hbody Γ xv m B2 (denv_binds_le_refl Γ) ltac:(solve_notin_auto)).
      apply d_sub_weakening_head.
      match goal with Hs : {{ _ ⨟ _ ⊢[ _ ] btyp_to_utyp_syn Bbody ⩽ B2 }}d |- _ =>
        eapply d_sub_equiv; [ | exact Hs ] end.
      fsetdec.
Qed.

Lemma d_tags_tags : forall Ψ C, d_tags Ψ C -> Ψ [=] ftag_in_utyp C.
Proof.
  intros Ψ C H. induction H; simpl.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - pick fresh α for (L `union` ftvar_in_utyp C).
    match goal with IH : forall _, _ -> _ [=] _ |- _ =>
      specialize (IH α ltac:(solve_notin_auto)) end.
    rewrite ftag_in_utyp_open_var in *. fsetdec.
Qed.

Lemma d_consis_ctx_subset_tags : forall Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢ C ∼ B }}d -> Ψ [<=] ftag_in_utyp C.
Proof.
  intros Ψ Γ C B H. induction H; simpl;
    try (pick fresh α for (L `union` ftvar_in_utyp C);
         match goal with IH : forall _, _ -> _ [<=] _ |- _ =>
           specialize (IH α ltac:(solve_notin_auto)) end;
         rewrite ftag_in_utyp_open_var in *); fsetdec.
Qed.

Lemma d_sub_ctx_subset_tags : forall M Ψ Γ C B,
    {{ Ψ ⨟ Γ ⊢[ M ] C ⩽ B }}d -> Ψ [<=] ftag_in_utyp C.
Proof.
  intros M Ψ Γ C B H. induction H; simpl.
  -  fsetdec.
  -  eapply d_consis_ctx_subset_tags; eassumption.
  -
    pick fresh α for L.
    match goal with IH : forall _, _ `notin` _ -> _ [<=] _ |- _ =>
      apply (IH α); fsetdec end.
  -
    match goal with Hc : {{ _ ⨟ _ ⊢ C1 ∼ _ }}d |- _ =>
      pose proof (d_consis_ctx_subset_tags Hc) as Htag end.
    fsetdec.
  -
    pose proof (d_tags_tags H2) as Hph.
    pose proof (ftag_in_utyp_open_upper C ph) as Hopen.
    fsetdec.
  -
    pose proof (d_tags_tags H2) as Hph.
    pose proof (ftag_in_utyp_open_upper C ph) as Hopen.
    fsetdec.
Qed.

Lemma d_sub_paint_lhs_empty : forall M Ψ Γ B B',
    {{ Ψ ⨟ Γ ⊢[ M ] (btyp_to_utyp_syn B) ⩽ B' }}d -> Ψ [=] empty.
Proof.
  intros M Ψ Γ B B' H.
  pose proof (d_sub_ctx_subset_tags H) as Hle.
  rewrite ftag_btyp_to_utyp_syn in Hle. fsetdec.
Qed.

Lemma d_sd_typing_general_subsumption_spine : forall m1 Γ e Bfull,
    {{ Γ ⊢ˢᵈ[ m1 ] e ⦂ Bfull }}d ->
    forall Γ',
      denv_binds_le Γ Γ' ->
      forall n B' M B Bres,
        is_fn_n n m1 ->
        btyp_spine n Bfull B' B Bres ->
        {{ empty ⨟ Γ' ⊢[ M ] (btyp_to_utyp_syn B') ⩽ B }}d ->
        {{ Γ' ⊢ˢᵈ[ mode_fn_n_subst m1 M ] e ⦂ Bres }}d.
Proof.
  intros m1 Γ e Bfull Hty.
  induction Hty; intros Γ' Hcw n A0 M0 B0 Bres Hfn Hspine Htail.
  -
    apply d_sd_typing__unit.
    pose proof (d_sub_tvar_mono H (denv_tbinds_le_of_binds_le Hcw)) as Hs0'.
    edestruct (d_sub_trans_spine Hs0' Hfn Hspine Htail) as [Δ'' [_ HΔ'']].
    pose proof HΔ'' as HΔ''b.
    replace (ptyp_to_utyp_syn ptyp_unit)
      with (btyp_to_utyp_syn (ptyp_to_btyp_syn ptyp_unit)) in HΔ''b
      by (rewrite <- ptyp_to_utyp_syn_btyp_to_ptyp, btyp_to_ptyp_ptyp_to_btyp_syn; reflexivity).
    apply d_sub_equiv with (Ψ := Δ'');
      [ eapply d_sub_paint_lhs_empty; exact HΔ''b | exact HΔ'' ].
  -
    apply d_sd_typing__var with (A := A).
    + eapply Hcw; eassumption.
    + pose proof (d_sub_tvar_mono H0 (denv_tbinds_le_of_binds_le Hcw)) as Hs0'.
      edestruct (d_sub_trans_spine Hs0' Hfn Hspine Htail) as [Δ'' [_ HΔ'']].
      pose proof HΔ'' as HΔ''b.
      replace (ptyp_to_utyp_syn A)
        with (btyp_to_utyp_syn (ptyp_to_btyp_syn A)) in HΔ''b
        by (rewrite <- ptyp_to_utyp_syn_btyp_to_ptyp, btyp_to_ptyp_ptyp_to_btyp_syn; reflexivity).
      apply d_sub_equiv with (Ψ := Δ'');
        [ eapply d_sub_paint_lhs_empty; exact HΔ''b | exact HΔ'' ].
  -
    assert (Hskm : mod_comp_ty Bres (mode_fn_n_subst m M0))
      by (eapply btyp_spine_skmod; [ exact Hspine | exact Hfn | exact (d_sub_skmod Htail) ]).
    dependent destruction Hspine.
    +
      inversion Hfn; subst. simpl.
      eapply d_sd_typing_abs_tail_gen with (L0 := L) (Bbody := B).
      * apply is_styp_ptyp_to_btyp_inh_mono.
        match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_l Hs) end.
      * match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_r Hs) end.
      * eapply d_wf_ptyp_tvar_mono;
          [ | apply denv_tbinds_le_of_binds_le; exact Hcw ]; eassumption.
      * intros Γ'' x M' B'' Hcw'' Hfr Hsb.
        eapply (H3 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ'')).
        -- apply denv_binds_le_cons. eapply denv_binds_le_trans; [ exact Hcw | exact Hcw'' ].
        -- apply is_fn_n__ti.
        -- apply btyp_spine__tail.
           match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_r Hs) end.
        -- exact Hsb.
      * exact Htail.
    +
      dependent destruction Hfn. simpl.
      apply d_sd_typing__abs with (L := L `union` dom Γ') (A := A).
      * discriminate.
      * eapply d_wf_ptyp_tvar_mono;
          [ | apply denv_tbinds_le_of_binds_le; exact Hcw ]; eassumption.
      * exact Hskm.
      * intros x Hx.
        eapply (H3 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ')).
        -- apply denv_binds_le_cons. exact Hcw.
        -- eassumption.
        -- eassumption.
        -- apply d_sub_weakening_head with (Γ' := (x ~ dbind_typ A)). exact Htail.
  -
    inversion Hfn.
  -
    inversion Hfn.
  -
    eapply d_sd_typing__anno.
    + eapply d_sd_typing_mono; eassumption.
    + match goal with Hs : {{ empty ⨟ _ ⊢[ _ ] ptyp_to_utyp_syn _ ⩽ _ }}d |- _ =>
        pose proof (d_sub_tvar_mono Hs (denv_tbinds_le_of_binds_le Hcw)) as Hs0' end.
      edestruct (d_sub_trans_spine Hs0' Hfn Hspine Htail) as [Δ'' [_ HΔ'']].
      pose proof HΔ'' as HΔ''b.
      replace (ptyp_to_utyp_syn A)
        with (btyp_to_utyp_syn (ptyp_to_btyp_syn A)) in HΔ''b
        by (rewrite <- ptyp_to_utyp_syn_btyp_to_ptyp, btyp_to_ptyp_ptyp_to_btyp_syn; reflexivity).
      apply d_sub_equiv with (Ψ := Δ'');
        [ eapply d_sub_paint_lhs_empty; exact HΔ''b | exact HΔ'' ].
  -
    assert (Hskm : mod_comp_ty Bres (mode_fn_n_subst m M0))
      by (eapply btyp_spine_skmod; [ exact Hspine | exact Hfn | exact (d_sub_skmod Htail) ]).
    dependent destruction Hspine.
    +
      inversion Hfn; subst. simpl.
      eapply d_sd_typing_abs_anno_tail_gen with (L0 := L) (Barg := B1) (Bbody := B2).
      * match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_l Hs) end.
      * reflexivity.
      * match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_r Hs) end.
      * eapply d_wf_ptyp_tvar_mono;
          [ | apply denv_tbinds_le_of_binds_le; exact Hcw ]; eassumption.
      * intros Γ'' x M' B'' Hcw'' Hfr Hsb.
        eapply (H4 x ltac:(solve_notin_auto) ((x ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ'')).
        -- apply denv_binds_le_cons. eapply denv_binds_le_trans; [ exact Hcw | exact Hcw'' ].
        -- apply is_fn_n__ti.
        -- apply btyp_spine__tail.
           match goal with Hs : is_styp (btyp_arrow _ _) |- _ => exact (is_styp_arrow_r Hs) end.
        -- exact Hsb.
      * exact Htail.
    +
      dependent destruction Hfn. simpl.
      apply d_sd_typing__abs_anno with (L := L `union` dom Γ') (A := A) (B1 := B1).
      * discriminate.
      * eapply d_wf_ptyp_tvar_mono;
          [ | apply denv_tbinds_le_of_binds_le; exact Hcw ]; eassumption.
      * eassumption.
      * exact Hskm.
      * intros x Hx.
        eapply (H4 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ')).
        -- apply denv_binds_le_cons. exact Hcw.
        -- eassumption.
        -- eassumption.
        -- apply d_sub_weakening_head with (Γ' := (x ~ dbind_typ A)). exact Htail.
  -
    inversion Hfn.
  -
    inversion Hfn.
  -
    inversion Hfn.
  -
    eapply d_sd_typing__app.
    + eapply d_pat_mono; eassumption.
    + eapply d_refine_syn_any_ctx; eassumption.
    + eapply IHHty1.
      * exact Hcw.
      * apply is_fn_n__fn. exact Hfn.
      * apply btyp_spine__arrow. exact Hspine.
      * exact Htail.
    + eapply d_sd_typing_mono; eassumption.
Qed.

Theorem d_sd_typing_general_subsumption : forall Γ e A B m,
    d_wf_denv Γ ->
    {{ Γ ⊢ˢᵈ[ mode_ti ] e ⦂ ptyp_to_btyp_syn A }}d ->
    {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
    {{ Γ ⊢ˢᵈ[ m ] e ⦂ B }}d.
Proof.
  intros Γ e A B m Hwf Hty Hsub.
  assert (Hst : is_styp (ptyp_to_btyp_syn A)).
  {
    apply is_styp_ptyp_to_btyp_syn, lc_ptyp_of_lc_utyp_syn.
    eapply d_sub_lc_l. exact Hsub. }
  eapply (d_sd_typing_general_subsumption_spine Hty (denv_binds_le_refl Γ)
            (n := 0) (B' := ptyp_to_btyp_syn A) (M := m) (B := B) (Bres := B)).
  - apply is_fn_n__ti.
  - apply btyp_spine__tail. exact Hst.
  - rewrite btyp_to_utyp_syn_ptyp_to_btyp_syn. exact Hsub.
Qed.
