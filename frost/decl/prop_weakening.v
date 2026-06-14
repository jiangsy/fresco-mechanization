(** Frost declarative typing weakening, native split-syntax form. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.predicates.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

(** ** Context weakening for consistency and subtyping (formerly
    [subtyping/prop_basics.v]). *)

Lemma d_consis_weakening : forall Γ1 Γ2 Γ3 Δ C B,
    Δ ⨟ (Γ1 ++ Γ3) ⊨ C ≈ B ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊨ C ≈ B.
Proof.
  intros Γ1 Γ2 Γ3 Δ C B H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst.
  - apply d_consis__unit. assumption.
  - apply d_consis__var; [ | assumption ].
    match goal with Hb : binds _ _ _ |- _ => analyze_binds Hb end.
  - eapply d_consis__arrow.
    + eapply IHd_consis1; reflexivity.
    + eapply IHd_consis2; reflexivity.
    + assumption.
  - eapply d_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ3)); [ | eassumption ].
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_consis__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_consis__forall_syn with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
Qed.

Lemma d_consis_weakening_head : forall Γ Γ' Δ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    Δ ⨟ (Γ' ++ Γ) ⊨ C ≈ B.
Proof.
  intros Γ Γ' Δ C B H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_consis_weakening. simpl. exact H.
Qed.

Lemma d_sub_weakening : forall Γ1 Γ2 Γ3 m Δ C B,
    Δ ⨟ (Γ1 ++ Γ3) ⊢[ m ] C ⊑ B ->
    Δ ⨟ (Γ1 ++ Γ2 ++ Γ3) ⊢[ m ] C ⊑ B.
Proof.
  intros Γ1 Γ2 Γ3 m Δ C B H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst.
  - apply d_sub__infer; [ apply d_consis_weakening; assumption | assumption | assumption ].
  - apply d_sub__check;
      [ assumption | assumption | apply d_consis_weakening; assumption | assumption ].
  - apply d_sub__forall_r with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ.
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - eapply d_sub__arg.
    + apply d_consis_weakening; eassumption.
    + match goal with IH : forall _ _, _ -> d_sub _ _ _ _ _ |- _ => apply (IH Γ1 Γ3 eq_refl) end.
    + eassumption.
  - eapply d_sub__forall_l_tagged.
    + assumption.
    + eassumption.
    + eassumption.
    + apply d_wf_utyp_weakening; eassumption.
    + assumption.
    + match goal with IH : forall _ _, _ -> d_sub _ _ _ _ _ |- _ => apply (IH Γ1 Γ3 eq_refl) end.
  - eapply d_sub__forall_l_untagged.
    + assumption.
    + eassumption.
    + eassumption.
    + apply d_wf_utyp_weakening; eassumption.
    + assumption.
    + match goal with IH : forall _ _, _ -> d_sub _ _ _ _ _ |- _ => apply (IH Γ1 Γ3 eq_refl) end.
Qed.

Lemma d_sub_weakening_head : forall Γ Γ' m Δ C B,
    Δ ⨟ Γ ⊢[ m ] C ⊑ B ->
    Δ ⨟ (Γ' ++ Γ) ⊢[ m ] C ⊑ B.
Proof.
  intros Γ Γ' m Δ C B H.
  rewrite_env (nil ++ Γ' ++ Γ).
  apply d_sub_weakening. simpl. exact H.
Qed.

Lemma d_refine_syn_weakening : forall Γ1 Γ2 Γ3 Ψ Q P,
    d_refine_syn Ψ (Γ1 ++ Γ3) Q P ->
    d_refine_syn Ψ (Γ1 ++ Γ2 ++ Γ3) Q P.
Proof.
  intros Γ1 Γ2 Γ3 Ψ Q P H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var.
    match goal with H : _ \/ _ |- _ => destruct H as [HΨ | Hb] end;
      [ left; assumption | right; analyze_binds Hb ].
  - apply d_refine_syn__arrow; auto.
  - apply d_refine_syn__all with (L := L `union` dom (Γ1 ++ Γ3)). intros X HX.
    eapply (H0 X ltac:(fsetdec) Γ1 Γ3). reflexivity.
  - apply d_refine_syn__hole. apply d_wf_pskl_weakening. assumption.
  - apply d_refine_syn__tophole_remove; auto.
  - apply d_refine_syn__tophole_fill with (L := L `union` dom (Γ1 ++ Γ3)). intros X HX.
    rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 X ltac:(fsetdec) ((X ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_refine_syn__tophole_keep; [ assumption | auto ].
Qed.


Lemma d_pat_consis_weakening : forall Γ1 Γ2 Γ3 Δ R Q,
    d_pat_consis Δ (Γ1 ++ Γ3) R Q ->
    d_pat_consis Δ (Γ1 ++ Γ2 ++ Γ3) R Q.
Proof.
  intros Γ1 Γ2 Γ3 Δ R Q H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_pat_consis__unit.
  - apply d_pat_consis__var. analyze_binds H.
  - eapply d_pat_consis__arrow;
      [ eapply IHd_pat_consis1 | eapply IHd_pat_consis2 ]; reflexivity.
  - apply d_pat_consis__forall_inh_tagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__forall_inh_untagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__forall_syn_tagged with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__forall_syn with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__ghostg.
  - apply d_pat_consis__topholeg. eapply IHd_pat_consis; reflexivity.
  - apply d_pat_consis__hole. apply d_wf_pskl_weakening. assumption.
  - apply d_pat_consis__tophole. eapply IHd_pat_consis; reflexivity.
  - apply d_pat_consis__tophole_inh with (L := L `union` dom (Γ1 ++ Γ3)).
    intros Z HZ. rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    eapply (H0 Z ltac:(fsetdec) ((Z ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  - apply d_pat_consis__tophole_drop. eapply IHd_pat_consis; reflexivity.
Qed.

Lemma d_pat_sub_weakening : forall Γ1 Γ2 Γ3 m Δ R Q,
    d_pat_sub m Δ (Γ1 ++ Γ3) R Q ->
    d_pat_sub m Δ (Γ1 ++ Γ2 ++ Γ3) R Q.
Proof.
  intros Γ1 Γ2 Γ3 m Δ R Q H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_pat_sub__infer; [ apply d_pat_consis_weakening; assumption | assumption ].
  - apply d_pat_sub__univ_ghost_r; try assumption.
    apply d_pat_consis_weakening; assumption.
  - eapply d_pat_sub__arg;
      [ apply d_pat_consis_weakening; eassumption | eapply IHd_pat_sub; reflexivity ].
  - eapply d_pat_sub__forall_l_tagged.
    + assumption.
    + eassumption.
    + eassumption.
    + apply d_wf_uskl_weakening; eassumption.
    + assumption.
    + eapply IHd_pat_sub; reflexivity.
  - eapply d_pat_sub__forall_l_untagged.
    + assumption.
    + eassumption.
    + eassumption.
    + apply d_wf_uskl_weakening; eassumption.
    + assumption.
    + eapply IHd_pat_sub; reflexivity.
  - apply d_pat_sub__ghost. apply d_wf_pskl_weakening. assumption.
  - apply d_pat_sub__univ_ghost_l; [ assumption | eapply IHd_pat_sub; reflexivity ].
  - apply d_pat_sub__ghostg.
  - apply d_pat_sub__univ_ghost_lg; [ assumption | eapply IHd_pat_sub; reflexivity ].
Qed.

Combined Scheme d_typing_pat_mutind from d_typing_mut, d_pat_mut.

Lemma d_typing_pat_weakening : forall Γ2,
  (forall m Γ e B, d_typing m Γ e B ->
     forall Γ1 Γ3, Γ = Γ1 ++ Γ3 -> d_typing m (Γ1 ++ Γ2 ++ Γ3) e B) /\
  (forall m Γ e Q, d_pat m Γ e Q ->
     forall Γ1 Γ3, Γ = Γ1 ++ Γ3 -> d_pat m (Γ1 ++ Γ2 ++ Γ3) e Q).
Proof.
  intros Γ2. apply d_typing_pat_mutind.
  (* d_typing__unit *)
  - intros Γ Γ1 Γ3 Heq; subst Γ. apply d_typing__unit.
  (* d_typing__var *)
  - intros Γ x A Hb Γ1 Γ3 Heq; subst Γ. apply d_typing__var. analyze_binds Hb.
  (* d_typing__anno *)
  - intros Γ e A Hty IHty Γ1 Γ3 Heq; subst Γ.
    apply d_typing__anno. apply IHty; reflexivity.
  (* d_typing__sub *)
  - intros Γ m e B1 B2 Hbase Hty IHty Hsub Γ1 Γ3 Heq; subst Γ.
    apply d_typing__sub with (B1 := B1);
      [ exact Hbase | apply IHty; reflexivity | apply d_sub_weakening; exact Hsub ].
  (* d_typing__freeze *)
  - intros Γ e B Hty IHty Γ1 Γ3 Heq; subst Γ.
    apply d_typing__freeze. apply IHty; reflexivity.
  (* d_typing__forall *)
  - intros L Γ e B Hval Hbody IHbody Γ1 Γ3 Heq; subst Γ.
    apply d_typing__forall with (L := L `union` dom (Γ1 ++ Γ3)); [ exact Hval | ].
    intros X HX. rewrite_env (((X ~ dbind_tvar) ++ Γ1) ++ Γ2 ++ Γ3).
    apply (IHbody X ltac:(fsetdec) ((X ~ dbind_tvar) ++ Γ1) Γ3). simpl. reflexivity.
  (* d_typing__abs *)
  - intros L Γ m e A B Hwf Hbody IHbody Γ1 Γ3 Heq; subst Γ.
    apply d_typing__abs with (L := L `union` dom (Γ1 ++ Γ3)) (A := A);
      [ apply d_wf_ptyp_weakening; assumption | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
    apply (IHbody x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ1) Γ3). simpl. reflexivity.
  (* d_typing__abs_anno *)
  - intros L Γ m e A Barg B Hwf Hbarg Hbody IHbody Γ1 Γ3 Heq; subst Γ.
    apply d_typing__abs_anno with (L := L `union` dom (Γ1 ++ Γ3)) (A := A) (Barg := Barg);
      [ apply d_wf_ptyp_weakening; assumption | exact Hbarg | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
    apply (IHbody x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ1) Γ3). simpl. reflexivity.
  (* d_typing__app *)
  - intros Γ m e1 e2 P A Barg B Hbarg Hpat IHpat Href Hty1 IHty1 Hty2 IHty2 Γ1 Γ3 Heq; subst Γ.
    eapply d_typing__app;
      [ exact Hbarg | apply IHpat; reflexivity | apply d_refine_syn_weakening; eassumption
      | apply IHty1; reflexivity | apply IHty2; reflexivity ].
  (* d_pat__unit *)
  - intros Γ Γ1 Γ3 Heq; subst Γ. apply d_pat__unit.
  (* d_pat__var *)
  - intros Γ x P Hb Γ1 Γ3 Heq; subst Γ. apply d_pat__var. analyze_binds Hb.
  (* d_pat__anno *)
  - intros Γ e A Hwf Γ1 Γ3 Heq; subst Γ.
    apply d_pat__anno. apply d_wf_ptyp_weakening; assumption.
  (* d_pat__sub *)
  - intros Γ m e Q1 Q2 Hbase Hpat IHpat Hsub Γ1 Γ3 Heq; subst Γ.
    apply d_pat__sub with (Q1 := Q1);
      [ exact Hbase | apply IHpat; reflexivity | apply d_pat_sub_weakening; exact Hsub ].
  (* d_pat__freeze *)
  - intros Γ e Q Hpat IHpat Γ1 Γ3 Heq; subst Γ.
    apply d_pat__freeze. apply IHpat; reflexivity.
  (* d_pat__abs *)
  - intros L Γ m e P Q Hm Hwf Hbody IHbody Γ1 Γ3 Heq; subst Γ.
    apply d_pat__abs with (L := L `union` dom (Γ1 ++ Γ3)) (P := P);
      [ exact Hm | apply d_wf_pskl_weakening; assumption | ].
    intros x Hx. rewrite_env (((x ~ dbind_skl P) ++ Γ1) ++ Γ2 ++ Γ3).
    apply (IHbody x ltac:(fsetdec) ((x ~ dbind_skl P) ++ Γ1) Γ3). simpl. reflexivity.
  (* d_pat__abs_check *)
  - intros L Γ e Q Hbody IHbody Γ1 Γ3 Heq; subst Γ.
    apply d_pat__abs_check with (L := L `union` dom (Γ1 ++ Γ3)).
    intros x Hx. rewrite_env (((x ~ dbind_skl pskl_hole) ++ Γ1) ++ Γ2 ++ Γ3).
    apply (IHbody x ltac:(fsetdec) ((x ~ dbind_skl pskl_hole) ++ Γ1) Γ3). simpl. reflexivity.
  (* d_pat__abs_anno *)
  - intros L Γ m e A Sarg Q Hm Hwf Hsarg Hbody IHbody Γ1 Γ3 Heq; subst Γ.
    apply d_pat__abs_anno with (L := L `union` dom (Γ1 ++ Γ3)) (A := A) (Sarg := Sarg);
      [ exact Hm | apply d_wf_ptyp_weakening; assumption | exact Hsarg | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
    apply (IHbody x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ1) Γ3). simpl. reflexivity.
  (* d_pat__abs_anno_check *)
  - intros L Γ e A Sarg Q Hwf Hsarg Hbody IHbody Γ1 Γ3 Heq; subst Γ.
    apply d_pat__abs_anno_check with (L := L `union` dom (Γ1 ++ Γ3)) (A := A) (Sarg := Sarg);
      [ apply d_wf_ptyp_weakening; assumption | exact Hsarg | ].
    intros x Hx. rewrite_env (((x ~ dbind_typ A) ++ Γ1) ++ Γ2 ++ Γ3).
    apply (IHbody x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ1) Γ3). simpl. reflexivity.
  (* d_pat__app *)
  - intros Γ m e1 e2 P A1 A2 Barg1 Sres Hbarg Hsres Hpat IHpat Href Hty IHty Γ1 Γ3 Heq; subst Γ.
    eapply d_pat__app;
      [ exact Hbarg | exact Hsres | apply IHpat; reflexivity
      | apply d_refine_syn_weakening; eassumption | apply IHty; reflexivity ].
Qed.

Lemma d_typing_weakening : forall Γ1 Γ2 Γ3 m e B,
    d_typing m (Γ1 ++ Γ3) e B ->
    d_typing m (Γ1 ++ Γ2 ++ Γ3) e B.
Proof.
  intros Γ1 Γ2 Γ3 m e B H.
  eapply (proj1 (d_typing_pat_weakening Γ2)); [ exact H | reflexivity ].
Qed.

Lemma d_pat_weakening : forall Γ1 Γ2 Γ3 m e Q,
    d_pat m (Γ1 ++ Γ3) e Q ->
    d_pat m (Γ1 ++ Γ2 ++ Γ3) e Q.
Proof.
  intros Γ1 Γ2 Γ3 m e Q H.
  eapply (proj2 (d_typing_pat_weakening Γ2)); [ exact H | reflexivity ].
Qed.


(** General (order-preserving) context weakening: [Γ'] is [Γ] with extra
    bindings inserted at arbitrary positions.  Encoded as a chain of the
    middle-insertions that [d_typing_weakening] already supports, so the
    judgement closures below are one-liners. *)
Inductive ctx_weaken : list (atom * dbind) -> list (atom * dbind) -> Prop :=
| ctx_weaken_refl : forall Γ, ctx_weaken Γ Γ
| ctx_weaken_insert : forall Γ1 Γ2 Γ3 Γ',
    ctx_weaken (Γ1 ++ Γ2 ++ Γ3) Γ' ->
    ctx_weaken (Γ1 ++ Γ3) Γ'.

Lemma d_typing_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall m e B, d_typing m Γ e B -> d_typing m Γ' e B.
Proof.
  induction 1; intros m e B Hty; [ assumption | ].
  apply IHctx_weaken. apply d_typing_weakening. exact Hty.
Qed.

Lemma d_pat_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall m e Q, d_pat m Γ e Q -> d_pat m Γ' e Q.
Proof.
  induction 1; intros m e Q Hp; [ assumption | ].
  apply IHctx_weaken. apply d_pat_weakening. exact Hp.
Qed.

Lemma d_refine_syn_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall Ψ Q P, d_refine_syn Ψ Γ Q P -> d_refine_syn Ψ Γ' Q P.
Proof.
  induction 1; intros Ψ Q P Hr; [ assumption | ].
  apply IHctx_weaken. apply d_refine_syn_weakening. exact Hr.
Qed.

Lemma binds_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall x b, binds x b Γ -> binds x b Γ'.
Proof.
  induction 1; intros x b Hb; [ assumption | ].
  apply IHctx_weaken. analyze_binds Hb.
Qed.

Lemma ctx_weaken_cons : forall Γ Γ' a,
    ctx_weaken Γ Γ' -> ctx_weaken (a ++ Γ) (a ++ Γ').
Proof.
  intros Γ Γ' a H. revert a. induction H; intros a.
  - apply ctx_weaken_refl.
  - rewrite_env ((a ++ Γ1) ++ Γ3).
    apply ctx_weaken_insert with (Γ2 := Γ2).
    rewrite_env (a ++ (Γ1 ++ Γ2 ++ Γ3)). apply IHctx_weaken.
Qed.

Lemma ctx_weaken_trans : forall Γ1 Γ2 Γ3,
    ctx_weaken Γ1 Γ2 -> ctx_weaken Γ2 Γ3 -> ctx_weaken Γ1 Γ3.
Proof.
  (* [induction H] reintroduces [ctx_weaken_insert]'s own [Γ1 Γ2 Γ3], so the
     reverted target is named [Γ0] to avoid colliding with the constructor's
     [Γ3] (the statement's [Γ1]/[Γ2] are fine — they are consumed by the
     induction). *)
  intros Γ1 Γ2 Γ3 H. revert Γ3. induction H; intros Γ0 Hbc; [ assumption | ].
  apply ctx_weaken_insert with (Γ2 := Γ2). apply IHctx_weaken. exact Hbc.
Qed.

(** Inserting a single block at the front. *)
Lemma ctx_weaken_app_front : forall Γ2 Γ,
    ctx_weaken Γ (Γ2 ++ Γ).
Proof.
  intros Γ2 Γ. rewrite_env (nil ++ Γ).
  apply ctx_weaken_insert with (Γ2 := Γ2). simpl. apply ctx_weaken_refl.
Qed.

Lemma d_wf_ptyp_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall A, d_wf_ptyp Γ A -> d_wf_ptyp Γ' A.
Proof.
  induction 1; intros A Hwf; [ assumption | ].
  apply IHctx_weaken. apply d_wf_ptyp_weakening. exact Hwf.
Qed.

Lemma d_sub_ctx_weaken : forall Γ Γ',
    ctx_weaken Γ Γ' -> forall m Δ C B, d_sub m Δ Γ C B -> d_sub m Δ Γ' C B.
Proof.
  induction 1; intros m Δ C B Hs; [ assumption | ].
  apply IHctx_weaken. apply d_sub_weakening. exact Hs.
Qed.
