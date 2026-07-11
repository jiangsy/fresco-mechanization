(** Information-increase (metasubstitution) algebra.

    Basic properties of [a_inc] / [⊴] (paper fig:information-increase) that
    every appendix-B/C soundness case threads: identity metasubstitutions
    are reflexive, and the target may grow by a fresh flexible suffix.
    Both come out of one generalized induction ([a_inc_refl_gen]). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Identity substitutions are identities                                 *)
(* ===================================================================== *)

Lemma subst_ptyp_in_ptyp_self : forall α A,
  subst_ptyp_in_ptyp (ptyp_var_f α) α A = A.
Proof.
  induction A; simpl; f_equal; auto.
  destruct (eq_var Xpt α); subst; auto.
Qed.

Lemma subst_pskl_in_pskl_self : forall α P,
  subst_pskl_in_pskl (ptyp_to_pskl (ptyp_var_f α)) α P = P.
Proof.
  induction P; simpl; f_equal; auto.
  destruct (eq_var Xps α); subst; auto.
Qed.

Lemma msubst_ptyp_id : forall θ A,
  is_id_msubst θ ->
  msubst_ptyp θ A = A.
Proof.
  induction θ as [ | [α τ] θ' IH ]; intros A Hid; simpl; auto.
  inversion Hid as [ | ? ? He Hid' ]; subst.
  unfold is_id_entry in He; simpl in He; subst.
  rewrite subst_ptyp_in_ptyp_self. auto.
Qed.

Lemma msubst_pskl_id : forall θ P,
  is_id_msubst θ ->
  msubst_pskl θ P = P.
Proof.
  induction θ as [ | [α τ] θ' IH ]; intros P Hid; simpl; auto.
  inversion Hid as [ | ? ? He Hid' ]; subst.
  unfold is_id_entry in He; simpl in He; subst.
  rewrite subst_pskl_in_pskl_self. auto.
Qed.

(* ===================================================================== *)
(*  Suffix bookkeeping                                                    *)
(* ===================================================================== *)

Lemma a_suffix_app : forall Ξ1 Ξ2,
  a_suffix Ξ1 -> a_suffix Ξ2 -> a_suffix (Ξ1 ++ Ξ2).
Proof.
  intros Ξ1 Ξ2 H1 H2; induction H1; simpl; auto.
  apply (a_suffix__cons a (b := b)); auto.
Qed.

(* ===================================================================== *)
(*  Reflexivity, generalized with a fresh-suffix target extension:        *)
(*  Θ ⊑[ι] Ξ0 ++ Θ  for any flexible suffix Ξ0.                           *)
(* ===================================================================== *)

Lemma a_inc_refl_gen : forall Θ Ξ0,
  a_suffix Ξ0 ->
  exists θ, is_id_msubst θ /\ Θ ≤[ θ ] (Ξ0 ++ Θ).
Proof.
  induction Θ as [ | [a b] Θ0 IH ]; intros Ξ0 HΞ.
  - exists nil. split; [ constructor | ].
    rewrite app_nil_r. apply a_inc__empty; auto.
  - destruct b.
    + (* abind_tvar : Θ,α ⊑ Ξ0,α,Θ — a_inc__tvar with Ξ := Ξ0 *)
      destruct (IH nil) as [θ0 [Hid Hinc]]; [ constructor | ].
      simpl in Hinc.
      exists θ0. split; auto.
      apply (a_inc__tvar (Ξ := Ξ0)); auto.
    + (* abind_var_typ A : entry carried over, type metasubstituted *)
      destruct (IH nil) as [θ0 [Hid Hinc]]; [ constructor | ].
      simpl in Hinc.
      exists θ0. split; auto.
      replace ((a, abind_var_typ p) :: Θ0)
        with ((a ~ abind_var_typ p) ++ Θ0) by reflexivity.
      replace (Ξ0 ++ (a ~ abind_var_typ p) ++ Θ0)
        with (Ξ0 ++ (a ~ abind_var_typ (msubst_ptyp θ0 p)) ++ Θ0)
        by (rewrite msubst_ptyp_id; auto).
      apply a_inc__var; auto.
    + (* abind_var_skl P *)
      destruct (IH nil) as [θ0 [Hid Hinc]]; [ constructor | ].
      simpl in Hinc.
      exists θ0. split; auto.
      replace ((a, abind_var_skl p) :: Θ0)
        with ((a ~ abind_var_skl p) ++ Θ0) by reflexivity.
      replace (Ξ0 ++ (a ~ abind_var_skl p) ++ Θ0)
        with (Ξ0 ++ (a ~ abind_var_skl (msubst_pskl θ0 p)) ++ Θ0)
        by (rewrite msubst_pskl_id; auto).
      apply a_inc__var_skl; auto.
    + (* abind_flex_mono : solve α̂ with itself; α̂ sits inside the target *)
      destruct (IH (Ξ0 ++ (a ~ abind_flex_mono)))
        as [θ0 [Hid Hinc]].
      { apply a_suffix_app; auto.
        apply (a_suffix__cons a (b := abind_flex_mono)); constructor. }
      first [ rewrite <- app_assoc in Hinc | rewrite app_assoc in Hinc ]; simpl in Hinc.
      exists ((a, ptyp_var_f a) :: θ0). split.
      { constructor; auto. unfold is_id_entry; reflexivity. }
      replace ((a, abind_flex_mono) :: Θ0)
        with ((a ~ abind_flex_mono) ++ Θ0) by reflexivity.
      apply a_inc__flex; auto.
      * apply a_wf_ptyp__var. right; left.
        unfold binds; apply in_or_app; right; left; reflexivity.
      * constructor.
    + (* abind_flex_mono_def τ : α̂:=τ, entry looked up in the target *)
      destruct (IH (Ξ0 ++ (a ~ abind_flex_mono_def p)))
        as [θ0 [Hid Hinc]].
      { apply a_suffix_app; auto.
        apply (a_suffix__cons a (b := abind_flex_mono_def p)); constructor. }
      first [ rewrite <- app_assoc in Hinc | rewrite app_assoc in Hinc ]; simpl in Hinc.
      exists ((a, ptyp_var_f a) :: θ0). split.
      { constructor; auto. unfold is_id_entry; reflexivity. }
      replace ((a, abind_flex_mono_def p) :: Θ0)
        with ((a ~ abind_flex_mono_def p) ++ Θ0) by reflexivity.
      apply a_inc__flex_def; auto.
      * apply a_wf_ptyp__var. right; right. exists p.
        unfold binds; apply in_or_app; right; left; reflexivity.
      * constructor.
      * rewrite msubst_ptyp_id; auto.
        apply a_tyequiv__flex_def.
        unfold binds; apply in_or_app; right; left; reflexivity.
Qed.

(** [Θ ⊴ Θ] — reflexivity of information increase. *)
Lemma a_isub_refl : forall Θ, Θ ⊴ Θ.
Proof.
  intros Θ. destruct (a_inc_refl_gen Θ (Ξ0 := nil)) as [θ [Hid Hinc]];
    [ constructor | ].
  exists θ. simpl in Hinc. auto.
Qed.

(** [Θ ⊴ Ξ ++ Θ] — the target may grow by a fresh flexible suffix. *)
Lemma a_isub_weaken_suffix : forall Θ Ξ,
  a_suffix Ξ ->
  Θ ⊴ (Ξ ++ Θ).
Proof.
  intros Θ Ξ HΞ. destruct (a_inc_refl_gen Θ (Ξ0 := Ξ)) as [θ [Hid Hinc]]; auto.
  exists θ. auto.
Qed.

(* ===================================================================== *)
(*  Transport of context lookups along an (identity) information increase *)
(*  — the mechanized content of the paper's "stability" remark            *)
(*  (proofs.tex:19-26)                                                    *)
(* ===================================================================== *)

Lemma is_id_msubst_inv : forall α τ θ,
  is_id_msubst ((α, τ) :: θ) ->
  τ = ptyp_var_f α /\ is_id_msubst θ.
Proof.
  intros * H; inversion H as [ | ? ? He Hθ ]; subst.
  unfold is_id_entry in He; simpl in He; subst; auto.
Qed.

(** The target of an increase from an all-flexible source is all-flexible. *)
Lemma a_inc_suffix_target : forall Θ θ Θ',
  Θ ≤[ θ ] Θ' ->
  a_suffix Θ ->
  a_suffix Θ'.
Proof.
  intros * Hinc; induction Hinc; intros Hsuf; auto;
    inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst; auto;
    inversion Hb.
Qed.

(** Peeling an all-flexible prefix of the source keeps the target. *)
Lemma a_inc_strengthen_suffix_src : forall Ξ Θ θ Θ',
  a_suffix Ξ ->
  (Ξ ++ Θ) ≤[ θ ] Θ' ->
  exists θ', (is_id_msubst θ -> is_id_msubst θ') /\ Θ ≤[ θ' ] Θ'.
Proof.
  intros Ξ; induction Ξ as [ | [a b] Ξ' IH ]; intros Θ θ Θ' Hsuf Hinc.
  - exists θ. auto.
  - inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst.
    inversion Hb; subst; simpl in Hinc;
      inversion Hinc; subst;
      match goal with
      | H : (Ξ' ++ Θ) ≤[ _ ] Θ' |- _ =>
          destruct (IH _ _ _ Hsuf' H) as [θ' [Hid' Hinc']]
      end;
      exists θ'; split; auto;
      intros Hid; apply Hid'; eapply proj2, is_id_msubst_inv; eauto.
Qed.

(** Head inversions: rigid and term-variable entries are carried over. *)
Lemma a_inc_tvar_inv : forall α Θ θ Θ',
  ((α ~ abind_tvar) ++ Θ) ≤[ θ ] Θ' ->
  exists Ξ Θ2, Θ' = Ξ ++ (α ~ abind_tvar) ++ Θ2 /\ a_suffix Ξ /\ Θ ≤[ θ ] Θ2.
Proof. intros * H; inversion H; subst; eauto 6. Qed.

Lemma a_inc_var_inv : forall x A Θ θ Θ',
  ((x ~ abind_var_typ A) ++ Θ) ≤[ θ ] Θ' ->
  exists Ξ Θ2,
    Θ' = Ξ ++ (x ~ abind_var_typ (msubst_ptyp θ A)) ++ Θ2 /\
    a_suffix Ξ /\ Θ ≤[ θ ] Θ2.
Proof. intros * H; inversion H; subst; eauto 6. Qed.

Lemma a_inc_var_skl_inv : forall x P Θ θ Θ',
  ((x ~ abind_var_skl P) ++ Θ) ≤[ θ ] Θ' ->
  exists Ξ Θ2,
    Θ' = Ξ ++ (x ~ abind_var_skl (msubst_pskl θ P)) ++ Θ2 /\
    a_suffix Ξ /\ Θ ≤[ θ ] Θ2.
Proof. intros * H; inversion H; subst; eauto 6. Qed.

Lemma binds_weaken_mid : forall (b : abind) x Ξ (e : list (atom * abind)) Θ,
  binds x b Θ ->
  binds x b (Ξ ++ e ++ Θ).
Proof.
  intros; unfold binds in *.
  apply in_or_app; right; apply in_or_app; right; auto.
Qed.

Lemma a_binds_tvar_weaken_mid : forall α Ξ (e : list (atom * abind)) Θ,
  a_binds_tvar α Θ ->
  a_binds_tvar α (Ξ ++ e ++ Θ).
Proof.
  intros * [Hb | [Hb | [τ Hb]]];
    [ left | right; left | right; right; exists τ ];
    auto using binds_weaken_mid.
Qed.

(** [a_tyequiv] uses its context only through positive [binds] lookups, so it
    is monotone in the context. *)
Lemma a_tyequiv_weaken : forall Θ Θ' A B,
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Θ ⊢ A ≡ᵗ B ->
  Θ' ⊢ A ≡ᵗ B.
Proof.
  intros * Hmon Heq; induction Heq; eauto using a_tyequiv.
Qed.

(** Rigid variables survive any increase. *)
Lemma a_inc_binds_tvar : forall Θ θ Θ' α,
  Θ ≤[ θ ] Θ' ->
  binds α abind_tvar Θ ->
  binds α abind_tvar Θ'.
Proof.
  intros * Hinc; induction Hinc; intros Hb.
  - inversion Hb.
  - (* flex head: lookup is in the tail *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | auto ].
  - (* flex_def head: tail *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | auto ].
  - (* var head: tail, then weaken into Ξ ++ e ++ Θ' *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | apply binds_weaken_mid; auto ].
  - (* var_skl head *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | apply binds_weaken_mid; auto ].
  - (* tvar head: either THE entry (kept in the middle) or the tail *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqa Heq] | Hb'].
    + subst. unfold binds; apply in_or_app; right; left; reflexivity.
    + apply binds_weaken_mid; auto.
Qed.

(** Declared flexible variables survive an identity increase (as SOME
    tvar-ish entry): the flex rule's well-formedness premise applied to the
    identity image [α̂]. *)
Lemma a_inc_binds_flex : forall Θ θ Θ' α,
  Θ ≤[ θ ] Θ' ->
  is_id_msubst θ ->
  binds α abind_flex_mono Θ ->
  a_binds_tvar α Θ'.
Proof.
  intros * Hinc; induction Hinc; intros Hid Hb.
  - inversion Hb.
  - (* flex head *)
    apply is_id_msubst_inv in Hid as [Heqτ Hid]; subst.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqa _] | Hb'].
    + subst. inversion H; subst; auto.
    + auto.
  - (* flex_def head: tail *)
    apply is_id_msubst_inv in Hid as [? Hid].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | auto ].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | apply a_binds_tvar_weaken_mid; auto ].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | apply a_binds_tvar_weaken_mid; auto ].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | apply a_binds_tvar_weaken_mid; auto ].
Qed.

(** Defined flexible variables survive an identity increase, and the target
    still equates them with their old definition. *)
Lemma a_inc_binds_flex_def : forall Θ θ Θ' α τ0,
  Θ ≤[ θ ] Θ' ->
  is_id_msubst θ ->
  binds α (abind_flex_mono_def τ0) Θ ->
  a_binds_tvar α Θ' /\ Θ' ⊢ (ptyp_var_f α) ≡ᵗ τ0.
Proof.
  intros * Hinc; induction Hinc; intros Hid Hb.
  - inversion Hb.
  - (* flex head: tail *)
    apply is_id_msubst_inv in Hid as [? Hid].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | auto ].
  - (* flex_def head *)
    apply is_id_msubst_inv in Hid as [Heqτ Hid]; subst.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqa Heq] | Hb'].
    + inversion Heq; subst. split.
      * inversion H; subst; auto.
      * rewrite msubst_ptyp_id in H1; auto.
    + auto.
  - (* var head: tail + weaken both conclusions *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    destruct (IHHinc Hid Hb') as [Htv Heqv].
    split; [ apply a_binds_tvar_weaken_mid; auto | ].
    eapply a_tyequiv_weaken; [ | eauto ].
    intros; apply binds_weaken_mid; auto.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    destruct (IHHinc Hid Hb') as [Htv Heqv].
    split; [ apply a_binds_tvar_weaken_mid; auto | ].
    eapply a_tyequiv_weaken; [ | eauto ].
    intros; apply binds_weaken_mid; auto.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    destruct (IHHinc Hid Hb') as [Htv Heqv].
    split; [ apply a_binds_tvar_weaken_mid; auto | ].
    eapply a_tyequiv_weaken; [ | eauto ].
    intros; apply binds_weaken_mid; auto.
Qed.

(** A tvar-ish occurrence survives an identity increase. *)
Lemma a_inc_binds_tvarish : forall Θ θ Θ' α,
  Θ ≤[ θ ] Θ' ->
  is_id_msubst θ ->
  a_binds_tvar α Θ ->
  a_binds_tvar α Θ'.
Proof.
  intros * Hinc Hid [Hb | [Hb | [τ0 Hb]]].
  - left; eauto using a_inc_binds_tvar.
  - eauto using a_inc_binds_flex.
  - eapply a_inc_binds_flex_def in Hb as [? ?]; eauto.
Qed.

(** Stability of type equivalence under identity increases. *)
Lemma a_tyequiv_isub : forall Θ θ Θ' A B,
  Θ ≤[ θ ] Θ' ->
  is_id_msubst θ ->
  Θ ⊢ A ≡ᵗ B ->
  Θ' ⊢ A ≡ᵗ B.
Proof.
  intros * Hinc Hid Heq; induction Heq.
  - apply a_tyequiv__refl; auto.
  - apply a_tyequiv__sym; auto.
  - eapply a_tyequiv__trans; eauto.
  - eapply a_inc_binds_flex_def in H as [_ ?]; eauto.
  - apply a_tyequiv__arrow; auto.
  - eapply a_tyequiv__all; eauto.
Qed.

(* ===================================================================== *)
(*  Transitivity of (identity) information increase                        *)
(* ===================================================================== *)

Lemma a_inc_trans : forall Θ0 θ1 Θ1,
  Θ0 ≤[ θ1 ] Θ1 ->
  is_id_msubst θ1 ->
  forall θ2 Θ2,
  Θ1 ≤[ θ2 ] Θ2 ->
  is_id_msubst θ2 ->
  exists θ, is_id_msubst θ /\ Θ0 ≤[ θ ] Θ2.
Proof.
  intros Θ0 θ1 Θ1 Hinc1;
    induction Hinc1 as
      [ Ξ HΞ
      | Θ θ Θ' α τ Hinc IH Hwf Hmono
      | Θ θ Θ' α τ τ' Hinc IH Hwf Hmono Hteq
      | Θ θ Θ' Ξ x A Hinc IH HΞ
      | Θ θ Θ' Ξ x P Hinc IH HΞ
      | Θ θ Θ' Ξ α Hinc IH HΞ ];
    intros Hid1 θ2 Θ2 Hinc2 Hid2.
  - (* empty: Θ0 = nil, Θ1 = Ξ all-flexible ⇒ Θ2 all-flexible *)
    exists nil. split; [ constructor | ].
    apply a_inc__empty. eauto using a_inc_suffix_target.
  - (* flex head *)
    apply is_id_msubst_inv in Hid1 as [Heqτ Hid1]; subst.
    destruct (IH Hid1 _ _ Hinc2 Hid2) as [θ' [Hid' Hinc']].
    assert (Htv2 : a_binds_tvar α Θ2).
    { inversion Hwf; subst. eauto using a_inc_binds_tvarish. }
    exists ((α, ptyp_var_f α) :: θ'). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex;
      [ exact Hinc' | apply a_wf_ptyp__var; exact Htv2 | constructor ].
  - (* flex_def head *)
    apply is_id_msubst_inv in Hid1 as [Heqτ Hid1]; subst.
    destruct (IH Hid1 _ _ Hinc2 Hid2) as [θ' [Hid' Hinc']].
    assert (Htv2 : a_binds_tvar α Θ2).
    { inversion Hwf; subst. eauto using a_inc_binds_tvarish. }
    assert (Heqv : Θ2 ⊢ (ptyp_var_f α) ≡ᵗ (msubst_ptyp θ' τ)).
    { rewrite msubst_ptyp_id; [ | exact Hid' ].
      rewrite msubst_ptyp_id in Hteq; [ | exact Hid1 ].
      exact (a_tyequiv_isub Hinc2 Hid2 Hteq). }
    exists ((α, ptyp_var_f α) :: θ'). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex_def;
      [ exact Hinc' | apply a_wf_ptyp__var; exact Htv2 | constructor
      | exact Heqv ].
  - (* var head: peel the suffix, invert the carried entry *)
    edestruct a_inc_strengthen_suffix_src as [θ2' [Hid2' Hinc2']];
      [ exact HΞ | exact Hinc2 | ].
    apply a_inc_var_inv in Hinc2' as [Ξ2 [Θ2' [Heq [HΞ2 Hinc2'']]]]; subst.
    destruct (IH Hid1 _ _ Hinc2'' (Hid2' Hid2)) as [θ' [Hid' Hinc']].
    exists θ'. split; auto.
    replace (msubst_ptyp θ2' (msubst_ptyp θ A))
      with (msubst_ptyp θ' A)
      by (repeat rewrite msubst_ptyp_id; auto).
    apply a_inc__var; auto.
  - (* var_skl head *)
    edestruct a_inc_strengthen_suffix_src as [θ2' [Hid2' Hinc2']];
      [ exact HΞ | exact Hinc2 | ].
    apply a_inc_var_skl_inv in Hinc2' as [Ξ2 [Θ2' [Heq [HΞ2 Hinc2'']]]]; subst.
    destruct (IH Hid1 _ _ Hinc2'' (Hid2' Hid2)) as [θ' [Hid' Hinc']].
    exists θ'. split; auto.
    replace (msubst_pskl θ2' (msubst_pskl θ P))
      with (msubst_pskl θ' P)
      by (repeat rewrite msubst_pskl_id; auto).
    apply a_inc__var_skl; auto.
  - (* tvar head *)
    edestruct a_inc_strengthen_suffix_src as [θ2' [Hid2' Hinc2']];
      [ exact HΞ | exact Hinc2 | ].
    apply a_inc_tvar_inv in Hinc2' as [Ξ2 [Θ2' [Heq [HΞ2 Hinc2'']]]]; subst.
    destruct (IH Hid1 _ _ Hinc2'' (Hid2' Hid2)) as [θ' [Hid' Hinc']].
    exists θ'. split; auto.
    apply a_inc__tvar; auto.
Qed.

(** [⊴] is transitive. *)
Lemma a_isub_trans : forall Θ0 Θ1 Θ2,
  Θ0 ⊴ Θ1 -> Θ1 ⊴ Θ2 -> Θ0 ⊴ Θ2.
Proof.
  intros * [θ1 [Hid1 H1]] [θ2 [Hid2 H2]].
  destruct (a_inc_trans H1 Hid1 H2 Hid2) as [θ [Hid Hinc]].
  exists θ; auto.
Qed.

