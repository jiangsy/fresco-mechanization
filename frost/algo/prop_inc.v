(** Information-increase (metasubstitution) algebra.

    Basic properties of [a_inc] / [⊴] (paper fig:information-increase) that
    every appendix-B/C soundness case threads: identity metasubstitutions
    are reflexive, and the target may grow by a fresh flexible suffix.
    Both come out of one generalized induction ([a_inc_refl_gen]). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.prop_basic.
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
  destruct (eq_var α0 α); subst; auto.
Qed.

Lemma subst_pskl_in_pskl_self : forall α P,
  subst_pskl_in_pskl (ptyp_to_pskl (ptyp_var_f α)) α P = P.
Proof.
  induction P; simpl; f_equal; auto.
  destruct (eq_var α0 α); subst; auto.
Qed.

(** The identity metasubstitution looks every variable up to itself. *)
Lemma msubst_lookup_id : forall ρ α',
  is_id_msubst ρ ->
  msubst_lookup ρ α' = ptyp_var_f α'.
Proof.
  induction ρ as [ | [α τ] ρ' IH ]; intros α' Hid; simpl; auto.
  inversion Hid as [ | ? ? He Hid' ]; subst.
  unfold is_id_entry in He; simpl in He; subst.
  destruct (α' == α) as [->|Hne]; [ reflexivity | apply IH; exact Hid' ].
Qed.

Lemma msubst_ptyp_id : forall ρ A,
  is_id_msubst ρ ->
  msubst_ptyp ρ A = A.
Proof.
  intros ρ A Hid; induction A; simpl; f_equal; auto.
  apply msubst_lookup_id; exact Hid.
Qed.

Lemma msubst_pskl_id : forall ρ P,
  is_id_msubst ρ ->
  msubst_pskl ρ P = P.
Proof.
  intros ρ P Hid; induction P; simpl; f_equal; auto.
  rewrite msubst_lookup_id by exact Hid. reflexivity.
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
(*  Local closure of a context's binding payloads.                        *)
(*                                                                        *)
(*  With the GMM-style SEMANTIC ENTRIES of [a_inc] (binder middles up to   *)
(*  ≡ᵗ/≡ˢ, def_meta.v), reflexivity of information increase needs the      *)
(*  reflexivity of the equational theory, whose only base rule demands     *)
(*  local closure.  [lc_aenv] is the minimal hypothesis; well-formed       *)
(*  contexts satisfy it ([a_wf_aenv_lc_aenv], algo/prop_flex.v).           *)
(* ===================================================================== *)

Definition lc_abind (b : abind) : Prop :=
  match b with
  | abind_var_typ A => lc_ptyp A
  | abind_var_skl P => lc_pskl P
  | _ => True
  end.

Definition lc_aenv (Θ : aenv) : Prop :=
  Forall (fun e => lc_abind (snd e)) Θ.

Lemma lc_aenv_nil : lc_aenv nil.
Proof. constructor. Qed.

Lemma lc_aenv_inv : forall (a : atom) (b : abind) Θ,
  lc_aenv ((a, b) :: Θ) -> lc_abind b /\ lc_aenv Θ.
Proof. intros * H; inversion H; subst; auto. Qed.

Lemma lc_aenv_app_inv : forall Ξ Θ,
  lc_aenv (Ξ ++ Θ) -> lc_aenv Ξ /\ lc_aenv Θ.
Proof. intros * H; apply Forall_app; auto. Qed.

Lemma lc_aenv_app : forall Ξ Θ,
  lc_aenv Ξ -> lc_aenv Θ -> lc_aenv (Ξ ++ Θ).
Proof. intros; apply Forall_app; auto. Qed.

#[export] Hint Resolve lc_aenv_nil : core.

(* ===================================================================== *)
(*  Reflexivity, generalized with a fresh-suffix target extension:        *)
(*  Θ ⊑[ι] Ξ0 ++ Θ  for any flexible suffix Ξ0.                           *)
(* ===================================================================== *)

Lemma a_inc_refl_gen : forall Θ Ξ0,
  lc_aenv Θ ->
  a_suffix Ξ0 ->
  exists ρ, is_id_msubst ρ /\ ρ ∷ Θ ⊑ (Ξ0 ++ Θ).
Proof.
  induction Θ as [ | [a b] Θ0 IH ]; intros Ξ0 Hlc HΞ.
  - exists nil. split; [ constructor | ].
    rewrite app_nil_r. apply a_inc__empty; auto.
  - apply lc_aenv_inv in Hlc; destruct Hlc as [Hlcb Hlc0].
    destruct b.
    + (* abind_tvar : Θ,α ⊑ Ξ0,α,Θ — a_inc__tvar with Ξ := Ξ0 *)
      destruct (IH nil) as [ρ0 [Hid Hinc]]; [ exact Hlc0 | constructor | ].
      simpl in Hinc.
      exists ρ0. split; auto.
      apply (a_inc__tvar (Ξ := Ξ0)); auto.
    + (* abind_var_typ A : entry carried over, ≡ᵗ-reflexive middle *)
      destruct (IH nil) as [ρ0 [Hid Hinc]]; [ exact Hlc0 | constructor | ].
      simpl in Hinc.
      exists ρ0. split; auto.
      replace ((a, abind_var_typ p) :: Θ0)
        with ((a ~ abind_var_typ p) ++ Θ0) by reflexivity.
      apply a_inc__var; auto.
      rewrite msubst_ptyp_id; auto.
      apply a_tyequiv__refl. exact Hlcb.
    + (* abind_var_skl P : ≡ˢ-reflexive middle *)
      destruct (IH nil) as [ρ0 [Hid Hinc]]; [ exact Hlc0 | constructor | ].
      simpl in Hinc.
      exists ρ0. split; auto.
      replace ((a, abind_var_skl p) :: Θ0)
        with ((a ~ abind_var_skl p) ++ Θ0) by reflexivity.
      apply a_inc__var_skl; auto.
      rewrite msubst_pskl_id; auto.
      apply a_pskl_tyequiv__refl. exact Hlcb.
    + (* abind_flex_mono : solve α̂ with itself; α̂ sits inside the target *)
      destruct (IH (Ξ0 ++ (a ~ abind_flex_mono)) Hlc0)
        as [ρ0 [Hid Hinc]].
      { apply a_suffix_app; auto.
        apply (a_suffix__cons a (b := abind_flex_mono)); constructor. }
      first [ rewrite <- app_assoc in Hinc | rewrite app_assoc in Hinc ]; simpl in Hinc.
      exists ((a, ptyp_var_f a) :: ρ0). split.
      { constructor; auto. unfold is_id_entry; reflexivity. }
      replace ((a, abind_flex_mono) :: Θ0)
        with ((a ~ abind_flex_mono) ++ Θ0) by reflexivity.
      apply a_inc__flex; auto.
      * apply a_wf_ptyp__var. right; left.
        unfold binds; apply in_or_app; right; left; reflexivity.
      * constructor.
    + (* abind_flex_mono_def τ : α̂:=τ, entry looked up in the target *)
      destruct (IH (Ξ0 ++ (a ~ abind_flex_mono_def p)) Hlc0)
        as [ρ0 [Hid Hinc]].
      { apply a_suffix_app; auto.
        apply (a_suffix__cons a (b := abind_flex_mono_def p)); constructor. }
      first [ rewrite <- app_assoc in Hinc | rewrite app_assoc in Hinc ]; simpl in Hinc.
      exists ((a, ptyp_var_f a) :: ρ0). split.
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

(** [Θ ⊴ Θ] — reflexivity of information increase (payloads locally
    closed; well-formed contexts qualify via [a_wf_aenv_lc_aenv]). *)
Lemma a_isub_refl_lc : forall Θ, lc_aenv Θ -> Θ ⊴ Θ.
Proof.
  intros Θ Hlc. split.
  - destruct (a_inc_refl_gen (Ξ0 := nil) Hlc) as [ρ [Hid Hinc]];
      [ constructor | ].
    exists ρ. simpl in Hinc. auto.
  - auto.
Qed.

(** [Θ ⊴ Ξ ++ Θ] — the target may grow by a fresh flexible suffix. *)
Lemma a_isub_weaken_suffix : forall Θ Ξ,
  lc_aenv Θ ->
  a_suffix Ξ ->
  Θ ⊴ (Ξ ++ Θ).
Proof.
  intros Θ Ξ Hlc HΞ. split.
  - destruct (a_inc_refl_gen (Ξ0 := Ξ) Hlc) as [ρ [Hid Hinc]]; auto.
    exists ρ. auto.
  - intros α τ Hb. unfold binds; apply in_or_app; auto.
Qed.

(* ===================================================================== *)
(*  Transport of context lookups along an (identity) information increase *)
(*  — the mechanized content of the paper's "stability" remark            *)
(*  (proofs.tex:19-26)                                                    *)
(* ===================================================================== *)

Lemma is_id_msubst_inv : forall α τ ρ,
  is_id_msubst ((α, τ) :: ρ) ->
  τ = ptyp_var_f α /\ is_id_msubst ρ.
Proof.
  intros * H; inversion H as [ | ? ? He Hρ ]; subst.
  unfold is_id_entry in He; simpl in He; subst; auto.
Qed.

(** The target of an increase from an all-flexible source is all-flexible. *)
Lemma a_inc_suffix_target : forall Θ ρ Θ',
  ρ ∷ Θ ⊑ Θ' ->
  a_suffix Θ ->
  a_suffix Θ'.
Proof.
  intros * Hinc; induction Hinc; intros Hsuf; auto;
    inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst; auto;
    inversion Hb.
Qed.

(** Peeling an all-flexible prefix of the source keeps the target. *)
Lemma a_inc_strengthen_suffix_src : forall Ξ Θ ρ Θ',
  a_suffix Ξ ->
  ρ ∷ (Ξ ++ Θ) ⊑ Θ' ->
  exists ρ', (is_id_msubst ρ -> is_id_msubst ρ') /\ ρ' ∷ Θ ⊑ Θ'.
Proof.
  intros Ξ; induction Ξ as [ | [a b] Ξ' IH ]; intros Θ ρ Θ' Hsuf Hinc.
  - exists ρ. auto.
  - inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst.
    inversion Hb; subst; simpl in Hinc;
      inversion Hinc; subst;
      match goal with
      | H : _ ∷ (Ξ' ++ Θ) ⊑ Θ' |- _ =>
          destruct (IH _ _ _ Hsuf' H) as [ρ' [Hid' Hinc']]
      end;
      exists ρ'; split; auto;
      intros Hid; apply Hid'; eapply proj2, is_id_msubst_inv; eauto.
Qed.

(** Head inversions: rigid and term-variable entries are carried over. *)
Lemma a_inc_tvar_inv : forall α Θ ρ Θ',
  ρ ∷ ((α ~ abind_tvar) ++ Θ) ⊑ Θ' ->
  exists Ξ Θ2, Θ' = Ξ ++ (α ~ abind_tvar) ++ Θ2 /\ a_suffix Ξ /\ ρ ∷ Θ ⊑ Θ2.
Proof. intros * H; inversion H; subst; eauto 6. Qed.

Lemma a_inc_var_inv : forall x A Θ ρ Θ',
  ρ ∷ ((x ~ abind_var_typ A) ++ Θ) ⊑ Θ' ->
  exists Ξ A' Θ2,
    Θ' = Ξ ++ (x ~ abind_var_typ A') ++ Θ2 /\
    (Θ2 ⊢ A' ≡ᵗ (msubst_ptyp ρ A)) /\
    a_suffix Ξ /\ ρ ∷ Θ ⊑ Θ2.
Proof. intros * H; inversion H; subst; eauto 8. Qed.

Lemma a_inc_var_skl_inv : forall x P Θ ρ Θ',
  ρ ∷ ((x ~ abind_var_skl P) ++ Θ) ⊑ Θ' ->
  exists Ξ P' Θ2,
    Θ' = Ξ ++ (x ~ abind_var_skl P') ++ Θ2 /\
    (Θ2 ⊢ P' ≡ˢ (msubst_pskl ρ P)) /\
    a_suffix Ξ /\ ρ ∷ Θ ⊑ Θ2.
Proof. intros * H; inversion H; subst; eauto 8. Qed.

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

(** Flexibility survives an arbitrary context PREFIX ([binds] is plain
    membership, so no freshness side condition is needed — contrast
    [a_flex_tvar_weaken_cons], which asks for one it does not use).
    (Relocated here from prop_consis_sound to break an import cycle.) *)
Lemma a_flex_tvar_weaken_prefix : forall α Ξ Θ,
  a_flex_tvar Θ α -> a_flex_tvar (Ξ ++ Θ) α.
Proof.
  intros * [Hb | [τ Hb]]; [ left | right; exists τ ];
    unfold binds in *; apply in_or_app; right; exact Hb.
Qed.

(** [a_tyequiv] uses its context only through positive [binds] lookups, so it
    is monotone in the context. *)
Lemma a_tyequiv_weaken : forall Θ Θ' A A',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  Θ ⊢ A ≡ᵗ A' ->
  Θ' ⊢ A ≡ᵗ A'.
Proof.
  intros * Hmon Heq; induction Heq; eauto using a_tyequiv.
Qed.

(** Rigid variables survive any increase. *)
Lemma a_inc_binds_tvar : forall Θ ρ Θ' α,
  ρ ∷ Θ ⊑ Θ' ->
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
Lemma a_inc_binds_flex : forall Θ ρ Θ' α,
  ρ ∷ Θ ⊑ Θ' ->
  is_id_msubst ρ ->
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
Lemma a_inc_binds_flex_def : forall Θ ρ Θ' α τ0,
  ρ ∷ Θ ⊑ Θ' ->
  is_id_msubst ρ ->
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
Lemma a_inc_binds_tvarish : forall Θ ρ Θ' α,
  ρ ∷ Θ ⊑ Θ' ->
  is_id_msubst ρ ->
  a_binds_tvar α Θ ->
  a_binds_tvar α Θ'.
Proof.
  intros * Hinc Hid [Hb | [Hb | [τ0 Hb]]].
  - left; eauto using a_inc_binds_tvar.
  - eauto using a_inc_binds_flex.
  - eapply a_inc_binds_flex_def in Hb as [? ?]; eauto.
Qed.

(** Stability of type equivalence under identity increases. *)
Lemma a_tyequiv_isub : forall Θ ρ Θ' A A',
  ρ ∷ Θ ⊑ Θ' ->
  is_id_msubst ρ ->
  Θ ⊢ A ≡ᵗ A' ->
  Θ' ⊢ A ≡ᵗ A'.
Proof.
  intros * Hinc Hid Heq; induction Heq.
  - apply a_tyequiv__refl; auto.
  - apply a_tyequiv__sym; auto.
  - eapply a_tyequiv__trans; eauto.
  - eapply a_inc_binds_flex_def in H as [_ ?]; eauto.
  - apply a_tyequiv__arrow; auto.
  - eapply a_tyequiv__all; eauto.
Qed.

(** [ptyp_to_pskl] preserves local closure. *)
Lemma lc_ptyp_to_pskl : forall A,
  lc_ptyp A -> lc_pskl (ptyp_to_pskl A).
Proof.
  intros A H; induction H; simpl; try solve [ constructor; auto ].
  constructor. intros α.
  rewrite <- ptyp_to_pskl_open. auto.
Qed.

(** Type equivalence embeds into skeleton equivalence. *)
Lemma a_tyequiv_pskl : forall Θ A A',
  Θ ⊢ A ≡ᵗ A' ->
  Θ ⊢ (ptyp_to_pskl A) ≡ˢ (ptyp_to_pskl A').
Proof.
  intros * Heq; induction Heq; simpl.
  - apply a_pskl_tyequiv__refl. apply lc_ptyp_to_pskl; auto.
  - apply a_pskl_tyequiv__sym; auto.
  - eapply a_pskl_tyequiv__trans; eauto.
  - apply a_pskl_tyequiv__flex_def; auto.
  - apply a_pskl_tyequiv__arrow; auto.
  - apply a_pskl_tyequiv__all with (L := L). intros α Hα.
    repeat rewrite <- ptyp_to_pskl_open. auto.
Qed.

(** Stability of skeleton equivalence under identity increases. *)
Lemma a_pskl_tyequiv_isub : forall Θ ρ Θ' P P',
  ρ ∷ Θ ⊑ Θ' ->
  is_id_msubst ρ ->
  Θ ⊢ P ≡ˢ P' ->
  Θ' ⊢ P ≡ˢ P'.
Proof.
  intros * Hinc Hid Heq; induction Heq.
  - apply a_pskl_tyequiv__refl; auto.
  - apply a_pskl_tyequiv__sym; auto.
  - eapply a_pskl_tyequiv__trans; eauto.
  - eapply a_inc_binds_flex_def in H as [_ Heqv]; eauto.
    change (pskl_var_f α) with (ptyp_to_pskl (ptyp_var_f α)).
    apply a_tyequiv_pskl. exact Heqv.
  - apply a_pskl_tyequiv__arrow; auto.
  - eapply a_pskl_tyequiv__all; eauto.
  - apply a_pskl_tyequiv__tophole; auto.
Qed.

(* ===================================================================== *)
(*  Transitivity of (identity) information increase                        *)
(* ===================================================================== *)

Lemma a_inc_trans : forall Θ0 ρ1 Θ1,
  ρ1 ∷ Θ0 ⊑ Θ1 ->
  is_id_msubst ρ1 ->
  forall ρ2 Θ2,
  ρ2 ∷ Θ1 ⊑ Θ2 ->
  is_id_msubst ρ2 ->
  exists ρ, is_id_msubst ρ /\ ρ ∷ Θ0 ⊑ Θ2.
Proof.
  intros Θ0 ρ1 Θ1 Hinc1;
    induction Hinc1 as
      [ Ξ HΞ
      | Θ ρ Θ' α τ Hinc IH Hwf Hmono
      | Θ ρ Θ' α τ τ' Hinc IH Hwf Hmono Hteq
      | Θ ρ Θ' Ξ x A A' Hinc IH Heqm HΞ
      | Θ ρ Θ' Ξ x P P' Hinc IH Heqm HΞ
      | Θ ρ Θ' Ξ α Hinc IH HΞ ];
    intros Hid1 ρ2 Θ2 Hinc2 Hid2.
  - (* empty: Θ0 = nil, Θ1 = Ξ all-flexible ⇒ Θ2 all-flexible *)
    exists nil. split; [ constructor | ].
    apply a_inc__empty. eauto using a_inc_suffix_target.
  - (* flex head *)
    apply is_id_msubst_inv in Hid1 as [Heqτ Hid1]; subst.
    destruct (IH Hid1 _ _ Hinc2 Hid2) as [ρ' [Hid' Hinc']].
    assert (Htv2 : a_binds_tvar α Θ2).
    { inversion Hwf; subst. eauto using a_inc_binds_tvarish. }
    exists ((α, ptyp_var_f α) :: ρ'). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex;
      [ exact Hinc' | apply a_wf_ptyp__var; exact Htv2 | constructor ].
  - (* flex_def head *)
    apply is_id_msubst_inv in Hid1 as [Heqτ Hid1]; subst.
    destruct (IH Hid1 _ _ Hinc2 Hid2) as [ρ' [Hid' Hinc']].
    assert (Htv2 : a_binds_tvar α Θ2).
    { inversion Hwf; subst. eauto using a_inc_binds_tvarish. }
    assert (Heqv : Θ2 ⊢ (ptyp_var_f α) ≡ᵗ (msubst_ptyp ρ' τ)).
    { rewrite msubst_ptyp_id; [ | exact Hid' ].
      rewrite msubst_ptyp_id in Hteq; [ | exact Hid1 ].
      exact (a_tyequiv_isub Hinc2 Hid2 Hteq). }
    exists ((α, ptyp_var_f α) :: ρ'). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex_def;
      [ exact Hinc' | apply a_wf_ptyp__var; exact Htv2 | constructor
      | exact Heqv ].
  - (* var head: peel the suffix, invert the carried entry *)
    edestruct a_inc_strengthen_suffix_src as [ρ2' [Hid2' Hinc2']];
      [ exact HΞ | exact Hinc2 | ].
    apply a_inc_var_inv in Hinc2'
      as [Ξ2 [A2' [Θ2' [Heq [Heqv2 [HΞ2 Hinc2'']]]]]]; subst.
    destruct (IH Hid1 _ _ Hinc2'' (Hid2' Hid2)) as [ρ' [Hid' Hinc']].
    exists ρ'. split; auto.
    apply a_inc__var; auto.
    (* compose the two semantic middles across the identity increase *)
    rewrite msubst_ptyp_id by exact Hid'.
    rewrite msubst_ptyp_id in Heqv2 by exact (Hid2' Hid2).
    rewrite msubst_ptyp_id in Heqm by exact Hid1.
    eapply a_tyequiv__trans; [ exact Heqv2 | ].
    eapply a_tyequiv_isub; [ exact Hinc2'' | exact (Hid2' Hid2) | exact Heqm ].
  - (* var_skl head *)
    edestruct a_inc_strengthen_suffix_src as [ρ2' [Hid2' Hinc2']];
      [ exact HΞ | exact Hinc2 | ].
    apply a_inc_var_skl_inv in Hinc2'
      as [Ξ2 [P2' [Θ2' [Heq [Heqv2 [HΞ2 Hinc2'']]]]]]; subst.
    destruct (IH Hid1 _ _ Hinc2'' (Hid2' Hid2)) as [ρ' [Hid' Hinc']].
    exists ρ'. split; auto.
    apply a_inc__var_skl; auto.
    rewrite msubst_pskl_id by exact Hid'.
    rewrite msubst_pskl_id in Heqv2 by exact (Hid2' Hid2).
    rewrite msubst_pskl_id in Heqm by exact Hid1.
    eapply a_pskl_tyequiv__trans; [ exact Heqv2 | ].
    eapply a_pskl_tyequiv_isub; [ exact Hinc2'' | exact (Hid2' Hid2) | exact Heqm ].
  - (* tvar head *)
    edestruct a_inc_strengthen_suffix_src as [ρ2' [Hid2' Hinc2']];
      [ exact HΞ | exact Hinc2 | ].
    apply a_inc_tvar_inv in Hinc2' as [Ξ2 [Θ2' [Heq [HΞ2 Hinc2'']]]]; subst.
    destruct (IH Hid1 _ _ Hinc2'' (Hid2' Hid2)) as [ρ' [Hid' Hinc']].
    exists ρ'. split; auto.
    apply a_inc__tvar; auto.
Qed.

(** [⊴] is transitive. *)
Lemma a_isub_trans : forall Θ0 Θ1 Θ2,
  Θ0 ⊴ Θ1 -> Θ1 ⊴ Θ2 -> Θ0 ⊴ Θ2.
Proof.
  intros * [[ρ1 [Hid1 H1]] Hd1] [[ρ2 [Hid2 H2]] Hd2].
  split.
  - destruct (a_inc_trans H1 Hid1 H2 Hid2) as [ρ [Hid Hinc]].
    exists ρ; auto.
  - auto.
Qed.

