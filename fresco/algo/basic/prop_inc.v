(** Information-increase (metasubstitution) algebra.

    Basic properties of [a_inc] / [⊴] (paper fig:information-increase) that
    every appendix-B/C soundness case threads: identity metasubstitutions
    are reflexive, and the target may grow by a fresh flexible suffix.
    Both come out of one generalized induction ([a_inc_refl_gen]). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Identity substitutions are identities                                 *)
(* ===================================================================== *)

(** The identity metasubstitution looks every variable up to itself. *)
Lemma msubst_lookup_id : forall κ α',
  is_id_msubst κ ->
  msubst_lookup κ α' = ptyp_var_f α'.
Proof.
  induction κ as [ | [α τ] κ' IH ]; intros α' Hid; simpl; auto.
  inversion Hid as [ | ? ? He Hid' ]; subst.
  unfold is_id_entry in He; simpl in He; subst.
  destruct (α' == α) as [->|Hne]; [ reflexivity | apply IH; exact Hid' ].
Qed.

Lemma msubst_ptyp_id : forall κ A,
  is_id_msubst κ ->
  msubst_ptyp κ A = A.
Proof.
  intros κ A Hid; induction A; simpl; f_equal; auto.
  apply msubst_lookup_id; exact Hid.
Qed.

Lemma msubst_pskl_id : forall κ P,
  is_id_msubst κ ->
  msubst_pskl κ P = P.
Proof.
  intros κ P Hid; induction P; simpl; f_equal; auto.
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
(*  contexts satisfy it ([a_wf_aenv_lc_aenv], algo/basic/prop_context.v).           *)
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

#[export] Hint Resolve lc_aenv_nil : core.

(* ===================================================================== *)
(*  Reflexivity, generalized with a fresh-suffix target extension:        *)
(*  Θ ⊑[ι] Ξ0 ++ Θ  for any flexible suffix Ξ0.                           *)
(* ===================================================================== *)

Lemma a_inc_refl_gen : forall Θ Ξ0,
  lc_aenv Θ ->
  a_suffix Ξ0 ->
  exists κ, is_id_msubst κ /\ κ ∷ Θ ⊑ (Ξ0 ++ Θ).
Proof.
  induction Θ as [ | [a b] Θ0 IH ]; intros Ξ0 Hlc HΞ.
  - exists nil. split; [ constructor | ].
    rewrite app_nil_r. apply a_inc__empty; auto.
  - apply lc_aenv_inv in Hlc; destruct Hlc as [Hlcb Hlc0].
    destruct b.
    + (* abind_tvar : Θ,α ⊑ Ξ0,α,Θ — a_inc__tvar with Ξ := Ξ0 *)
      destruct (IH nil) as [κ0 [Hid Hinc]]; [ exact Hlc0 | constructor | ].
      simpl in Hinc.
      exists κ0. split; auto.
      apply (a_inc__tvar (Ξ := Ξ0)); auto.
    + (* abind_var_typ A : entry carried over, ≡ᵗ-reflexive middle *)
      destruct (IH nil) as [κ0 [Hid Hinc]]; [ exact Hlc0 | constructor | ].
      simpl in Hinc.
      exists κ0. split; auto.
      replace ((a, abind_var_typ p) :: Θ0)
        with ((a ~ abind_var_typ p) ++ Θ0) by reflexivity.
      apply a_inc__var; auto.
      rewrite msubst_ptyp_id; auto.
      apply a_tyequiv__refl. exact Hlcb.
    + (* abind_var_skl P : ≡ˢ-reflexive middle *)
      destruct (IH nil) as [κ0 [Hid Hinc]]; [ exact Hlc0 | constructor | ].
      simpl in Hinc.
      exists κ0. split; auto.
      replace ((a, abind_var_skl p) :: Θ0)
        with ((a ~ abind_var_skl p) ++ Θ0) by reflexivity.
      apply a_inc__var_skl; auto.
      rewrite msubst_pskl_id; auto.
      apply a_pskl_tyequiv__refl. exact Hlcb.
    + (* abind_flex_mono : solve α̂ with itself; α̂ sits inside the target *)
      destruct (IH (Ξ0 ++ (a ~ abind_flex_mono)) Hlc0)
        as [κ0 [Hid Hinc]].
      { apply a_suffix_app; auto.
        apply (a_suffix__cons a (b := abind_flex_mono)); constructor. }
      first [ rewrite <- app_assoc in Hinc | rewrite app_assoc in Hinc ]; simpl in Hinc.
      exists ((a, ptyp_var_f a) :: κ0). split.
      { constructor; auto. unfold is_id_entry; reflexivity. }
      replace ((a, abind_flex_mono) :: Θ0)
        with ((a ~ abind_flex_mono) ++ Θ0) by reflexivity.
      apply a_inc__flex; auto.
      * apply a_wf_ptyp__var. right; left.
        unfold binds; apply in_or_app; right; left; reflexivity.
      * constructor.
    + (* abind_flex_mono_def τ : α̂:=τ, entry looked up in the target *)
      destruct (IH (Ξ0 ++ (a ~ abind_flex_mono_def p)) Hlc0)
        as [κ0 [Hid Hinc]].
      { apply a_suffix_app; auto.
        apply (a_suffix__cons a (b := abind_flex_mono_def p)); constructor. }
      first [ rewrite <- app_assoc in Hinc | rewrite app_assoc in Hinc ]; simpl in Hinc.
      exists ((a, ptyp_var_f a) :: κ0). split.
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

(** [Θ ⊴ Ξ ++ Θ] — the target may grow by a fresh flexible suffix (at
    [Ξ = nil] this is reflexivity, [a_isub_refl] in prop_basic.v). *)
Lemma a_isub_weaken_suffix : forall Θ Ξ,
  lc_aenv Θ ->
  a_suffix Ξ ->
  Θ ⊴ (Ξ ++ Θ).
Proof.
  intros Θ Ξ Hlc HΞ. split.
  - destruct (a_inc_refl_gen (Ξ0 := Ξ) Hlc) as [κ [Hid Hinc]]; auto.
    exists κ. auto.
  - intros α τ Hb. unfold binds; apply in_or_app; auto.
Qed.

(* ===================================================================== *)
(*  Transport of context lookups along an (identity) information increase *)
(*  — the mechanized content of the paper's "stability" remark            *)
(*  (proofs.tex:19-26)                                                    *)
(* ===================================================================== *)

Lemma is_id_msubst_inv : forall α τ κ,
  is_id_msubst ((α, τ) :: κ) ->
  τ = ptyp_var_f α /\ is_id_msubst κ.
Proof.
  intros * H; inversion H as [ | ? ? He Hκ ]; subst.
  unfold is_id_entry in He; simpl in He; subst; auto.
Qed.

(** The target of an increase from an all-flexible source is all-flexible. *)
Lemma a_inc_suffix_target : forall Θ κ Θ',
  κ ∷ Θ ⊑ Θ' ->
  a_suffix Θ ->
  a_suffix Θ'.
Proof.
  intros * Hinc; induction Hinc; intros Hsuf; auto;
    inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst; auto;
    inversion Hb.
Qed.

(** Peeling an all-flexible prefix of the source keeps the target. *)
Lemma a_inc_strengthen_suffix_src : forall Ξ Θ κ Θ',
  a_suffix Ξ ->
  κ ∷ (Ξ ++ Θ) ⊑ Θ' ->
  exists κ', (is_id_msubst κ -> is_id_msubst κ') /\ κ' ∷ Θ ⊑ Θ'.
Proof.
  intros Ξ; induction Ξ as [ | [a b] Ξ' IH ]; intros Θ κ Θ' Hsuf Hinc.
  - exists κ. auto.
  - inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst.
    inversion Hb; subst; simpl in Hinc;
      inversion Hinc; subst;
      match goal with
      | H : _ ∷ (Ξ' ++ Θ) ⊑ Θ' |- _ =>
          destruct (IH _ _ _ Hsuf' H) as [κ' [Hid' Hinc']]
      end;
      exists κ'; split; auto;
      intros Hid; apply Hid'; eapply proj2, is_id_msubst_inv; eauto.
Qed.

(** Head inversions: rigid and term-variable entries are carried over. *)
Lemma a_inc_tvar_inv : forall α Θ κ Θ',
  κ ∷ ((α ~ abind_tvar) ++ Θ) ⊑ Θ' ->
  exists Ξ Θ2, Θ' = Ξ ++ (α ~ abind_tvar) ++ Θ2 /\ a_suffix Ξ /\ κ ∷ Θ ⊑ Θ2.
Proof. intros * H; inversion H; subst; eauto 6. Qed.

Lemma a_inc_var_inv : forall x A Θ κ Θ',
  κ ∷ ((x ~ abind_var_typ A) ++ Θ) ⊑ Θ' ->
  exists Ξ A' Θ2,
    Θ' = Ξ ++ (x ~ abind_var_typ A') ++ Θ2 /\
    ({{ Θ2 ⊢ A' ≡ᵗ (msubst_ptyp κ A) }}a) /\
    a_suffix Ξ /\ κ ∷ Θ ⊑ Θ2.
Proof. intros * H; inversion H; subst; eauto 8. Qed.

Lemma a_inc_var_skl_inv : forall x P Θ κ Θ',
  κ ∷ ((x ~ abind_var_skl P) ++ Θ) ⊑ Θ' ->
  exists Ξ P' Θ2,
    Θ' = Ξ ++ (x ~ abind_var_skl P') ++ Θ2 /\
    ({{ Θ2 ⊢ P' ≡ˢ (msubst_pskl κ P) }}a) /\
    a_suffix Ξ /\ κ ∷ Θ ⊑ Θ2.
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

(** Transport equivalence by interpreting each flexible definition in the
    target context; a syntactically identical binding is not required. *)
Lemma a_tyequiv_transport : forall Θ Θ' A B,
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     {{ Θ' ⊢ (ptyp_var_f α) ≡ᵗ τ }}a) ->
  {{ Θ ⊢ A ≡ᵗ B }}a -> {{ Θ' ⊢ A ≡ᵗ B }}a.
Proof.
  intros * Hdefs Heq; induction Heq; eauto using a_tyequiv.
Qed.

Lemma a_pskl_tyequiv_transport : forall Θ Θ' P Q,
  (forall α τ, binds α (abind_flex_mono_def τ) Θ ->
     {{ Θ' ⊢ (pskl_var_f α) ≡ˢ (ptyp_to_pskl τ) }}a) ->
  {{ Θ ⊢ P ≡ˢ Q }}a -> {{ Θ' ⊢ P ≡ˢ Q }}a.
Proof.
  intros * Hdefs Heq; induction Heq; eauto using a_pskl_tyequiv.
Qed.

(** [a_tyequiv] uses its context only through positive [binds] lookups, so it
    is monotone in the context. *)
Lemma a_tyequiv_weaken : forall Θ Θ' A A',
  (forall x b, binds x b Θ -> binds x b Θ') ->
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ Θ' ⊢ A ≡ᵗ A' }}a.
Proof.
  intros * Hmon. apply a_tyequiv_transport.
  intros; apply a_tyequiv__flex_def; auto.
Qed.

(** Rigid variables survive any increase. *)
Lemma a_inc_binds_tvar : forall Θ κ Θ' α,
  κ ∷ Θ ⊑ Θ' ->
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

(** A suffix carries no rigid entry. *)
Lemma a_suffix_no_tvar : forall Ξ α,
  a_suffix Ξ -> binds α abind_tvar Ξ -> False.
Proof.
  intros Ξ α H; induction H; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
    [ subst; inversion H0 | auto ].
Qed.

(** …and the CONVERSE of [a_inc_binds_tvar]: an increase never INVENTS a
    rigid, so a rigid of the target is already a rigid of the source.  It is
    what lets a consumer discharge the "…or the run invented this name" arm
    of the disjunctive ftv bounds ([a_looksub_lookeq_ftv],
    [a_solve_cstr_ftv]) for a variable it only knows to be rigid in the
    LARGER context — the ρ-replaced variables of P6-Cs / P6-Ss are exactly
    that.  Promoted here from cex/cex_p6cs_rsubst_delta_vacuous.v, which is
    where it was first needed (to show the old [Δρ ∩ dom Θ0 = ∅] premise
    forced [Δρ = ∅]). *)
Lemma a_inc_binds_tvar_rev : forall Θ κ Θ' α,
  κ ∷ Θ ⊑ Θ' ->
  binds α abind_tvar Θ' ->
  binds α abind_tvar Θ.
Proof.
  intros Θ κ Θ' α Hinc; induction Hinc; intros Hb;
    try solve [ exfalso; eapply a_suffix_no_tvar; eassumption
              | apply binds_cons_3; auto ];
    analyze_binds Hb;
    solve [ exfalso; eapply a_suffix_no_tvar; eassumption
          | apply binds_cons_3; auto
          | unfold binds; left; reflexivity ].
Qed.

(** Declared flexible variables survive an identity increase (as SOME
    tvar-ish entry): the flex rule's well-formedness premise applied to the
    identity image [α̂]. *)
Lemma a_inc_binds_flex : forall Θ κ Θ' α,
  κ ∷ Θ ⊑ Θ' ->
  is_id_msubst κ ->
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
Lemma a_inc_binds_flex_def : forall Θ κ Θ' α τ0,
  κ ∷ Θ ⊑ Θ' ->
  is_id_msubst κ ->
  binds α (abind_flex_mono_def τ0) Θ ->
  a_binds_tvar α Θ' /\ {{ Θ' ⊢ (ptyp_var_f α) ≡ᵗ τ0 }}a.
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
Lemma a_inc_binds_tvarish : forall Θ κ Θ' α,
  κ ∷ Θ ⊑ Θ' ->
  is_id_msubst κ ->
  a_binds_tvar α Θ ->
  a_binds_tvar α Θ'.
Proof.
  intros * Hinc Hid [Hb | [Hb | [τ0 Hb]]].
  - left; eauto using a_inc_binds_tvar.
  - eauto using a_inc_binds_flex.
  - eapply a_inc_binds_flex_def in Hb as [? ?]; eauto.
Qed.

(** Stability of type equivalence under identity increases. *)
Lemma a_tyequiv_isub : forall Θ κ Θ' A A',
  κ ∷ Θ ⊑ Θ' ->
  is_id_msubst κ ->
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ Θ' ⊢ A ≡ᵗ A' }}a.
Proof.
  intros * Hinc Hid. apply a_tyequiv_transport.
  intros; eapply a_inc_binds_flex_def; eauto.
Qed.

(** Type equivalence embeds into skeleton equivalence. *)
Lemma a_tyequiv_pskl : forall Θ A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ Θ ⊢ (ptyp_to_pskl A) ≡ˢ (ptyp_to_pskl A') }}a.
Proof.
  intros * Heq; induction Heq; simpl.
  - apply a_pskl_tyequiv__refl. apply ptyp_to_pskl_lc; auto.
  - apply a_pskl_tyequiv__sym; auto.
  - eapply a_pskl_tyequiv__trans; eauto.
  - apply a_pskl_tyequiv__flex_def; auto.
  - apply a_pskl_tyequiv__arrow; auto.
  - apply a_pskl_tyequiv__all with (L := L). intros α Hα.
    repeat rewrite <- ptyp_to_pskl_open. auto.
Qed.

(** Stability of skeleton equivalence under identity increases. *)
Lemma a_pskl_tyequiv_isub : forall Θ κ Θ' P P',
  κ ∷ Θ ⊑ Θ' ->
  is_id_msubst κ ->
  {{ Θ ⊢ P ≡ˢ P' }}a ->
  {{ Θ' ⊢ P ≡ˢ P' }}a.
Proof.
  intros * Hinc Hid. apply a_pskl_tyequiv_transport.
  intros; change (pskl_var_f _) with (ptyp_to_pskl (ptyp_var_f α)).
  apply a_tyequiv_pskl. eapply a_inc_binds_flex_def; eauto.
Qed.

(* ===================================================================== *)
(*  Transitivity of (identity) information increase                        *)
(* ===================================================================== *)

Lemma a_inc_trans : forall Θ0 κ1 Θ1,
  κ1 ∷ Θ0 ⊑ Θ1 ->
  is_id_msubst κ1 ->
  forall κ2 Θ2,
  κ2 ∷ Θ1 ⊑ Θ2 ->
  is_id_msubst κ2 ->
  exists κ, is_id_msubst κ /\ κ ∷ Θ0 ⊑ Θ2.
Proof.
  intros Θ0 κ1 Θ1 Hinc1;
    induction Hinc1 as
      [ Ξ HΞ
      | Θ κ Θ' α τ Hinc IH Hwf Hmono
      | Θ κ Θ' α τ τ' Hinc IH Hwf Hmono Hteq
      | Θ κ Θ' Ξ x A A' Hinc IH Heqm HΞ
      | Θ κ Θ' Ξ x P P' Hinc IH Heqm HΞ
      | Θ κ Θ' Ξ α Hinc IH HΞ ];
    intros Hid1 κ2 Θ2 Hinc2 Hid2.
  - (* empty: Θ0 = nil, Θ1 = Ξ all-flexible ⇒ Θ2 all-flexible *)
    exists nil. split; [ constructor | ].
    apply a_inc__empty. eauto using a_inc_suffix_target.
  - (* flex head *)
    apply is_id_msubst_inv in Hid1 as [Heqτ Hid1]; subst.
    destruct (IH Hid1 _ _ Hinc2 Hid2) as [κ' [Hid' Hinc']].
    assert (Htv2 : a_binds_tvar α Θ2).
    { inversion Hwf; subst. eauto using a_inc_binds_tvarish. }
    exists ((α, ptyp_var_f α) :: κ'). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex;
      [ exact Hinc' | apply a_wf_ptyp__var; exact Htv2 | constructor ].
  - (* flex_def head *)
    apply is_id_msubst_inv in Hid1 as [Heqτ Hid1]; subst.
    destruct (IH Hid1 _ _ Hinc2 Hid2) as [κ' [Hid' Hinc']].
    assert (Htv2 : a_binds_tvar α Θ2).
    { inversion Hwf; subst. eauto using a_inc_binds_tvarish. }
    assert (Heqv : {{ Θ2 ⊢ (ptyp_var_f α) ≡ᵗ (msubst_ptyp κ' τ) }}a).
    { rewrite msubst_ptyp_id; [ | exact Hid' ].
      rewrite msubst_ptyp_id in Hteq; [ | exact Hid1 ].
      exact (a_tyequiv_isub Hinc2 Hid2 Hteq). }
    exists ((α, ptyp_var_f α) :: κ'). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex_def;
      [ exact Hinc' | apply a_wf_ptyp__var; exact Htv2 | constructor
      | exact Heqv ].
  - (* var head: peel the suffix, invert the carried entry *)
    edestruct a_inc_strengthen_suffix_src as [κ2' [Hid2' Hinc2']];
      [ exact HΞ | exact Hinc2 | ].
    apply a_inc_var_inv in Hinc2'
      as [Ξ2 [A2' [Θ2' [Heq [Heqv2 [HΞ2 Hinc2'']]]]]]; subst.
    destruct (IH Hid1 _ _ Hinc2'' (Hid2' Hid2)) as [κ' [Hid' Hinc']].
    exists κ'. split; auto.
    apply a_inc__var; auto.
    (* compose the two semantic middles across the identity increase *)
    rewrite msubst_ptyp_id by exact Hid'.
    rewrite msubst_ptyp_id in Heqv2 by exact (Hid2' Hid2).
    rewrite msubst_ptyp_id in Heqm by exact Hid1.
    eapply a_tyequiv__trans; [ exact Heqv2 | ].
    eapply a_tyequiv_isub; [ exact Hinc2'' | exact (Hid2' Hid2) | exact Heqm ].
  - (* var_skl head *)
    edestruct a_inc_strengthen_suffix_src as [κ2' [Hid2' Hinc2']];
      [ exact HΞ | exact Hinc2 | ].
    apply a_inc_var_skl_inv in Hinc2'
      as [Ξ2 [P2' [Θ2' [Heq [Heqv2 [HΞ2 Hinc2'']]]]]]; subst.
    destruct (IH Hid1 _ _ Hinc2'' (Hid2' Hid2)) as [κ' [Hid' Hinc']].
    exists κ'. split; auto.
    apply a_inc__var_skl; auto.
    rewrite msubst_pskl_id by exact Hid'.
    rewrite msubst_pskl_id in Heqv2 by exact (Hid2' Hid2).
    rewrite msubst_pskl_id in Heqm by exact Hid1.
    eapply a_pskl_tyequiv__trans; [ exact Heqv2 | ].
    eapply a_pskl_tyequiv_isub; [ exact Hinc2'' | exact (Hid2' Hid2) | exact Heqm ].
  - (* tvar head *)
    edestruct a_inc_strengthen_suffix_src as [κ2' [Hid2' Hinc2']];
      [ exact HΞ | exact Hinc2 | ].
    apply a_inc_tvar_inv in Hinc2' as [Ξ2 [Θ2' [Heq [HΞ2 Hinc2'']]]]; subst.
    destruct (IH Hid1 _ _ Hinc2'' (Hid2' Hid2)) as [κ' [Hid' Hinc']].
    exists κ'. split; auto.
    apply a_inc__tvar; auto.
Qed.

(** [⊴] is transitive. *)
Lemma a_isub_trans : forall Θ0 Θ1 Θ2,
  Θ0 ⊴ Θ1 -> Θ1 ⊴ Θ2 -> Θ0 ⊴ Θ2.
Proof.
  intros * [[κ1 [Hid1 H1]] Hd1] [[κ2 [Hid2 H2]] Hd2].
  split.
  - destruct (a_inc_trans H1 Hid1 H2 Hid2) as [κ [Hid Hinc]].
    exists κ; auto.
  - auto.
Qed.

Lemma lc_aenv_app_intro : forall Θ1 Θ2,
  lc_aenv Θ1 -> lc_aenv Θ2 -> lc_aenv (Θ1 ++ Θ2).
Proof. intros * H1 H2; unfold lc_aenv in *; apply Forall_app; auto. Qed.
