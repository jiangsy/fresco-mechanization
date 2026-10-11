(** Algorithmic contexts: well-formedness, bindings, flexible declarations,
    information increase, guessing and context surgery. Syntax-only shape
    and substitution facts live in [src.fresco.prop_shapes]. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_shapes.          (* the monotype-substitution kit *)
Require Import src.fresco.def_shapes.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo_decl.prop_stability.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Monotype / wf bookkeeping                                             *)
(* ===================================================================== *)


Lemma a_wf_ptyp_weaken : forall Θ Θ' A,
  (forall x b, binds x b Θ -> binds x b Θ') ->
  a_wf_ptyp Θ A ->
  a_wf_ptyp Θ' A.
Proof.
  intros * Hmon Hwf.
  eapply a_wf_ptyp_mono; [ exact Hwf | ].
  apply aenv_tbinds_le_of_binds_le. exact Hmon.
Qed.

Lemma a_tyequiv_weaken_cons : forall Θ (e : list (atom * abind)) A A',
  {{ Θ ⊢ A ≡ᵗ A' }}a ->
  {{ (e ++ Θ) ⊢ A ≡ᵗ A' }}a.
Proof.
  intros. eapply a_tyequiv_weaken; [ | eauto ].
  intros x b Hb. unfold binds; apply in_or_app; auto.
Qed.

(** Unfolding a definition inside a monotype: [A ≡ A[τ/α1̂]] when [α1̂:=τ]. *)
Lemma a_tyequiv_subst_def : forall Θ α1 τ A,
  binds α1 (abind_flex_mono_def τ) Θ ->
  mono_ptyp A ->
  lc_ptyp τ ->
  {{ Θ ⊢ A ≡ᵗ (subst_ptyp_in_ptyp τ α1 A) }}a.
Proof.
  intros * Hb Hm Hlc; induction Hm; simpl.
  - apply a_tyequiv__refl; auto.
  - destruct (eq_var α α1); subst.
    + apply a_tyequiv__flex_def; auto.
    + apply a_tyequiv__refl; auto.
  - apply a_tyequiv__arrow; auto.
Qed.

(* ===================================================================== *)
(*  Target weakening of information increase, and ⊴ cons congruences      *)
(* ===================================================================== *)

Lemma a_inc_target_weaken : forall Θ κ Θ' Ξ,
  κ ∷ Θ ⊑ Θ' ->
  a_suffix Ξ ->
  κ ∷ Θ ⊑ (Ξ ++ Θ').
Proof.
  intros * Hinc; revert Ξ; induction Hinc; intros Ξ0 HΞ0.
  - apply a_inc__empty. apply a_suffix_app; auto.
  - apply a_inc__flex; auto.
    eapply a_wf_ptyp_weaken; [ | eauto ].
    intros; unfold binds; apply in_or_app; auto.
  - apply a_inc__flex_def; auto.
    + eapply a_wf_ptyp_weaken; [ | eauto ].
      intros; unfold binds; apply in_or_app; auto.
    + apply a_tyequiv_weaken_cons; auto.
  - first [ rewrite <- app_assoc | rewrite app_assoc ].
    apply a_inc__var; auto using a_suffix_app.
  - first [ rewrite <- app_assoc | rewrite app_assoc ].
    apply a_inc__var_skl; auto using a_suffix_app.
  - first [ rewrite <- app_assoc | rewrite app_assoc ].
    apply a_inc__tvar; auto using a_suffix_app.
Qed.

(** ⊴ is preserved by pushing the SAME flexible declaration / definition /
    term-var / rigid entry on both sides. *)
Lemma a_isub_cons_flex : forall Θ Θ' α1,
  Θ ⊴ Θ' ->
  ((α1 ~ abind_flex_mono) ++ Θ) ⊴ ((α1 ~ abind_flex_mono) ++ Θ').
Proof.
  intros * [[κ [Hid Hinc]] Hd]. split.
  - exists ((α1, ptyp_var_f α1) :: κ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex.
    + apply a_inc_target_weaken; auto.
      apply (a_suffix__cons α1 (b := abind_flex_mono)); constructor.
    + apply a_wf_ptyp__var. right; left. unfold binds; left; reflexivity.
    + constructor.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

Lemma a_isub_cons_flex_def : forall Θ Θ' α1 τ,
  Θ ⊴ Θ' ->
  lc_ptyp τ ->
  ((α1 ~ abind_flex_mono_def τ) ++ Θ) ⊴ ((α1 ~ abind_flex_mono_def τ) ++ Θ').
Proof.
  intros * [[κ [Hid Hinc]] Hd] Hlc. split.
  - exists ((α1, ptyp_var_f α1) :: κ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc__flex_def.
    + apply a_inc_target_weaken; auto.
      apply (a_suffix__cons α1 (b := abind_flex_mono_def τ)); constructor.
    + apply a_wf_ptyp__var. right; right. exists τ.
      unfold binds; left; reflexivity.
    + constructor.
    + rewrite msubst_ptyp_id; auto.
      apply a_tyequiv__flex_def. unfold binds; left; reflexivity.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb']; subst.
    + inversion Heq; subst. unfold binds; left; reflexivity.
    + unfold binds; right. apply Hd; auto.
Qed.

Lemma a_isub_cons_var_typ : forall Θ Θ' x A,
  Θ ⊴ Θ' ->
  lc_ptyp A ->
  ((x ~ abind_var_typ A) ++ Θ) ⊴ ((x ~ abind_var_typ A) ++ Θ').
Proof.
  intros * [[κ [Hid Hinc]] Hd] Hlc. split.
  - exists κ. split; auto.
    replace ((x ~ abind_var_typ A) ++ Θ')
      with (nil ++ (x ~ abind_var_typ A) ++ Θ') by reflexivity.
    apply a_inc__var; auto; [ | constructor ].
    rewrite msubst_ptyp_id; auto. apply a_tyequiv__refl; auto.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

Lemma a_isub_cons_var_skl : forall Θ Θ' x P,
  Θ ⊴ Θ' ->
  lc_pskl P ->
  ((x ~ abind_var_skl P) ++ Θ) ⊴ ((x ~ abind_var_skl P) ++ Θ').
Proof.
  intros * [[κ [Hid Hinc]] Hd] Hlc. split.
  - exists κ. split; auto.
    replace ((x ~ abind_var_skl P) ++ Θ')
      with (nil ++ (x ~ abind_var_skl P) ++ Θ') by reflexivity.
    apply a_inc__var_skl; auto; [ | constructor ].
    rewrite msubst_pskl_id; auto. apply a_pskl_tyequiv__refl; auto.
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | ].
    simpl. unfold binds. right. apply Hd; auto.
Qed.

(* ===================================================================== *)
(*  Source-prefix machinery for assignvar (the [Θ0 | Ξ] split): flexible  *)
(*  declarations can be prepended to the SOURCE of an increase whenever   *)
(*  they are still visible in the target.                                 *)
(* ===================================================================== *)

Lemma a_wf_ptyp_lc : forall Θ A, a_wf_ptyp Θ A -> lc_ptyp A.
Proof.
  intros * H; induction H; auto.
Qed.

(** Well-formed contexts have locally closed binding payloads — the bridge
    that feeds [lc_aenv]-hypothesised reflexivity ([a_isub_refl] below). *)
Lemma a_wf_aenv_lc_aenv : forall Θ, {{ ⊢ Θ }}a -> lc_aenv Θ.
Proof.
  intros Θ H; induction H; constructor; simpl; auto.
  - eapply a_wf_pskl_lc; eauto.
  - eapply a_wf_ptyp_lc; eauto.
Qed.

#[export] Hint Resolve a_wf_aenv_lc_aenv : core.

(** The unconditional [a_isub_refl] of the syntactic-middle era, restored
    for well-formed contexts. *)
Lemma a_isub_refl : forall Θ, {{ ⊢ Θ }}a -> Θ ⊴ Θ.
Proof.
  intros Θ Hwf. apply (a_isub_weaken_suffix (Ξ := nil)); auto using a_suffix.
Qed.

(** Declaration-only suffixes (the paper's "Ξ only contains declarations
    of flexible variables"). *)
Inductive a_decls : aenv -> Prop :=
| a_decls__nil : a_decls nil
| a_decls__cons : forall α1 Ξ,
    a_decls Ξ ->
    a_decls ((α1 ~ abind_flex_mono) ++ Ξ).

Lemma a_decls_suffix : forall Ξ, a_decls Ξ -> a_suffix Ξ.
Proof.
  intros Ξ H; induction H; [ constructor | ].
  apply (a_suffix__cons α1 (b := abind_flex_mono)); auto; constructor.
Qed.

(** A declaration block carries no payload, so its variables ARE its
    domain.  ⚙ Moved here from algo/subtyping/prop_completeness_sub_gen.v
    (2026-08-16): the extract level's look re-rootings need it below the
    P7 stack, and this is [a_decls]'s home. *)
Lemma a_decls_no_ftvar : forall Ξ,
  a_decls Ξ -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros Ξ H; induction H as [| α1 Ξ' Hd IH]; simpl;
    [ clear; fsetdec | clear - IH; fsetdec ].
Qed.

Lemma a_inc_prepend_flex_src : forall Θ κ Θ' α1,
  κ ∷ Θ ⊑ Θ' ->
  a_binds_tvar α1 Θ' ->
  (α1, ptyp_var_f α1) :: κ ∷ ((α1 ~ abind_flex_mono) ++ Θ) ⊑ Θ'.
Proof.
  intros * Hinc Hb.
  apply a_inc__flex; auto;
    try (apply a_wf_ptyp__var; auto);
    try constructor.
Qed.

Lemma a_isub_prepend_decls_src : forall Ξ Θ Θ',
  a_decls Ξ ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ') ->
  Θ ⊴ Θ' ->
  (Ξ ++ Θ) ⊴ Θ'.
Proof.
  intros Ξ; induction Ξ as [ | [α1 b] Ξ' IH ]; intros Θ Θ' Hdecl Hvis Hle; auto.
  inversion Hdecl; subst.
  assert (Hle' : (Ξ' ++ Θ) ⊴ Θ').
  { apply IH; auto;
      try (intros α10 Hb0; apply Hvis; unfold binds; right; auto). }
  destruct Hle' as [[κ [Hid Hinc]] Hd].
  split.
  - exists ((α1, ptyp_var_f α1) :: κ). split.
    { constructor; auto. unfold is_id_entry; reflexivity. }
    apply a_inc_prepend_flex_src; auto;
      try (apply Hvis; unfold binds; left; reflexivity).
  - intros α τ0 Hb.
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      [ discriminate | auto ].
Qed.

(** Every declaration in the source of an identity increase is still
    tvar-ish in the target (specialization of the transport kit). *)
Lemma a_isub_binds_flex : forall Θ Θ' α1,
  Θ ⊴ Θ' ->
  binds α1 abind_flex_mono Θ ->
  a_binds_tvar α1 Θ'.
Proof.
  intros * [[κ [Hid Hinc]] _] Hb. eauto using a_inc_binds_flex.
Qed.

(** [guess^TY] emits a declaration-only fresh suffix. *)
Lemma a_decls_app : forall Ξ1 Ξ2,
  a_decls Ξ1 -> a_decls Ξ2 -> a_decls (Ξ1 ++ Ξ2).
Proof.
  intros * H1 H2; induction H1; simpl; auto.
  apply (a_decls__cons α1); auto.
Qed.

Lemma a_guess_mono_decls : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  a_decls βs.
Proof.
  intros * H;
    induction H as [ Θ α | Θ P Ξ A Hg IH | Θ α | Θ
                   | Θ P Q Ξ1 Ξ2 A B Hg1 IH1 Hg2 IH2
                   | L Θ P Ξ A Hg IH ].
  - apply (a_decls__cons α). constructor.
  - auto.
  - constructor.
  - constructor.
  - apply a_decls_app; auto.
  - pick fresh α. eauto.
Qed.

(* ⚙ The embedding/open commutation [ptyp_to_bskl_syn_open_var] that sat
   here lives in fresco/prop_coercions.v §6 (2026-10-10). *)

Lemma a_binds_tvar_weaken_cons : forall α (e : list (atom * abind)) Θ,
  a_binds_tvar α Θ ->
  a_binds_tvar α (e ++ Θ).
Proof.
  intros. rewrite_env (nil ++ e ++ Θ). apply a_binds_tvar_weaken_mid; auto.
Qed.

(* ===================================================================== *)
(*  THE GUESS FRESHNESS KIT (freshness campaign, DESIGN.md §4.3).          *)
(*                                                                        *)
(*  [a_guess_mono] is exists-fresh with INPUT-only side conditions and an  *)
(*  explicit CLOSE; its ∀ rule's witness enters the avoid-input.  This     *)
(*  block derives the junk-freeness that makes the kit provable            *)
(*  ([a_guess_mono_generated_fresh]), the renaming lemma, and the          *)
(*  decl/algo boundary bridge ([a_guess_mono_open_at]).                    *)
(*                                                                        *)
(*  THE INDUCTIONS ARE ON THE SUBJECT'S SIZE, NOT THE DERIVATION.  In the  *)
(*  rename's ∀ case, when the target name γ IS the recorded witness the    *)
(*  derivation must be renamed TWICE — witness off to a fresh δ, then the  *)
(*  requested rename — and the second rename applies to the RESULT of the  *)
(*  first, which is no sub-derivation.  [a_guess_mono] is syntax-directed  *)
(*  on its input [P] and opening with a variable preserves [size_pskl],   *)
(*  so a size induction has an IH for both.                                *)
(* ===================================================================== *)

Lemma ftvar_in_aenv_app : forall Θ1 Θ2,
  ftvar_in_aenv (Θ1 ++ Θ2) [=] ftvar_in_aenv Θ1 `union` ftvar_in_aenv Θ2.
Proof.
  induction Θ1 as [ | [x bd] Θ1' IH ]; intros; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

Lemma ftvar_in_aenv_cons : forall x bd Θ,
  ftvar_in_aenv ((x, bd) :: Θ)
  [=] add x (ftvar_in_abind bd `union` ftvar_in_aenv Θ).
Proof. intros. simpl. fsetdec. Qed.

Lemma ftvar_in_aenv_one : forall x bd,
  ftvar_in_aenv (x ~ bd) [=] add x (ftvar_in_abind bd).
Proof. intros. simpl. fsetdec. Qed.

Lemma dom_subset_ftvar_in_aenv : forall Θ, dom Θ [<=] ftvar_in_aenv Θ.
Proof. induction Θ as [ | [x bd] Θ' IH ]; simpl; fsetdec. Qed.

(** A flexible's DEFINITION is part of what the context mentions.  So a name
    chosen fresh for [ftvar_in_aenv Θ] is fresh for every definition in Θ —
    which is the shape the renaming lemmas ask their side condition in. *)
Lemma ftvar_in_aenv_binds_def : forall Θ β τ,
  binds β (abind_flex_mono_def τ) Θ ->
  ftvar_in_ptyp τ [<=] ftvar_in_aenv Θ.
Proof.
  induction Θ as [ | [x bd] Θ' IH ]; intros β τ Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [ [ Heq Hbd ] | Hb' ].
  - subst bd. simpl. fsetdec.
  - pose proof (IH _ _ Hb') as Hsub. simpl. fsetdec.
Qed.

(** ⭐ THE PROPERTY THAT MAKES THE KIT PROVABLE.  Every name guess^TY
    GENERATES avoids everything the ambient context mentions — DERIVED,
    not assumed: the ghost rule picks fresh for [Θ] and the ∀ rule puts its
    witness INTO [Θ], so in the ∀ case the premise's block avoids the
    witness itself.  Exactly the fact a renaming lemma needs when its
    target happens to BE that witness, and the fact the ∀-opening bridge
    needs unconditionally. *)
Lemma a_guess_mono_generated_fresh : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A ->
  forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ.
Proof.
  intros Θ P Ξ A H; induction H; intros α0 Hα0; simpl in *.
  - assert (α0 = α) by (clear - Hα0; fsetdec). subst. assumption.
  - auto.
  - clear - Hα0; fsetdec.
  - clear - Hα0; fsetdec.
  - rewrite dom_app in Hα0.
    destruct (union_1 Hα0) as [H1 | H1]; auto.
  - (* ∀ : the premise ran at (β~tvar) ++ Θ, so its block dodges β too *)
    specialize (IHa_guess_mono α0 Hα0). simpl in IHa_guess_mono. fsetdec.
Qed.

Corollary a_guess_mono_generated_fresh_binder : forall Θ P Ξ A β,
  a_guess_mono ((β ~ abind_tvar) ++ Θ) P Ξ A ->
  β `notin` dom Ξ.
Proof.
  intros Θ P Ξ A β H Hin.
  assert (Hfr : β `notin` ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
    by (eapply a_guess_mono_generated_fresh; eauto).
  simpl in Hfr. fsetdec.
Qed.

(** The generated block holds only bare flexibles, so it mentions exactly
    its own domain. *)
Lemma a_guess_mono_generated_ftvar : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  intros Θ P Ξ A H; induction H; simpl; try fsetdec.
  rewrite ftvar_in_aenv_app, dom_app. fsetdec.
Qed.

(** "Close after renaming": renaming [α] to a fresh [β] and closing at [β]
    is closing at [α] — [subst = open ∘ close] plus the close/open round
    trip, no induction needed. *)

(** [rename_aenv] basics. *)
Lemma rename_aenv_fresh_eq : forall Ξ γ β,
  β `notin` ftvar_in_aenv Ξ ->
  rename_aenv γ β Ξ = Ξ.
Proof.
  induction Ξ as [ | [x bd] Ξ' IH ]; intros γ β Hβ; simpl in *; auto.
  destruct (x == β); [ subst; clear - Hβ; fsetdec | ].
  rewrite IH by (clear - Hβ; fsetdec).
  f_equal. f_equal.
  destruct bd; simpl in *; try reflexivity; f_equal;
    first [ apply subst_ptyp_in_ptyp_fresh_eq; clear - Hβ; fsetdec
          | apply subst_pskl_in_pskl_fresh_eq; clear - Hβ; fsetdec ].
Qed.

Lemma rename_aenv_cons_tvar_eq : forall γ β Θ,
  rename_aenv γ β ((β ~ abind_tvar) ++ Θ)
  = (γ ~ abind_tvar) ++ rename_aenv γ β Θ.
Proof.
  intros. simpl. destruct (β == β); [ reflexivity | contradiction ].
Qed.

Lemma ftvar_in_aenv_rename_aenv : forall Θ γ β,
  ftvar_in_aenv (rename_aenv γ β Θ) [<=] add γ (ftvar_in_aenv Θ).
Proof.
  induction Θ as [ | [x bd] Θ' IH ]; intros γ β; simpl; [ fsetdec | ].
  assert (Hbd : ftvar_in_abind (rename_abind γ β bd)
                  [<=] add γ (ftvar_in_abind bd)).
  { destruct bd; simpl; try fsetdec;
      (etransitivity;
       [ first [ apply ftvar_in_ptyp_subst_ptyp_in_ptyp_upper
               | apply ftvar_in_pskl_subst_pskl_in_pskl_upper ]
       | simpl; fsetdec ]). }
  specialize (IH γ β).
  destruct (x == β); subst; fsetdec.
Qed.

(** guess^TY scopes its result by the source and the generated names.
    (Moved here from prop_soundness_consis.v: the kit derives target-side
    freshness from it instead of assuming output-side hypotheses.) *)
Lemma a_guess_mono_ftv : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A ->
  ftvar_in_ptyp A [<=] (ftvar_in_pskl P `union` dom Ξ).
Proof.
  intros Θ P Ξ A H; induction H; simpl; try solve [ fsetdec ].
  - (* arrow *)
    repeat rewrite dom_app.
    clear - IHa_guess_mono1 IHa_guess_mono2. fsetdec.
  - (* ∀ : the payload is CLOSED at β, so β drops out of the bound *)
    assert (Hcl : ftvar_in_ptyp (close_ptyp_wrt_ptyp β A)
                    [=] AtomSetImpl.remove β (ftvar_in_ptyp A))
      by (apply ftvar_in_ptyp_close_ptyp_wrt_ptyp).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
    simpl in Hup.
    clear - IHa_guess_mono Hcl Hup. fsetdec.
Qed.

(** One-step domain arithmetic for a rigid cons.  ⚙ PERF: stated as a lemma
    rather than re-derived by [simpl; fsetdec] at each use site.  The three
    uses below sit under a context full of large set hypotheses, and
    [fsetdec] preprocesses ALL of them — the three [assert]s alone cost 160 s
    of build time before this (Ltac-profiled, 2026-08-06). *)
Lemma ftvar_in_aenv_cons_tvar : forall β Θ,
  ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] add β (ftvar_in_aenv Θ).
Proof. intros; simpl; fsetdec. Qed.

(** The ∀ introduction in OPENED form — the shape call sites have.  The
    rule takes the payload unclosed and closes it; when the caller already
    holds the [A] it means to re-bind, [β ∉ ftv A] makes the closure a
    round trip. *)
Lemma a_guess_mono_all_of_one : forall Θ P Ξ A β,
  a_guess_mono ((β ~ abind_tvar) ++ Θ)
    (open_pskl_wrt_pskl P (pskl_var_f β)) Ξ
    (open_ptyp_wrt_ptyp A (ptyp_var_f β)) ->
  β `notin` ftvar_in_aenv Θ ->
  β `notin` ftvar_in_pskl P -> β `notin` ftvar_in_ptyp A ->
  a_guess_mono Θ (pskl_all_syn P) Ξ (ptyp_all A).
Proof.
  intros Θ P Ξ A β Hg Hβ HβP HβA.
  rewrite <- (close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp A β) at 1 by exact HβA.
  apply a_guess_mono__forall with (β := β); [ fsetdec | exact Hg ].
Qed.

(** ⭐ THE decl/algo BOUNDARY BRIDGE.  Not cofinite quantification creeping
    back into the algorithmic layer: the DECLARATIVE targets stay cofinite
    (correctly — relations, no outputs to leak into), so wherever an
    exists-fresh algorithmic premise feeds one, the single recorded
    instance must become a family.  This is the packaged binder-move that
    does it.  Junk-freeness makes it TRUE: without the witness entering the
    premise's context, a ghost below the ∀ could generate the witness
    itself, and this statement is false on that derivation.

    ⚙ The move is the TRANSPOSITION [b0 ⇄ α] ([a_guess_mono_swap],
    prop_swap.v), not a substitution-shaped rename: the recorded witness
    [b0] sits INSIDE the premise's context, so no "source dodges Θ" side
    condition can hold for it.  Both halves of the swap then collapse to
    the identity where they must — on [Θ] and on the generated block [Ξ],
    because both atoms dodge their free atoms — and on the payload the swap
    IS the rename ([swap_ptyp_as_subst], [α ∉ ftv A'] from
    [a_guess_mono_ftv]).  This retired the 150-line size-induction rename
    [a_guess_mono_rename_tvar] (DESIGN.md §4.3 ⚙). *)
Lemma a_guess_mono_open_at : forall Θ P Ξ A α,
  a_guess_mono Θ (pskl_all_syn P) Ξ (ptyp_all A) ->
  α `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union` dom Ξ ->
  a_guess_mono ((α ~ abind_tvar) ++ Θ)
    (open_pskl_wrt_pskl P (pskl_var_f α)) Ξ
    (open_ptyp_wrt_ptyp A (ptyp_var_f α)).
Proof.
  intros Θ P Ξ A α H Hα.
  inversion H as [ | | | | | Θ' P' Ξ' A' b0 Hfr Hg ]; subst.
  pose proof (a_guess_mono_generated_fresh_binder Hg) as Hb0Ξ.
  pose proof (a_guess_mono_generated_ftvar Hg) as HΞftv.
  assert (Hb0Ξf : b0 `notin` ftvar_in_aenv Ξ) by (clear - Hb0Ξ HΞftv; fsetdec).
  destruct (α == b0) as [-> | Hne].
  { (* α IS the recorded witness: the instance is literally the premise *)
    rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp. exact Hg. }
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b0)) as Hup.
  cbn in Hup.
  assert (HαA : α `notin` ftvar_in_ptyp A').
  { pose proof (a_guess_mono_ftv Hg) as HAftv.
    clear - HAftv Hup Hα Hne. fsetdec. }
  (* the payload IS the closure at b0, so opening at α is the b0 ⇄ α swap *)
  rewrite <- subst_ptyp_in_ptyp_spec.
  pose proof (a_guess_mono_swap b0 α _ _ _ _ Hg) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  rewrite (swap_aenv_fresh_id b0 α Θ) in Hr by (clear - Hfr Hα; fsetdec).
  rewrite (swap_aenv_fresh_id b0 α Ξ) in Hr by (clear - Hb0Ξf Hα HΞftv; fsetdec).
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b0 α P) in Hr by (clear - Hfr Hα; fsetdec).
  rewrite (swap_ptyp_as_subst b0 α A') in Hr by exact HαA.
  exact Hr.
Qed.

(* ===================================================================== *)
(*  guess^TY is consistent with its input skeleton                         *)
(*  (the declarative content of Assign-SolveM's definition)               *)
(* ===================================================================== *)

(* SIZE INDUCTION, not derivation induction: the TARGET [ad_pat_consis] is
   declarative, hence still COFINITE, while the source [a_guess_mono] is
   exists-fresh — the ∀ case turns ONE guess instance into a family with
   [a_guess_mono_open_at], whose output is no sub-derivation. *)
Lemma a_guess_mono_consis_size : forall n Θ P βs τ,
  size_pskl P <= n ->
  a_guess_mono Θ P βs τ ->
  forall Θ1,
  (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono βs -> a_binds_tvar α1 Θ1) ->
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (ptyp_to_bskl_syn τ).
Proof.
  induction n as [| n IHn]; intros Θ P βs τ Hsz H;
    [ destruct H; cbn in Hsz; lia | ].
  destruct H as [ Θ α Hα | Θ P Ξ A Hg | Θ α | Θ
                | Θ P Q Ξ1 Ξ2 A B Hg1 Hg2
                | Θ P Ξ A β Hfr Hg ];
    cbn in Hsz; intros Θ1 Hvars Hβs.
  - (* ghost ↦ fresh flexible variable *)
    replace (ptyp_to_bskl_syn (ptyp_var_f α))
      with (pskl_to_bskl_inh (pskl_var_f α)) by reflexivity.
    replace (pskl_to_uskl pskl_ghost) with uskl_ghost by reflexivity.
    apply ad_pat_consis__ghost; fsetdec.
  - (* ∀◇P : the universal ghost is dropped *)
    replace (pskl_to_uskl (pskl_univ_ghost P))
      with (uskl_univ_ghost (pskl_to_uskl P)) by reflexivity.
    apply ad_pat_consis__univ_ghost_drop.
    eapply IHn; [ lia | exact Hg | exact Hvars | exact Hβs ].
  - (* variable *)
    replace (pskl_to_uskl (pskl_var_f α))
      with (uskl_var_f α) by reflexivity.
    replace (ptyp_to_bskl_syn (ptyp_var_f α))
      with (bskl_var_f α) by reflexivity.
    apply ad_pat_consis__var; [ fsetdec | ].
    apply Hvars. simpl. fsetdec.
  - (* unit *)
    replace (pskl_to_uskl pskl_unit) with uskl_unit by reflexivity.
    replace (ptyp_to_bskl_syn ptyp_unit) with bskl_unit by reflexivity.
    apply ad_pat_consis__unit. fsetdec.
  - (* arrow *)
    replace (pskl_to_uskl (pskl_arrow P Q))
      with (uskl_arrow (pskl_to_uskl P) (pskl_to_uskl Q)) by reflexivity.
    replace (ptyp_to_bskl_syn (ptyp_arrow A B))
      with (bskl_arrow (ptyp_to_bskl_syn A) (ptyp_to_bskl_syn B))
      by reflexivity.
    apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ eapply IHn with (P := P) | eapply IHn with (P := Q) | fsetdec ].
    + lia.
    + exact Hg1.
    + intros α Hα. apply Hvars. simpl. fsetdec.
    + intros α1 Hb. apply Hβs. unfold binds in *. apply in_or_app; auto.
    + lia.
    + exact Hg2.
    + intros α Hα. apply Hvars. simpl. fsetdec.
    + intros α1 Hb. apply Hβs. unfold binds in *. apply in_or_app; auto.
  - (* forall: synthesised quantifier on both sides.  EXISTS-FRESH source,
       COFINITE target — the family comes from [a_guess_mono_open_at]. *)
    replace (pskl_to_uskl (pskl_all_syn P))
      with (uskl_all_syn (pskl_to_uskl P)) by reflexivity.
    replace (ptyp_to_bskl_syn (ptyp_all (close_ptyp_wrt_ptyp β A)))
      with (bskl_all_syn (ptyp_to_bskl_syn (close_ptyp_wrt_ptyp β A)))
      by reflexivity.
    apply ad_pat_consis__forall_syn
      with (L := dom Ξ `union` dom Θ1 `union` ftvar_in_aenv Θ
                   `union` ftvar_in_pskl P `union` singleton β).
    intros α Hα.
    rewrite <- pskl_to_uskl_open_var.
    rewrite <- ptyp_to_bskl_syn_open_var.
    eapply IHn with (P := open_pskl_wrt_pskl P (pskl_var_f α))
                    (Θ := (α ~ abind_tvar) ++ Θ);
      [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia | | | ].
    + apply a_guess_mono_open_at;
        [ apply a_guess_mono__forall with (β := β); [ exact Hfr | exact Hg ]
        | clear - Hα; fsetdec ].
    + intros β0 Hβ0.
      apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in Hβ0.
      simpl in Hβ0.
      destruct (union_1 Hβ0) as [HY' | HY'].
      * apply singleton_1 in HY'; subst.
        left. unfold binds; left; reflexivity.
      * apply a_binds_tvar_weaken_cons; auto.
    + intros α1 Hb. apply a_binds_tvar_weaken_cons; auto.
Qed.

Corollary a_guess_mono_consis : forall Θ P βs τ,
  a_guess_mono Θ P βs τ ->
  forall Θ1,
  (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono βs -> a_binds_tvar α1 Θ1) ->
  ad_pat_consis empty Θ1 (pskl_to_uskl P) (ptyp_to_bskl_syn τ).
Proof.
  intros. eapply a_guess_mono_consis_size; eauto.
Qed.

(* ===================================================================== *)
(*  Support for a_assign soundness: ⊴-level wrappers, wf bookkeeping      *)
(*  across the [Θ0 | Ξ] split, and embedding/substitution commutation.    *)
(* ===================================================================== *)

Lemma a_isub_target_weaken : forall Θ Θ' Ξ,
  Θ ⊴ Θ' ->
  a_suffix Ξ ->
  Θ ⊴ (Ξ ++ Θ').
Proof.
  intros * [[κ [Hid Hinc]] Hd] HΞ. split.
  - exists κ. eauto using a_inc_target_weaken.
  - intros α τ0 Hb. unfold binds; apply in_or_app; right. apply Hd; auto.
Qed.

Lemma a_isub_strengthen_decls_src : forall Ξ Θ Θ',
  a_decls Ξ ->
  (Ξ ++ Θ) ⊴ Θ' ->
  Θ ⊴ Θ'.
Proof.
  intros * Hdecl [[κ [Hid Hinc]] Hd]. split.
  - edestruct a_inc_strengthen_suffix_src as [κ' [Hid' Hinc']];
      [ eapply a_decls_suffix; eauto | exact Hinc | ].
    exists κ'. auto.
  - intros α τ0 Hb. apply Hd.
    unfold binds in *; apply in_or_app; auto.
Qed.

(** Inverting a well-formed univ_ghost: the body is GUARDED and well-formed at
    the EMPTY tag scope.
    ⚙ ONE name for this fact (2026-08-12): it used to exist three times —
    here in its strong form (consis/prop_consis_precise.v), a wf-only weak
    form (deco_algo/prop_decorate_sub.v) that COLLIDED with it, and a copy
    named [_x] (algo_decl/prop_precision.v) that existed only to escape the shadow.
    Weak uses read the second component. *)
Lemma a_wf_pskl_univ_ghost_inv : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_univ_ghost P) }}a ->
  guarded_pskl P /\ ({{ Θ ⨟ empty ⊢ₚₛ P }}a).
Proof.
  intros * H; inversion H; subst. split; [ assumption | ].
  eapply a_wf_pskl_tvar_mono; [ eassumption | ].
  intros α Hα. apply a_binds_tvar_aenv_minus in Hα. apply Hα.
Qed.

(** Removing a whole prefix preserves well-formedness of the tail. *)
Lemma a_wf_aenv_strip_prefix : forall Ξ Θ,
  {{ ⊢ (Ξ ++ Θ) }}a -> {{ ⊢ Θ }}a.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros Θ Hwf; simpl in *; auto.
  inversion Hwf; subst; eauto.
Qed.

(** Stripping a middle entry below a declaration-only prefix preserves
    context well-formedness (declarations carry no scoping content). *)
Lemma a_wf_aenv_strip_mid : forall Ξ (c : atom) (b : abind) Θ,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ (c ~ b) ++ Θ) }}a ->
  {{ ⊢ (Ξ ++ Θ) }}a.
Proof.
  intros Ξ; induction Ξ as [ | [α1 bγ] Ξ' IH ]; intros * Hdecl Hwf.
  - simpl in Hwf. inversion Hwf; subst; auto.
  - inversion Hdecl; subst.
    inversion Hwf; subst.
    apply a_wf_aenv__flex.
    + match goal with
      | Hf : _ `notin` dom _ |- _ `notin` dom _ =>
          repeat rewrite dom_app in *; simpl in *; clear - Hf; fsetdec
      end.
    + apply (IH c b Θ); auto.
Qed.

(** Removing a middle entry that cannot witness the lookup: either the
    atoms differ, or the entry's payload has none of the tvar-ish shapes. *)
Lemma binds_strip_mid : forall (b b' : abind) x c Ξ Θ,
  binds x b (Ξ ++ (c ~ b') ++ Θ) ->
  (x, b) <> (c, b') ->
  binds x b (Ξ ++ Θ).
Proof.
  intros * Hb Hne. unfold binds in *.
  apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb | Hb]; auto.
  destruct Hb as [Hb | Hb]; [ congruence | auto ].
Qed.

Lemma a_binds_tvar_strip_mid : forall α c (b : abind) Ξ Θ,
  a_binds_tvar α (Ξ ++ (c ~ b) ++ Θ) ->
  ((α, abind_tvar) <> (c, b)) ->
  ((α, abind_flex_mono) <> (c, b)) ->
  (forall τ0, (α, abind_flex_mono_def τ0) <> (c, b)) ->
  a_binds_tvar α (Ξ ++ Θ).
Proof.
  intros * [Hb | [Hb | [τ0 Hb]]] Hn1 Hn2 Hn3;
    [ left | right; left | right; right; exists τ0 ];
    eauto using binds_strip_mid.
Qed.

(** ** [wf] / [scope] bound the free variables by the domain.  ⚠️ These four
    and [a_wf_ptyp_ftv_tvarish] (prop_swap.v) are ONE family and this is their
    only home — do not re-prove an instance in a downstream file. *)

Lemma a_wf_ptyp_ftv_dom : forall Θ A,
  a_wf_ptyp Θ A -> ftvar_in_ptyp A [<=] dom Θ.
Proof.
  intros Θ A H α Hα.
  apply (a_wf_ptyp_ftv_tvarish H) in Hα.
  destruct Hα as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

Lemma a_binds_tvar_in_dom : forall β Θ, a_binds_tvar β Θ -> β `in` dom Θ.
Proof. intros β Θ [Hb | [Hb | [τ Hb]]]; apply binds_In in Hb; exact Hb. Qed.

Lemma a_scope_pskl_ftv_dom : forall Θ P,
  a_scope_pskl Θ P -> ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros Θ P [_ H] α Hα. exact (a_binds_tvar_in_dom (H α Hα)).
Qed.

(* ===================================================================== *)
(*  Binds-monotone weakening of the Θ-level judgments, and the last two    *)
(*  extraction helpers for assignvar                                       *)
(* ===================================================================== *)

Lemma a_wf_pskl_weaken : forall Θ Θ' Δ P,
  (forall x b, binds x b Θ -> binds x b Θ') ->
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  {{ Θ' ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros * Hmon Hwf. eapply a_wf_pskl_tvar_mono; [ exact Hwf | ].
  intros α [Hb | [Hb | [τ Hb]]]; unfold a_binds_tvar; eauto.
Qed.



(** Extracting a definition's payload facts from a wf context with a
    declaration-only prefix. *)
Lemma a_wf_aenv_mid_def_inv : forall Ξ β τ Θ,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ (β ~ abind_flex_mono_def τ) ++ Θ) }}a ->
  a_wf_ptyp Θ τ /\ mono_ptyp τ.
Proof.
  intros * Hdecl; revert β τ Θ; induction Hdecl; intros * Hwf;
    simpl_env in *.
  - inversion Hwf; subst. auto.
  - inversion Hwf; subst.
    match goal with
    | Hw : {{ ⊢ _ }}a |- _ => eapply IHHdecl; exact Hw
    end.
Qed.

(* ===================================================================== *)
(*  Skeleton wf: context strengthening and forward definition-folding     *)
(*  (the two [a_assign] motive obligations: Skip drops a flex binding,    *)
(*  Assign folds a definition into the assigned skeleton).                *)
(* ===================================================================== *)

(** Skeleton wf survives removing ANY entry the skeleton avoids.
    Generalises [a_wf_pskl_strip_tvar] (which only drops [abind_tvar]);
    [a_assign__skip] drops a *flex* binding. *)
Lemma a_wf_pskl_strip_mid : forall Θ1 c b Θ2 Δ P,
  {{ (Θ1 ++ (c ~ b) ++ Θ2) ⨟ Δ ⊢ₚₛ P }}a ->
  c `notin` ftvar_in_pskl P ->
  {{ (Θ1 ++ Θ2) ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  intros * H Hfr. eapply a_wf_pskl_tvar_mono_ftv; [ exact H | ].
  intros α Hα Htv.
  assert (Hne : α <> c) by (clear - Hfr Hα; fsetdec).
  eapply a_binds_tvar_strip_mid; eauto;
    try (intro Hc; inversion Hc; subst; congruence);
    try (intros τ0 Hc; inversion Hc; subst; congruence).
Qed.

(** A well-formed monotype's skeleton is a well-formed skeleton, in any [Δ]. *)
Lemma a_wf_pskl_mono_ptyp : forall Θ Δ τ,
  mono_ptyp τ ->
  a_wf_ptyp Θ τ ->
  {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl τ) }}a.
Proof.
  intros Θ Δ τ Hm; revert Δ; induction Hm; intros Δ Hwf; simpl;
    inversion Hwf; subst.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var; auto.
  - apply a_wf_pskl__arrow; auto.
Qed.

(** A definition is a monotype (it is stored that way). *)
Lemma a_wf_aenv_binds_def_mono : forall Θ α1 τ,
  {{ ⊢ Θ }}a ->
  binds α1 (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ.
Proof.
  intros Θ α1 τ Hwf; induction Hwf; intros Hb;
    try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
    try discriminate; try (inversion Heqb; subst; assumption); auto.
Qed.

(** A defined flexible variable's definition is well-formed in the whole
    well-formed context.  (Payload companion of [a_wf_aenv_binds_def_mono].) *)
Lemma a_wf_aenv_binds_def_wf : forall Θ β τ,
  {{ ⊢ Θ }}a ->
  binds β (abind_flex_mono_def τ) Θ ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ β τ Hwf; induction Hwf; intros Hb; simpl_env in *;
    try solve [ inversion Hb ];
    (* every cons case: either the head binding IS the one we look for
       (only possible for [flex_def]) or we recurse and weaken. *)
    (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqx Heqb] | Hb'];
     [ try discriminate Heqb
     | ]);
    try (eapply a_wf_ptyp_weaken;
         [ intros y b0 Hb0; unfold binds; simpl; right; exact Hb0
         | apply IHHwf; exact Hb' ]).
  (* [flex_def], head hit: [τ0 = τ]. *)
  inversion Heqb; subst.
  eapply a_wf_ptyp_weaken;
    [ intros y b0 Hb0; unfold binds; simpl; right; exact Hb0 | auto ].
Qed.

(** A name outside a well-formed context's domain is fresh for every
    flexible definition in it. *)
Lemma a_wf_aenv_def_ftv_notin : forall Θ β,
  {{ ⊢ Θ }}a -> β `notin` dom Θ ->
  forall α τ, binds α (abind_flex_mono_def τ) Θ -> β `notin` ftvar_in_ptyp τ.
Proof.
  intros Θ β Hwf Hβ α τ Hb.
  assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
    by (eapply a_wf_ptyp_ftv_dom, a_wf_aenv_binds_def_wf; eassumption).
  clear - Hβ Hsc; fsetdec.
Qed.

(** A flexible definition's payload, read back as a skeleton through the
    syn painting, is well-formed (it is a well-formed monotype). *)
Lemma a_wf_pskl_flex_def_payload : forall Θ Δ α τ,
  {{ ⊢ Θ }}a ->
  binds α (abind_flex_mono_def τ) Θ ->
  {{ Θ ⨟ Δ ⊢ₚₛ (bskl_to_pskl (ptyp_to_bskl_syn τ)) }}a.
Proof.
  intros * Hwf Hb. rewrite bskl_to_pskl_ptyp_to_bskl_syn.
  apply a_wf_pskl_mono_ptyp;
    [ eapply a_wf_aenv_binds_def_mono | eapply a_wf_aenv_binds_def_wf ];
    eassumption.
Qed.

Lemma a_wf_pskl_arrow_inv : forall Θ Δ P1 P2,
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_arrow P1 P2) }}a -> {{ Θ ⨟ Δ ⊢ₚₛ P1 }}a /\ {{ Θ ⨟ Δ ⊢ₚₛ P2 }}a.
Proof. intros * H; inversion H; auto. Qed.


(** A monotype whose variables are all [a_binds_tvar] in Θ paints to a
    well-formed skeleton, in any [Δ]. *)
Lemma a_wf_pskl_mono_ptyp_ftv : forall Θ Δ τ,
  mono_ptyp τ ->
  (forall α, α `in` ftvar_in_ptyp τ -> a_binds_tvar α Θ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (ptyp_to_pskl τ) }}a.
Proof.
  intros Θ Δ τ Hm; induction Hm; intros Hv; simpl in *.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var. apply Hv. clear; fsetdec.
  - apply a_wf_pskl__arrow;
      [ apply IHHm1 | apply IHHm2 ]; intros α Hα; apply Hv; clear - Hα; fsetdec.
Qed.

(** A well-formed monotype's variables are [a_binds_tvar]. *)
Lemma a_wf_ptyp_mono_ftv : forall Θ τ,
  mono_ptyp τ -> a_wf_ptyp Θ τ ->
  forall α, α `in` ftvar_in_ptyp τ -> a_binds_tvar α Θ.
Proof.
  intros Θ τ Hm; induction Hm; intros Hwf α0 Hα0; inversion Hwf; subst;
    simpl in Hα0.
  - fsetdec.
  - assert (α0 = α) by (clear - Hα0; fsetdec). subst. assumption.
  - apply union_iff in Hα0. destruct Hα0; auto.
Qed.

(** The general form of [a_wf_pskl_mono_subst]: substituting ANY variable by
    a monotype whose variables are bound in Θ and OUTSIDE [Δ].  The [∖Δ]
    side condition is what the [∀◇] rule needs: its premise is read at
    [Θ∖Δ], where a variable of [Δ] is no longer bound. *)
Lemma a_wf_pskl_mono_subst_gen : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall β τ, mono_ptyp τ ->
  (forall α, α `in` ftvar_in_ptyp τ -> a_binds_tvar α Θ /\ α `notin` Δ) ->
  {{ Θ ⨟ Δ ⊢ₚₛ (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) }}a.
Proof.
  intros Θ Δ P H; induction H; intros β τ Hm Hτ; simpl.
  - apply a_wf_pskl__unit.
  - (* NB: the scrutinee of [subst_pskl_in_pskl] lives at [ptypvar], so the
       [eq_dec] instance must be given at that type for [destruct] to
       abstract the [if] in the goal. *)
    destruct (@eq_dec ptypvar EqDec_eq_of_X α β) as [Heq | Hne].
    + subst. apply a_wf_pskl_mono_ptyp_ftv; [ exact Hm | ].
      intros α Hα. apply Hτ; exact Hα.
    + apply a_wf_pskl__var; auto.
  - apply a_wf_pskl__arrow; auto.
  - apply a_wf_pskl__all with (L := L `union` singleton β `union` ftvar_in_ptyp τ).
    intros α Hα.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα; fsetdec | apply mono_ptyp_to_pskl_lc; auto ].
    apply H0; [ clear - Hα; fsetdec | exact Hm | ].
    intros α' Hα'. destruct (Hτ α' Hα') as [Hb Hn]. split.
    + apply a_binds_tvar_cons_tvar. right; exact Hb.
    + assert (α' <> α) by (intro; subst; clear - Hα Hα'; fsetdec).
      clear - Hn H1. fsetdec.
  - apply a_wf_pskl__ghost.
  - apply a_wf_pskl__univ_ghost;
      [ apply guarded_pskl_subst_mono; auto | ].
    apply IHa_wf_pskl; [ exact Hm | ].
    intros α Hα. destruct (Hτ α Hα) as [Hb Hn]. split.
    + apply a_binds_tvar_aenv_minus. auto.
    + clear; fsetdec.
Qed.

(** FORWARD monotype substitution: folding a defined flexible variable's
    definition INTO a well-formed skeleton keeps it well-formed.
    Stated at the EMPTY tag scope: at a nonempty [Δ] it is false, since a
    [∀◇] body is read at [Θ∖Δ] and the definition may mention [Δ]. *)
Lemma a_wf_pskl_mono_subst : forall Θ β τ P,
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  {{ ⊢ Θ }}a ->
  binds β (abind_flex_mono_def τ) Θ ->
  mono_ptyp τ ->
  {{ Θ ⨟ empty ⊢ₚₛ (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) }}a.
Proof.
  intros Θ β τ P H Hwfenv Hb Hm.
  apply a_wf_pskl_mono_subst_gen; [ exact H | exact Hm | ].
  intros α Hα. split; [ | clear; fsetdec ].
  eapply a_wf_ptyp_mono_ftv; [ exact Hm | | exact Hα ].
  eapply a_wf_aenv_binds_def_wf; eauto.
Qed.

Lemma a_wf_aenv_uniq : forall Θ,
  {{ ⊢ Θ }}a -> uniq Θ.
Proof.
  intros Θ H; induction H; solve_uniq.
Qed.

(** A TERM entry is never [a_binds_tvar], so a skeleton well-formed in the
    context cannot mention it — the freshness [a_wf_pskl_strip_mid] needs
    at every Flex-SkipTmVar / Assign-SkipTmVar row, which the rules do not
    carry. *)
Lemma a_wf_pskl_tm_entry_fresh : forall Ξ x bd Θ0 Δ P,
  {{ ⊢ (Ξ ++ (x ~ bd) ++ Θ0) }}a ->
  abind_is_tm bd ->
  {{ (Ξ ++ (x ~ bd) ++ Θ0) ⨟ Δ ⊢ₚₛ P }}a ->
  x `notin` ftvar_in_pskl P.
Proof.
  intros * Hwf Htm HwfP Hin.
  assert (Huq : uniq (Ξ ++ (x ~ bd) ++ Θ0)) by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Hbx : binds x bd (Ξ ++ (x ~ bd) ++ Θ0))
    by (apply binds_app_3; apply binds_app_2; unfold binds; simpl; left; reflexivity).
  destruct (a_wf_pskl_ftv_binds HwfP Hin) as [Hb | [Hb | [τ0 Hb]]];
    pose proof (binds_unique _ _ _ _ _ Hbx Hb Huq); subst; exact Htm.
Qed.


(* ===================================================================== *)
(*  a_wf_ptyp / a_guess_mono / a_decls plumbing                           *)
(* ===================================================================== *)

(** The converse of [a_wf_ptyp_to_wf_pskl] on a painting.  Both judgements
    push a [∀] binder into Θ ([a_wf_pskl] also records it in [Δ], which the
    type judgement does not need). *)
Lemma a_wf_ptyp_of_wf_pskl : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a ->
  forall A, P = ptyp_to_pskl A -> a_wf_ptyp Θ A.
Proof.
  intros Θ Δ P H; induction H; intros A0 Heq;
    destruct A0; simpl in Heq; try discriminate; inversion Heq; subst.
  - (* unit *) apply a_wf_ptyp__unit.
  - (* var *) apply a_wf_ptyp__var; assumption.
  - (* arrow *) apply a_wf_ptyp__arrow; eauto.
  - (* all *)
    apply a_wf_ptyp__all with (L := L). intros α Hα.
    eapply (H0 α Hα). rewrite ptyp_to_pskl_open; reflexivity.
Qed.

Corollary a_wf_ptyp_of_wf_pskl_empty : forall Θ A,
  {{ Θ ⨟ empty ⊢ₚₛ (ptyp_to_pskl A) }}a -> a_wf_ptyp Θ A.
Proof. intros Θ A H. eapply a_wf_ptyp_of_wf_pskl; [ exact H | reflexivity ]. Qed.

(** The [a_guess_mono_refine] (§9) companion: [guess^TY]'s output type is
    well formed wherever its input skeleton's variables and its own
    generated block are.  Same SIZE induction, same reason. *)
Lemma a_guess_mono_wf_size : forall n Θ P Ξ A,
  size_pskl P <= n ->
  a_guess_mono Θ P Ξ A ->
  forall Θ1,
  (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ1) ->
  a_wf_ptyp Θ1 A.
Proof.
  induction n as [| n IHn]; intros Θ P Ξ A Hsz H;
    [ destruct H; cbn in Hsz; lia | ].
  destruct H as [ Θ α Hα | Θ P Ξ A Hg | Θ α | Θ
                | Θ P Q Ξ1 Ξ2 A B Hg1 Hg2
                | Θ P Ξ A β Hfr Hg ];
    cbn in Hsz; intros Θ1 Hvars HΞ.
  - (* ghost ↦ fresh flexible *)
    apply a_wf_ptyp__var. apply HΞ. unfold binds; left; reflexivity.
  - (* ∀◇.P *)
    eapply IHn with (P := P); [ lia | exact Hg | exact Hvars | exact HΞ ].
  - (* variable *) apply a_wf_ptyp__var. apply Hvars. simpl. fsetdec.
  - (* unit *) apply a_wf_ptyp__unit.
  - (* arrow *)
    apply a_wf_ptyp__arrow;
      [ eapply IHn with (P := P) | eapply IHn with (P := Q) ];
      solve [ lia | eassumption
            | intros α Hα; apply Hvars; simpl; clear - Hα; fsetdec
            | intros α1 Hb; apply HΞ; unfold binds in *;
              apply in_or_app; auto ].
  - (* ∀ : exists-fresh source, cofinite target *)
    apply a_wf_ptyp__all
      with (L := dom Ξ `union` dom Θ1 `union` ftvar_in_aenv Θ
                   `union` ftvar_in_pskl P `union` ftvar_in_ptyp A
                   `union` singleton β).
    intros α Hα.
    eapply IHn with (P := open_pskl_wrt_pskl P (pskl_var_f α))
                    (Θ := (α ~ abind_tvar) ++ Θ);
      [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia | | | ].
    + apply a_guess_mono_open_at;
        [ apply a_guess_mono__forall with (β := β); [ exact Hfr | exact Hg ]
        | clear - Hα; fsetdec ].
    + intros β0 Hβ0.
      apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in Hβ0.
      simpl in Hβ0.
      destruct (union_1 Hβ0) as [HY' | HY'].
      * apply singleton_1 in HY'; subst.
        unfold a_binds_tvar; left; unfold binds; simpl; left; reflexivity.
      * apply a_binds_tvar_weaken_cons. apply Hvars; exact HY'.
    + intros α1 Hb. apply a_binds_tvar_weaken_cons. apply HΞ; exact Hb.
Qed.

Corollary a_guess_mono_wf : forall Θ P Ξ A Θ1,
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` ftvar_in_pskl P -> a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ1) ->
  a_wf_ptyp Θ1 A.
Proof. intros. eapply a_guess_mono_wf_size; eauto. Qed.

(** [uniq] is what [AT-Abs]'s own premise supplies (algo/def_rules.v): the
    block is declaration-only, so nothing else is needed to put it in
    front of a well-formed context. *)
Lemma a_wf_aenv_decls_app : forall Ξ Θ,
  a_decls Ξ -> uniq (Ξ ++ Θ) -> {{ ⊢ Θ }}a -> {{ ⊢ (Ξ ++ Θ) }}a.
Proof.
  intros Ξ Θ Hd; induction Hd as [ | α1 Ξ' Hd IH ];
    intros Huq Hwf; simpl_env in *; [ exact Hwf | ].
  apply a_wf_aenv__flex;
    [ clear - Huq; destruct_uniq; simpl_env in *;
      unfold disjoint in *; fsetdec
    | apply IH; [ solve_uniq | exact Hwf ] ].
Qed.

Lemma a_wf_ptyp_arrow_inv : forall Θ A1 A2,
  a_wf_ptyp Θ (ptyp_arrow A1 A2) -> a_wf_ptyp Θ A1 /\ a_wf_ptyp Θ A2.
Proof. intros * H; inversion H; subst; split; assumption. Qed.

(** A monotype all of whose free variables are tvar-ish is well-formed. *)
Lemma mono_ptyp_wf : forall Θ τ,
  mono_ptyp τ ->
  (forall α, α `in` ftvar_in_ptyp τ -> a_binds_tvar α Θ) ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ τ H; induction H; intros Hvis; simpl in *.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. apply Hvis. fsetdec.
  - apply a_wf_ptyp__arrow;
      [ apply IHmono_ptyp1 | apply IHmono_ptyp2 ];
      intros α Hα; apply Hvis; fsetdec.
Qed.

(** ⚙ A well-formed context MENTIONS only its own domain: every payload is
    scoped in the tail.  This is what turns the uniform substitution back
    into the identity on the surviving context. *)
Lemma a_wf_aenv_ftv_dom : forall Θ,
  {{ ⊢ Θ }}a -> ftvar_in_aenv Θ [<=] dom Θ.
Proof.
  intros Θ H; induction H; simpl; try (clear - IHa_wf_aenv; fsetdec).
  - fsetdec.
  - assert (ftvar_in_ptyp τ [<=] dom Θ)
      by (intros β Hβ; apply a_binds_tvar_in_dom;
          eapply a_wf_ptyp_ftv_tvarish; eassumption).
    clear - IHa_wf_aenv H3. fsetdec.
  - assert (ftvar_in_pskl P [<=] dom Θ)
      by (apply a_scope_pskl_ftv_dom; eauto).
    clear - IHa_wf_aenv H2. fsetdec.
  - assert (ftvar_in_ptyp A [<=] dom Θ)
      by (intros β Hβ; apply a_binds_tvar_in_dom;
          eapply a_wf_ptyp_ftv_tvarish; eassumption).
    clear - IHa_wf_aenv H2. fsetdec.
Qed.

(** ⭐ A RIGID entry is INVISIBLE to [a_flex_tvar] — at EVERY atom, its own
    included, because [binds] is MEMBERSHIP: a rigid binding neither creates a
    flexible one nor hides one further down.  ⚙ The FlexR-priority guard's
    transports all rest on this (2026-08-18). *)
Lemma a_flex_tvar_cons_tvar_any : forall b (Θ : aenv) x,
  a_flex_tvar ((b ~ abind_tvar) ++ Θ) x <-> a_flex_tvar Θ x.
Proof.
  intros b Θ x; unfold a_flex_tvar; split.
  - intros [Hb | [τ Hb]]; analyze_binds Hb;
      solve [ left; assumption | right; exists τ; assumption ].
  - intros [Hb | [τ Hb]]; [ left | right; exists τ ];
      unfold binds; simpl; right; assumption.
Qed.

(** …and an atom outside a context's domain is not flexible in it. *)
Lemma a_flex_tvar_in_dom : forall (Θ : aenv) x,
  a_flex_tvar Θ x -> x `in` dom Θ.
Proof. intros Θ x [Hb | [τ Hb]]; eapply binds_In; eassumption. Qed.

(** Flexibility survives an arbitrary context PREFIX ([binds] is plain
    membership, so no freshness side condition is needed). *)
Lemma a_flex_tvar_weaken_app : forall Ξ Θ α,
  a_flex_tvar Θ α -> a_flex_tvar (Ξ ++ Θ) α.
Proof.
  intros * [Hb | [τ Hb]]; [ left | right; exists τ ];
    unfold binds in *; apply in_or_app; right; assumption.
Qed.

(** ⭐ NON-FLEXIBILITY FROM A SCOPE BOUND, as LEMMAS rather than a tactic
    search: an atom outside a context's [ftvar_in_aenv] bound cannot be
    flexible in it.  ⚠️⚠️ The tactic version of this HANGS — [match goal] has to
    guess which scope hypothesis to use, and every wrong guess pays an
    exponential [fsetdec] on a context with dozens of set variables. *)
Lemma nonflex_of_scope : forall (Θ : aenv) S b,
  ftvar_in_aenv Θ [<=] S -> b `notin` S -> ~ a_flex_tvar Θ b.
Proof.
  intros Θ S b Hs Hb Hf. apply a_flex_tvar_in_dom in Hf.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hd.
  clear - Hs Hb Hd Hf. fsetdec.
Qed.

Lemma nonflex_of_scope_cons : forall (Θ : aenv) S b c,
  ftvar_in_aenv Θ [<=] S -> b `notin` S ->
  ~ a_flex_tvar ((c ~ abind_tvar) ++ Θ) b.
Proof.
  intros Θ S b c Hs Hb Hf.
  rewrite a_flex_tvar_cons_tvar_any in Hf.
  exact (nonflex_of_scope Hs Hb Hf).
Qed.

(** ⭐⭐ THE FLEXIBILITY-PRESERVING SHRINK (2026-08-18).  Under the
    FlexR-PRIORITY GUARD a consumer can no longer throw a collection's context
    away wholesale — the eq layer reads it for HATTEDNESS.  What it CAN do is
    keep exactly the flexibles the COUNTERPART mentions, with their payloads
    dropped: that is enough for the guard (whose condition is scoped to
    [ftv P']) and it lands [ftvar_in_aenv] inside [S], which is what the
    freshness side conditions wanted the shrink for in the first place. *)
Fixpoint flex_restrict (S : atoms) (Θ : aenv) : aenv :=
  match Θ with
  | nil => nil
  | (x, abind_flex_mono) :: Θ' =>
      if AtomSetImpl.mem x S
      then (x, abind_flex_mono) :: flex_restrict S Θ'
      else flex_restrict S Θ'
  | (x, abind_flex_mono_def _) :: Θ' =>
      if AtomSetImpl.mem x S
      then (x, abind_flex_mono) :: flex_restrict S Θ'
      else flex_restrict S Θ'
  | _ :: Θ' => flex_restrict S Θ'
  end.

Lemma flex_restrict_ftvar : forall S Θ,
  ftvar_in_aenv (flex_restrict S Θ) [<=] S.
Proof.
  intros S Θ; induction Θ as [ | [x b] Θ' IH ]; simpl; [ fsetdec | ].
  destruct b;
    try (destruct (AtomSetImpl.mem x S) eqn:Hm; simpl;
         [ assert (x `in` S) by (apply AtomSetImpl.mem_2; exact Hm);
           clear - IH H; fsetdec
         | exact IH ]);
    exact IH.
Qed.

Lemma flex_restrict_dom : forall S Θ,
  ftvar_in_aenv (flex_restrict S Θ) [<=] ftvar_in_aenv Θ.
Proof.
  intros S Θ; induction Θ as [ | [x b] Θ' IH ]; simpl; [ fsetdec | ].
  destruct b;
    try (destruct (AtomSetImpl.mem x S); simpl; clear - IH; fsetdec);
    clear - IH; fsetdec.
Qed.

(** Everything the restriction keeps is an UNDEFINED flexible drawn from [S]
    and flexible in the source. *)
Lemma flex_restrict_binds_inv : forall S Θ x bd,
  binds x bd (flex_restrict S Θ) ->
  x `in` S /\ a_flex_tvar Θ x.
Proof.
  intros S Θ; induction Θ as [ | [y b] Θ' IH ]; intros x bd Hb; simpl in Hb.
  - inversion Hb.
  - assert (Hup : x `in` S /\ a_flex_tvar Θ' x ->
                  x `in` S /\ a_flex_tvar ((y, b) :: Θ') x).
    { intros [HS [H1 | [τ H1]]]; split;
        [ exact HS | left | exact HS | right; exists τ ];
        unfold binds; simpl; right; exact H1. }
    destruct b;
      try (apply Hup; exact (IH x bd Hb));
      (destruct (AtomSetImpl.mem y S) eqn:Hm;
       [ destruct Hb as [E | Hb];
         [ inversion E; subst; split;
           [ apply AtomSetImpl.mem_2; exact Hm
           | solve [ left; unfold binds; simpl; left; reflexivity
                   | right; eexists; unfold binds; simpl; left; reflexivity ] ]
         | apply Hup; exact (IH x bd Hb) ]
       | apply Hup; exact (IH x bd Hb) ]).
Qed.

(** …and it keeps EVERY flexible of [S]. *)
Lemma flex_restrict_binds : forall S Θ x,
  x `in` S -> a_flex_tvar Θ x -> binds x abind_flex_mono (flex_restrict S Θ).
Proof.
  intros S Θ; induction Θ as [ | [y b] Θ' IH ]; intros x HS Hf; simpl.
  - destruct Hf as [Hb | [τ Hb]]; inversion Hb.
  - assert (Hmem : AtomSetImpl.mem x S = true)
      by (apply AtomSetImpl.mem_1; exact HS).
    destruct b;
      try (apply IH; [ exact HS | ];
           destruct Hf as [Hb | [τ Hb]]; analyze_binds Hb;
           solve [ left; assumption | right; exists τ; assumption ]);
      (destruct (AtomSetImpl.mem y S) eqn:Hm;
       [ destruct (x == y) as [-> | Hne];
         [ unfold binds; simpl; left; reflexivity
         | unfold binds; simpl; right; apply IH; [ exact HS | ];
           destruct Hf as [Hb | [τ Hb]]; analyze_binds Hb;
           solve [ left; assumption | right; exists τ; assumption ] ]
       | destruct (x == y) as [-> | Hne];
         [ exfalso; rewrite Hmem in Hm; discriminate
         | apply IH; [ exact HS | ];
           destruct Hf as [Hb | [τ Hb]]; analyze_binds Hb;
           solve [ left; assumption | right; exists τ; assumption ] ] ]).
Qed.

Lemma flex_restrict_iff : forall S Θ β,
  β `in` S -> (a_flex_tvar Θ β <-> a_flex_tvar (flex_restrict S Θ) β).
Proof.
  intros S Θ β HβS; split.
  - intros Hf. left. apply flex_restrict_binds; assumption.
  - intros [Hb | [τ Hb]];
      exact (proj2 (flex_restrict_binds_inv _ _ _ _ Hb)).
Qed.

(** …and a PREFIX the atom is not bound in is likewise invisible — the shape
    the FlexR-priority guard's context moves need (2026-08-18). *)
Lemma a_flex_tvar_app_notin : forall (Ξ Θ : aenv) α,
  α `notin` dom Ξ -> (a_flex_tvar (Ξ ++ Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros Ξ Θ α Hα; split; [ | apply a_flex_tvar_weaken_app ].
  intros [Hb | [τ Hb]]; unfold binds in Hb; apply in_app_or in Hb;
    destruct Hb as [Hin | Hin];
    solve [ exfalso; apply Hα; eapply binds_In; exact Hin
          | left; exact Hin
          | right; exists τ; exact Hin ].
Qed.

Lemma a_flex_tvar_weaken_mid : forall Ξl Ξm Θ0 α,
  a_flex_tvar (Ξl ++ Θ0) α -> a_flex_tvar (Ξl ++ Ξm ++ Θ0) α.
Proof.
  intros Ξl Ξm Θ0 α [Hb | [τ Hb]];
    [ left | right; exists τ ]; apply binds_weaken; exact Hb.
Qed.

(** …and hence PEELING one head entry the atom is not the subject of.
    ⚙ MOVED here from ext_algo/subtyping/prop_solve_rel.v §10 (2026-08-20): the consis
    rung's [a_assign_unify_consis_flex_rev] lives in [algo/] and needs it. *)
Lemma a_flex_tvar_cons_other : forall (c : atom) (bd : abind) (Θ : aenv) x,
  x <> c -> (a_flex_tvar ((c ~ bd) ++ Θ) x <-> a_flex_tvar Θ x).
Proof.
  intros c bd Θ x Hne. apply a_flex_tvar_app_notin.
  simpl_env. clear - Hne. fsetdec.
Qed.

(** …and anywhere under a PENDING SUFFIX.  ⚙ MOVED here from
    ext_algo/subtyping/prop_solve_rel.v §10 with its cons-instance above (2026-08-20):
    the `a_sub` rung's [a_sub_sub_flex_flex_rev] lives in [algo/] and its
    Flex-Solve row peels THREE mid entries at once. *)
Lemma a_flex_tvar_mid_other : forall (Ξ : aenv) (c : atom) (bd : abind)
    (Θ : aenv) x,
  x <> c ->
  (a_flex_tvar (Ξ ++ (c ~ bd) ++ Θ) x <-> a_flex_tvar (Ξ ++ Θ) x).
Proof.
  intros Ξ c bd Θ x Hne; split; [ | apply a_flex_tvar_weaken_mid ].
  intros [Hb | [τ Hb]]; [ left | right; exists τ ];
    (unfold binds in *; apply in_app_or in Hb; destruct Hb as [H | H];
     [ apply in_or_app; left; exact H
     | destruct H as [E | H];
       [ exfalso; inversion E; subst; apply Hne; reflexivity
       | apply in_or_app; right; exact H ] ]).
Qed.

(* ===================================================================== *)
(*  ⭐ SS-Vacuous, GENERALIZED PAST THE SOLVE-DISPATCH GUARD (2026-08-18)  *)
(*                                                                        *)
(*  Under guard 5 [SS-Vacuous] no longer fires at a [∀] or [∀◇] subject —  *)
(*  the implementation peels there first (type.ml:494 matches              *)
(*  [SolS-ForallL] and [SolS-UnivGhostL] before [SolS-Vacuous]).  ⭐ But    *)
(*  the PEELED route gives the SAME answer: an empty block and the         *)
(*  subject back, because [∀]'s row re-CLOSES over the opener it drew and  *)
(*  [∀◇]'s re-wraps.  So every old [apply a_solve_sub__vacuous] site can   *)
(*  read this lemma instead, with no change to what it proves.            *)
(*                                                                        *)
(*  ⚙ SIZE induction: the [∀] row opens, which preserves [size_pskl], so   *)
(*  a structural induction on the skeleton would not go through.          *)
(* ===================================================================== *)

Lemma a_solve_sub_vacuous_gen_n : forall n Θ m P,
  size_pskl P <= n ->
  {{ Θ ⊢ₛ P ≼[ m ] pskl_ghost ⤳ nil ⨾ P }}a.
Proof.
  induction n as [ | n IH ]; intros Θ m P Hsz;
    [ exfalso; destruct P; simpl in Hsz; lia | ].
  destruct P as [ | k | α | P1 P2 | P0 | | P0 ];
    try solve [ apply a_solve_sub__vacuous;
                solve [ apply peel_l_off_unit | apply peel_l_off_var_b
                      | apply peel_l_off_var | apply peel_l_off_arrow
                      | apply peel_l_off_ghost ] ].
  - (* ∀ — peel, then RE-CLOSE over the same opener *)
    simpl in Hsz.
    destruct (atom_fresh (ftvar_in_aenv Θ ∪ ftvar_in_pskl P0)) as [β Hβ].
    replace (pskl_all_syn P0)
      with (pskl_all_syn
              (close_pskl_wrt_pskl β (open_pskl_wrt_pskl P0 (pskl_var_f β))))
      at 2
      by (f_equal; apply close_pskl_wrt_pskl_open_pskl_wrt_pskl;
          clear - Hβ; fsetdec).
    apply a_solve_sub__forall_l with (β := β).
    + simpl. clear - Hβ. fsetdec.
    + apply IH. rewrite size_pskl_open_pskl_wrt_pskl_var. lia.
  - (* ∀◇ — strip, then RE-WRAP *)
    simpl in Hsz.
    apply a_solve_sub__univ_ghost_l. apply IH. lia.
Qed.

Lemma a_solve_sub_vacuous_gen : forall Θ m P,
  {{ Θ ⊢ₛ P ≼[ m ] pskl_ghost ⤳ nil ⨾ P }}a.
Proof. intros. exact (a_solve_sub_vacuous_gen_n Θ m P (le_n _)). Qed.

(* ===================================================================== *)
(*  §  ⭐ TWO [a_flex_tvar] SHAPES THE a_sub LIFT NEEDS (2026-08-21)       *)
(*                                                                        *)
(*  Both are about what a WALK row does to the context's flexibility       *)
(*  picture; they sit here beside [a_flex_tvar_{cons,mid}_other] for the   *)
(*  same reason the consis rung's flex-reflect does.                       *)
(* ===================================================================== *)


(** ⭐ [Flex-Solve]'s CONTEXT SURGERY, as one flexibility equivalence: the
    head goes from undefined to defined and TWO fresh flexibles appear under
    it, and neither move changes any OTHER atom's flex status.  ⚙ The consis
    rung's [a_flex_tvar_solve_m] does NOT serve here — that row moves the
    definition to the FRONT, this one leaves it under [Ξ]. *)
Lemma a_flex_tvar_solve_shape : forall (Ξ : aenv) (c : atom) (t : ptyp)
    (β α : atom) (Θ : aenv) x,
  x <> α -> x <> β ->
  (a_flex_tvar (Ξ ++ (c ~ abind_flex_mono_def t) ++ (β ~ abind_flex_mono)
                  ++ (α ~ abind_flex_mono) ++ Θ) x
   <-> a_flex_tvar (Ξ ++ (c ~ abind_flex_mono) ++ Θ) x).
Proof.
  intros Ξ c t β α Θ x Hnα Hnβ.
  destruct (x == c) as [-> | Hnc].
  - split; intros _;
      [ left | right; exists t ];
      unfold binds; apply in_or_app; right; left; reflexivity.
  - rewrite (a_flex_tvar_mid_other Ξ (abind_flex_mono_def t) _ Hnc).
    rewrite (a_flex_tvar_mid_other Ξ abind_flex_mono _ Hnβ).
    rewrite (a_flex_tvar_mid_other Ξ abind_flex_mono Θ Hnα).
    rewrite (a_flex_tvar_mid_other Ξ abind_flex_mono Θ Hnc).
    reflexivity.
Qed.


(** ⚙ A RIGID or TERM head is not the flexible witness, so the witness is in
    the tail — which the Barendregt premises of the walk forbid. *)
Lemma a_flex_tvar_head_tail : forall (c : atom) (bd : abind) Θ,
  a_flex_tvar ((c ~ bd) ++ Θ) c ->
  bd <> abind_flex_mono ->
  (forall τ, bd <> abind_flex_mono_def τ) ->
  a_flex_tvar Θ c.
Proof.
  intros c bd Θ [Hb | [τ Hb]] Hn1 Hn2;
    apply binds_cons_1 in Hb as [[_ Heq] | Hb];
    solve [ exfalso; apply Hn1; symmetry; exact Heq
          | exfalso; apply (Hn2 τ); symmetry; exact Heq
          | left; exact Hb | right; exists τ; exact Hb ].
Qed.

(* ===================================================================== *)
(*  §  ⚙ TERM ENTRIES ARE INERT FOR THE FLEXIBILITY PICTURE (2026-08-22,   *)
(*  the a_pat rung) — inserting or stripping one changes nothing.          *)
(* ===================================================================== *)

Lemma a_flex_tvar_app_iff : forall (Ξ Θ : aenv) x,
  a_flex_tvar (Ξ ++ Θ) x <-> (a_flex_tvar Ξ x \/ a_flex_tvar Θ x).
Proof.
  intros Ξ Θ x. unfold a_flex_tvar, binds. split.
  - intros [Hb | [t Hb]]; apply in_app_or in Hb; destruct Hb as [Hb | Hb].
    + left; left; exact Hb.
    + right; left; exact Hb.
    + left; right; exists t; exact Hb.
    + right; right; exists t; exact Hb.
  - intros [[Hb | [t Hb]] | [Hb | [t Hb]]].
    + left; apply in_or_app; left; exact Hb.
    + right; exists t; apply in_or_app; left; exact Hb.
    + left; apply in_or_app; right; exact Hb.
    + right; exists t; apply in_or_app; right; exact Hb.
Qed.


(** ⚙ The term-entry moves the abs rows make on the flexibility picture:
    INSERTING an entry is [a_flex_tvar_mid_other] above (the former
    [a_flex_tvar_insert_mid] was that lemma with its arguments reordered). *)

Definition abind_nonflex (bd : abind) : Prop :=
  bd <> abind_flex_mono /\ forall τ, bd <> abind_flex_mono_def τ.

Lemma abind_is_tm_nonflex : forall bd, abind_is_tm bd -> abind_nonflex bd.
Proof.
  intros bd Htm; destruct bd; simpl in Htm; try contradiction;
    split; intros; discriminate.
Qed.

(** A NON-FLEX cons is invisible to [a_flex_tvar] — at EVERY atom, the
    entry's own included (it carries no flex binding, and with the atom
    off the tail's domain nothing hides behind it). *)
Lemma a_flex_tvar_cons_nonflex : forall x (bd : abind) Θ a,
  abind_nonflex bd ->
  (a_flex_tvar ((x ~ bd) ++ Θ) a <-> a_flex_tvar Θ a).
Proof.
  intros x bd Θ a [Hn1 Hn2].
  destruct (a == x) as [-> | Hne];
    [ | apply a_flex_tvar_cons_other; exact Hne ].
  split; intros Hf.
  - eapply a_flex_tvar_head_tail; [ exact Hf | exact Hn1 | exact Hn2 ].
  - destruct Hf as [Hb | [τ Hb]]; [ left | right; exists τ ];
      unfold binds in *; simpl; right; assumption.
Qed.

(** ⚙ The flexibility facts below were proved in ext_algo/ (prop_look_pair.v,
    prop_solve_rel.v, prop_lift_context.v) while that campaign left fresco/algo
    alone; they are about [algo/]'s relations only and moved here
    2026-10-10.  [a_flex_var_iff_tvar] also absorbs ext_algo/consistency/prop_consis.v's
    one-direction copy [a_flex_tvar_flex]. *)

Lemma a_flex_tvar_app_congr : forall (Ξ Θ Θ' : aenv),
  (forall α, a_flex_tvar Θ α <-> a_flex_tvar Θ' α) ->
  forall α, a_flex_tvar (Ξ ++ Θ) α <-> a_flex_tvar (Ξ ++ Θ') α.
Proof.
  intros * Hiff α.
  pose proof (a_flex_tvar_app_iff Ξ Θ α).
  pose proof (a_flex_tvar_app_iff Ξ Θ' α).
  pose proof (Hiff α).
  tauto.
Qed.

Lemma a_flex_of_tvar_iff : forall Θ Θ' P,
  (forall α, a_flex_tvar Θ α <-> a_flex_tvar Θ' α) ->
  a_flex Θ P -> a_flex Θ' P.
Proof.
  intros * Hiff Hf.
  inversion Hf; subst.
  - assert (Hft : a_flex_tvar Θ' α) by (apply Hiff; left; assumption).
    destruct Hft as [Hb | [τ Hb]];
      [ apply a_flex__var | eapply a_flex__var_def ]; eassumption.
  - assert (Hft : a_flex_tvar Θ' α)
      by (apply Hiff; right; eexists; eassumption).
    destruct Hft as [Hb | [τ0 Hb]];
      [ apply a_flex__var | eapply a_flex__var_def ]; eassumption.
Qed.

Lemma a_flex_tvar_rigid_prefix_iff : forall (Δr Θ : aenv) α,
  (forall x bd, binds x bd Δr -> bd = abind_tvar) ->
  (a_flex_tvar (Δr ++ Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros * Hr.
  pose proof (a_flex_tvar_app_iff Δr Θ α) as Hor.
  assert (Hnf : ~ a_flex_tvar Δr α).
  { intros [Hb | [τ Hb]]; pose proof (Hr _ _ Hb); discriminate. }
  tauto.
Qed.

(** [a_flex] at a variable IS [a_flex_tvar] — the SE-FlexR side
    conditions' bridge. *)
Lemma a_flex_var_iff_tvar : forall Θ α,
  a_flex Θ (pskl_var_f α) <-> a_flex_tvar Θ α.
Proof.
  intros. split.
  - intros Hf; inversion Hf; subst;
      [ left; assumption | right; eexists; eassumption ].
  - intros [Hb | [τ Hb]];
      [ eapply a_flex__var | eapply a_flex__var_def ]; eassumption.
Qed.

(** A rigid entry at an UNBOUND name is not flexible — the pair rows'
    both-false case. *)
Lemma a_flex_tvar_cons_tvar_self : forall β (Θ : aenv),
  β `notin` dom Θ ->
  ~ a_flex_tvar ((β ~ abind_tvar) ++ Θ) β.
Proof.
  intros * Hn [Hb | [τ Hb]]; unfold binds in Hb; simpl in Hb;
    (destruct Hb as [Hb | Hb];
     [ solve [ inversion Hb ]
     | apply Hn; eapply binds_In; exact Hb ]).
Qed.

Lemma a_flex_tvar_one_flex : forall α (b : abind) x,
  (b = abind_flex_mono \/ exists t, b = abind_flex_mono_def t) ->
  (a_flex_tvar (α ~ b) x <-> x = α).
Proof.
  intros α b x Hb. split.
  - intros [Hbd | [t Hbd]]; unfold binds in Hbd; simpl in Hbd;
      destruct Hbd as [E | E]; try contradiction; inversion E; reflexivity.
  - intros ->. destruct Hb as [-> | [t ->]];
      [ left | right; exists t ]; unfold binds; simpl; left; reflexivity.
Qed.

Lemma a_flex_tvar_one_nonflex : forall (c : atom) (bd : abind) x,
  bd <> abind_flex_mono ->
  (forall t, bd <> abind_flex_mono_def t) ->
  ~ a_flex_tvar (c ~ bd) x.
Proof.
  intros c bd x H1 H2 [Hb | [t Hb]]; unfold binds in Hb; simpl in Hb;
    destruct Hb as [E | E]; try contradiction; inversion E; subst.
  - apply H1; reflexivity.
  - apply (H2 t); reflexivity.
Qed.

Lemma a_flex_tvar_cons_absent : forall (c : atom) (bd : abind) (Θ : aenv) x,
  bd <> abind_flex_mono ->
  (forall t, bd <> abind_flex_mono_def t) ->
  x `notin` dom Θ ->
  ~ a_flex_tvar ((c ~ bd) ++ Θ) x.
Proof.
  intros c bd Θ x H1 H2 Hx Hf. rewrite a_flex_tvar_app_iff in Hf.
  destruct Hf as [Hf | Hf];
    [ exact (@a_flex_tvar_one_nonflex c bd x H1 H2 Hf)
    | exact (Hx (a_flex_tvar_in_dom Hf)) ].
Qed.


Lemma a_flex_tvar_strip_tvar : forall b Θ α,
  a_flex_tvar ((b ~ abind_tvar) ++ Θ) α -> a_flex_tvar Θ α.
Proof.
  intros b Θ α [Hb | [τ Hb]];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Habs] | Hb'];
    solve [ discriminate Habs | left; exact Hb' | right; exists τ; exact Hb' ].
Qed.


(** Binding inclusion implies domain inclusion. *)

Lemma aenv_binds_dom_sub : forall (Θ Θ' : aenv),
  (forall x b, binds x b Θ -> binds x b Θ') ->
  dom Θ [<=] dom Θ'.
Proof.
  intros Θ Θ' Hmon x Hx.
  apply binds_In_inv in Hx; destruct Hx as [b Hb].
  eapply binds_In; apply Hmon; exact Hb.
Qed.
