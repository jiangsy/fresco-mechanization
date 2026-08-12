(** Composition of metasubstitutions  [ζ ∘ κ]  (algorithmic.tex:123-147).

    Completeness/optimality is stated up to `κ ≡ ζ ∘ κ₁` (full-algo-spec.tex:1502),
    so it needs GENERAL metasubstitutions and their composition.  Everything so
    far only ever needed the IDENTITY shorthand `⊴`, for which [a_inc_trans]
    (prop_inc.v) suffices.

    A metasubstitution is a finite MAP (algorithmic.tex:123), so composition is
    pointwise on the domain:

      (ζ ∘ κ)(α)  =  ζ(κ(α))

    and its action law is [msubst_ptyp_compose] below.  NB the action law needs a
    side condition — a variable that κ does not touch but ζ does would be treated
    differently by the two sides.  It is discharged for every type WELL-FORMED IN
    THE SOURCE context: such a type's flexible variables are exactly κ's domain,
    and its rigid variables stay rigid in the target, hence miss ζ's domain. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Composition, and the algebra of [msubst_lookup]                       *)
(* ===================================================================== *)

Lemma dom_msubst_compose : forall ζ κ,
  dom (msubst_compose ζ κ) [=] dom κ.
Proof.
  intros ζ κ; induction κ as [ | [α τ] κ' IH ]; simpl; fsetdec.
Qed.

(** Outside its domain a metasubstitution is the identity. *)
Lemma msubst_lookup_notin : forall κ α',
  α' `notin` dom κ ->
  msubst_lookup κ α' = ptyp_var_f α'.
Proof.
  induction κ as [ | [α τ] κ' IH ]; intros α' Hα; simpl in *; auto.
  destruct (α' == α) as [->|Hne]; [ exfalso; clear - Hα; fsetdec | ].
  apply IH. clear - Hα. fsetdec.
Qed.

Lemma msubst_ptyp_notin : forall κ A,
  (forall α, α `in` ftvar_in_ptyp A -> α `notin` dom κ) ->
  msubst_ptyp κ A = A.
Proof.
  intros κ A; induction A; intros Hfr; simpl in *; f_equal; auto;
    try (apply msubst_lookup_notin; apply Hfr; simpl; fsetdec);
    try (first [ apply IHA1 | apply IHA2 | apply IHA ];
         intros α Hα; apply Hfr; simpl; fsetdec).
Qed.

(** THE action law, at a variable.  The side condition is exactly what rules out
    a variable that κ misses but ζ hits. *)
Lemma msubst_lookup_compose : forall ζ κ α',
  (α' `in` dom κ \/ α' `notin` dom ζ) ->
  msubst_lookup (msubst_compose ζ κ) α' = msubst_ptyp ζ (msubst_lookup κ α').
Proof.
  intros ζ κ; induction κ as [ | [α τ] κ' IH ]; intros α' Hcond; simpl.
  - (* κ = · : α' is untouched by κ, so by hypothesis ζ misses it too *)
    destruct Hcond as [Hin | Hni]; [ simpl in Hin; exfalso; clear - Hin; fsetdec | ].
    rewrite msubst_lookup_notin by exact Hni. reflexivity.
  - destruct (α' == α) as [->|Hne]; [ reflexivity | ].
    apply IH.
    destruct Hcond as [Hin | Hni]; [ left | right; exact Hni ].
    simpl in Hin. clear - Hin Hne. fsetdec.
Qed.

Lemma msubst_ptyp_compose : forall ζ κ A,
  (forall α, α `in` ftvar_in_ptyp A -> α `in` dom κ \/ α `notin` dom ζ) ->
  msubst_ptyp (msubst_compose ζ κ) A = msubst_ptyp ζ (msubst_ptyp κ A).
Proof.
  intros ζ κ A; induction A; intros Hvis; simpl; f_equal; auto;
    try (apply msubst_lookup_compose; apply Hvis; simpl; fsetdec);
    try (first [ apply IHA1 | apply IHA2 | apply IHA ];
         intros α Hα; apply Hvis; simpl; fsetdec).
Qed.

(* ===================================================================== *)
(*  κ's domain is EXACTLY the source's flexible variables                  *)
(* ===================================================================== *)

(** The skeleton mirror of [a_wf_ptyp_ftv_tvarish]. *)
Lemma a_scope_pskl_ftv_tvarish : forall Θ P α,
  a_scope_pskl Θ P ->
  α `in` ftvar_in_pskl P ->
  a_binds_tvar α Θ.
Proof.
  intros Θ P α Hwf; revert α; induction Hwf; intros β Hβ; simpl in Hβ.
  - exfalso. clear - Hβ. fsetdec.
  (* [α] is the var rule's OWN binder ([a_scope_pskl__var], algo/def_extra.v),
     auto-bound by [induction Hwf] — not this lemma's α ([revert α]). *)
  - assert (HeqY : β = α) by (clear - Hβ; fsetdec). subst. exact H.
  - destruct (union_1 Hβ); auto.
  - (* ∀ : the bound variable is fresh, so it is not the one we are tracking *)
    pick fresh α2 for (L `union` ftvar_in_pskl P `union` singleton β).
    assert (HYo : β `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α2))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α2)) as Hl.
      clear - Hβ Hl. fsetdec. }
    specialize (H0 α2 ltac:(auto) β HYo).
    destruct H0 as [Hb | [Hb | [τ Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[HeqZ ?] | Hb'];
      try (subst; exfalso; clear - Fr; fsetdec);
      [ left | right; left | right; right; exists τ ]; exact Hb'.
  - exfalso. clear - Hβ. fsetdec.
  - auto.
Qed.

Lemma a_inc_dom_flex : forall Θ κ Θ',
  κ ∷ Θ ⊑ Θ' ->
  forall α', α' `in` dom κ -> a_flex_tvar Θ α'.
Proof.
  intros Θ κ Θ' H; induction H; intros α' Hα; simpl in Hα.
  - exfalso. clear - Hα. fsetdec.
  - destruct (α' == α) as [->|Hne].
    + left. unfold binds; left; reflexivity.
    + destruct (IHa_inc α' ltac:(clear - Hα Hne; solve_notin_auto)) as [Hb | [τ0 Hb]];
        [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
  - destruct (α' == α) as [->|Hne].
    + right. exists τ. unfold binds; left; reflexivity.
    + destruct (IHa_inc α' ltac:(clear - Hα Hne; solve_notin_auto)) as [Hb | [τ0 Hb]];
        [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
  - destruct (IHa_inc α' Hα) as [Hb | [τ0 Hb]];
      [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
  - destruct (IHa_inc α' Hα) as [Hb | [τ0 Hb]];
      [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
  - destruct (IHa_inc α' Hα) as [Hb | [τ0 Hb]];
      [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
Qed.

Lemma a_inc_flex_dom : forall Θ κ Θ',
  κ ∷ Θ ⊑ Θ' ->
  {{ ⊢ Θ }}a ->
  forall α', a_flex_tvar Θ α' -> α' `in` dom κ.
Proof.
  intros Θ κ Θ' H; induction H; intros Hwf α' Hfx; simpl.
  - destruct Hfx as [Hb | [τ Hb]]; inversion Hb.
  - inversion Hwf; subst.
    destruct (α' == α) as [->|Hne]; [ clear; fsetdec | ].
    assert (Hfx' : a_flex_tvar Θ α').
    { destruct Hfx as [Hb | [τ0 Hb]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
        try (exfalso; apply Hne; exact Heq);
        [ left; exact Hb' | right; exists τ0; exact Hb' ]. }
    assert (Hd : α' `in` dom κ) by (apply IHa_inc; auto).
    clear - Hd. fsetdec.
  - inversion Hwf; subst.
    destruct (α' == α) as [->|Hne]; [ clear; fsetdec | ].
    assert (Hfx' : a_flex_tvar Θ α').
    { destruct Hfx as [Hb | [τ0 Hb]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
        try (exfalso; apply Hne; exact Heq);
        [ left; exact Hb' | right; exists τ0; exact Hb' ]. }
    assert (Hd : α' `in` dom κ) by (apply IHa_inc; auto).
    clear - Hd. fsetdec.
  - inversion Hwf; subst. apply IHa_inc; auto.
    destruct Hfx as [Hb | [τ0 Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      try discriminate; [ left; exact Hb' | right; exists τ0; exact Hb' ].
  - inversion Hwf; subst. apply IHa_inc; auto.
    destruct Hfx as [Hb | [τ0 Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      try discriminate; [ left; exact Hb' | right; exists τ0; exact Hb' ].
  - inversion Hwf; subst. apply IHa_inc; auto.
    destruct Hfx as [Hb | [τ0 Hb]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heq] | Hb'];
      try discriminate; [ left; exact Hb' | right; exists τ0; exact Hb' ].
Qed.

(** A RIGID variable of the source stays rigid, hence misses ζ's domain. *)
Lemma a_inc_tvar_notin_dom : forall Θ1 ζ Θ α,
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  binds α abind_tvar Θ1 ->
  α `notin` dom ζ.
Proof.
  intros Θ1 ζ Θ α Hinc Hwf Hb Hα.
  pose proof (a_inc_dom_flex Hinc Hα) as Hfx.
  pose proof (a_wf_aenv_uniq Hwf) as Hu.
  destruct Hfx as [Hb' | [τ Hb']];
    pose proof (binds_unique _ _ _ _ _ Hb Hb' Hu) as He; discriminate.
Qed.

(** THE visibility side condition, discharged for a source-well-formed type. *)
Lemma a_inc_compose_vis : forall Θ0 κ Θ1 ζ Θ,
  κ ∷ Θ0 ⊑ Θ1 ->
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θ1 }}a ->
  forall α, a_binds_tvar α Θ0 ->
  α `in` dom κ \/ α `notin` dom ζ.
Proof.
  intros Θ0 κ Θ1 ζ Θ Hinc1 Hinc2 Hwf0 Hwf1 α Hbt.
  destruct Hbt as [Hb | [Hb | [τ Hb]]].
  - (* rigid : stays rigid in Θ1, so ζ misses it *)
    right. eapply a_inc_tvar_notin_dom;
      [ exact Hinc2 | exact Hwf1 | eapply a_inc_binds_tvar; eauto ].
  - left. eapply a_inc_flex_dom; [ exact Hinc1 | exact Hwf0 | left; exact Hb ].
  - left. eapply a_inc_flex_dom;
      [ exact Hinc1 | exact Hwf0 | right; exists τ; exact Hb ].
Qed.

(* ===================================================================== *)
(*  A metasubstitution transports lc / mono / wf / ≡ into the target       *)
(* ===================================================================== *)

Lemma a_inc_lookup_lc : forall Θ1 ζ Θ α',
  ζ ∷ Θ1 ⊑ Θ ->
  lc_ptyp (msubst_lookup ζ α').
Proof.
  intros Θ1 ζ Θ α' H; revert α'; induction H; intros α'; simpl;
    try (apply IHa_inc).
  - constructor.
  - destruct (α' == α) as [->|Hne]; [ eapply a_wf_ptyp_lc; eauto | apply IHa_inc ].
  - destruct (α' == α) as [->|Hne]; [ eapply a_wf_ptyp_lc; eauto | apply IHa_inc ].
Qed.

Lemma a_inc_lookup_mono : forall Θ1 ζ Θ α',
  ζ ∷ Θ1 ⊑ Θ ->
  mono_ptyp (msubst_lookup ζ α').
Proof.
  intros Θ1 ζ Θ α' H; revert α'; induction H; intros α'; simpl;
    try (apply IHa_inc).
  - constructor.
  - destruct (α' == α) as [->|Hne]; [ assumption | apply IHa_inc ].
  - destruct (α' == α) as [->|Hne]; [ assumption | apply IHa_inc ].
Qed.

Lemma a_inc_lookup_wf : forall Θ1 ζ Θ α',
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  a_binds_tvar α' Θ1 ->
  a_wf_ptyp Θ (msubst_lookup ζ α').
Proof.
  intros Θ1 ζ Θ α' Hinc Hwf Hbt.
  destruct (AtomSetProperties.In_dec α' (dom ζ)) as [Hin | Hni].
  - (* in κ's domain : the image is well-formed in the target by construction *)
    clear Hbt. revert α' Hin; induction Hinc; intros α' Hin; simpl in *.
    + exfalso. clear - Hin. fsetdec.
    + destruct (α' == α) as [->|Hne]; [ assumption | ].
      apply IHHinc; [ inversion Hwf; auto | clear - Hin Hne; fsetdec ].
    + destruct (α' == α) as [->|Hne]; [ assumption | ].
      apply IHHinc; [ inversion Hwf; auto | clear - Hin Hne; fsetdec ].
    + (* the target grows by a suffix + one entry : weaken *)
      eapply a_wf_ptyp_weaken;
        [ intros y b Hb; unfold binds in *;
          apply in_or_app; right; simpl; right; exact Hb
        | apply IHHinc; [ inversion Hwf; auto | exact Hin ] ].
    + eapply a_wf_ptyp_weaken;
        [ intros y b Hb; unfold binds in *;
          apply in_or_app; right; simpl; right; exact Hb
        | apply IHHinc; [ inversion Hwf; auto | exact Hin ] ].
    + eapply a_wf_ptyp_weaken;
        [ intros y b Hb; unfold binds in *;
          apply in_or_app; right; simpl; right; exact Hb
        | apply IHHinc; [ inversion Hwf; auto | exact Hin ] ].
  - (* outside the domain : α' is a RIGID of Θ1, and rigids survive *)
    rewrite msubst_lookup_notin by exact Hni.
    apply a_wf_ptyp__var.
    destruct Hbt as [Hb | [Hb | [τ Hb]]].
    + left. eapply a_inc_binds_tvar; [ exact Hinc | exact Hb ].
    + exfalso. apply Hni.
      eapply a_inc_flex_dom; [ exact Hinc | exact Hwf | left; exact Hb ].
    + exfalso. apply Hni.
      eapply a_inc_flex_dom; [ exact Hinc | exact Hwf | right; exists τ; exact Hb ].
Qed.

(** [msubst] commutes with opening: its images are locally closed, so opening
    cannot reach inside them. *)
Lemma msubst_ptyp_open_rec : forall Θ1 ζ Θ A A' k,
  ζ ∷ Θ1 ⊑ Θ ->
  msubst_ptyp ζ (open_ptyp_wrt_ptyp_rec k A' A)
  = open_ptyp_wrt_ptyp_rec k (msubst_ptyp ζ A') (msubst_ptyp ζ A).
Proof.
  intros Θ1 ζ Θ A; induction A; intros A' k Hinc; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - (* a free variable's image is lc, so [open_rec] is a no-op on it *)
    symmetry.
    apply open_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp.
    apply degree_ptyp_wrt_ptyp_O.
    apply degree_ptyp_wrt_ptyp_of_lc_ptyp.
    eapply a_inc_lookup_lc; exact Hinc.
Qed.

Lemma msubst_ptyp_open : forall Θ1 ζ Θ A α,
  ζ ∷ Θ1 ⊑ Θ ->
  α `notin` dom ζ ->
  msubst_ptyp ζ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
  = open_ptyp_wrt_ptyp (msubst_ptyp ζ A) (ptyp_var_f α).
Proof.
  intros Θ1 ζ Θ A α Hinc Hα.
  unfold open_ptyp_wrt_ptyp.
  rewrite (msubst_ptyp_open_rec A (ptyp_var_f α) 0 Hinc).
  simpl. rewrite msubst_lookup_notin by exact Hα. reflexivity.
Qed.

Lemma msubst_ptyp_lc : forall Θ1 ζ Θ A,
  ζ ∷ Θ1 ⊑ Θ ->
  lc_ptyp A ->
  lc_ptyp (msubst_ptyp ζ A).
Proof.
  intros Θ1 ζ Θ A Hinc Hlc; induction Hlc; simpl.
  - constructor.
  - eapply a_inc_lookup_lc; eauto.
  - constructor; auto.
  - (* ∀ : pick a variable outside ζ's domain and push the substitution in *)
    pick fresh α for (dom ζ).
    apply lc_ptyp_all_exists with (α1 := α).
    erewrite <- msubst_ptyp_open;
      [ apply H0 | exact Hinc | clear - Fr; fsetdec ].
Qed.

(** An increase extends by a fresh rigid on both sides. *)
Lemma a_inc_cons_tvar : forall Θ1 ζ Θ α,
  ζ ∷ Θ1 ⊑ Θ ->
  ζ ∷ ((α ~ abind_tvar) ++ Θ1) ⊑ ((α ~ abind_tvar) ++ Θ).
Proof.
  intros Θ1 ζ Θ α Hinc.
  change ((α ~ abind_tvar) ++ Θ)
    with (nil ++ (α ~ abind_tvar) ++ Θ).
  apply a_inc__tvar; [ exact Hinc | apply a_suffix__nil ].
Qed.

Lemma mono_ptyp_msubst : forall Θ1 ζ Θ A,
  ζ ∷ Θ1 ⊑ Θ ->
  mono_ptyp A ->
  mono_ptyp (msubst_ptyp ζ A).
Proof.
  intros Θ1 ζ Θ A Hinc Hm; induction Hm; simpl.
  - constructor.
  - eapply a_inc_lookup_mono; eauto.
  - constructor; auto.
Qed.

Lemma a_wf_ptyp_msubst : forall Θ1 A,
  a_wf_ptyp Θ1 A ->
  {{ ⊢ Θ1 }}a ->
  forall ζ Θ, ζ ∷ Θ1 ⊑ Θ ->
  a_wf_ptyp Θ (msubst_ptyp ζ A).
Proof.
  intros Θ1 A Hwa; induction Hwa; intros Hwf ζ Θt Hinc; simpl.
  - apply a_wf_ptyp__unit.
  - eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact H ].
  - apply a_wf_ptyp__arrow;
      [ apply IHHwa1 | apply IHHwa2 ]; auto.
  - apply a_wf_ptyp__all
      with (L := L `union` dom ζ `union` dom Θt `union` dom Θ).
    intros α Hα.
    assert (Heq : msubst_ptyp ζ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
                  = open_ptyp_wrt_ptyp (msubst_ptyp ζ A) (ptyp_var_f α)).
    { eapply msubst_ptyp_open;
        [ apply a_inc_cons_tvar; exact Hinc | clear - Hα; fsetdec ]. }
    rewrite <- Heq.
    apply H0;
      [ clear - Hα; fsetdec
      | apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]
      | apply a_inc_cons_tvar; exact Hinc ].
  Unshelve. all: eauto.
Qed.

(* ===================================================================== *)
(*  A definition's free variables live STRICTLY BELOW it.                 *)
(*  This is exactly what [a_wf_aenv__flex_def] says: it carries            *)
(*  [a_wf_ptyp Θ τ] on the TAIL.  It is what makes entries ABOVE a         *)
(*  definition unable to interfere with it — and hence what makes the      *)
(*  composite well behaved.  (With the old SEQUENTIAL msubst this was      *)
(*  silently false, which is why the fold computed the wrong composite.)   *)
(* ===================================================================== *)

(* ⚙ RENAMED from [a_wf_aenv_def_ftv_dom] 2026-08-09 (cleanup audit §8.1c):
   it collided with prop_soundness_consis.v:1586's, which concludes the same
   fact in [ [<=] ] form.  The two are logically equal but NOT apply-compatible,
   so which one an unqualified reference picked up depended on import ORDER —
   adding a [Require Import] to prop_rho_relation.v silently flipped four call sites and
   broke the build.  This one is the POINTWISE form; hence the suffix. *)
Lemma a_wf_aenv_def_ftv_dom_in : forall Θ β τ,
  {{ ⊢ Θ }}a ->
  binds β (abind_flex_mono_def τ) Θ ->
  forall α', α' `in` ftvar_in_ptyp τ -> α' `in` dom Θ.
Proof.
  intros Θ β τ Hwf; induction Hwf; intros Hb α' Hα; simpl in *.
  - inversion Hb.
  - (* flex *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    assert (Hd : α' `in` dom Θ) by (eapply IHHwf; eauto).
    clear - Hd; fsetdec.
  - (* flex_def : the definition's type is well-formed in the TAIL *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'].
    + inversion Heqb; subst.
      assert (Hbt : a_binds_tvar α' Θ) by (eapply a_wf_ptyp_ftv_tvarish; eauto).
      assert (Hd : α' `in` dom Θ).
      { destruct Hbt as [Hbb | [Hbb | [τd Hbb]]];
          apply binds_In in Hbb; exact Hbb. }
      clear - Hd; fsetdec.
    + assert (Hd : α' `in` dom Θ) by (eapply IHHwf; eauto).
      clear - Hd; fsetdec.
  - (* var_skl *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    assert (Hd : α' `in` dom Θ) by (eapply IHHwf; eauto).
    clear - Hd; fsetdec.
  - (* var_typ *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    assert (Hd : α' `in` dom Θ) by (eapply IHHwf; eauto).
    clear - Hd; fsetdec.
  - (* tvar *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    assert (Hd : α' `in` dom Θ) by (eapply IHHwf; eauto).
    clear - Hd; fsetdec.
Qed.

(** Consequently an entry ABOVE a definition never occurs free in it. *)
Lemma a_wf_aenv_head_notin_def_ftv : forall α0 b Θ' β τ,
  {{ ⊢ ((α0 ~ b) ++ Θ') }}a ->
  binds β (abind_flex_mono_def τ) Θ' ->
  α0 `notin` ftvar_in_ptyp τ.
Proof.
  intros α0 b Θ' β τ Hwf Hb Hα.
  assert (Hnd : α0 `notin` dom Θ' /\ {{ ⊢ Θ' }}a)
    by (inversion Hwf; subst; auto).
  destruct Hnd as [Hnd Hwf'].
  apply Hnd. eapply a_wf_aenv_def_ftv_dom_in; eauto.
Qed.

(** Two metasubstitutions agreeing on a type's free variables act alike. *)
Lemma msubst_ptyp_agree : forall ζ ζ' A,
  (forall α, α `in` ftvar_in_ptyp A -> msubst_lookup ζ α = msubst_lookup ζ' α) ->
  msubst_ptyp ζ A = msubst_ptyp ζ' A.
Proof.
  intros ζ ζ' A; induction A; intros Hag; simpl.
  - reflexivity.
  - reflexivity.
  - (* NB do NOT [f_equal] here: both sides are [msubst_lookup _ _], and
       [f_equal] would demand [ζ = ζ'] *)
    apply Hag. simpl. fsetdec.
  - f_equal; [ apply IHA1 | apply IHA2 ];
      intros α Hα; apply Hag; simpl; fsetdec.
  - f_equal. apply IHA. intros α Hα; apply Hag; simpl; fsetdec.
Qed.

(** An entry the type does not mention may be dropped. *)
Lemma msubst_ptyp_cons_notin : forall α0 τ0 ζ A,
  α0 `notin` ftvar_in_ptyp A ->
  msubst_ptyp ((α0, τ0) :: ζ) A = msubst_ptyp ζ A.
Proof.
  intros α0 τ0 ζ A HA.
  apply msubst_ptyp_agree. intros α Hα. simpl.
  destruct (α == α0) as [->|Hne]; [ exfalso; auto | reflexivity ].
Qed.

(* ===================================================================== *)
(*  A metasubstitution respects definitions, hence type equivalence        *)
(* ===================================================================== *)

(** A definition's own variable is not free in it. *)
Lemma a_wf_aenv_def_head_fresh : forall α τ Θ,
  {{ ⊢ ((α ~ abind_flex_mono_def τ) ++ Θ) }}a ->
  α `notin` ftvar_in_ptyp τ.
Proof.
  intros α τ Θ Hwf Hα.
  inversion Hwf as [ | | α' τ' Θ'' Hnd Hwp Hm Hwa | | | ]; subst.
  apply Hnd.
  eapply a_wf_ptyp_ftv_tvarish in Hα; [ | exact Hwp ].
  destruct Hα as [Hb | [Hb | [τd Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

(** ζ maps a defined variable and its definition to equivalent types.  The
    entries ABOVE the definition drop out — that is what "definitions live
    strictly below" buys. *)
Lemma a_inc_lookup_def : forall Θ1 ζ Θ,
  ζ ∷ Θ1 ⊑ Θ ->
  {{ ⊢ Θ1 }}a ->
  forall α τ, binds α (abind_flex_mono_def τ) Θ1 ->
  {{ Θ ⊢ (msubst_lookup ζ α) ≡ᵗ (msubst_ptyp ζ τ) }}a.
Proof.
  intros Θ1 ζ Θ Hinc; induction Hinc; intros Hwf α0 τ0 Hb; simpl.
  - inversion Hb.
  - (* flex head : α0 is below it, so the head entry drops out *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    assert (Hfr : α `notin` ftvar_in_ptyp τ0)
      by (eapply a_wf_aenv_head_notin_def_ftv; eauto).
    rewrite msubst_ptyp_cons_notin by exact Hfr.
    destruct (α0 == α) as [->|Hne].
    { exfalso. apply binds_In in Hb'.
      inversion Hwf as [ | αh Θh Hnd Hwa | | | | ]; subst.
      clear - Hb' Hnd. fsetdec. }
    apply IHHinc; [ inversion Hwf; auto | exact Hb' ].
  - (* flex_def head *)
    assert (Hwf' : {{ ⊢ Θ }}a) by (inversion Hwf; auto).
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> Heqb] | Hb'].
    + (* the head IS the definition : this is exactly the rule's premise *)
      inversion Heqb; subst.
      assert (Hfr : α `notin` ftvar_in_ptyp τ)
        by (eapply a_wf_aenv_def_head_fresh; exact Hwf).
      rewrite msubst_ptyp_cons_notin by exact Hfr.
      destruct (α == α) as [_|Hc]; [ | congruence ].
      assumption.
    + assert (Hfr : α `notin` ftvar_in_ptyp τ0)
        by (eapply a_wf_aenv_head_notin_def_ftv; eauto).
      rewrite msubst_ptyp_cons_notin by exact Hfr.
      destruct (α0 == α) as [->|Hne].
      { exfalso. apply binds_In in Hb'.
        inversion Hwf as [ | | αh τh Θh Hnd Hwp Hm Hwa | | | ]; subst.
        clear - Hb' Hnd. fsetdec. }
      apply IHHinc; [ exact Hwf' | exact Hb' ].
  - (* var_skl / var_typ / tvar heads : weaken into the grown target *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds in *;
        apply in_or_app; right; simpl; right; exact Hby
      | apply IHHinc; [ inversion Hwf; auto | exact Hb' ] ].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds in *;
        apply in_or_app; right; simpl; right; exact Hby
      | apply IHHinc; [ inversion Hwf; auto | exact Hb' ] ].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    eapply a_tyequiv_weaken;
      [ intros y b Hby; unfold binds in *;
        apply in_or_app; right; simpl; right; exact Hby
      | apply IHHinc; [ inversion Hwf; auto | exact Hb' ] ].
Qed.

Lemma a_tyequiv_msubst : forall Θ1 A A',
  {{ Θ1 ⊢ A ≡ᵗ A' }}a ->
  {{ ⊢ Θ1 }}a ->
  forall ζ Θ, ζ ∷ Θ1 ⊑ Θ ->
  {{ Θ ⊢ (msubst_ptyp ζ A) ≡ᵗ (msubst_ptyp ζ A') }}a.
Proof.
  intros Θ1 A A' Heq; induction Heq; intros Hwf ζ Θt Hinc; simpl.
  - apply a_tyequiv__refl. eapply msubst_ptyp_lc; eauto.
  - apply a_tyequiv__sym. auto.
  - eapply a_tyequiv__trans; [ apply IHHeq1 | apply IHHeq2 ]; auto.
  - (* the definition-lookup rule *)
    eapply a_inc_lookup_def; eauto.
  - apply a_tyequiv__arrow; auto.
  - apply a_tyequiv__all
      with (L := L `union` dom ζ `union` dom Θt `union` dom Θ).
    intros α Hα.
    (* NB [a_tyequiv__all] does NOT extend the context, unlike [a_wf_ptyp__all] *)
    assert (HeqA : msubst_ptyp ζ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
                   = open_ptyp_wrt_ptyp (msubst_ptyp ζ A) (ptyp_var_f α))
      by (eapply msubst_ptyp_open; [ exact Hinc | clear - Hα; fsetdec ]).
    assert (HeqB : msubst_ptyp ζ (open_ptyp_wrt_ptyp B (ptyp_var_f α))
                   = open_ptyp_wrt_ptyp (msubst_ptyp ζ B) (ptyp_var_f α))
      by (eapply msubst_ptyp_open; [ exact Hinc | clear - Hα; fsetdec ]).
    rewrite <- HeqA, <- HeqB.
    apply H0; [ clear - Hα; fsetdec | exact Hwf | exact Hinc ].
Qed.

(* ===================================================================== *)
(*  Mirrors for skeletons (needed by the [var_skl] binder case)            *)
(* ===================================================================== *)

Lemma msubst_pskl_agree : forall ζ ζ' P,
  (forall α, α `in` ftvar_in_pskl P -> msubst_lookup ζ α = msubst_lookup ζ' α) ->
  msubst_pskl ζ P = msubst_pskl ζ' P.
Proof.
  intros ζ ζ' P; induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hag; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. apply Hag. simpl. fsetdec.
  - f_equal; [ apply IHa | apply IHb ];
      intros α Hα; apply Hag; simpl; fsetdec.
  - f_equal. apply IHall. intros α Hα; apply Hag; simpl; fsetdec.
  - reflexivity.
  - f_equal. apply IHt. intros α Hα; apply Hag; simpl; fsetdec.
Qed.

Lemma msubst_pskl_compose : forall ζ κ P,
  (forall α, α `in` ftvar_in_pskl P -> α `in` dom κ \/ α `notin` dom ζ) ->
  msubst_pskl (msubst_compose ζ κ) P = msubst_pskl ζ (msubst_pskl κ P).
Proof.
  intros ζ κ P; induction P as [ | n | β | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hvis; simpl.
  - reflexivity.
  - reflexivity.
  - (* a variable : its image is a monotype, and [ptyp_to_pskl] commutes with
       the substitution *)
    rewrite msubst_lookup_compose by (apply Hvis; simpl; fsetdec).
    generalize (msubst_lookup κ β); intros τ.
    induction τ; simpl; f_equal; auto.
  - f_equal; [ apply IHa | apply IHb ];
      intros α Hα; apply Hvis; simpl; fsetdec.
  - f_equal. apply IHall. intros α Hα; apply Hvis; simpl; fsetdec.
  - reflexivity.
  - f_equal. apply IHt. intros α Hα; apply Hvis; simpl; fsetdec.
Qed.

(* ===================================================================== *)
(*  Skeleton-equivalence mirrors (for the semantic [var_skl] middles)      *)
(* ===================================================================== *)

(** [msubst_pskl] on an embedded type is the embedded [msubst_ptyp]. *)
Lemma msubst_pskl_embed_ptyp : forall ζ A,
  msubst_pskl ζ (ptyp_to_pskl A) = ptyp_to_pskl (msubst_ptyp ζ A).
Proof.
  induction A; simpl; f_equal; auto.
Qed.

Lemma msubst_pskl_open_rec : forall Θ1 ζ Θ P P' k,
  ζ ∷ Θ1 ⊑ Θ ->
  msubst_pskl ζ (open_pskl_wrt_pskl_rec k P' P)
  = open_pskl_wrt_pskl_rec k (msubst_pskl ζ P') (msubst_pskl ζ P).
Proof.
  intros Θ1 ζ Θ P; induction P; intros P' k Hinc; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - (* a free variable's image is lc, so [open_rec] is a no-op on it *)
    symmetry.
    apply open_pskl_wrt_pskl_rec_degree_pskl_wrt_pskl.
    apply degree_pskl_wrt_pskl_O.
    apply degree_pskl_wrt_pskl_of_lc_pskl.
    apply lc_ptyp_to_pskl.
    eapply a_inc_lookup_lc; exact Hinc.
Qed.

Lemma msubst_pskl_open : forall Θ1 ζ Θ P α,
  ζ ∷ Θ1 ⊑ Θ ->
  α `notin` dom ζ ->
  msubst_pskl ζ (open_pskl_wrt_pskl P (pskl_var_f α))
  = open_pskl_wrt_pskl (msubst_pskl ζ P) (pskl_var_f α).
Proof.
  intros Θ1 ζ Θ P α Hinc Hα.
  unfold open_pskl_wrt_pskl.
  rewrite (msubst_pskl_open_rec P (pskl_var_f α) 0 Hinc).
  simpl. rewrite msubst_lookup_notin by exact Hα. reflexivity.
Qed.

Lemma msubst_pskl_lc : forall Θ1 ζ Θ P,
  ζ ∷ Θ1 ⊑ Θ ->
  lc_pskl P ->
  lc_pskl (msubst_pskl ζ P).
Proof.
  intros Θ1 ζ Θ P Hinc Hlc; induction Hlc; simpl; try solve [ constructor; auto ].
  - apply lc_ptyp_to_pskl. eapply a_inc_lookup_lc; eauto.
  - (* ∀ : pick a variable outside ζ's domain and push the substitution in *)
    pick fresh α for (dom ζ).
    apply lc_pskl_all_syn_exists with (α1 := α).
    erewrite <- msubst_pskl_open;
      [ apply H0 | exact Hinc | clear - Fr; fsetdec ].
Qed.

(** [a_tyequiv_msubst], on skeletons. *)
Lemma a_pskl_tyequiv_msubst : forall Θ1 P P',
  {{ Θ1 ⊢ P ≡ˢ P' }}a ->
  {{ ⊢ Θ1 }}a ->
  forall ζ Θ, ζ ∷ Θ1 ⊑ Θ ->
  {{ Θ ⊢ (msubst_pskl ζ P) ≡ˢ (msubst_pskl ζ P') }}a.
Proof.
  intros Θ1 P P' Heq; induction Heq; intros Hwf ζ Θt Hinc; simpl.
  - apply a_pskl_tyequiv__refl. eapply msubst_pskl_lc; eauto.
  - apply a_pskl_tyequiv__sym. auto.
  - eapply a_pskl_tyequiv__trans; [ apply IHHeq1 | apply IHHeq2 ]; auto.
  - (* the definition-lookup rule : embed the type-level lookup lemma *)
    rewrite msubst_pskl_embed_ptyp.
    change (msubst_pskl ζ (pskl_var_f α))
      with (ptyp_to_pskl (msubst_lookup ζ α)).
    apply a_tyequiv_pskl.
    eapply a_inc_lookup_def; eauto.
  - apply a_pskl_tyequiv__arrow; auto.
  - apply a_pskl_tyequiv__all
      with (L := L `union` dom ζ `union` dom Θt).
    intros α Hα.
    assert (HeqP : msubst_pskl ζ (open_pskl_wrt_pskl P (pskl_var_f α))
                   = open_pskl_wrt_pskl (msubst_pskl ζ P) (pskl_var_f α))
      by (eapply msubst_pskl_open; [ exact Hinc | clear - Hα; fsetdec ]).
    assert (HeqQ : msubst_pskl ζ (open_pskl_wrt_pskl Q (pskl_var_f α))
                   = open_pskl_wrt_pskl (msubst_pskl ζ Q) (pskl_var_f α))
      by (eapply msubst_pskl_open; [ exact Hinc | clear - Hα; fsetdec ]).
    rewrite <- HeqP, <- HeqQ.
    apply H0; [ clear - Hα; fsetdec | exact Hwf | exact Hinc ].
  - apply a_pskl_tyequiv__tophole; auto.
Qed.

(* ===================================================================== *)
(*  Peeling the fresh flexible suffix a binder rule adds to the target     *)
(* ===================================================================== *)

Lemma msubst_lookup_app_notin : forall ζ1 ζ2 α',
  α' `notin` dom ζ1 ->
  msubst_lookup (ζ1 ++ ζ2) α' = msubst_lookup ζ2 α'.
Proof.
  induction ζ1 as [ | [α τ] ζ1' IH ]; intros ζ2 α' Hα; simpl in *; auto.
  destruct (α' == α) as [->|Hne]; [ exfalso; clear - Hα; fsetdec | ].
  apply IH. clear - Hα. fsetdec.
Qed.

(** The binder rules of [a_inc] prepend an all-flexible Ξ to the TARGET.  When
    that target is in turn increased, ζ splits along Ξ. *)
Lemma a_inc_peel_suffix : forall Ξ Θ ζ Θ',
  a_suffix Ξ ->
  ζ ∷ (Ξ ++ Θ) ⊑ Θ' ->
  exists ζ1 ζ2,
    ζ = ζ1 ++ ζ2 /\ dom ζ1 [=] dom Ξ /\ ζ2 ∷ Θ ⊑ Θ'.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros Θ ζ Θ' Hsuf Hinc.
  - exists nil, ζ. simpl in *.
    split; [ reflexivity | split; [ clear; fsetdec | exact Hinc ] ].
  - inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst.
    inversion Hb; subst; simpl in Hinc.
    + (* a flexible entry *)
      inversion Hinc as [ | Θa κa Θb αa τa Hi Hw Hm | | | | ]; subst.
      destruct (IH _ _ _ Hsuf' Hi) as [ζ1 [ζ2 [-> [Hd Hinc2]]]].
      exists ((a, τa) :: ζ1), ζ2. simpl.
      split; [ reflexivity | ].
      split; [ rewrite Hd; clear; fsetdec | exact Hinc2 ].
    + (* a defined flexible entry *)
      inversion Hinc as [ | | Θa κa Θb αa τa τb Hi Hw Hm He | | | ]; subst.
      destruct (IH _ _ _ Hsuf' Hi) as [ζ1 [ζ2 [-> [Hd Hinc2]]]].
      exists ((a, τb) :: ζ1), ζ2. simpl.
      split; [ reflexivity | ].
      split; [ rewrite Hd; clear; fsetdec | exact Hinc2 ].
Qed.

(** κ's images live in κ's target. *)
Lemma a_inc_entry_ftv : forall Θs κ Θt,
  κ ∷ Θs ⊑ Θt ->
  forall β τ, List.In (β, τ) κ ->
  forall α, α `in` ftvar_in_ptyp τ -> α `in` dom Θt.
Proof.
  intros Θs κ Θt H; induction H; intros β τ0 Hin α0 Hα0; simpl in *.
  - inversion Hin.
  - destruct Hin as [Heq | Hin]; [ inversion Heq; subst | eauto ].
    assert (Hbt : a_binds_tvar α0 Θ') by (eapply a_wf_ptyp_ftv_tvarish; eauto).
    destruct Hbt as [Hb | [Hb | [τd Hb]]]; apply binds_In in Hb; exact Hb.
  - destruct Hin as [Heq | Hin]; [ inversion Heq; subst | eauto ].
    assert (Hbt : a_binds_tvar α0 Θ') by (eapply a_wf_ptyp_ftv_tvarish; eauto).
    destruct Hbt as [Hb | [Hb | [τd Hb]]]; apply binds_In in Hb; exact Hb.
  - assert (Hd : α0 `in` dom Θ') by eauto.
    clear - Hd. simpl_env. fsetdec.
  - assert (Hd : α0 `in` dom Θ') by eauto.
    clear - Hd. simpl_env. fsetdec.
  - assert (Hd : α0 `in` dom Θ') by eauto.
    clear - Hd. simpl_env. fsetdec.
Qed.

(** Hence ζ and its Ξ-peeled part act alike on κ's images. *)
Lemma msubst_compose_peel : forall Θs κ Θt ζ1 ζ2,
  κ ∷ Θs ⊑ Θt ->
  (forall α, α `in` dom ζ1 -> α `notin` dom Θt) ->
  msubst_compose (ζ1 ++ ζ2) κ = msubst_compose ζ2 κ.
Proof.
  intros Θs κ Θt ζ1 ζ2 Hinc Hdisj.
  unfold msubst_compose. apply List.map_ext_in.
  intros [β τ] Hin. simpl. f_equal.
  apply msubst_ptyp_agree. intros α Hα.
  apply msubst_lookup_app_notin.
  intro Hc. apply (Hdisj α Hc).
  eapply a_inc_entry_ftv; eauto.
Qed.

(* ===================================================================== *)
(*  COMPOSITION OF INCREASES  (the paper's [ζ ∘ κ₁])                       *)
(* ===================================================================== *)

Lemma a_inc_compose : forall Θ0 κ Θ1,
  κ ∷ Θ0 ⊑ Θ1 ->
  {{ ⊢ Θ0 }}a ->
  {{ ⊢ Θ1 }}a ->
  forall ζ Θ, ζ ∷ Θ1 ⊑ Θ ->
  msubst_compose ζ κ ∷ Θ0 ⊑ Θ.
Proof.
  intros Θ0 κ Θ1 Hinc1; induction Hinc1;
    intros Hwf0 Hwf1 ζ Θt Hinc2.
  - (* ι ∷ · ⊑ Ξ : the target of an all-flexible source is all-flexible *)
    simpl. apply a_inc__empty. eapply a_inc_suffix_target; eauto.
  - (* flexible *)
    inversion Hwf0 as [ | αh Θh Hnd Hwa | | | | ]; subst.
    simpl. apply a_inc__flex.
    + apply IHHinc1; auto.
    + eapply a_wf_ptyp_msubst; eauto.
    + eapply mono_ptyp_msubst; eauto.
  - (* defined flexible : the equivalence premise composes *)
    inversion Hwf0 as [ | | αh τh Θh Hnd Hwp Hm Hwa | | | ]; subst.
    simpl. apply a_inc__flex_def.
    + apply IHHinc1; auto.
    + eapply a_wf_ptyp_msubst; eauto.
    + eapply mono_ptyp_msubst; eauto.
    + (* Θ ⊢ ζτ' ≡ (ζ∘κ)τ,  from  Θ1 ⊢ τ' ≡ κτ  by [a_tyequiv_msubst] *)
      rewrite msubst_ptyp_compose.
      * eapply a_tyequiv_msubst; eauto.
      * intros α0 Hα0.
        eapply a_inc_compose_vis;
          [ exact Hinc1 | exact Hinc2 | exact Hwa | exact Hwf1 | ].
        eapply a_wf_ptyp_ftv_tvarish; eauto.
  - (* term variable (type) : peel the fresh suffix, compose the two
       semantic middles, then rebuild *)
    inversion Hwf0 as [ | | | | xh Ah Θh Hnd Hwp Hwa | ]; subst.
    assert (Hpeel : exists ζ1 ζ2, ζ = ζ1 ++ ζ2 /\ dom ζ1 [=] dom Ξ /\
              ζ2 ∷ ((x ~ abind_var_typ A') ++ Θ') ⊑ Θt)
      by (eapply a_inc_peel_suffix; [ eassumption | exact Hinc2 ]).
    destruct Hpeel as [ζ1 [ζ2 [-> [Hd Hinc2']]]].
    assert (Hu1 : uniq (Ξ ++ (x ~ abind_var_typ A') ++ Θ'))
      by (apply a_wf_aenv_uniq; exact Hwf1).
    assert (Hdisj : forall α0, α0 `in` dom ζ1 -> α0 `notin` dom Θ').
    { intros α0 Hα0. rewrite Hd in Hα0. clear - Hu1 Hα0. solve_uniq. }
    assert (Hceq : msubst_compose (ζ1 ++ ζ2) κ = msubst_compose ζ2 κ)
      by (eapply msubst_compose_peel; eauto).
    assert (Hwf1c : {{ ⊢ ((x ~ abind_var_typ A') ++ Θ') }}a)
      by (eapply a_wf_aenv_strip_prefix; exact Hwf1).
    assert (Hwf1t : {{ ⊢ Θ' }}a) by (inversion Hwf1c; subst; auto).
    destruct (a_inc_var_inv Hinc2')
      as [Ξ2 [A2 [Θt2 [-> [Heq2 [Hs2 Hinc2'']]]]]].
    rewrite Hceq.
    apply a_inc__var;
      [ apply IHHinc1; [ exact Hwa | exact Hwf1t | exact Hinc2'' ] | | exact Hs2 ].
    assert (HA : msubst_ptyp (msubst_compose ζ2 κ) A
                 = msubst_ptyp ζ2 (msubst_ptyp κ A)).
    { apply msubst_ptyp_compose. intros α0 Hα0.
      eapply a_inc_compose_vis;
        [ exact Hinc1 | exact Hinc2'' | exact Hwa | exact Hwf1t
        | eapply a_wf_ptyp_ftv_tvarish; eauto ]. }
    rewrite HA.
    eapply a_tyequiv__trans; [ exact Heq2 | ].
    eapply a_tyequiv_msubst; [ exact H | exact Hwf1t | exact Hinc2'' ].
  - (* term variable (skeleton) : same shape, on skeletons *)
    inversion Hwf0 as [ | | | xh Ph Θh Hnd Hwp Hwa | | ]; subst.
    assert (Hpeel : exists ζ1 ζ2, ζ = ζ1 ++ ζ2 /\ dom ζ1 [=] dom Ξ /\
              ζ2 ∷ ((x ~ abind_var_skl P') ++ Θ') ⊑ Θt)
      by (eapply a_inc_peel_suffix; [ eassumption | exact Hinc2 ]).
    destruct Hpeel as [ζ1 [ζ2 [-> [Hd Hinc2']]]].
    assert (Hu1 : uniq (Ξ ++ (x ~ abind_var_skl P') ++ Θ'))
      by (apply a_wf_aenv_uniq; exact Hwf1).
    assert (Hdisj : forall α0, α0 `in` dom ζ1 -> α0 `notin` dom Θ').
    { intros α0 Hα0. rewrite Hd in Hα0. clear - Hu1 Hα0. solve_uniq. }
    assert (Hceq : msubst_compose (ζ1 ++ ζ2) κ = msubst_compose ζ2 κ)
      by (eapply msubst_compose_peel; eauto).
    assert (Hwf1c : {{ ⊢ ((x ~ abind_var_skl P') ++ Θ') }}a)
      by (eapply a_wf_aenv_strip_prefix; exact Hwf1).
    assert (Hwf1t : {{ ⊢ Θ' }}a) by (inversion Hwf1c; subst; auto).
    destruct (a_inc_var_skl_inv Hinc2')
      as [Ξ2 [P2 [Θt2 [-> [Heq2 [Hs2 Hinc2'']]]]]].
    rewrite Hceq.
    apply a_inc__var_skl;
      [ apply IHHinc1; [ exact Hwa | exact Hwf1t | exact Hinc2'' ] | | exact Hs2 ].
    assert (HP : msubst_pskl (msubst_compose ζ2 κ) P
                 = msubst_pskl ζ2 (msubst_pskl κ P)).
    { apply msubst_pskl_compose. intros α0 Hα0.
      eapply a_inc_compose_vis;
        [ exact Hinc1 | exact Hinc2'' | exact Hwa | exact Hwf1t
        | eapply a_scope_pskl_ftv_tvarish; eauto ]. }
    rewrite HP.
    eapply a_pskl_tyequiv__trans; [ exact Heq2 | ].
    eapply a_pskl_tyequiv_msubst; [ exact H | exact Hwf1t | exact Hinc2'' ].
  - (* rigid *)
    inversion Hwf0 as [ | | | | | αh Θh Hnd Hwa ]; subst.
    assert (Hpeel : exists ζ1 ζ2, ζ = ζ1 ++ ζ2 /\ dom ζ1 [=] dom Ξ /\
              ζ2 ∷ ((α ~ abind_tvar) ++ Θ') ⊑ Θt)
      by (eapply a_inc_peel_suffix; [ eassumption | exact Hinc2 ]).
    destruct Hpeel as [ζ1 [ζ2 [-> [Hd Hinc2']]]].
    assert (Hu1 : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ'))
      by (apply a_wf_aenv_uniq; exact Hwf1).
    assert (Hdisj : forall α0, α0 `in` dom ζ1 -> α0 `notin` dom Θ').
    { intros α0 Hα0. rewrite Hd in Hα0. clear - Hu1 Hα0. solve_uniq. }
    assert (Hceq : msubst_compose (ζ1 ++ ζ2) κ = msubst_compose ζ2 κ)
      by (eapply msubst_compose_peel; eauto).
    assert (Hwf1c : {{ ⊢ ((α ~ abind_tvar) ++ Θ') }}a)
      by (eapply a_wf_aenv_strip_prefix; exact Hwf1).
    assert (Hwf1t : {{ ⊢ Θ' }}a) by (inversion Hwf1c; subst; auto).
    destruct (a_inc_tvar_inv Hinc2') as [Ξ2 [Θt2 [-> [Hs2 Hinc2'']]]].
    rewrite Hceq.
    apply a_inc__tvar; [ | exact Hs2 ].
    apply IHHinc1; [ exact Hwa | exact Hwf1t | exact Hinc2'' ].
Qed.
