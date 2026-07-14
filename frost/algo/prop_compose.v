(** Composition of metasubstitutions  [ζ ∘ θ]  (algorithmic.tex:123-147).

    Completeness/optimality is stated up to `θ ≡ ζ ∘ θ₁` (full-algo-spec.tex:1502),
    so it needs GENERAL metasubstitutions and their composition.  Everything so
    far only ever needed the IDENTITY shorthand `⊴`, for which [a_inc_trans]
    (prop_inc.v) suffices.

    A metasubstitution is a finite MAP (algorithmic.tex:123), so composition is
    pointwise on the domain:

      (ζ ∘ θ)(α)  =  ζ(θ(α))

    and its action law is [msubst_ptyp_compose] below.  NB the action law needs a
    side condition — a variable that θ does not touch but ζ does would be treated
    differently by the two sides.  It is discharged for every type WELL-FORMED IN
    THE SOURCE context: such a type's flexible variables are exactly θ's domain,
    and its rigid variables stay rigid in the target, hence miss ζ's domain. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_flex.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Composition, and the algebra of [msubst_lookup]                       *)
(* ===================================================================== *)

Definition msubst_compose (ζ θ : metasubst) : metasubst :=
  List.map (fun e => (fst e, msubst_ptyp ζ (snd e))) θ.

Lemma dom_msubst_compose : forall ζ θ,
  dom (msubst_compose ζ θ) [=] dom θ.
Proof.
  intros ζ θ; induction θ as [ | [α τ] θ' IH ]; simpl; fsetdec.
Qed.

(** Outside its domain a metasubstitution is the identity. *)
Lemma msubst_lookup_notin : forall θ X,
  X `notin` dom θ ->
  msubst_lookup θ X = ptyp_var_f X.
Proof.
  induction θ as [ | [α τ] θ' IH ]; intros X HX; simpl in *; auto.
  destruct (X == α) as [->|Hne]; [ exfalso; clear - HX; fsetdec | ].
  apply IH. clear - HX. fsetdec.
Qed.

Lemma msubst_ptyp_notin : forall θ A,
  (forall X, X `in` ftvar_in_ptyp A -> X `notin` dom θ) ->
  msubst_ptyp θ A = A.
Proof.
  intros θ A; induction A; intros Hfr; simpl in *; f_equal; auto;
    try (apply msubst_lookup_notin; apply Hfr; simpl; fsetdec);
    try (first [ apply IHA1 | apply IHA2 | apply IHA ];
         intros X HX; apply Hfr; simpl; fsetdec).
Qed.

(** THE action law, at a variable.  The side condition is exactly what rules out
    a variable that θ misses but ζ hits. *)
Lemma msubst_lookup_compose : forall ζ θ X,
  (X `in` dom θ \/ X `notin` dom ζ) ->
  msubst_lookup (msubst_compose ζ θ) X = msubst_ptyp ζ (msubst_lookup θ X).
Proof.
  intros ζ θ; induction θ as [ | [α τ] θ' IH ]; intros X Hcond; simpl.
  - (* θ = · : X is untouched by θ, so by hypothesis ζ misses it too *)
    destruct Hcond as [Hin | Hni]; [ simpl in Hin; exfalso; clear - Hin; fsetdec | ].
    rewrite msubst_lookup_notin by exact Hni. reflexivity.
  - destruct (X == α) as [->|Hne]; [ reflexivity | ].
    apply IH.
    destruct Hcond as [Hin | Hni]; [ left | right; exact Hni ].
    simpl in Hin. clear - Hin Hne. fsetdec.
Qed.

Lemma msubst_ptyp_compose : forall ζ θ A,
  (forall X, X `in` ftvar_in_ptyp A -> X `in` dom θ \/ X `notin` dom ζ) ->
  msubst_ptyp (msubst_compose ζ θ) A = msubst_ptyp ζ (msubst_ptyp θ A).
Proof.
  intros ζ θ A; induction A; intros Hvis; simpl; f_equal; auto;
    try (apply msubst_lookup_compose; apply Hvis; simpl; fsetdec);
    try (first [ apply IHA1 | apply IHA2 | apply IHA ];
         intros X HX; apply Hvis; simpl; fsetdec).
Qed.

(* ===================================================================== *)
(*  θ's domain is EXACTLY the source's flexible variables                  *)
(* ===================================================================== *)

Lemma a_wf_aenv_uniq_local : forall Θ, a_wf_aenv Θ -> uniq Θ.
Proof. intros Θ H; induction H; solve_uniq. Qed.

(** The skeleton mirror of [a_wf_ptyp_ftv_tvarish]. *)
Lemma a_wf_pskl_ftv_tvarish : forall Θ P X,
  a_wf_pskl Θ P ->
  X `in` ftvar_in_pskl P ->
  a_binds_tvar X Θ.
Proof.
  intros Θ P X Hwf; revert X; induction Hwf; intros Y HY; simpl in HY.
  - exfalso. clear - HY. fsetdec.
  - assert (HeqY : Y = X) by (clear - HY; fsetdec). subst. exact H.
  - destruct (AtomSetImpl.union_1 HY); auto.
  - (* ∀ : the bound variable is fresh, so it is not the one we are tracking *)
    pick fresh Z for (L `union` ftvar_in_pskl P `union` singleton Y).
    assert (HYo : Y `in` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f Z))).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f Z)) as Hl.
      clear - HY Hl. fsetdec. }
    specialize (H0 Z ltac:(auto) Y HYo).
    destruct H0 as [Hb | [Hb | [τ Hb]]];
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[HeqZ ?] | Hb'];
      try (subst; exfalso; clear - Fr; fsetdec);
      [ left | right; left | right; right; exists τ ]; exact Hb'.
  - exfalso. clear - HY. fsetdec.
  - auto.
Qed.

Lemma a_wf_aenv_strip_prefix_local : forall Ξ Θ,
  a_wf_aenv (Ξ ++ Θ) -> a_wf_aenv Θ.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros Θ Hwf; simpl in *; auto.
  inversion Hwf; subst; eauto.
Qed.

Lemma a_inc_dom_flex : forall Θ θ Θ',
  Θ ≤[ θ ] Θ' ->
  forall X, X `in` dom θ -> a_flex_tvar Θ X.
Proof.
  intros Θ θ Θ' H; induction H; intros X HX; simpl in HX.
  - exfalso. clear - HX. fsetdec.
  - destruct (X == α) as [->|Hne].
    + left. unfold binds; left; reflexivity.
    + destruct (IHa_inc X ltac:(clear - HX Hne; fsetdec)) as [Hb | [τ0 Hb]];
        [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
  - destruct (X == α) as [->|Hne].
    + right. exists τ. unfold binds; left; reflexivity.
    + destruct (IHa_inc X ltac:(clear - HX Hne; fsetdec)) as [Hb | [τ0 Hb]];
        [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
  - destruct (IHa_inc X HX) as [Hb | [τ0 Hb]];
      [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
  - destruct (IHa_inc X HX) as [Hb | [τ0 Hb]];
      [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
  - destruct (IHa_inc X HX) as [Hb | [τ0 Hb]];
      [ left | right; exists τ0 ]; unfold binds; right; exact Hb.
Qed.

Lemma a_inc_flex_dom : forall Θ θ Θ',
  Θ ≤[ θ ] Θ' ->
  a_wf_aenv Θ ->
  forall X, a_flex_tvar Θ X -> X `in` dom θ.
Proof.
  intros Θ θ Θ' H; induction H; intros Hwf X Hfx; simpl.
  - destruct Hfx as [Hb | [τ Hb]]; inversion Hb.
  - inversion Hwf; subst.
    destruct (X == α) as [->|Hne]; [ clear; fsetdec | ].
    assert (Hfx' : a_flex_tvar Θ X).
    { destruct Hfx as [Hb | [τ0 Hb]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
        try (exfalso; apply Hne; exact Heq);
        [ left; exact Hb' | right; exists τ0; exact Hb' ]. }
    assert (Hd : X `in` dom θ) by (apply IHa_inc; auto).
    clear - Hd. fsetdec.
  - inversion Hwf; subst.
    destruct (X == α) as [->|Hne]; [ clear; fsetdec | ].
    assert (Hfx' : a_flex_tvar Θ X).
    { destruct Hfx as [Hb | [τ0 Hb]];
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq ?] | Hb'];
        try (exfalso; apply Hne; exact Heq);
        [ left; exact Hb' | right; exists τ0; exact Hb' ]. }
    assert (Hd : X `in` dom θ) by (apply IHa_inc; auto).
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
Lemma a_inc_tvar_notin_dom : forall Θ1 ζ Θ X,
  Θ1 ≤[ ζ ] Θ ->
  a_wf_aenv Θ1 ->
  binds X abind_tvar Θ1 ->
  X `notin` dom ζ.
Proof.
  intros Θ1 ζ Θ X Hinc Hwf Hb HX.
  pose proof (a_inc_dom_flex Hinc HX) as Hfx.
  pose proof (a_wf_aenv_uniq_local Hwf) as Hu.
  destruct Hfx as [Hb' | [τ Hb']];
    pose proof (binds_unique _ _ _ _ _ Hb Hb' Hu) as He; discriminate.
Qed.

(** THE visibility side condition, discharged for a source-well-formed type. *)
Lemma a_inc_compose_vis : forall Θ0 θ Θ1 ζ Θ,
  Θ0 ≤[ θ ] Θ1 ->
  Θ1 ≤[ ζ ] Θ ->
  a_wf_aenv Θ0 ->
  a_wf_aenv Θ1 ->
  forall X, a_binds_tvar X Θ0 ->
  X `in` dom θ \/ X `notin` dom ζ.
Proof.
  intros Θ0 θ Θ1 ζ Θ Hinc1 Hinc2 Hwf0 Hwf1 X Hbt.
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

Lemma a_inc_lookup_lc : forall Θ1 ζ Θ X,
  Θ1 ≤[ ζ ] Θ ->
  lc_ptyp (msubst_lookup ζ X).
Proof.
  intros Θ1 ζ Θ X H; revert X; induction H; intros X; simpl;
    try (apply IHa_inc).
  - constructor.
  - destruct (X == α) as [->|Hne]; [ eapply a_wf_ptyp_lc; eauto | apply IHa_inc ].
  - destruct (X == α) as [->|Hne]; [ eapply a_wf_ptyp_lc; eauto | apply IHa_inc ].
Qed.

Lemma a_inc_lookup_mono : forall Θ1 ζ Θ X,
  Θ1 ≤[ ζ ] Θ ->
  mono_ptyp (msubst_lookup ζ X).
Proof.
  intros Θ1 ζ Θ X H; revert X; induction H; intros X; simpl;
    try (apply IHa_inc).
  - constructor.
  - destruct (X == α) as [->|Hne]; [ assumption | apply IHa_inc ].
  - destruct (X == α) as [->|Hne]; [ assumption | apply IHa_inc ].
Qed.

Lemma a_inc_lookup_wf : forall Θ1 ζ Θ X,
  Θ1 ≤[ ζ ] Θ ->
  a_wf_aenv Θ1 ->
  a_binds_tvar X Θ1 ->
  a_wf_ptyp Θ (msubst_lookup ζ X).
Proof.
  intros Θ1 ζ Θ X Hinc Hwf Hbt.
  destruct (AtomSetProperties.In_dec X (dom ζ)) as [Hin | Hni].
  - (* in θ's domain : the image is well-formed in the target by construction *)
    clear Hbt. revert X Hin; induction Hinc; intros X Hin; simpl in *.
    + exfalso. clear - Hin. fsetdec.
    + destruct (X == α) as [->|Hne]; [ assumption | ].
      apply IHHinc; [ inversion Hwf; auto | clear - Hin Hne; fsetdec ].
    + destruct (X == α) as [->|Hne]; [ assumption | ].
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
  - (* outside the domain : X is a RIGID of Θ1, and rigids survive *)
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
Lemma msubst_ptyp_open_rec : forall Θ1 ζ Θ A V k,
  Θ1 ≤[ ζ ] Θ ->
  msubst_ptyp ζ (open_ptyp_wrt_ptyp_rec k V A)
  = open_ptyp_wrt_ptyp_rec k (msubst_ptyp ζ V) (msubst_ptyp ζ A).
Proof.
  intros Θ1 ζ Θ A; induction A; intros V k Hinc; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - (* a free variable's image is lc, so [open_rec] is a no-op on it *)
    symmetry.
    apply open_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp.
    apply degree_ptyp_wrt_ptyp_O.
    apply degree_ptyp_wrt_ptyp_of_lc_ptyp.
    eapply a_inc_lookup_lc; exact Hinc.
Qed.

Lemma msubst_ptyp_open : forall Θ1 ζ Θ A X,
  Θ1 ≤[ ζ ] Θ ->
  X `notin` dom ζ ->
  msubst_ptyp ζ (open_ptyp_wrt_ptyp A (ptyp_var_f X))
  = open_ptyp_wrt_ptyp (msubst_ptyp ζ A) (ptyp_var_f X).
Proof.
  intros Θ1 ζ Θ A X Hinc HX.
  unfold open_ptyp_wrt_ptyp.
  rewrite (msubst_ptyp_open_rec A (ptyp_var_f X) 0 Hinc).
  simpl. rewrite msubst_lookup_notin by exact HX. reflexivity.
Qed.

Lemma msubst_ptyp_lc : forall Θ1 ζ Θ A,
  Θ1 ≤[ ζ ] Θ ->
  lc_ptyp A ->
  lc_ptyp (msubst_ptyp ζ A).
Proof.
  intros Θ1 ζ Θ A Hinc Hlc; induction Hlc; simpl.
  - constructor.
  - eapply a_inc_lookup_lc; eauto.
  - constructor; auto.
  - (* ∀ : pick a variable outside ζ's domain and push the substitution in *)
    pick fresh X for (dom ζ).
    apply lc_ptyp_all_exists with (Xpt1 := X).
    erewrite <- msubst_ptyp_open;
      [ apply H0 | exact Hinc | clear - Fr; fsetdec ].
Qed.

(** An increase extends by a fresh rigid on both sides. *)
Lemma a_inc_cons_tvar : forall Θ1 ζ Θ X,
  Θ1 ≤[ ζ ] Θ ->
  ((X ~ abind_tvar) ++ Θ1) ≤[ ζ ] ((X ~ abind_tvar) ++ Θ).
Proof.
  intros Θ1 ζ Θ X Hinc.
  change ((X ~ abind_tvar) ++ Θ)
    with (nil ++ (X ~ abind_tvar) ++ Θ).
  apply a_inc__tvar; [ exact Hinc | apply a_suffix__nil ].
Qed.

Lemma mono_ptyp_msubst : forall Θ1 ζ Θ A,
  Θ1 ≤[ ζ ] Θ ->
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
  a_wf_aenv Θ1 ->
  forall ζ Θ, Θ1 ≤[ ζ ] Θ ->
  a_wf_ptyp Θ (msubst_ptyp ζ A).
Proof.
  intros Θ1 A Hwa; induction Hwa; intros Hwf ζ Θt Hinc; simpl.
  - apply a_wf_ptyp__unit.
  - eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact H ].
  - apply a_wf_ptyp__arrow;
      [ apply IHHwa1 | apply IHHwa2 ]; auto.
  - apply a_wf_ptyp__all
      with (L := L `union` dom ζ `union` dom Θt `union` dom Θ).
    intros X HX.
    assert (Heq : msubst_ptyp ζ (open_ptyp_wrt_ptyp A (ptyp_var_f X))
                  = open_ptyp_wrt_ptyp (msubst_ptyp ζ A) (ptyp_var_f X)).
    { eapply msubst_ptyp_open;
        [ apply a_inc_cons_tvar; exact Hinc | clear - HX; fsetdec ]. }
    rewrite <- Heq.
    apply H0;
      [ clear - HX; fsetdec
      | apply a_wf_aenv__tvar; [ clear - HX; fsetdec | exact Hwf ]
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

Lemma a_wf_aenv_def_ftv_dom : forall Θ β τ,
  a_wf_aenv Θ ->
  binds β (abind_flex_mono_def τ) Θ ->
  forall X, X `in` ftvar_in_ptyp τ -> X `in` dom Θ.
Proof.
  intros Θ β τ Hwf; induction Hwf; intros Hb X HX; simpl in *.
  - inversion Hb.
  - (* flex *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    assert (Hd : X `in` dom Θ) by (eapply IHHwf; eauto).
    clear - Hd; fsetdec.
  - (* flex_def : the definition's type is well-formed in the TAIL *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'].
    + inversion Heqb; subst.
      assert (Hbt : a_binds_tvar X Θ) by (eapply a_wf_ptyp_ftv_tvarish; eauto).
      assert (Hd : X `in` dom Θ).
      { destruct Hbt as [Hbb | [Hbb | [τd Hbb]]];
          apply binds_In in Hbb; exact Hbb. }
      clear - Hd; fsetdec.
    + assert (Hd : X `in` dom Θ) by (eapply IHHwf; eauto).
      clear - Hd; fsetdec.
  - (* var_skl *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    assert (Hd : X `in` dom Θ) by (eapply IHHwf; eauto).
    clear - Hd; fsetdec.
  - (* var_typ *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    assert (Hd : X `in` dom Θ) by (eapply IHHwf; eauto).
    clear - Hd; fsetdec.
  - (* tvar *)
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[? Heqb] | Hb'];
      [ discriminate | ].
    assert (Hd : X `in` dom Θ) by (eapply IHHwf; eauto).
    clear - Hd; fsetdec.
Qed.

(** Consequently an entry ABOVE a definition never occurs free in it. *)
Lemma a_wf_aenv_head_notin_def_ftv : forall α0 b Θ' β τ,
  a_wf_aenv ((α0 ~ b) ++ Θ') ->
  binds β (abind_flex_mono_def τ) Θ' ->
  α0 `notin` ftvar_in_ptyp τ.
Proof.
  intros α0 b Θ' β τ Hwf Hb HX.
  assert (Hnd : α0 `notin` dom Θ' /\ a_wf_aenv Θ')
    by (inversion Hwf; subst; auto).
  destruct Hnd as [Hnd Hwf'].
  apply Hnd. eapply a_wf_aenv_def_ftv_dom; eauto.
Qed.

(** Two metasubstitutions agreeing on a type's free variables act alike. *)
Lemma msubst_ptyp_agree : forall ζ ζ' A,
  (forall X, X `in` ftvar_in_ptyp A -> msubst_lookup ζ X = msubst_lookup ζ' X) ->
  msubst_ptyp ζ A = msubst_ptyp ζ' A.
Proof.
  intros ζ ζ' A; induction A; intros Hag; simpl.
  - reflexivity.
  - reflexivity.
  - (* NB do NOT [f_equal] here: both sides are [msubst_lookup _ _], and
       [f_equal] would demand [ζ = ζ'] *)
    apply Hag. simpl. fsetdec.
  - f_equal; [ apply IHA1 | apply IHA2 ];
      intros X HX; apply Hag; simpl; fsetdec.
  - f_equal. apply IHA. intros X HX; apply Hag; simpl; fsetdec.
Qed.

(** An entry the type does not mention may be dropped. *)
Lemma msubst_ptyp_cons_notin : forall α0 τ0 ζ A,
  α0 `notin` ftvar_in_ptyp A ->
  msubst_ptyp ((α0, τ0) :: ζ) A = msubst_ptyp ζ A.
Proof.
  intros α0 τ0 ζ A HA.
  apply msubst_ptyp_agree. intros X HX. simpl.
  destruct (X == α0) as [->|Hne]; [ exfalso; auto | reflexivity ].
Qed.

(* ===================================================================== *)
(*  A metasubstitution respects definitions, hence type equivalence        *)
(* ===================================================================== *)

(** A definition's own variable is not free in it. *)
Lemma a_wf_aenv_def_head_fresh : forall α τ Θ,
  a_wf_aenv ((α ~ abind_flex_mono_def τ) ++ Θ) ->
  α `notin` ftvar_in_ptyp τ.
Proof.
  intros α τ Θ Hwf HX.
  inversion Hwf as [ | | α' τ' Θ'' Hnd Hwp Hm Hwa | | | ]; subst.
  apply Hnd.
  eapply a_wf_ptyp_ftv_tvarish in HX; [ | exact Hwp ].
  destruct HX as [Hb | [Hb | [τd Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

(** ζ maps a defined variable and its definition to equivalent types.  The
    entries ABOVE the definition drop out — that is what "definitions live
    strictly below" buys. *)
Lemma a_inc_lookup_def : forall Θ1 ζ Θ,
  Θ1 ≤[ ζ ] Θ ->
  a_wf_aenv Θ1 ->
  forall α τ, binds α (abind_flex_mono_def τ) Θ1 ->
  Θ ⊢ (msubst_lookup ζ α) ≡ᵗ (msubst_ptyp ζ τ).
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
    assert (Hwf' : a_wf_aenv Θ) by (inversion Hwf; auto).
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

Lemma a_tyequiv_msubst : forall Θ1 A B,
  Θ1 ⊢ A ≡ᵗ B ->
  a_wf_aenv Θ1 ->
  forall ζ Θ, Θ1 ≤[ ζ ] Θ ->
  Θ ⊢ (msubst_ptyp ζ A) ≡ᵗ (msubst_ptyp ζ B).
Proof.
  intros Θ1 A B Heq; induction Heq; intros Hwf ζ Θt Hinc; simpl.
  - apply a_tyequiv__refl. eapply msubst_ptyp_lc; eauto.
  - apply a_tyequiv__sym. auto.
  - eapply a_tyequiv__trans; [ apply IHHeq1 | apply IHHeq2 ]; auto.
  - (* the definition-lookup rule *)
    eapply a_inc_lookup_def; eauto.
  - apply a_tyequiv__arrow; auto.
  - apply a_tyequiv__all
      with (L := L `union` dom ζ `union` dom Θt `union` dom Θ).
    intros X HX.
    (* NB [a_tyequiv__all] does NOT extend the context, unlike [a_wf_ptyp__all] *)
    assert (HeqA : msubst_ptyp ζ (open_ptyp_wrt_ptyp A (ptyp_var_f X))
                   = open_ptyp_wrt_ptyp (msubst_ptyp ζ A) (ptyp_var_f X))
      by (eapply msubst_ptyp_open; [ exact Hinc | clear - HX; fsetdec ]).
    assert (HeqB : msubst_ptyp ζ (open_ptyp_wrt_ptyp B (ptyp_var_f X))
                   = open_ptyp_wrt_ptyp (msubst_ptyp ζ B) (ptyp_var_f X))
      by (eapply msubst_ptyp_open; [ exact Hinc | clear - HX; fsetdec ]).
    rewrite <- HeqA, <- HeqB.
    apply H0; [ clear - HX; fsetdec | exact Hwf | exact Hinc ].
Qed.

(* ===================================================================== *)
(*  Mirrors for skeletons (needed by the [var_skl] binder case)            *)
(* ===================================================================== *)

Lemma msubst_pskl_agree : forall ζ ζ' P,
  (forall X, X `in` ftvar_in_pskl P -> msubst_lookup ζ X = msubst_lookup ζ' X) ->
  msubst_pskl ζ P = msubst_pskl ζ' P.
Proof.
  intros ζ ζ' P; induction P as [ | n | Y | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hag; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. apply Hag. simpl. fsetdec.
  - f_equal; [ apply IHa | apply IHb ];
      intros X HX; apply Hag; simpl; fsetdec.
  - f_equal. apply IHall. intros X HX; apply Hag; simpl; fsetdec.
  - reflexivity.
  - f_equal. apply IHt. intros X HX; apply Hag; simpl; fsetdec.
Qed.

Lemma msubst_pskl_compose : forall ζ θ P,
  (forall X, X `in` ftvar_in_pskl P -> X `in` dom θ \/ X `notin` dom ζ) ->
  msubst_pskl (msubst_compose ζ θ) P = msubst_pskl ζ (msubst_pskl θ P).
Proof.
  intros ζ θ P; induction P as [ | n | Y | Pa IHa Pb IHb | Pall IHall | | Pt IHt ];
    intros Hvis; simpl.
  - reflexivity.
  - reflexivity.
  - (* a variable : its image is a monotype, and [ptyp_to_pskl] commutes with
       the substitution *)
    rewrite msubst_lookup_compose by (apply Hvis; simpl; fsetdec).
    generalize (msubst_lookup θ Y); intros τ.
    induction τ; simpl; f_equal; auto.
  - f_equal; [ apply IHa | apply IHb ];
      intros X HX; apply Hvis; simpl; fsetdec.
  - f_equal. apply IHall. intros X HX; apply Hvis; simpl; fsetdec.
  - reflexivity.
  - f_equal. apply IHt. intros X HX; apply Hvis; simpl; fsetdec.
Qed.

(* ===================================================================== *)
(*  Peeling the fresh flexible suffix a binder rule adds to the target     *)
(* ===================================================================== *)

Lemma msubst_lookup_app_notin : forall ζ1 ζ2 X,
  X `notin` dom ζ1 ->
  msubst_lookup (ζ1 ++ ζ2) X = msubst_lookup ζ2 X.
Proof.
  induction ζ1 as [ | [α τ] ζ1' IH ]; intros ζ2 X HX; simpl in *; auto.
  destruct (X == α) as [->|Hne]; [ exfalso; clear - HX; fsetdec | ].
  apply IH. clear - HX. fsetdec.
Qed.

(** The binder rules of [a_inc] prepend an all-flexible Ξ to the TARGET.  When
    that target is in turn increased, ζ splits along Ξ. *)
Lemma a_inc_peel_suffix : forall Ξ Θ ζ Θ',
  a_suffix Ξ ->
  (Ξ ++ Θ) ≤[ ζ ] Θ' ->
  exists ζ1 ζ2,
    ζ = ζ1 ++ ζ2 /\ dom ζ1 [=] dom Ξ /\ Θ ≤[ ζ2 ] Θ'.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros Θ ζ Θ' Hsuf Hinc.
  - exists nil, ζ. simpl in *.
    split; [ reflexivity | split; [ clear; fsetdec | exact Hinc ] ].
  - inversion Hsuf as [ | ? ? ? Hsuf' Hb ]; subst.
    inversion Hb; subst; simpl in Hinc.
    + (* a flexible entry *)
      inversion Hinc as [ | Θa θa Θb αa τa Hi Hw Hm | | | | ]; subst.
      destruct (IH _ _ _ Hsuf' Hi) as [ζ1 [ζ2 [-> [Hd Hinc2]]]].
      exists ((a, τa) :: ζ1), ζ2. simpl.
      split; [ reflexivity | ].
      split; [ rewrite Hd; clear; fsetdec | exact Hinc2 ].
    + (* a defined flexible entry *)
      inversion Hinc as [ | | Θa θa Θb αa τa τb Hi Hw Hm He | | | ]; subst.
      destruct (IH _ _ _ Hsuf' Hi) as [ζ1 [ζ2 [-> [Hd Hinc2]]]].
      exists ((a, τb) :: ζ1), ζ2. simpl.
      split; [ reflexivity | ].
      split; [ rewrite Hd; clear; fsetdec | exact Hinc2 ].
Qed.

(** θ's images live in θ's target. *)
Lemma a_inc_entry_ftv : forall Θs θ Θt,
  Θs ≤[ θ ] Θt ->
  forall β τ, List.In (β, τ) θ ->
  forall X, X `in` ftvar_in_ptyp τ -> X `in` dom Θt.
Proof.
  intros Θs θ Θt H; induction H; intros β τ0 Hin X HX; simpl in *.
  - inversion Hin.
  - destruct Hin as [Heq | Hin]; [ inversion Heq; subst | eauto ].
    assert (Hbt : a_binds_tvar X Θ') by (eapply a_wf_ptyp_ftv_tvarish; eauto).
    destruct Hbt as [Hb | [Hb | [τd Hb]]]; apply binds_In in Hb; exact Hb.
  - destruct Hin as [Heq | Hin]; [ inversion Heq; subst | eauto ].
    assert (Hbt : a_binds_tvar X Θ') by (eapply a_wf_ptyp_ftv_tvarish; eauto).
    destruct Hbt as [Hb | [Hb | [τd Hb]]]; apply binds_In in Hb; exact Hb.
  - assert (Hd : X `in` dom Θ') by eauto.
    clear - Hd. simpl_env. fsetdec.
  - assert (Hd : X `in` dom Θ') by eauto.
    clear - Hd. simpl_env. fsetdec.
  - assert (Hd : X `in` dom Θ') by eauto.
    clear - Hd. simpl_env. fsetdec.
Qed.

(** Hence ζ and its Ξ-peeled part act alike on θ's images. *)
Lemma msubst_compose_peel : forall Θs θ Θt ζ1 ζ2,
  Θs ≤[ θ ] Θt ->
  (forall X, X `in` dom ζ1 -> X `notin` dom Θt) ->
  msubst_compose (ζ1 ++ ζ2) θ = msubst_compose ζ2 θ.
Proof.
  intros Θs θ Θt ζ1 ζ2 Hinc Hdisj.
  unfold msubst_compose. apply List.map_ext_in.
  intros [β τ] Hin. simpl. f_equal.
  apply msubst_ptyp_agree. intros X HX.
  apply msubst_lookup_app_notin.
  intro Hc. apply (Hdisj X Hc).
  eapply a_inc_entry_ftv; eauto.
Qed.

(* ===================================================================== *)
(*  COMPOSITION OF INCREASES  (the paper's [ζ ∘ θ₁])                       *)
(* ===================================================================== *)

Lemma a_inc_compose : forall Θ0 θ Θ1,
  Θ0 ≤[ θ ] Θ1 ->
  a_wf_aenv Θ0 ->
  a_wf_aenv Θ1 ->
  forall ζ Θ, Θ1 ≤[ ζ ] Θ ->
  Θ0 ≤[ msubst_compose ζ θ ] Θ.
Proof.
  intros Θ0 θ Θ1 Hinc1; induction Hinc1;
    intros Hwf0 Hwf1 ζ Θt Hinc2.
  - (* · ≤[ι] Ξ : the target of an all-flexible source is all-flexible *)
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
    + (* Θ ⊢ ζτ' ≡ (ζ∘θ)τ,  from  Θ1 ⊢ τ' ≡ θτ  by [a_tyequiv_msubst] *)
      rewrite msubst_ptyp_compose.
      * eapply a_tyequiv_msubst; eauto.
      * intros X HX.
        eapply a_inc_compose_vis;
          [ exact Hinc1 | exact Hinc2 | exact Hwa | exact Hwf1 | ].
        eapply a_wf_ptyp_ftv_tvarish; eauto.
  - (* term variable (type) : peel the fresh suffix, then rebuild *)
    inversion Hwf0 as [ | | | | xh Ah Θh Hnd Hwp Hwa | ]; subst.
    assert (Hpeel : exists ζ1 ζ2, ζ = ζ1 ++ ζ2 /\ dom ζ1 [=] dom Ξ /\
              ((x ~ abind_var_typ (msubst_ptyp θ A)) ++ Θ') ≤[ ζ2 ] Θt)
      by (eapply a_inc_peel_suffix; [ eassumption | exact Hinc2 ]).
    destruct Hpeel as [ζ1 [ζ2 [-> [Hd Hinc2']]]].
    assert (Hu1 : uniq (Ξ ++ (x ~ abind_var_typ (msubst_ptyp θ A)) ++ Θ'))
      by (apply a_wf_aenv_uniq_local; exact Hwf1).
    assert (Hdisj : forall X, X `in` dom ζ1 -> X `notin` dom Θ').
    { intros X HX. rewrite Hd in HX. clear - Hu1 HX. solve_uniq. }
    assert (Hceq : msubst_compose (ζ1 ++ ζ2) θ = msubst_compose ζ2 θ)
      by (eapply msubst_compose_peel; eauto).
    assert (Hwf1c : a_wf_aenv ((x ~ abind_var_typ (msubst_ptyp θ A)) ++ Θ'))
      by (eapply a_wf_aenv_strip_prefix_local; exact Hwf1).
    assert (Hwf1t : a_wf_aenv Θ') by (inversion Hwf1c; subst; auto).
    destruct (a_inc_var_inv Hinc2') as [Ξ2 [Θt2 [-> [Hs2 Hinc2'']]]].
    rewrite Hceq.
    assert (HA : msubst_ptyp (msubst_compose ζ2 θ) A
                 = msubst_ptyp ζ2 (msubst_ptyp θ A)).
    { apply msubst_ptyp_compose. intros X HX.
      eapply a_inc_compose_vis;
        [ exact Hinc1 | exact Hinc2'' | exact Hwa | exact Hwf1t
        | eapply a_wf_ptyp_ftv_tvarish; eauto ]. }
    rewrite <- HA.
    apply a_inc__var; [ | exact Hs2 ].
    apply IHHinc1; [ exact Hwa | exact Hwf1t | exact Hinc2'' ].
  - (* term variable (skeleton) : same shape, on skeletons *)
    inversion Hwf0 as [ | | | xh Ph Θh Hnd Hwp Hwa | | ]; subst.
    assert (Hpeel : exists ζ1 ζ2, ζ = ζ1 ++ ζ2 /\ dom ζ1 [=] dom Ξ /\
              ((x ~ abind_var_skl (msubst_pskl θ P)) ++ Θ') ≤[ ζ2 ] Θt)
      by (eapply a_inc_peel_suffix; [ eassumption | exact Hinc2 ]).
    destruct Hpeel as [ζ1 [ζ2 [-> [Hd Hinc2']]]].
    assert (Hu1 : uniq (Ξ ++ (x ~ abind_var_skl (msubst_pskl θ P)) ++ Θ'))
      by (apply a_wf_aenv_uniq_local; exact Hwf1).
    assert (Hdisj : forall X, X `in` dom ζ1 -> X `notin` dom Θ').
    { intros X HX. rewrite Hd in HX. clear - Hu1 HX. solve_uniq. }
    assert (Hceq : msubst_compose (ζ1 ++ ζ2) θ = msubst_compose ζ2 θ)
      by (eapply msubst_compose_peel; eauto).
    assert (Hwf1c : a_wf_aenv ((x ~ abind_var_skl (msubst_pskl θ P)) ++ Θ'))
      by (eapply a_wf_aenv_strip_prefix_local; exact Hwf1).
    assert (Hwf1t : a_wf_aenv Θ') by (inversion Hwf1c; subst; auto).
    destruct (a_inc_var_skl_inv Hinc2') as [Ξ2 [Θt2 [-> [Hs2 Hinc2'']]]].
    rewrite Hceq.
    assert (HP : msubst_pskl (msubst_compose ζ2 θ) P
                 = msubst_pskl ζ2 (msubst_pskl θ P)).
    { apply msubst_pskl_compose. intros X HX.
      eapply a_inc_compose_vis;
        [ exact Hinc1 | exact Hinc2'' | exact Hwa | exact Hwf1t
        | eapply a_wf_pskl_ftv_tvarish; eauto ]. }
    rewrite <- HP.
    apply a_inc__var_skl; [ | exact Hs2 ].
    apply IHHinc1; [ exact Hwa | exact Hwf1t | exact Hinc2'' ].
  - (* rigid *)
    inversion Hwf0 as [ | | | | | αh Θh Hnd Hwa ]; subst.
    assert (Hpeel : exists ζ1 ζ2, ζ = ζ1 ++ ζ2 /\ dom ζ1 [=] dom Ξ /\
              ((α ~ abind_tvar) ++ Θ') ≤[ ζ2 ] Θt)
      by (eapply a_inc_peel_suffix; [ eassumption | exact Hinc2 ]).
    destruct Hpeel as [ζ1 [ζ2 [-> [Hd Hinc2']]]].
    assert (Hu1 : uniq (Ξ ++ (α ~ abind_tvar) ++ Θ'))
      by (apply a_wf_aenv_uniq_local; exact Hwf1).
    assert (Hdisj : forall X, X `in` dom ζ1 -> X `notin` dom Θ').
    { intros X HX. rewrite Hd in HX. clear - Hu1 HX. solve_uniq. }
    assert (Hceq : msubst_compose (ζ1 ++ ζ2) θ = msubst_compose ζ2 θ)
      by (eapply msubst_compose_peel; eauto).
    assert (Hwf1c : a_wf_aenv ((α ~ abind_tvar) ++ Θ'))
      by (eapply a_wf_aenv_strip_prefix_local; exact Hwf1).
    assert (Hwf1t : a_wf_aenv Θ') by (inversion Hwf1c; subst; auto).
    destruct (a_inc_tvar_inv Hinc2') as [Ξ2 [Θt2 [-> [Hs2 Hinc2'']]]].
    rewrite Hceq.
    apply a_inc__tvar; [ | exact Hs2 ].
    apply IHHinc1; [ exact Hwa | exact Hwf1t | exact Hinc2'' ].
Qed.
