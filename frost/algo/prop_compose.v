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
