(** TAGGED SUBJECT EQUIVALENCE [Θ ⊢ R ≡ᵘ R'] and its msubst generation.

    P7b's Sub-Arrow (and later ForallR / P7a) re-enter the induction after a
    consistency/subtyping run has advanced the context Θ0 to Θ1: the paper
    silently swaps the solution's metasubstitution θ for the package's θ1
    ("I used type equivalence a bit informally" — the author's own margin
    note at completeSubtyping).  The two subjects [msubst κ R] and
    [msubst σ R] are then only EQUIVALENT — same skeleton, ≡ᵗ-monotype
    paintings at the flexible leaves — never equal.

    The motive absorbs this by carrying the join at an arbitrary subject [T]
    with [Θ ⊢ T ≡ᵘ msubst κ R] (see prop_sub_complete_thm.v): the IH then
    takes the ORIGINAL join derivation unchanged, and only the consistency
    LEAVES ever transport — via the erasure of ≡ᵘ into ≡ˢ and the EXISTING
    pskl-level transports (skl_tyequiv_{consis,refine_syn_f,refine_pskl_f}_
    transport, prop_consis_complete.v).

    Design notes:
    - STRUCTURAL rows only (no sym/trans/refl closure): inversion at a known
      subject shape must stay trivial.  Reflexivity/symmetry are lemmas.
    - The one non-congruence row is [__mono]: paintings of ≡ᵗ monotypes.
      It carries wf AT THE RELATION'S OWN Θ so that a later substitution
      lemma (ForallL) can keep the leaves clear of the substituted variable.
    - Binder rows keep the SAME Θ (mirroring ≡ˢ's [__all]); transports pass
      a binds-monotone context parameter instead. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.prop_inc.            (* a_tyequiv_pskl *)
Require Import src.frost.algo.prop_compose.        (* a_inc_lookup_{wf,mono}, msubst_lookup_notin *)
Require Import src.frost.algo.prop_normal.         (* a_inc_equiv_lookup *)
Require Import src.frost.algo.prop_pat_sub.        (* uskl_to_pskl_ptyp_to_uskl_syn *)
Require Import src.frost.algo.prop_consis_sound.   (* uskl_to_pskl_open *)
Require Import src.frost.algo.prop_look_complete_cstr. (* msubst_uskl_syn_open *)

Set Implicit Arguments.

Reserved Notation "Θ ⊢ R1 ≡ᵘ R2"
  (at level 75, R1 at level 74, R2 at level 74, no associativity).

Inductive a_uskl_tyequiv (Θ : aenv) : uskl -> uskl -> Prop :=
| a_uskl_tyequiv__mono : forall τ1 τ2,
    mono_ptyp τ1 -> mono_ptyp τ2 ->
    a_wf_ptyp Θ τ1 -> a_wf_ptyp Θ τ2 ->
    Θ ⊢ τ1 ≡ᵗ τ2 ->
    Θ ⊢ (ptyp_to_uskl_syn τ1) ≡ᵘ (ptyp_to_uskl_syn τ2)
| a_uskl_tyequiv__unit :
    Θ ⊢ uskl_unit ≡ᵘ uskl_unit
| a_uskl_tyequiv__var : forall α,
    Θ ⊢ (uskl_var_f α) ≡ᵘ (uskl_var_f α)
| a_uskl_tyequiv__arrow : forall R1 R2 R1' R2',
    Θ ⊢ R1 ≡ᵘ R1' ->
    Θ ⊢ R2 ≡ᵘ R2' ->
    Θ ⊢ (uskl_arrow R1 R2) ≡ᵘ (uskl_arrow R1' R2')
| a_uskl_tyequiv__all_syn : forall L R R',
    (forall α, α `notin` L ->
       Θ ⊢ (open_uskl_wrt_uskl R (uskl_var_f α)) ≡ᵘ
           (open_uskl_wrt_uskl R' (uskl_var_f α))) ->
    Θ ⊢ (uskl_all_syn R) ≡ᵘ (uskl_all_syn R')
| a_uskl_tyequiv__all_etag : forall L ε R R',
    (forall α, α `notin` L ->
       Θ ⊢ (open_uskl_wrt_uskl R (uskl_var_f α)) ≡ᵘ
           (open_uskl_wrt_uskl R' (uskl_var_f α))) ->
    Θ ⊢ (uskl_all_etag ε R) ≡ᵘ (uskl_all_etag ε R')
| a_uskl_tyequiv__hole :
    Θ ⊢ uskl_hole ≡ᵘ uskl_hole
| a_uskl_tyequiv__holeg :
    Θ ⊢ uskl_holeg ≡ᵘ uskl_holeg
| a_uskl_tyequiv__tophole : forall R R',
    Θ ⊢ R ≡ᵘ R' ->
    Θ ⊢ (uskl_tophole R) ≡ᵘ (uskl_tophole R')
| a_uskl_tyequiv__topholeg : forall R R',
    Θ ⊢ R ≡ᵘ R' ->
    Θ ⊢ (uskl_topholeg R) ≡ᵘ (uskl_topholeg R')
where "Θ ⊢ R1 ≡ᵘ R2" := (a_uskl_tyequiv Θ R1 R2) : type_scope.

(* ===================================================================== *)
(*  Reflexivity (from local closure) and symmetry                          *)
(* ===================================================================== *)

Lemma a_uskl_tyequiv_refl : forall Θ R,
  lc_uskl R ->
  Θ ⊢ R ≡ᵘ R.
Proof.
  intros Θ R Hlc; induction Hlc;
    try (apply a_uskl_tyequiv__all_syn with (L := empty); intros α _; auto);
    try (apply a_uskl_tyequiv__all_etag with (L := empty); intros α _; auto);
    eauto using a_uskl_tyequiv.
Qed.

Lemma a_uskl_tyequiv_sym : forall Θ R R',
  Θ ⊢ R ≡ᵘ R' ->
  Θ ⊢ R' ≡ᵘ R.
Proof.
  intros Θ R R' H; induction H;
    try (apply a_uskl_tyequiv__all_syn with (L := L); intros α Hα; auto);
    try (apply a_uskl_tyequiv__all_etag with (L := L); intros α Hα; auto);
    eauto using a_uskl_tyequiv, a_tyequiv__sym.
Qed.

(* ===================================================================== *)
(*  Erasure: ≡ᵘ projects onto ≡ˢ                                          *)
(* ===================================================================== *)

Lemma a_uskl_tyequiv_erase : forall Θ R R',
  Θ ⊢ R ≡ᵘ R' ->
  Θ ⊢ ⌊ R ⌋ˢ ≡ˢ ⌊ R' ⌋ˢ.
Proof.
  intros Θ R R' H; induction H; cbn.
  - (* mono paintings erase to the type's own skeleton *)
    rewrite !uskl_to_pskl_ptyp_to_uskl_syn.
    apply a_tyequiv_pskl; assumption.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_unit.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_var_f.
  - apply a_pskl_tyequiv__arrow; assumption.
  - apply a_pskl_tyequiv__all with (L := L); intros α Hα.
    rewrite <- !uskl_to_pskl_open. auto.
  - apply a_pskl_tyequiv__all with (L := L); intros α Hα.
    rewrite <- !uskl_to_pskl_open. auto.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_hole.
  - apply a_pskl_tyequiv__refl; apply lc_pskl_hole.
  - apply a_pskl_tyequiv__tophole; assumption.
  - apply a_pskl_tyequiv__tophole; assumption.
Qed.

(* ===================================================================== *)
(*  Generation: equivalent metasubstitutions give ≡ᵘ images                *)
(* ===================================================================== *)

(** The workhorse.  [R] is the unresolved subject; every free variable is
    either Θ0-bound (where the a_inc kit supplies the leaf facts) or seen by
    NEITHER metasubstitution (the fresh binder-openers).  Stated with BOTH
    increases so wf / mono / ≡ᵗ of the images read off the kit. *)
Lemma a_inc_equiv_msubst_uskl : forall Θ0 κ σ Θ R,
  lc_uskl R ->
  (forall α, α `in` ftvar_in_uskl R ->
     a_binds_tvar α Θ0 \/ (α `notin` dom κ /\ α `notin` dom σ)) ->
  a_inc_equiv Θ0 κ σ Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  σ ∷ Θ0 ⊑ Θ ->
  a_wf_aenv Θ0 ->
  Θ ⊢ (msubst_uskl_syn κ R) ≡ᵘ (msubst_uskl_syn σ R).
Proof.
  intros Θ0 κ σ Θ R Hlc; revert Θ0 κ σ Θ.
  induction Hlc; intros Θ0 κ σ Θ Hftv Hie Hincκ Hincσ Hwf0; cbn.
  - (* unit *) apply a_uskl_tyequiv__unit.
  - (* var_f α *)
    destruct (Hftv α ltac:(cbn; fsetdec)) as [Hbt | [Hκ Hσ]].
    + apply a_uskl_tyequiv__mono;
        [ eapply a_inc_lookup_mono; exact Hincκ
        | eapply a_inc_lookup_mono; exact Hincσ
        | eapply a_inc_lookup_wf; eassumption
        | eapply a_inc_lookup_wf; eassumption
        | eapply a_inc_equiv_lookup; eassumption ].
    + rewrite (msubst_lookup_notin κ Hκ), (msubst_lookup_notin σ Hσ).
      cbn. apply a_uskl_tyequiv__var.
  - (* arrow *)
    apply a_uskl_tyequiv__arrow;
      [ eapply IHHlc1 | eapply IHHlc2 ]; try eassumption;
      intros α Hα; apply Hftv; cbn; clear - Hα; fsetdec.
  - (* all_syn *)
    apply a_uskl_tyequiv__all_syn with (L := dom κ `union` dom σ).
    intros α Hα.
    assert (Hoκ : msubst_uskl_syn κ (open_uskl_wrt_uskl R (uskl_var_f α))
                  = open_uskl_wrt_uskl (msubst_uskl_syn κ R) (uskl_var_f α))
      by (eapply msubst_uskl_syn_open;
          [ exact Hincκ | clear - Hα; fsetdec ]).
    assert (Hoσ : msubst_uskl_syn σ (open_uskl_wrt_uskl R (uskl_var_f α))
                  = open_uskl_wrt_uskl (msubst_uskl_syn σ R) (uskl_var_f α))
      by (eapply msubst_uskl_syn_open;
          [ exact Hincσ | clear - Hα; fsetdec ]).
    rewrite <- Hoκ, <- Hoσ.
    eapply H0; try eassumption.
    intros β Hβ.
    destruct (β == α) as [-> | Hne].
    + right. split; clear - Hα; fsetdec.
    + apply Hftv.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                    R (uskl_var_f α)) as Hup.
      cbn in Hup. clear - Hβ Hne Hup.
      assert (Hd : β `in` (singleton α `union` ftvar_in_uskl R)) by fsetdec.
      apply union_1 in Hd; destruct Hd as [Hd | Hd];
        [ exfalso; apply Hne; apply singleton_1 in Hd; auto | exact Hd ].
  - (* all_etag *)
    apply a_uskl_tyequiv__all_etag with (L := dom κ `union` dom σ).
    intros α Hα.
    assert (Hoκ : msubst_uskl_syn κ (open_uskl_wrt_uskl R (uskl_var_f α))
                  = open_uskl_wrt_uskl (msubst_uskl_syn κ R) (uskl_var_f α))
      by (eapply msubst_uskl_syn_open;
          [ exact Hincκ | clear - Hα; fsetdec ]).
    assert (Hoσ : msubst_uskl_syn σ (open_uskl_wrt_uskl R (uskl_var_f α))
                  = open_uskl_wrt_uskl (msubst_uskl_syn σ R) (uskl_var_f α))
      by (eapply msubst_uskl_syn_open;
          [ exact Hincσ | clear - Hα; fsetdec ]).
    rewrite <- Hoκ, <- Hoσ.
    eapply H0; try eassumption.
    intros β Hβ.
    destruct (β == α) as [-> | Hne].
    + right. split; clear - Hα; fsetdec.
    + apply Hftv.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                    R (uskl_var_f α)) as Hup.
      cbn in Hup. clear - Hβ Hne Hup.
      assert (Hd : β `in` (singleton α `union` ftvar_in_uskl R)) by fsetdec.
      apply union_1 in Hd; destruct Hd as [Hd | Hd];
        [ exfalso; apply Hne; apply singleton_1 in Hd; auto | exact Hd ].
  - (* hole *) apply a_uskl_tyequiv__hole.
  - (* tophole *) apply a_uskl_tyequiv__tophole; eauto.
  - (* holeg *) apply a_uskl_tyequiv__holeg.
  - (* topholeg *) apply a_uskl_tyequiv__topholeg; eauto.
Qed.

(* ===================================================================== *)
(*  Small inversions and transports the motive's rows read off             *)
(* ===================================================================== *)

(** A ghost is ≡ᵘ-inert: mono paintings are never ghosts. *)
Lemma a_uskl_tyequiv_hole_l_inv : forall Θ R',
  Θ ⊢ uskl_hole ≡ᵘ R' ->
  R' = uskl_hole.
Proof.
  intros Θ R' H; inversion H; subst; try reflexivity.
  destruct τ1; cbn in *; discriminate.
Qed.

Lemma a_uskl_tyequiv_holeg_l_inv : forall Θ R',
  Θ ⊢ uskl_holeg ≡ᵘ R' ->
  R' = uskl_holeg.
Proof.
  intros Θ R' H; inversion H; subst; try reflexivity.
  destruct τ1; cbn in *; discriminate.
Qed.

(** Both sides of ≡ᵘ are locally closed. *)
Lemma a_uskl_tyequiv_lc : forall Θ R R',
  Θ ⊢ R ≡ᵘ R' ->
  lc_uskl R /\ lc_uskl R'.
Proof.
  intros Θ R R' H; induction H.
  - split; apply mono_ptyp_to_uskl_syn_lc; assumption.
  - split; apply lc_uskl_unit.
  - split; apply lc_uskl_var_f.
  - destruct IHa_uskl_tyequiv1, IHa_uskl_tyequiv2.
    split; apply lc_uskl_arrow; assumption.
  - pick fresh α. destruct (H0 α ltac:(clear - Fr; fsetdec)) as [Hl Hr].
    split; [ eapply lc_uskl_all_syn_exists; exact Hl
           | eapply lc_uskl_all_syn_exists; exact Hr ].
  - pick fresh α. destruct (H0 α ltac:(clear - Fr; fsetdec)) as [Hl Hr].
    split; [ eapply lc_uskl_all_etag_exists; exact Hl
           | eapply lc_uskl_all_etag_exists; exact Hr ].
  - split; apply lc_uskl_hole.
  - split; apply lc_uskl_holeg.
  - destruct IHa_uskl_tyequiv. split; apply lc_uskl_tophole; assumption.
  - destruct IHa_uskl_tyequiv. split; apply lc_uskl_topholeg; assumption.
Qed.

(** A monotype's painting is guarded (its head is unit / var / arrow). *)
Lemma guarded_ptyp_to_uskl_syn : forall τ,
  mono_ptyp τ ->
  guarded_uskl (ptyp_to_uskl_syn τ).
Proof.
  intros τ Hm; destruct Hm; cbn.
  - apply guarded_uskl__unit.
  - apply guarded_uskl__var.
  - apply guarded_uskl__arrow;
      apply mono_ptyp_to_uskl_syn_lc; assumption.
Qed.

(** Guardedness transports along ≡ᵘ (only the head matters, and a guarded
    head is congruent or a mono painting on both sides). *)
Lemma a_uskl_tyequiv_guarded : forall Θ R R',
  Θ ⊢ R ≡ᵘ R' ->
  guarded_uskl R ->
  guarded_uskl R'.
Proof.
  intros Θ R R' H Hg; inversion H; subst.
  - (* mono row: any monotype painting is guarded *)
    apply guarded_ptyp_to_uskl_syn; assumption.
  - apply guarded_uskl__unit.
  - apply guarded_uskl__var.
  - (* arrow congruence: the components' lc comes from the relation *)
    match goal with
    | H1 : _ ⊢ _ ≡ᵘ ?A, H2 : _ ⊢ _ ≡ᵘ ?B
      |- guarded_uskl (uskl_arrow ?A ?B) =>
        apply guarded_uskl__arrow;
        [ exact (proj2 (a_uskl_tyequiv_lc H1))
        | exact (proj2 (a_uskl_tyequiv_lc H2)) ]
    end.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
  - inversion Hg.
Qed.
