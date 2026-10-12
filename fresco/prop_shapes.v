Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Export src.fresco.prop_coercions.

Set Implicit Arguments.

Lemma is_ityp_lc : forall B, is_ityp B -> lc_btyp B.
Proof.
  intros B H. induction H; eauto.
Qed.

Lemma is_styp_lc : forall B, is_styp B -> lc_btyp B.
Proof.
  intros B H. induction H; eauto.
Qed.

Lemma is_dtyp_lc : forall C, is_dtyp C -> lc_utyp C.
Proof.
  intros C H. induction H; eauto.
Qed.

Lemma pskl_eq_dec : forall (P Q : pskl), sumbool (P = Q) (P <> Q).
Proof.
  decide equality; solve [ apply Nat.eq_dec | apply eq_var ].
Qed.

Lemma pskl_var_dec : forall P,
  (exists α, P = pskl_var_f α) \/ (forall α, P <> pskl_var_f α).
Proof.
  destruct P;
    first [ left; eexists; reflexivity
          | right; intros ? Hcx; discriminate Hcx ].
Qed.

Unset Implicit Arguments.

Lemma ptyp_to_pskl_ghost_free : forall A, pskl_ghost_free (ptyp_to_pskl A).
Proof. induction A; simpl; auto. Qed.

Lemma pskl_ghost_free_to_ptyp : forall P,
  pskl_ghost_free P -> exists A, P = ptyp_to_pskl A.
Proof.
  induction P; simpl; intros Hg; try contradiction.
  - exists ptyp_unit; reflexivity.
  - exists (ptyp_var_b n); reflexivity.
  - exists (ptyp_var_f α); reflexivity.
  - destruct Hg as [Hg1 Hg2].
    destruct (IHP1 Hg1) as [A1 ->]; destruct (IHP2 Hg2) as [A2 ->].
    exists (ptyp_arrow A1 A2); reflexivity.
  - destruct (IHP Hg) as [A ->]. exists (ptyp_all A); reflexivity.
Qed.

Lemma pskl_ghost_free_open_rec_gen : forall P P' k,
  pskl_ghost_free P -> pskl_ghost_free P' ->
  pskl_ghost_free (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k Hg Hg'; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma pskl_ghost_free_open_gen : forall P P',
  pskl_ghost_free P -> pskl_ghost_free P' ->
  pskl_ghost_free (open_pskl_wrt_pskl P P').
Proof. intros P P' Hg Hg'; apply pskl_ghost_free_open_rec_gen; assumption. Qed.

Lemma pskl_ghost_free_open_rec : forall P α' k,
  pskl_ghost_free P ->
  pskl_ghost_free (open_pskl_wrt_pskl_rec k (pskl_var_f α') P).
Proof. intros; apply pskl_ghost_free_open_rec_gen; simpl; auto. Qed.

Lemma pskl_ghost_free_open : forall P α',
  pskl_ghost_free P ->
  pskl_ghost_free (open_pskl_wrt_pskl P (pskl_var_f α')).
Proof. intros; apply pskl_ghost_free_open_gen; simpl; auto. Qed.

Lemma pskl_ghost_free_close_rec : forall P α k,
  pskl_ghost_free P ->
  pskl_ghost_free (close_pskl_wrt_pskl_rec k α P).
Proof.
  induction P; intros α0 k Hg; simpl in *; try contradiction; auto.
  - destruct (lt_ge_dec n k); simpl; auto.
  - destruct_if; simpl; auto.
  - destruct Hg as [Hg1 Hg2]; split; auto.
Qed.

Lemma pskl_ghost_free_close : forall P α,
  pskl_ghost_free P -> pskl_ghost_free (close_pskl_wrt_pskl α P).
Proof. intros P α Hg; apply pskl_ghost_free_close_rec; exact Hg. Qed.

Lemma pskl_ghost_free_subst : forall P P' β,
  pskl_ghost_free P -> pskl_ghost_free P' ->
  pskl_ghost_free (subst_pskl_in_pskl P' β P).
Proof.
  induction P; intros P' β Hg Hg'; simpl in *; intuition.
  destruct_if; simpl; auto.
Qed.

Lemma pskl_ghost_free_subst_var : forall P α β,
  pskl_ghost_free P ->
  pskl_ghost_free (subst_pskl_in_pskl (pskl_var_f α) β P).
Proof. intros P α β Hg; apply pskl_ghost_free_subst; [ exact Hg | exact I ]. Qed.

Lemma bskl_ghost_free_open_rec : forall Q α' k,
  bskl_ghost_free Q ->
  bskl_ghost_free (open_bskl_wrt_bskl_rec k (bskl_var_f α') Q).
Proof.
  induction Q; intros α' k Hg; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma pskl_to_bskl_inh_ghost_free : forall P,
  pskl_ghost_free P ->
  bskl_ghost_free (pskl_to_bskl_inh P).
Proof. induction P; simpl; intuition. Qed.

Lemma pskl_to_bskl_syn_ghost_free : forall P,
  pskl_ghost_free P ->
  bskl_ghost_free (pskl_to_bskl_syn P).
Proof. induction P; simpl; intuition. Qed.

Lemma is_iskl_pskl_to_bskl_inh : forall P,
  lc_pskl P -> is_iskl (pskl_to_bskl_inh P).
Proof.
  intros P Hlc; induction Hlc; simpl; try solve [ constructor; auto ].
  apply is_iskl__all with (L := {}). intros α _.
  rewrite <- pskl_to_bskl_inh_open. auto.
Qed.

Ltac ghost_free_auto :=
  solve [ assumption
        | apply ptyp_to_pskl_ghost_free
        | (apply pskl_ghost_free_subst_var; ghost_free_auto)
        | (apply pskl_ghost_free_open; ghost_free_auto)
        | (apply pskl_ghost_free_close; ghost_free_auto)
        | (apply pskl_ghost_free_subst; ghost_free_auto)
        | (simpl; intuition) ].

Lemma pskl_ghost_free_open_rec_inv : forall P P' k,
  pskl_ghost_free (open_pskl_wrt_pskl_rec k P' P) ->
  pskl_ghost_free P.
Proof.
  induction P; intros P' k Hg; simpl in *; auto.
  - destruct Hg as [Hg1 Hg2]; split; eauto.
  - eauto.
Qed.

Lemma pskl_ghost_free_dec : forall P,
  sumbool (pskl_ghost_free P) (~ pskl_ghost_free P).
Proof.
  induction P; simpl;
    try solve [ left; exact I | right; auto ].
  - destruct IHP1 as [H1 | H1]; [ | right; tauto ].
    destruct IHP2 as [H2 | H2]; [ left; split; assumption | right; tauto ].
  - exact IHP.
Qed.

Lemma mod_comp_ty_tc_inv : forall B, mod_comp_ty B mode_tc -> is_ityp B.
Proof. intros B H. inversion H; subst; assumption. Qed.

Lemma pskl_no_ghost_open_rec : forall P P' k,
  pskl_no_ghost P -> pskl_no_ghost P' ->
  pskl_no_ghost (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k HP HV; simpl in *; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
  - destruct HP; split; auto.
Qed.

Lemma pskl_no_ghost_open : forall P α,
  pskl_no_ghost P ->
  pskl_no_ghost (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof.
  intros P α HP. apply pskl_no_ghost_open_rec; simpl; auto.
Qed.

Set Implicit Arguments.

Lemma mono_ptyp_to_btyp_syn_lc : forall τ,
  mono_ptyp τ -> lc_btyp (ptyp_to_btyp_syn τ).
Proof. induction 1; simpl; auto. Qed.

Lemma mono_ptyp_to_utyp_syn_lc : forall τ,
  mono_ptyp τ -> lc_utyp (ptyp_to_utyp_syn τ).
Proof. induction 1; simpl; auto. Qed.

Lemma mono_ptyp_to_uskl_syn_lc : forall τ,
  mono_ptyp τ -> lc_uskl (ptyp_to_uskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply lc_uskl_unit | apply lc_uskl_var_f | apply lc_uskl_arrow; auto ].
Qed.

Lemma mono_ptyp_to_bskl_syn_lc : forall τ,
  mono_ptyp τ -> lc_bskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply lc_bskl_unit | apply lc_bskl_var_f | apply lc_bskl_arrow; auto ].
Qed.

Lemma mono_ptyp_to_pskl_guarded : forall τ,
  mono_ptyp τ -> guarded_pskl (ptyp_to_pskl τ).
Proof.
  destruct 1 as [ | α | A1 A2 ]; simpl;
    [ apply guarded_pskl__unit | apply guarded_pskl__var
    | apply guarded_pskl__arrow; apply mono_ptyp_to_pskl_lc; auto ].
Qed.

Lemma mono_ptyp_to_btyp_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_btyp (ptyp_to_btyp_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_btyp__unit | apply guarded_btyp__var
    | apply guarded_btyp__arrow; apply mono_ptyp_to_btyp_syn_lc; auto ].
Qed.

Lemma mono_ptyp_to_utyp_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_utyp (ptyp_to_utyp_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_utyp__unit | apply guarded_utyp__var
    | apply guarded_utyp__arrow; apply mono_ptyp_to_utyp_syn_lc; auto ].
Qed.

Lemma mono_ptyp_to_uskl_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_uskl (ptyp_to_uskl_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_uskl__unit | apply guarded_uskl__var
    | apply guarded_uskl__arrow; apply mono_ptyp_to_uskl_syn_lc; auto ].
Qed.

Lemma mono_ptyp_to_bskl_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_bskl (ptyp_to_bskl_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_bskl__unit | apply guarded_bskl__var
    | apply guarded_bskl__arrow; apply mono_ptyp_to_bskl_syn_lc; auto ].
Qed.

Lemma mono_ptyp_to_btyp_syn_is_styp : forall τ,
  mono_ptyp τ -> is_styp (ptyp_to_btyp_syn τ).
Proof.
  induction 1; simpl; eauto 3 using is_styp.
Qed.

Lemma mono_ptyp_to_btyp_syn_is_ityp : forall τ,
  mono_ptyp τ -> is_ityp (ptyp_to_btyp_syn τ).
Proof.
  induction 1; simpl; eauto 3 using is_ityp.
Qed.

Lemma mono_ptyp_to_utyp_syn_is_dtyp : forall τ,
  mono_ptyp τ -> is_dtyp (ptyp_to_utyp_syn τ).
Proof.
  induction 1; simpl; eauto 3 using is_dtyp.
Qed.

Lemma mono_ptyp_to_bskl_syn_is_sskl : forall τ,
  mono_ptyp τ -> is_sskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; cbn [ptyp_to_bskl_syn ptyp_to_pskl pskl_to_bskl_syn]; eauto 3 using is_sskl.
Qed.

Lemma mono_ptyp_to_bskl_syn_is_iskl : forall τ,
  mono_ptyp τ -> is_iskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; cbn [ptyp_to_bskl_syn ptyp_to_pskl pskl_to_bskl_syn]; eauto 3 using is_iskl.
Qed.

Lemma mono_ptyp_to_uskl_syn_is_dskl : forall τ,
  mono_ptyp τ -> is_dskl (ptyp_to_uskl_syn τ).
Proof.
  induction 1; cbn [ptyp_to_uskl_syn ptyp_to_bskl_syn ptyp_to_pskl pskl_to_bskl_syn bskl_to_uskl]; eauto 3 using is_dskl.
Qed.

Lemma is_styp_subst_mono : forall B τ α,
  is_styp B -> mono_ptyp τ ->
  is_styp (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B).
Proof.
  intros B τ α H Hm; induction H; simpl; try solve [eauto 3 using is_styp].
  - destruct_if; eauto 3 using is_styp, mono_ptyp_to_btyp_syn_is_styp.
  - apply is_styp__all with (L := L `union` singleton α). intros β Hβ.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var;
      [ | clear - Hβ; fsetdec | apply mono_ptyp_to_btyp_syn_lc; assumption ].
    apply H0. clear - Hβ; fsetdec.
Qed.

Lemma is_ityp_subst_mono : forall B τ α,
  is_ityp B -> mono_ptyp τ ->
  is_ityp (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B).
Proof.
  intros B τ α H Hm; induction H; simpl; try solve [eauto 3 using is_ityp].
  - destruct_if; eauto 3 using is_ityp, mono_ptyp_to_btyp_syn_is_ityp.
  - apply is_ityp__all with (L := L `union` singleton α). intros β Hβ.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var;
      [ | clear - Hβ; fsetdec | apply mono_ptyp_to_btyp_syn_lc; assumption ].
    apply H0. clear - Hβ; fsetdec.
Qed.

Lemma mod_comp_ty_subst_mono : forall B m τ α,
  mod_comp_ty B m -> mono_ptyp τ ->
  mod_comp_ty (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B) m.
Proof.
  intros B m τ α H Hm; induction H; simpl;
    eauto 3 using mod_comp_ty, is_styp_subst_mono, is_ityp_subst_mono.
Qed.

Lemma guarded_btyp_subst_mono : forall B τ α,
  guarded_btyp B -> mono_ptyp τ ->
  guarded_btyp (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B).
Proof.
  intros B τ α H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_btyp_syn_guarded with fresco.
  - apply guarded_btyp__arrow;
      apply subst_btyp_in_btyp_lc_btyp;
      auto using mono_ptyp_to_btyp_syn_lc.
Qed.

Lemma guarded_utyp_subst_mono : forall C τ α,
  guarded_utyp C -> mono_ptyp τ ->
  guarded_utyp (subst_utyp_in_utyp (ptyp_to_utyp_syn τ) α C).
Proof.
  intros C τ α H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_utyp_syn_guarded with fresco.
  - apply guarded_utyp__arrow;
      apply subst_utyp_in_utyp_lc_utyp;
      auto using mono_ptyp_to_utyp_syn_lc.
Qed.

Lemma is_dtyp_subst_mono : forall C τ α,
  is_dtyp C -> mono_ptyp τ ->
  is_dtyp (subst_utyp_in_utyp (ptyp_to_utyp_syn τ) α C).
Proof.
  intros C τ α H Hm; induction H; simpl; try solve [eauto 3 using is_dtyp].
  - destruct_if; eauto 3 using is_dtyp, mono_ptyp_to_utyp_syn_is_dtyp.
  - apply is_dtyp__all_tag with (L := L `union` {{α}}). intros β Hβ.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var;
      [ auto | clear - Hβ; fsetdec | apply mono_ptyp_to_utyp_syn_lc; assumption ].
Qed.

Lemma guarded_pskl_subst_mono : forall P τ β,
  guarded_pskl P -> mono_ptyp τ ->
  guarded_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros P τ β H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_pskl_guarded with fresco.
  - apply guarded_pskl__arrow;
      apply subst_pskl_in_pskl_lc_pskl;
      auto using mono_ptyp_to_pskl_lc.
Qed.

Lemma guarded_uskl_subst_mono : forall R τ β,
  guarded_uskl R -> mono_ptyp τ ->
  guarded_uskl (subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β R).
Proof.
  intros R τ β H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_uskl_syn_guarded with fresco.
  - apply guarded_uskl__arrow;
      apply subst_uskl_in_uskl_lc_uskl;
      auto using mono_ptyp_to_uskl_syn_lc.
Qed.

Lemma guarded_bskl_subst_mono : forall Q τ β,
  guarded_bskl Q -> mono_ptyp τ ->
  guarded_bskl (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q).
Proof.
  intros Q τ β H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_bskl_syn_guarded with fresco.
  - apply guarded_bskl__arrow;
      apply subst_bskl_in_bskl_lc_bskl;
      auto using mono_ptyp_to_bskl_syn_lc.
Qed.

Lemma is_sskl_subst_mono : forall Q τ β,
  is_sskl Q -> mono_ptyp τ ->
  is_sskl (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q).
Proof.
  intros Q τ β H Hm; induction H; simpl; try solve [eauto 3 using is_sskl].
  - destruct_if; eauto 3 using is_sskl, mono_ptyp_to_bskl_syn_is_sskl.
  - apply is_sskl__all with (L := L `union` {{β}}).
    intros α Hα.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ auto | intro He; subst; clear - Hα; fsetdec
      | apply mono_ptyp_to_bskl_syn_lc; assumption ].
Qed.

Lemma is_iskl_subst_mono : forall Q τ β,
  is_iskl Q -> mono_ptyp τ ->
  is_iskl (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q).
Proof.
  intros Q τ β H Hm; induction H; simpl; try solve [eauto 3 using is_iskl].
  - destruct_if; eauto 3 using is_iskl, mono_ptyp_to_bskl_syn_is_iskl.
  - apply is_iskl__all with (L := L `union` {{β}}).
    intros α Hα.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ auto | intro He; subst; clear - Hα; fsetdec
      | apply mono_ptyp_to_bskl_syn_lc; assumption ].
Qed.

Lemma mod_comp_sk_subst_mono : forall Q m τ β,
  mod_comp_sk Q m -> mono_ptyp τ ->
  mod_comp_sk (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q) m.
Proof.
  intros Q m τ β H Hm; induction H.
  - auto using is_sskl_subst_mono with fresco.
  - auto using is_sskl_subst_mono with fresco.
  - simpl; auto with fresco.
Qed.

Lemma is_dskl_subst_mono : forall ψ τ β,
  is_dskl ψ -> mono_ptyp τ ->
  is_dskl (subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β ψ).
Proof.
  intros ψ τ β H Hm; induction H; simpl; try solve [eauto 3 using is_dskl].
  - destruct_if; eauto 3 using is_dskl, mono_ptyp_to_uskl_syn_is_dskl.
  - apply is_dskl__all_tag with (L := L `union` {{β}}).
    intros α Hα.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ auto | intro He; subst; clear - Hα; fsetdec
      | apply mono_ptyp_to_uskl_syn_lc; assumption ].
Qed.

Unset Implicit Arguments.

Set Implicit Arguments.

Lemma pskl_no_ghost_close_rec : forall P β k,
  pskl_no_ghost P -> pskl_no_ghost (close_pskl_wrt_pskl_rec k β P).
Proof.
  induction P; intros β k H; simpl in *; auto.
  -  destruct (lt_ge_dec n k); simpl; auto.
  -  destruct (β == α); simpl; auto.
  -  destruct H; split; auto.
Qed.

Lemma pskl_no_ghost_close : forall P β,
  pskl_no_ghost P -> pskl_no_ghost (close_pskl_wrt_pskl β P).
Proof.
  intros P β H; unfold close_pskl_wrt_pskl;
    apply pskl_no_ghost_close_rec; exact H.
Qed.

Lemma is_dskl_all_tag_inv : forall ε ψ,
  is_dskl (uskl_all_tag ε ψ) ->
  exists L, forall α, α `notin` L ->
    is_dskl (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof. intros ε ψ H; inversion H; subst. eexists; eassumption. Qed.
Unset Implicit Arguments.

Set Implicit Arguments.

Lemma mono_ptyp_subst : forall A τ α1,
  mono_ptyp A -> mono_ptyp τ ->
  mono_ptyp (subst_ptyp_in_ptyp τ α1 A).
Proof.
  intros * HA Hτ; induction HA; simpl; eauto using mono_ptyp.
  destruct (eq_var α α1); eauto using mono_ptyp.
Qed.

Lemma close_ptyp_subst_var : forall A α β,
  β `notin` ftvar_in_ptyp A ->
  close_ptyp_wrt_ptyp β (subst_ptyp_in_ptyp (ptyp_var_f β) α A)
  = close_ptyp_wrt_ptyp α A.
Proof.
  intros A α β Hβ.
  rewrite subst_ptyp_in_ptyp_spec.
  apply close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp.
  assert (Hcl : ftvar_in_ptyp (close_ptyp_wrt_ptyp α A)
                  [=] AtomSetImpl.remove α (ftvar_in_ptyp A))
    by (apply ftvar_in_ptyp_close_ptyp_wrt_ptyp).
  clear - Hβ Hcl. fsetdec.
Qed.

Lemma notin_ftvar_open_pskl_var : forall β α P,
  β <> α -> β `notin` ftvar_in_pskl P ->
  β `notin` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof.
  intros β α P Hne HβP.
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α)) as Hs.
  simpl in Hs. clear - Hs Hne HβP. fsetdec.
Qed.

Lemma ftvar_in_pskl_subst_keep : forall α β P0 P,
  β <> α ->
  α `in` ftvar_in_pskl P ->
  α `in` ftvar_in_pskl (subst_pskl_in_pskl P0 β P).
Proof.
  intros α β P0 P Hne Hin.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower P P0 β) as Hlo.
  clear - Hne Hin Hlo. fsetdec.
Qed.

Lemma ghost_free_open_var_neq_ghost : forall P β,
  pskl_ghost_free P ->
  open_pskl_wrt_pskl P (pskl_var_f β) <> pskl_ghost.
Proof.
  intros P β Hgf. unfold open_pskl_wrt_pskl.
  destruct P; simpl in *; try contradiction; try discriminate.
  destruct (lt_eq_lt_dec n 0) as [ [ _ | _ ] | _ ]; discriminate.
Qed.

Lemma open_var_eq_var_inv : forall Q β α,
  open_pskl_wrt_pskl Q (pskl_var_f β) = pskl_var_f α -> β <> α ->
  Q = pskl_var_f α.
Proof.
  intros Q β α Heq Hne. unfold open_pskl_wrt_pskl in Heq.
  destruct Q; simpl in Heq; try discriminate Heq.
  - destruct (lt_eq_lt_dec n 0) as [ [ _ | _ ] | _ ]; simpl in Heq;
      [ discriminate Heq
      | injection Heq as Heq0; exfalso; apply Hne; exact Heq0
      | discriminate Heq ].
  - exact Heq.
Qed.

Lemma guarded_pskl_subst_var : forall P α β,
  guarded_pskl P ->
  guarded_pskl (subst_pskl_in_pskl (pskl_var_f β) α P).
Proof.
  intros P α β H.
  exact (@guarded_pskl_subst_mono P (ptyp_var_f β) α H (mono_ptyp__var β)).
Qed.
