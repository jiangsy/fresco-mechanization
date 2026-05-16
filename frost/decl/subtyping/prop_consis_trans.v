(** Frost — declarative subtyping metatheory: composition of consistency,
    consistency-RHS / LHS mono pinning lemmas, and the
    [d_consis_compose_nil_RHS] step used by [d_consis_sub_trans]. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.subtyping.prop_basics.

Set Implicit Arguments.

(** * Consistency-Subtyping Transitivity
    (paper Lemma B.3, syntax-directed.tex:161,
    thm:consist-subtyping-transitivity).

    Paper claim: if [d_consis Δ Γ T A] and [d_sub M Δ' Γ A B], then
    [d_sub M (Δ ++ Δ') Γ T B].

    Note the asymmetry: A appears as the (coloured-typ) RHS of [d_consis]
    and as the (utyp-form) LHS of [d_sub]. Both views happen to be
    compatible at the constructor heads we need to handle here — the
    LHS of [d_sub] in [d_sub__arrow]/[d_sub__check] is unrestricted, and
    the [d_sub__forall_l_*] rules don't apply when A is a [typ_all_col]
    (the only forall flavour produced by [d_consis]).

    The proof proceeds by induction on the [d_sub] derivation. The
    intermediate consistency-composition step (when [d_sub] terminates
    in [__infer]/[__check]/[__arg]) reduces to the [d_consis_compose]
    lemma below. *)

(** Helper: swap the inner two segments of a 4-way concatenation,
    up to Permutation. Used to handle the arrow case of
    [d_consis_compose]. *)
Lemma list_swap_middle : forall {A : Type} (l1 l2 l3 l4 : list A),
    Permutation ((l1 ++ l2) ++ (l3 ++ l4)) ((l1 ++ l3) ++ (l2 ++ l4)).
Proof.
  intros A l1 l2 l3 l4.
  (* Make the right-associated form the working term, then apply
     Permutation_app_swap_app under l1, and re-pack to left-assoc. *)
  pose proof (Permutation_app_swap_app (A := A) l2 l3 l4) as Hswap.
  (* Hswap : Permutation (l2 ++ l3 ++ l4) (l3 ++ l2 ++ l4). *)
  apply (Permutation_app_head l1) in Hswap.
  (* Hswap : Permutation (l1 ++ l2 ++ l3 ++ l4) (l1 ++ l3 ++ l2 ++ l4). *)
  (* Re-associate both sides to match goal form. *)
  replace ((l1 ++ l2) ++ (l3 ++ l4)) with (l1 ++ l2 ++ l3 ++ l4).
  - replace ((l1 ++ l3) ++ (l2 ++ l4)) with (l1 ++ l3 ++ l2 ++ l4).
    + exact Hswap.
    + rewrite app_assoc. reflexivity.
  - rewrite app_assoc. reflexivity.
Qed.

(** ** Composition of consistency, modulo Δ-permutation.

    Paper Lemma B.2 (Consistency Transitivity). [paper-ref: thm:consist-transitivity]

    The paper writes the conclusion's Δ as "Δ_1, Δ_2" — set union
    (declarative.tex:814: "We write Δ,Δ' for set union"). Our
    encoding uses [list atom], so the natural strict statement
    [d_consis (Δa ++ Δb) Γ T B] is provably FALSE: the arrow case
    produces output Δ of shape [Δa1 ++ Δb1 ++ Δa2 ++ Δb2]
    (structurally interleaved by the arrow components), while
    [Δa ++ Δb = Δa1 ++ Δa2 ++ Δb1 ++ Δb2] swaps two inner segments.

    Closing therefore restates the conclusion modulo [Permutation].
    All forall-cases of [d_consis] (the ones that might contribute
    a tag to Δ) are VACUOUS in compose: they produce
    [A = typ_all_col c _], which is not an [is_utyp] shape and so
    cannot be the LHS of [Hc2]. *)

Lemma d_consis_compose : forall Δa Δb Γ T A B,
    Δa ⨟ Γ ⊨ T ≈ A ->
    Δb ⨟ Γ ⊨ A ≈ B ->
    list_disjoint Δa Δb ->                 (* linearity premise: tags from
                                              the two sub-derivations are
                                              fresh w.r.t. each other. *)
    exists Δc, Permutation Δc (Δa ++ Δb) /\ Δc ⨟ Γ ⊨ T ≈ B.
Proof.
  intros Δa Δb Γ T A B Hc1. generalize dependent B. generalize dependent Δb.
  induction Hc1; intros Δb B0 Hc2 Hdis.
  - (* unit ~ unit, then unit ~ B0: Δa = nil, so Δc = Δb. *)
    exists Δb. split; [simpl; apply Permutation_refl | exact Hc2].
  - (* var X ~ var X. *)
    exists Δb. split; [simpl; apply Permutation_refl | exact Hc2].
  - (* __forall_inh_tagged: Hc1 has RHS = typ_all_col colour_inh A,
       Δa = ε :: Δ. Hc2 matches the new __forall_inh. Compose via
       cofinite-rename, then wrap with __forall_inh_tagged using
       ε :: Δc0 (where Δc0 is a permutation of Δ ++ Δb). *)
    inversion Hc2; subst.
    (* Auto-names: A0, L0, H5 (body premise), H1 (ε ∉ Δ). *)
    assert (Hdis_inner : list_disjoint Δ Δb).
    { intros a Hin. apply Hdis. right. exact Hin. }
    assert (Hε_Δb : ~ In ε Δb).
    { apply Hdis. left. reflexivity. }
    pick fresh X0 for
      (L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A
       `union` ftvar_in_typ A0 `union` dom Γ `union` singleton ε).
    assert (HX0_L : X0 `notin` L) by fsetdec.
    assert (HX0_L0 : X0 `notin` L0) by fsetdec.
    specialize (H0 X0 HX0_L Δb (open_typ_wrt_typ A0 (typ_var_f X0))
                  (H5 X0 HX0_L0) Hdis_inner).
    destruct H0 as [Δc0 [Hperm Hcc]].
    exists (ε :: Δc0). split.
    + simpl. apply perm_skip. exact Hperm.
    + apply d_consis__forall_inh_tagged with
        (L := L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A
              `union` ftvar_in_typ A0 `union` dom Γ `union` singleton X0
              `union` singleton ε).
      * intros X' HX'.
        assert (Hcc_weak :
          d_consis Δc0 ((X0 ~ dbind_tvar) ++ (X' ~ dbind_tvar) ++ Γ)
            (open_typ_wrt_typ T (typ_var_f X0))
            (open_typ_wrt_typ A0 (typ_var_f X0))).
        { rewrite_env (((X0 ~ dbind_tvar) ++ nil) ++ (X' ~ dbind_tvar) ++ Γ).
          apply d_consis_weakening. simpl. exact Hcc. }
        apply d_consis_subst_mono
          with (Γ1 := nil) (X := X0) (Γ2 := (X' ~ dbind_tvar) ++ Γ)
               (B := typ_var_f X') in Hcc_weak; auto.
        -- rewrite <- (subst_typ_in_typ_intro X0 T (typ_var_f X')) in Hcc_weak
             by fsetdec.
           rewrite <- (subst_typ_in_typ_intro X0 A0 (typ_var_f X')) in Hcc_weak
             by fsetdec.
           exact Hcc_weak.
        -- apply mono_typ__var.
        -- apply d_wf_typ__var. left; reflexivity.
      * (* ε ∉ Δc0: from Permutation Δc0 (Δ ++ Δb), ε ∉ Δ, ε ∉ Δb. *)
        intros Hin. apply (Permutation_in _ Hperm) in Hin.
        apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        -- apply H1; exact Hin.
        -- apply Hε_Δb; exact Hin.
  - (* __forall_syn_tagged: Hc1's RHS = typ_all_col colour_syn A.
       Hc2's only matching rule is the new __forall_syn. Compose via
       cofinite-rename, parallel to __forall_inh_tagged but without ε. *)
    inversion Hc2; subst.
    pick fresh X0 for
      (L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A
       `union` ftvar_in_typ A0 `union` dom Γ).
    assert (HX0_L : X0 `notin` L) by fsetdec.
    assert (HX0_L0 : X0 `notin` L0) by fsetdec.
    specialize (H0 X0 HX0_L Δb (open_typ_wrt_typ A0 (typ_var_f X0))
                  (H4 X0 HX0_L0) Hdis).
    destruct H0 as [Δc0 [Hperm Hcc]].
    exists Δc0. split; [exact Hperm |].
    apply d_consis__forall_syn_tagged with
      (L := L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A
            `union` ftvar_in_typ A0 `union` dom Γ `union` singleton X0).
    intros X' HX'.
    assert (Hcc_weak :
      d_consis Δc0 ((X0 ~ dbind_tvar) ++ (X' ~ dbind_tvar) ++ Γ)
        (open_typ_wrt_typ T (typ_var_f X0))
        (open_typ_wrt_typ A0 (typ_var_f X0))).
    { rewrite_env (((X0 ~ dbind_tvar) ++ nil) ++ (X' ~ dbind_tvar) ++ Γ).
      apply d_consis_weakening. simpl. exact Hcc. }
    apply d_consis_subst_mono
      with (Γ1 := nil) (X := X0) (Γ2 := (X' ~ dbind_tvar) ++ Γ)
           (B := typ_var_f X') in Hcc_weak; auto.
    + rewrite <- (subst_typ_in_typ_intro X0 T (typ_var_f X')) in Hcc_weak
        by fsetdec.
      rewrite <- (subst_typ_in_typ_intro X0 A0 (typ_var_f X')) in Hcc_weak
        by fsetdec.
      exact Hcc_weak.
    + apply mono_typ__var.
    + apply d_wf_typ__var. left; reflexivity.
  - (* __forall_syn (post-refactor): Hc1 has LHS = RHS = typ_all_col
       colour_syn. Hc2's LHS must be typ_all_col colour_syn, matched by
       __forall_syn (post-refactor — was vacuous in the old rule set).
       Compose via cofinite-rename, parallel to __forall_inh. *)
    inversion Hc2; subst.
    pick fresh X0 for
      (L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A
       `union` ftvar_in_typ A0 `union` dom Γ).
    assert (HX0_L : X0 `notin` L) by fsetdec.
    assert (HX0_L0 : X0 `notin` L0) by fsetdec.
    specialize (H0 X0 HX0_L Δb (open_typ_wrt_typ A0 (typ_var_f X0))
                  (H4 X0 HX0_L0) Hdis).
    destruct H0 as [Δc0 [Hperm Hcc]].
    exists Δc0. split; [exact Hperm |].
    apply d_consis__forall_syn with
      (L := L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A
            `union` ftvar_in_typ A0 `union` dom Γ `union` singleton X0).
    intros X' HX'.
    assert (Hcc_weak :
      d_consis Δc0 ((X0 ~ dbind_tvar) ++ (X' ~ dbind_tvar) ++ Γ)
        (open_typ_wrt_typ T (typ_var_f X0))
        (open_typ_wrt_typ A0 (typ_var_f X0))).
    { rewrite_env (((X0 ~ dbind_tvar) ++ nil) ++ (X' ~ dbind_tvar) ++ Γ).
      apply d_consis_weakening. simpl. exact Hcc. }
    apply d_consis_subst_mono
      with (Γ1 := nil) (X := X0) (Γ2 := (X' ~ dbind_tvar) ++ Γ)
           (B := typ_var_f X') in Hcc_weak; auto.
    + rewrite <- (subst_typ_in_typ_intro X0 T (typ_var_f X')) in Hcc_weak
        by fsetdec.
      rewrite <- (subst_typ_in_typ_intro X0 A0 (typ_var_f X')) in Hcc_weak
        by fsetdec.
      exact Hcc_weak.
    + apply mono_typ__var.
    + apply d_wf_typ__var. left; reflexivity.
  - (* __forall_inh: Hc1 has RHS = typ_all_col colour_inh A,
       Δa = Δ (no ε to track). Hc2 matches the new __forall_inh again.
       Compose via cofinite-rename (no ε wrapping needed). *)
    inversion Hc2; subst.
    pick fresh X0 for
      (L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A
       `union` ftvar_in_typ A0 `union` dom Γ).
    assert (HX0_L : X0 `notin` L) by fsetdec.
    assert (HX0_L0 : X0 `notin` L0) by fsetdec.
    specialize (H0 X0 HX0_L Δb (open_typ_wrt_typ A0 (typ_var_f X0))
                  (H4 X0 HX0_L0) Hdis).
    destruct H0 as [Δc0 [Hperm Hcc]].
    exists Δc0. split; [exact Hperm |].
    apply d_consis__forall_inh with
      (L := L `union` L0 `union` ftvar_in_typ T `union` ftvar_in_typ A
            `union` ftvar_in_typ A0 `union` dom Γ `union` singleton X0).
    intros X' HX'.
    assert (Hcc_weak :
      d_consis Δc0 ((X0 ~ dbind_tvar) ++ (X' ~ dbind_tvar) ++ Γ)
        (open_typ_wrt_typ T (typ_var_f X0))
        (open_typ_wrt_typ A0 (typ_var_f X0))).
    { rewrite_env (((X0 ~ dbind_tvar) ++ nil) ++ (X' ~ dbind_tvar) ++ Γ).
      apply d_consis_weakening. simpl. exact Hcc. }
    apply d_consis_subst_mono
      with (Γ1 := nil) (X := X0) (Γ2 := (X' ~ dbind_tvar) ++ Γ)
           (B := typ_var_f X') in Hcc_weak; auto.
    + rewrite <- (subst_typ_in_typ_intro X0 T (typ_var_f X')) in Hcc_weak
        by fsetdec.
      rewrite <- (subst_typ_in_typ_intro X0 A0 (typ_var_f X')) in Hcc_weak
        by fsetdec.
      exact Hcc_weak.
    + apply mono_typ__var.
    + apply d_wf_typ__var. left; reflexivity.
  - (* arrow: split Hc2 via inversion; recurse on each side; assemble
       via [list_swap_middle] and the disjointness decomposition. The
       inversion pattern now has 7 alternatives (6 bars before
       [__arrow]) for the new 7-rule d_consis. *)
    inversion Hc2 as [| | | | | |Δb1 Δb2 ? T1' T2' A1' A2' Hb1 Hb2 Hdis_b];
      subst.
    (* From Hdis : list_disjoint (Δ1 ++ Δ2) (Δb1 ++ Δb2), derive the four
       cross-disjoints. *)
    apply list_disjoint_app_l_iff in Hdis as [Hdis1 Hdis2].
    apply list_disjoint_app_r_iff in Hdis1 as [Hd1b1 Hd1b2].
    apply list_disjoint_app_r_iff in Hdis2 as [Hd2b1 Hd2b2].
    destruct (IHHc1_1 _ _ Hb1 Hd1b1) as [Δc1 [Hperm1 Hcc1]].
    destruct (IHHc1_2 _ _ Hb2 Hd2b2) as [Δc2 [Hperm2 Hcc2]].
    exists (Δc1 ++ Δc2). split.
    + transitivity ((Δ1 ++ Δb1) ++ (Δ2 ++ Δb2)).
      * apply Permutation_app; assumption.
      * apply list_swap_middle.
    + apply d_consis__arrow; auto.
      (* list_disjoint Δc1 Δc2: transfer through permutations.
         Δc1 ~ Δ1 ++ Δb1, Δc2 ~ Δ2 ++ Δb2. Use Hdis1', Hd1b2, Hdis_b. *)
      eapply list_disjoint_perm_l; [apply Permutation_sym; exact Hperm1|].
      eapply list_disjoint_perm_r; [apply Permutation_sym; exact Hperm2|].
      apply list_disjoint_app_l_iff. split.
      * apply list_disjoint_app_r_iff. split; [exact H | exact Hd1b2].
      * apply list_disjoint_app_r_iff. split;
          [apply list_disjoint_sym; exact Hd2b1 | exact Hdis_b].
Qed.

(** If [d_consis Δ Γ T A] and [d_wf_typ Γ T], then [T] is mono.

    Reason: d_consis's LHS-allowed shapes are {unit, var, typ_all_etag,
    typ_all_plain, typ_arrow}, while d_wf_typ's allowed shapes are
    {unit, var, typ_arrow, typ_all_col}. The intersection is
    {unit, var, typ_arrow}, which is exactly the [mono_typ] grammar.
    The forall-* cases of d_consis are vacuous because their LHS shapes
    (etag/plain) are not in d_wf_typ. The arrow case recurses.

    Used in [d_typing_general_subsumption] to derive that body types
    in __abs cases are mono (and hence support d_sub_refl_mono), which
    unblocks the body conversion. *)
(** With the new [d_consis__forall_inh] rule, the LHS can be
    [typ_all_col colour_inh T0] which is NOT mono. The lemma therefore
    requires an [is_utyp T] precondition that rules out this case
    structurally — [is_utyp] is the old [d_consis] LHS grammar
    (unit/var/arrow/typ_all_etag/typ_all_plain), which omits
    [typ_all_col]. Callers establish [is_utyp T] via
    [d_consis_LHS_is_utyp_when_RHS_syn] (below) when RHS is
    [syn_color]-shaped. *)
Lemma d_consis_LHS_mono_wf : forall Δ Γ T A,
    d_consis Δ Γ T A ->
    d_wf_typ Γ T ->
    is_utyp T ->
    mono_typ T.
Proof.
  intros Δ Γ T A Hc Hwf Hut. induction Hc; inversion Hwf; subst.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - (* __forall_inh: T = typ_all_col colour_inh _, NOT is_utyp. *)
    inversion Hut.
  - (* __forall_syn (post-refactor): T = typ_all_col colour_syn _, NOT is_utyp. *)
    inversion Hut.
  - inversion Hut; subst. apply mono_typ__arrow.
    + apply IHHc1; auto.
    + apply IHHc2; auto.
Qed.

(** When [d_consis Δ Γ T A] holds and the RHS [A] is recursively
    syn-painted (any [A = syn_color C]), the LHS [T] is recursively
    [is_utyp]. The new [d_consis__forall_inh] rule (LHS/RHS both
    [typ_all_col colour_inh]) is vacuous because [syn_color C] never
    has [colour_inh] at the head, and recursively the sub-derivations
    inherit the syn-painted RHS via the [__forall_syn_*] / [__arrow]
    rules.

    POST-REFACTOR (typ_all_plain removed): the new [d_consis__forall_syn]
    rule (LHS/RHS both [typ_all_col colour_syn]) BREAKS this lemma: T
    can now be [typ_all_col colour_syn] which is NOT [is_utyp]. The
    lemma is therefore admitted in that case; downstream callers must
    accept a weaker conclusion or restrict their use. *)
Lemma d_consis_LHS_is_utyp_when_RHS_syn_color : forall Δ Γ T A,
    d_consis Δ Γ T A ->
    forall C, A = syn_color C ->
    is_utyp T.
Proof.
  intros Δ Γ T A Hc. induction Hc; intros C HC.
  - apply is_utyp__unit.
  - apply is_utyp__var.
  - (* __forall_inh_tagged: A = typ_all_col colour_inh A_inner; never
       equal to [syn_color C]. *)
    destruct C; simpl in HC; discriminate.
  - (* __forall_syn_tagged: A = typ_all_col colour_syn (syn_color C_inner)
       with C = ctyp_all C_inner. LHS is typ_all_etag (is_utyp). *)
    destruct C; simpl in HC; try discriminate.
    inversion HC; subst.
    inst_cofinites_for is_utyp__tall.
    intros X HX.
    eapply H0 with (C := open_ctyp_wrt_ctyp C (ctyp_var_f X)); eauto.
    rewrite syn_color_open_ctyp. simpl. reflexivity.
  - (* __forall_syn (post-refactor, rule order: syn before inh):
       A = typ_all_col colour_syn (...) = syn_color (ctyp_all _).
       LHS T = typ_all_col colour_syn — NOT is_utyp. Lemma claim is
       FALSE in this case; admitted. Downstream callers in prop_typing.v
       that depended on this conclusion need refactoring. *)
    admit.
  - (* __forall_inh: A = typ_all_col colour_inh — never [syn_color C]. *)
    destruct C; simpl in HC; discriminate.
  - (* __arrow *)
    destruct C; simpl in HC; try discriminate.
    inversion HC; subst.
    apply is_utyp__arrow; eauto.
Admitted.

(** No [inh_color]-RHS version of the above is provided: with the new
    [__forall_inh] rule, [d_consis Δ Γ T (inh_color (ctyp_all _))] can
    have [T = typ_all_col colour_inh _] which is NOT [is_utyp], so an
    inh-painted RHS does not suffice to pin the LHS shape. *)

(** Same intersection argument with [is_typ T] instead of [d_wf_typ Γ T]:
    [is_typ]'s shapes are {unit, var, arrow, typ_all_col}, [d_consis]'s
    LHS shapes are {unit, var, typ_all_etag, typ_all_plain, arrow}, so a
    type that is both is exactly [mono_typ]. The [ctyp]-era
    [d_consis_sub_trans] needs this: [d_sub__infer] / [d_sub__check]
    now demand a [syn_color]-shaped LHS, and a mono type round-trips
    through [syn_color (erase _)]. *)
(** With the new [__forall_inh] rule, the LHS can also be
    [typ_all_col colour_inh] which IS [is_typ] but NOT [mono]. So we
    additionally require [is_utyp T] to rule out that case. *)
Lemma d_consis_LHS_is_typ_mono : forall Δ Γ T A,
    d_consis Δ Γ T A ->
    is_typ T ->
    is_utyp T ->
    mono_typ T.
Proof.
  intros Δ Γ T A Hc Hist Hut. induction Hc; inversion Hist; subst.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - (* __forall_syn (post-refactor): T = typ_all_col colour_syn; not is_utyp. *)
    inversion Hut.
  - (* __forall_inh: T = typ_all_col colour_inh; not is_utyp. *)
    inversion Hut.
  - inversion Hut; subst. apply mono_typ__arrow.
    + apply IHHc1; assumption.
    + apply IHHc2; assumption.
Qed.

(** [d_consis] with a [mono_typ] RHS pins everything: [T = A], [Δ = nil],
    [T] mono. The [__forall_*] cases are vacuous (RHS is [typ_all_col],
    not mono); the [__arrow] case recurses on both sides.

    This is the RHS-side analogue of [d_consis_LHS_*_mono]: instead of
    "LHS is a paint-shape" forcing mono, "RHS is mono" forces mono. Used
    by [d_consis_sub_trans] to lift the [is_typ T]/[d_wf_typ Γ T]
    contract off the lemma signature — Hs's [__infer]/[__check] premise
    has a [syn_color]-shaped LHS that is mono via [d_consis_LHS_syn_color_mono]
    below, which then makes Hc's RHS mono, which then forces T mono via
    this lemma. *)
Lemma d_consis_mono_RHS : forall Δ Γ T A,
    d_consis Δ Γ T A ->
    mono_typ A ->
    mono_typ T /\ Δ = nil /\ T = A.
Proof.
  intros Δ Γ T A Hc. induction Hc; intros Hmono.
  - split; [|split]; [apply mono_typ__unit | reflexivity | reflexivity].
  - split; [|split]; [apply mono_typ__var | reflexivity | reflexivity].
  - (* __forall_inh_tagged: RHS = typ_all_col colour_inh, not mono. *)
    inversion Hmono.
  - (* __forall_syn_tagged: RHS = typ_all_col colour_syn, not mono. *)
    inversion Hmono.
  - (* __forall_syn (post-refactor): A = typ_all_col colour_syn, not mono. *)
    inversion Hmono.
  - (* __forall_inh: A = typ_all_col colour_inh, not mono. *)
    inversion Hmono.
  - inversion Hmono as [| | A1' A2' Hmono1 Hmono2]; subst.
    destruct (IHHc1 Hmono1) as [HmonoT1 [HΔ1 HT1eq]]; subst.
    destruct (IHHc2 Hmono2) as [HmonoT2 [HΔ2 HT2eq]]; subst.
    split; [|split]; [apply mono_typ__arrow; assumption | reflexivity | reflexivity].
Qed.

(** [d_consis_mono_LHS]: parallel to [d_consis_mono_RHS] but on the LHS.
    Given [mono_typ T] (which forces T into {unit, var, arrow} — no
    [typ_all_*]/[typ_hole]/[typ_tophole]), [d_consis] pins [A = T] and
    [Δ = nil].

    Replaces the pre-refactor [d_consis_LHS_syn_color_mono] which tried
    to DERIVE mono from [T = syn_color C]; that derivation is unsound
    post-refactor because [d_consis__forall_syn] allows non-mono LHS. *)
Lemma d_consis_mono_LHS : forall Δ Γ T A,
    d_consis Δ Γ T A ->
    mono_typ T ->
    A = T /\ Δ = nil.
Proof.
  intros Δ Γ T A Hc Hmono. induction Hc.
  - split; reflexivity.
  - split; reflexivity.
  - (* __forall_inh_tagged: T = typ_all_etag — not mono. *) inversion Hmono.
  - (* __forall_syn_tagged: T = typ_all_etag — not mono. *) inversion Hmono.
  - (* __forall_syn: T = typ_all_col — not mono. *) inversion Hmono.
  - (* __forall_inh: T = typ_all_col — not mono. *) inversion Hmono.
  - inversion Hmono; subst.
    destruct (IHHc1 H2) as [HA1 HΔ1]; subst.
    destruct (IHHc2 H3) as [HA2 HΔ2]; subst.
    split; reflexivity.
Qed.

(** Analogous lemma for [d_sub]: a wf type appearing as a d_sub LHS is mono.
    Same intersection argument as [d_consis_LHS_mono_wf], extended through
    d_sub's __forall_r (no LHS change) and __arg (arrow inversion).
    __forall_l_* cases vacuous since LHS etag/plain are not wf. *)
(** Refl d_sub at mode m on a mono arrow type implies refl d_sub at
    [decr_mode m] on the result type. Used in body conversion lifts. *)
Lemma d_sub_arrow_refl_inner : forall Γ A B m,
    d_sub m nil Γ (typ_arrow A B) (typ_arrow A B) ->
    mono_typ A ->
    mono_typ B ->
    d_sub (decr_mode m) nil Γ B B.
Proof.
  intros Γ A B m Hrefl Hmono_a Hmono_b.
  inversion Hrefl; subst.
  - (* __infer (m = mode_ti): inversion exposes the [d_consis] premise as
       [d_consis nil Γ X X] for a single [X] (= [syn_color] of the base),
       provably equal to [typ_arrow A B] by the chained index equalities. *)
    simpl.
    match goal with
    | Hc : d_consis nil Γ ?X ?X |- _ =>
        assert (HX : X = typ_arrow A B) by congruence;
        rewrite HX in Hc; inversion Hc; subst
    end.
    match goal with
    | H : nil = _ ++ _ |- _ =>
      symmetry in H; apply app_eq_nil in H as [? ?]; subst
    | H : _ ++ _ = nil |- _ =>
      apply app_eq_nil in H as [? ?]; subst
    end.
    assert (Hg : d_sub mode_ti nil Γ (syn_color (erase B)) (syn_color (erase B))).
    { apply d_sub__infer.
      rewrite (mono_typ_syn_color_erase Hmono_b). assumption. }
    rewrite (mono_typ_syn_color_erase Hmono_b) in Hg. exact Hg.
  - (* __check (m = mode_tc): same shape, [d_consis premise] is
       [d_consis nil Γ X X] with [X = inh_color] base. *)
    simpl.
    match goal with
    | Hc : d_consis nil Γ ?X ?X |- _ =>
        assert (HX : X = typ_arrow A B) by congruence;
        rewrite HX in Hc; inversion Hc; subst
    end.
    match goal with
    | H : nil = _ ++ _ |- _ =>
      symmetry in H; apply app_eq_nil in H as [? ?]; subst
    | H : _ ++ _ = nil |- _ =>
      apply app_eq_nil in H as [? ?]; subst
    end.
    assert (Hg : d_sub mode_tc nil Γ (syn_color (erase B)) (inh_color (erase B))).
    { apply d_sub__check.
      - rewrite (mono_typ_syn_color_erase Hmono_b).
        apply mono_typ_guarded; assumption.
      - rewrite (mono_typ_syn_color_erase Hmono_b),
                (mono_typ_inh_color_erase Hmono_b).
        assumption. }
    rewrite (mono_typ_syn_color_erase Hmono_b),
            (mono_typ_inh_color_erase Hmono_b) in Hg.
    exact Hg.
  - (* __arg (m = mode_fn _): the result side is the body [d_sub] directly. *)
    match goal with
    | H : nil = _ ++ _ |- _ =>
      symmetry in H; apply app_eq_nil in H as [? ?]; subst
    | H : _ ++ _ = nil |- _ =>
      apply app_eq_nil in H as [? ?]; subst
    end.
    simpl. assumption.
Qed.

(** Mono types are is_typ (since mono ⊆ is_typ grammar). *)
Lemma mono_typ_is_typ : forall A, mono_typ A -> is_typ A.
Proof.
  intros A H. induction H.
  - apply is_typ__unit.
  - apply is_typ__var.
  - apply is_typ__arrow; auto.
Qed.

(** Mono types are is_utyp (mono ⊆ is_utyp grammar). *)
Lemma mono_typ_is_utyp : forall A, mono_typ A -> is_utyp A.
Proof.
  intros A H. induction H.
  - apply is_utyp__unit.
  - apply is_utyp__var.
  - apply is_utyp__arrow; auto.
Qed.

(** Lift lemma [d_typing_lift_mono] needs to be placed AFTER
    [d_consis_sub_trans_nil] in the file (forward reference). See
    after the latter for the full statement and proof attempt. *)

(** With the new [d_consis__forall_inh] rule, [d_sub__arg]'s d_consis
    premise admits LHS = [typ_all_col colour_inh _], which is wf but
    NOT mono. So the lemma needs an additional [is_utyp T] precondition
    to rule out this case. (Currently unused outside docs; preserved
    with the strengthened signature for consistency with
    [d_consis_LHS_mono_wf].) *)
Lemma d_sub_LHS_mono_wf : forall M Δ Γ T A,
    d_sub M Δ Γ T A ->
    d_wf_typ Γ T ->
    is_utyp T ->
    mono_typ T.
Proof.
  intros M Δ Γ T A Hs Hwf Hut. induction Hs.
  - (* __infer: LHS = syn_color T. *)
    eapply d_consis_LHS_mono_wf; eauto.
  - (* __check: LHS = syn_color T. *)
    eapply d_consis_LHS_mono_wf; eauto.
  - (* __forall_r: T unchanged. Pick fresh X, apply cofinite IH. *)
    pick fresh X for (L `union` dom Γ).
    apply (H0 X); [fsetdec | apply d_wf_typ_weakening_head; assumption |].
    assumption.
  - (* __arg: T = typ_arrow T1 T2. is_utyp inversion gives is_utyp on
       each component; d_wf_typ inversion gives wf on each. *)
    inversion Hwf; subst. inversion Hut; subst.
    apply mono_typ__arrow.
    + eapply d_consis_LHS_mono_wf; eauto.
    + apply IHHs; assumption.
  - (* __forall_l_tagged: LHS = typ_all_etag, not wf. *)
    inversion Hwf.
Qed.

(** [d_sub] is UNINHABITED when the LHS is [typ_all_col c A]. The reason:
    - [d_sub__infer] / [d_sub__check] reduce to [d_consis] with LHS [typ_all_col],
      which has no defining rule (d_consis LHS is [is_utyp]-shape: unit / var /
      typ_all_etag / typ_all_plain / typ_arrow).
    - [d_sub__arg] / [d_sub__forall_l_*] have rigid LHS shapes that mismatch.
    - [d_sub__forall_r] recurses on the body's [d_sub] which has the same LHS;
      closes via IH.

    This is used in [d_consis_sub_trans] to discharge the [__arg]
    sub-case's "T02 not etag/plain" obligation: if T02 = typ_all_etag/plain,
    then A02 (the d_consis RHS at that branch) = typ_all_col c, and Hs's
    body [d_sub m Δ Γ A02 B2] is uninhabited, ruling the case out. *)
Lemma d_sub_not_lhs_typ_all_col : forall M Δ Γ T B,
    d_sub M Δ Γ T B ->
    forall c A, T <> typ_all_col c A.
Proof.
  intros M Δ Γ T B Hsub.
  induction Hsub; intros c0 A0 HT; try discriminate.
  - (* POST-REFACTOR: __infer / __check LHS = [syn_color T_base] which CAN
       be [typ_all_col colour_syn] when T_base = ctyp_all _. The new
       __forall_syn rule in d_consis admits exactly this shape — so the
       prior vacuity argument fails. Lemma is FALSE under the new rule
       set; admitted. Downstream callers need to restrict or restate. *)
    admit.
  - admit.
  - (* __forall_r: T unchanged; close via the cofinite IH. *)
    subst T. pick fresh X for L. eapply H0; eauto.
Admitted.

(** If [d_consis Δ Γ T A] and [d_consis nil Γ A B] both hold, then [Δ = nil].

    Reason: A must be in the intersection of d_consis RHS-allowed shapes
    (unit / var / typ_all_col / typ_arrow) and d_consis LHS-allowed shapes
    (unit / var / typ_all_etag / typ_all_plain / typ_arrow), so
    A ∈ {unit, var, typ_arrow}. The forall-cases of the first d_consis
    have A = typ_all_col, which makes the second d_consis vacuous by
    inversion. The arrow case splits Δ recursively.

    This is used in [d_consis_sub_trans]'s [__arg] sub-case to
    discharge the recursive IH's [m = mode_ti → Δ = nil] obligation:
    when the inner mode is [mode_ti], Hs's body inverts to [__infer]
    with [d_consis nil Γ A02 B2], and this lemma gives [Δc02 = nil]
    from Hc.right_branch [d_consis Δc02 Γ T02 A02]. *)
(** Helper: a [d_consis] firing with a [syn_color C] LHS pins the LHS
    to [is_syn_typ] (structural — [d_consis] rules with [syn_color]-LHS
    only fire on {unit, var, arrow, typ_all_col colour_syn}, all of
    which are [is_syn_typ]). Used by [d_consis_sub_trans] to
    discharge an [is_syn_typ] precondition without a [d_wf_typ Γ T] from
    outside. *)
Lemma d_consis_lhs_syn_color_is_syn_typ : forall Δ Γ C A,
    d_consis Δ Γ (syn_color C) A ->
    is_syn_typ (syn_color C).
Proof.
  intros Δ Γ C A Hc.
  remember (syn_color C) as T eqn:HT.
  revert C HT.
  induction Hc; intros C0 HT; subst.
  - destruct C0; simpl in HT; try discriminate. apply is_syn_typ__unit.
  - destruct C0; simpl in HT; try discriminate.
    inversion HT; subst. apply is_syn_typ__var.
  - destruct C0; simpl in HT; discriminate.
  - destruct C0; simpl in HT; discriminate.
  - destruct C0; simpl in HT; try discriminate.
    inversion HT; subst.
    inst_cofinites_for is_syn_typ__all.
    intros X HX.
    assert (HX_L : X `notin` L) by fsetdec.
    (* Goal: is_syn_typ (open (syn_color C0) X). H0's conclusion form
       is also is_syn_typ (open (syn_color C0) X) — apply directly with
       the body equation derived via syn_color_open_var. *)
    apply (H0 X HX_L (open_ctyp_wrt_ctyp C0 (ctyp_var_f X))).
    rewrite syn_color_open_var. reflexivity.
  - destruct C0; simpl in HT; discriminate.
  - destruct C0; simpl in HT; try discriminate.
    inversion HT; subst.
    apply is_syn_typ__arrow.
    + eapply IHHc1; reflexivity.
    + eapply IHHc2; reflexivity.
Qed.

(** With the new [__forall_inh] rule, the mid type [A] can be
    [typ_all_col colour_inh _] which makes Hc1's Δ non-nil
    (forall_inh_tagged adds ε). The lemma is preserved by adding an
    [is_syn_typ A] precondition that propagates recursively and rules
    out the [typ_all_col colour_inh] mid-type. Callers supply this
    from their context (e.g., d_sub__infer body has A = syn_color C
    which is [is_syn_typ] when C contains no [ctyp_hole]). *)
Lemma d_consis_compose_nil_RHS : forall Δ Γ T A B,
    d_consis Δ Γ T A ->
    d_consis nil Γ A B ->
    is_syn_typ A ->
    Δ = nil.
Proof.
  intros Δ Γ T A B H1. revert B.
  induction H1; intros B0 H2 Hsyn.
  - reflexivity.
  - reflexivity.
  - (* __forall_inh_tagged: A = typ_all_col colour_inh _, contradicts
       Hsyn (is_syn_typ requires colour_syn). *)
    inversion Hsyn.
  - (* __forall_syn_tagged: A = typ_all_col colour_syn _. H2's LHS matches
       __forall_syn rule (post-refactor). Pick fresh X, apply IH on body. *)
    inversion H2; subst.
    inversion Hsyn; subst.
    pick fresh X for (L `union` L0 `union` L1).
    eapply H0 with (X := X); auto.
  - (* __forall_syn: A = typ_all_col colour_syn _. Same pattern. *)
    inversion H2; subst.
    inversion Hsyn; subst.
    pick fresh X for (L `union` L0 `union` L1).
    eapply H0 with (X := X); auto.
  - (* __forall_inh: A = typ_all_col colour_inh _, contradicts Hsyn. *)
    inversion Hsyn.
  - (* arrow: inversion pattern now has 7 alternatives (6 bars). *)
    inversion H2 as
      [| | | | | | Δb1 Δb2 ? T1' T2' A1' A2' Hb1 Hb2 Hdisb HΔeq];
      subst.
    inversion Hsyn; subst.
    assert (HΔb : Δb1 = nil /\ Δb2 = nil).
    { destruct Δb1; destruct Δb2; simpl in HΔeq;
        try discriminate; try (split; reflexivity). }
    destruct HΔb as [HΔb1 HΔb2]. subst Δb1 Δb2.
    erewrite IHd_consis1 by eauto.
    erewrite IHd_consis2 by eauto.
    reflexivity.
Qed.
