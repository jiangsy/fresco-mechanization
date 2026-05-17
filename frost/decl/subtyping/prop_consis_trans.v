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
  (* δ-encoding refactor (2026-05-17): adding [d_consis__forall_inh_untagged]
     introduces 3 new compositional sub-cases in this proof:
     - Hc1 = __forall_syn_tagged × Hc2 = __forall_inh_untagged
     - Hc1 = __forall_syn × Hc2 = __forall_inh_untagged
     - Hc1 = __forall_inh_untagged (new top-level case) × Hc2 = __forall_inh
     Each requires a new cofinite-rename argument. The full restructure is
     deferred — admitting wholesale to gate the n-arg lemma work.
     See [docs/superpowers/specs/2026-05-17-delta-encoding-refactor-design.md]. *)
  admit.
  (* original proof preserved below as a comment for re-introduction. *)
  (*
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
       Hc2's matching rules: __forall_syn (existing) and
       __forall_inh_untagged (NEW δ=·, constructor declared earlier so
       appears as FIRST surviving subgoal in inversion order). *)
    inversion Hc2; subst;
      [ (* Hc2 = __forall_inh_untagged: compose syn-tagged with untagged-inh
           gives a [__forall_inh_tagged] result. Non-trivial composition
           involving cross-colour bridge — admitted.
           See [docs/superpowers/specs/2026-05-17-delta-encoding-refactor-design.md]. *)
        admit
      | ].
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
  - (* __forall_syn: Hc1 LHS = RHS = typ_all_col colour_syn. Hc2's
       matching rules: __forall_syn (existing) and __forall_inh_untagged
       (NEW, appears first in inversion order). *)
    inversion Hc2; subst;
      [ (* Hc2 = __forall_inh_untagged: compose syn-untagged with
           untagged-inh gives __forall_inh_untagged result. Admitted. *)
        admit
      | ].
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
  - (* __forall_inh_untagged (NEW Hc1 case): Hc1's RHS = typ_all_col
       colour_inh A. Hc2's only matching rule is __forall_inh.
       Compose via cofinite-rename, parallel to __forall_inh. *)
    admit.
  - (* arrow: split Hc2 via inversion; recurse on each side; assemble
       via [list_swap_middle] and the disjointness decomposition. The
       inversion pattern has 8 alternatives (7 bars before [__arrow])
       for the now 8-rule d_consis (added __forall_inh_untagged). *)
    inversion Hc2 as [| | | | | | |Δb1 Δb2 ? T1' T2' A1' A2' Hb1 Hb2 Hdis_b];
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
  *)
Admitted.
(* d_consis_compose: WHOLESALE ADMIT — δ-encoding refactor (2026-05-17)
   adds new sub-cases (3 sub-case combinations + 1 new top-level)
   requiring substantial proof restructuring. Original proof body
   commented out; needs adaptation for [d_consis__forall_inh_untagged].
   See spec at docs/superpowers/specs/2026-05-17-delta-encoding-refactor-design.md *)

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
    Δ ⨟ Γ ⊨ T ≈ A ->
    d_wf_typ Γ T ->
    is_utyp T ->
    mono_typ T.
Proof.
  intros Δ Γ T A Hc Hwf Hut. induction Hc; inversion Hwf; subst.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - (* __forall_inh_untagged (NEW d_consis rule): T = typ_all_col colour_syn _.
       With is_utyp__pall (NEW), is_utyp now PERMITS typ_all_col colour_syn,
       so this case is no longer vacuous. The conclusion [mono_typ T] is
       false here (typ_all_col is not mono). Lemma is provably false in
       this case post-δ-refactor — strengthening needed. Admitted. *)
    admit.
  - (* __forall_syn: T = typ_all_col colour_syn _. Same issue. *)
    admit.
  - (* __forall_inh: T = typ_all_col colour_inh _, NOT is_utyp (only
       colour_syn permitted via __pall). *)
    inversion Hut.
  - inversion Hut; subst. apply mono_typ__arrow.
    + apply IHHc1; auto.
    + apply IHHc2; auto.
Admitted.
(* d_consis_LHS_mono_wf: 2 admits post-δ-refactor — lemma's conclusion
   [mono_typ T] is FALSE when T = typ_all_col colour_syn (now allowed by
   is_utyp__pall). Needs strengthening (e.g., exclude __pall, restrict
   T further). See spec at
   docs/superpowers/specs/2026-05-17-delta-encoding-refactor-design.md *)

(* [d_consis_LHS_is_utyp_when_RHS_syn_color] (formerly here) DELETED
   2026-05-17 — provably FALSE post-refactor: the new
   [d_consis__forall_syn] rule (LHS/RHS both [typ_all_col colour_syn])
   admits a non-[is_utyp] LHS. Had zero callers; the original
   callsites in [prop_general_subsumption.v] / [d12.v] were rewritten
   to use [d_consis_gen_RHS_syn_color_eq] (a Qed analogue with stronger
   wf hypothesis) before this deletion. *)

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
    Δ ⨟ Γ ⊨ T ≈ A ->
    is_typ T ->
    is_utyp T ->
    mono_typ T.
Proof.
  intros Δ Γ T A Hc Hist Hut. induction Hc; inversion Hist; subst.
  - apply mono_typ__unit.
  - apply mono_typ__var.
  - (* __forall_inh_untagged (NEW): T = typ_all_col colour_syn; is_utyp
       NOW PERMITS this via __pall. Lemma false here. *)
    admit.
  - (* __forall_syn: T = typ_all_col colour_syn; is_utyp permits via __pall. *)
    admit.
  - (* __forall_inh: T = typ_all_col colour_inh; not is_utyp. *)
    inversion Hut.
  - inversion Hut; subst. apply mono_typ__arrow.
    + apply IHHc1; assumption.
    + apply IHHc2; assumption.
Admitted.
(* d_consis_LHS_is_typ_mono: same δ-refactor admits as
   d_consis_LHS_mono_wf. *)

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
    Δ ⨟ Γ ⊨ T ≈ A ->
    mono_typ A ->
    mono_typ T /\ Δ = nil /\ T = A.
Proof.
  intros Δ Γ T A Hc. induction Hc; intros Hmono.
  - split; [|split]; [apply mono_typ__unit | reflexivity | reflexivity].
  - split; [|split]; [apply mono_typ__var | reflexivity | reflexivity].
  - (* __forall_inh_tagged: RHS = typ_all_col colour_inh, not mono. *)
    inversion Hmono.
  - (* __forall_inh_untagged (NEW): RHS = typ_all_col colour_inh, not mono. *)
    inversion Hmono.
  - (* __forall_syn_tagged: RHS = typ_all_col colour_syn, not mono. *)
    inversion Hmono.
  - (* __forall_syn: A = typ_all_col colour_syn, not mono. *)
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
    Δ ⨟ Γ ⊨ T ≈ A ->
    mono_typ T ->
    A = T /\ Δ = nil.
Proof.
  intros Δ Γ T A Hc Hmono. induction Hc.
  - split; reflexivity.
  - split; reflexivity.
  - (* __forall_inh_tagged: T = typ_all_etag — not mono. *) inversion Hmono.
  - (* __forall_inh_untagged (NEW): T = typ_all_col — not mono. *) inversion Hmono.
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
    Γ ⊢[ m ; nil ] (typ_arrow A B) ⊑ (typ_arrow A B) ->
    mono_typ A ->
    mono_typ B ->
    Γ ⊢[ (decr_mode m) ; nil ] B ⊑ B.
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
    Γ ⊢[ M ; Δ ] T ⊑ A ->
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
  - (* __forall_l_untagged (NEW): LHS = typ_all_col colour_syn. With
       is_utyp__pall (NEW), this IS is_utyp. Conclusion [mono_typ] is
       false here — admitted. *)
    admit.
Admitted.
(* d_sub_LHS_mono_wf: 1 admit post-δ-refactor — same shape issue as
   d_consis_LHS_mono_wf. *)

(* [d_sub_not_lhs_typ_all_col] (formerly here) DELETED 2026-05-17 —
   provably FALSE post-refactor: [d_sub__infer] / [d_sub__check] LHS
   is [syn_color T_base] which CAN be [typ_all_col colour_syn] (when
   T_base = ctyp_all _), admitted by the new [d_consis__forall_syn]
   rule. Had zero callers. *)

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
    Δ ⨟ Γ ⊨ (syn_color C) ≈ A ->
    is_syn_typ (syn_color C).
Proof.
  intros Δ Γ C A Hc.
  remember (syn_color C) as T eqn:HT.
  revert C HT.
  induction Hc; intros C0 HT; subst.
  - destruct C0; simpl in HT; try discriminate. apply is_syn_typ__unit.
  - destruct C0; simpl in HT; try discriminate.
    inversion HT; subst. apply is_syn_typ__var.
  - (* __forall_inh_tagged: LHS = typ_all_etag, syn_color never produces. *)
    destruct C0; simpl in HT; discriminate.
  - (* __forall_inh_untagged (NEW): LHS = typ_all_col colour_syn, syn_color
       produces this when C0 = ctyp_all C0'. Same handling as forall_syn. *)
    destruct C0; simpl in HT; try discriminate.
    inversion HT; subst.
    inst_cofinites_for is_syn_typ__all.
    intros X HX.
    assert (HX_L : X `notin` L) by fsetdec.
    apply (H0 X HX_L (open_ctyp_wrt_ctyp C0 (ctyp_var_f X))).
    rewrite syn_color_open_var. reflexivity.
  - (* __forall_syn_tagged: LHS = typ_all_etag, syn_color never produces. *)
    destruct C0; simpl in HT; discriminate.
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
    Δ ⨟ Γ ⊨ T ≈ A ->
    nil ⨟ Γ ⊨ A ≈ B ->
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
  - (* __forall_inh_untagged (NEW): A = typ_all_col colour_inh _,
       contradicts Hsyn. *)
    inversion Hsyn.
  - (* __forall_syn_tagged: A = typ_all_col colour_syn _. H2's LHS matches
       __forall_syn OR new __forall_inh_untagged (constructor order puts
       the latter first in inversion). *)
    inversion H2; subst.
    + (* H2 = __forall_inh_untagged NEW: deferred. *) admit.
    + (* H2 = __forall_syn: original body. *)
      inversion Hsyn; subst.
      pick fresh X for (L `union` L0 `union` L1).
      eapply H0 with (X := X); auto.
  - (* __forall_syn: A = typ_all_col colour_syn _. Same multi-case as above. *)
    inversion H2; subst.
    + (* H2 = __forall_inh_untagged NEW: deferred. *) admit.
    + (* H2 = __forall_syn: original body. *)
      inversion Hsyn; subst.
      pick fresh X for (L `union` L0 `union` L1).
      eapply H0 with (X := X); auto.
  - (* __forall_inh: A = typ_all_col colour_inh _, contradicts Hsyn. *)
    inversion Hsyn.
  - (* arrow: inversion pattern now has 8 alternatives (7 bars) for the
       8-rule d_consis. *)
    inversion H2 as
      [| | | | | | | Δb1 Δb2 ? T1' T2' A1' A2' Hb1 Hb2 Hdisb HΔeq];
      subst.
    inversion Hsyn; subst.
    assert (HΔb : Δb1 = nil /\ Δb2 = nil).
    { destruct Δb1; destruct Δb2; simpl in HΔeq;
        try discriminate; try (split; reflexivity). }
    destruct HΔb as [HΔb1 HΔb2]. subst Δb1 Δb2.
    erewrite IHd_consis1 by eauto.
    erewrite IHd_consis2 by eauto.
    reflexivity.
Admitted.
(* d_consis_compose_nil_RHS: 2 sub-case admits for H2 = __forall_inh_untagged
   in Hc1 = __forall_syn_tagged / __forall_syn cases. See spec. *)

(** [d_consis_syn_inh_erase_eq]: a [d_consis] with [is_syn_typ] LHS and
    [is_inh_typ] RHS gives an [erase]-equality (colour-blind ctyp
    equality). This is the [erase] weakening of the literally-false
    "syn-LHS = inh-RHS" claim — the literal version fails for the new
    [__forall_inh_untagged] case (LHS [typ_all_col colour_syn _] vs RHS
    [typ_all_col colour_inh _] — same erase shape, different colours).

    The lemma IS provable because [erase] discards colour: for
    [__forall_inh_untagged], [erase (typ_all_col colour_syn T') =
    erase (typ_all_col colour_inh A') = ctyp_all _], and the cofinite
    IH on the body gives the inner erase-equality.

    Used by the SPLIT helpers to derive ctyp-equality between the
    cofinitely-bound types, enabling the chain that previously used the
    provably-false [d_consis_lhs_syn_eq]. *)
Lemma d_consis_syn_inh_erase_eq : forall Γ Δ T A,
    Δ ⨟ Γ ⊨ T ≈ A ->
    is_syn_typ T ->
    is_inh_typ A ->
    erase T = erase A.
Proof.
  intros Γ Δ T A Hc.
  induction Hc; intros Hsyn Hinh.
  - (* __unit *) reflexivity.
  - (* __var *) reflexivity.
  - (* __forall_inh_tagged: T = typ_all_etag — is_syn_typ excludes. *)
    inversion Hsyn.
  - (* __forall_inh_untagged (NEW δ): T = typ_all_col colour_syn,
       A = typ_all_col colour_inh. erase typ_all_col c X = ctyp_all (erase X)
       — colour discarded; both sides give ctyp_all (erase body). *)
    simpl. f_equal.
    inversion Hsyn; subst.
    inversion Hinh; subst.
    pick fresh X for (L `union` L0 `union` L1
                      `union` ftvar_in_typ T `union` ftvar_in_typ A).
    assert (Heq_open : erase (open_typ_wrt_typ T (typ_var_f X))
                     = erase (open_typ_wrt_typ A (typ_var_f X))).
    { eapply H0; auto. }
    rewrite !erase_open_typ in Heq_open.
    simpl in Heq_open.
    apply open_ctyp_wrt_ctyp_inj in Heq_open; auto; rewrite erase_ftvar; auto.
  - (* __forall_syn_tagged: T = typ_all_etag — is_syn_typ excludes. *)
    inversion Hsyn.
  - (* __forall_syn: T = typ_all_col colour_syn, A = typ_all_col colour_syn.
       is_inh_typ A requires colour_inh — contradicts. *)
    inversion Hinh.
  - (* __forall_inh: T = typ_all_col colour_inh — is_syn_typ excludes. *)
    inversion Hsyn.
  - (* __arrow: recurse on sub-parts. *)
    simpl. f_equal.
    + inversion Hsyn; subst. inversion Hinh; subst. eauto.
    + inversion Hsyn; subst. inversion Hinh; subst. eauto.
Qed.
