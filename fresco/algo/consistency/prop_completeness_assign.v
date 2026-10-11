(** Assignment completeness step and its witnesses. *)

Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.consistency.prop_precision_recovery.
Require Import src.fresco.algo.consistency.prop_consis_rename.

Set Implicit Arguments.

Require Export src.fresco.algo.consistency.prop_consis_solution.
Require Export src.fresco.algo.consistency.prop_completeness_unify.

(** Part 3 of the paper's proof (:2403-2559): assignment, by a walk of the
    context pair [Θ0 ∣ Ξ] ([n = |Ξ|+|Θ0|] on the skips, [k = |Θ0|] on
    Assign-Depend; the Assign-Assign back-edge re-enters part 1 with [V]
    constant and [n] one smaller). *)

(* ===================================================================== *)
(*  §2f  Assign-SolveM enablers: metasubstitution helpers                                    *)
(* ===================================================================== *)

(** An identity metasubstitution's mid entry is the identity on its key. *)
Lemma is_id_msubst_mid : forall κa β τ κb,
  is_id_msubst (κa ++ (β, τ) :: κb) ->
  τ = ptyp_var_f β /\ is_id_msubst (κa ++ κb).
Proof.
  induction κa as [ | [a t] κa' IH ]; intros β τ κb Hid; simpl in *.
  - apply is_id_msubst_inv in Hid as [Heq Hid']; auto.
  - inversion Hid as [ | e es He Hes ]; subst.
    destruct (IH _ _ _ Hes) as [Heq Hid']; subst.
    split; [ reflexivity | constructor; assumption ].
Qed.

(** Composition with an identity multiplicand only reads the left factor's
    lookups on the identity's keys. *)
Lemma msubst_compose_agree_id : forall ζ ζ' κ1,
  is_id_msubst κ1 ->
  (forall α, α `in` dom κ1 -> msubst_lookup ζ α = msubst_lookup ζ' α) ->
  msubst_compose ζ κ1 = msubst_compose ζ' κ1.
Proof.
  intros ζ ζ' κ1; induction κ1 as [ | [a t] κ1' IH ]; intros Hid Hag;
    [ reflexivity | ].
  apply is_id_msubst_inv in Hid as [Heq Hid']; subst.
  unfold msubst_compose in *; simpl.
  rewrite (Hag a) by (simpl; fsetdec).
  rewrite IH; [ reflexivity | exact Hid' | ].
  intros α Hα. apply Hag. simpl. fsetdec.
Qed.

(** [msubst_compose_is_id_r] with a source-disjoint prefix on the left
    factor: the prefix is never consulted on the identity's keys. *)
Lemma msubst_compose_is_id_r_ext : forall Θ0 κ1 Θ1 κ Θ ζpre,
  {{ ⊢ Θ0 }}a ->
  is_id_msubst κ1 ->
  κ1 ∷ Θ0 ⊑ Θ1 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, α `in` dom ζpre -> α `notin` dom Θ0) ->
  msubst_compose (ζpre ++ κ) κ1 = κ.
Proof.
  intros Θ0 κ1 Θ1 κ Θ ζpre Hwf Hid Hinc1 Hinc Hdisj.
  assert (Hag : forall α, α `in` dom κ1 ->
            msubst_lookup (ζpre ++ κ) α = msubst_lookup κ α).
  { intros α Hα.
    pose proof (a_inc_dom_sub Hinc1) as Hsub.
    apply msubst_lookup_app_notin.
    assert (HαΘ0 : α `in` dom Θ0) by (clear - Hα Hsub; fsetdec).
    destruct (AtomSetProperties.In_dec α (dom ζpre)) as [Hin | Hni];
      [ exfalso; exact (Hdisj α Hin HαΘ0) | exact Hni ]. }
  rewrite (@msubst_compose_agree_id (ζpre ++ κ) κ κ1 Hid Hag).
  eapply msubst_compose_is_id_r; eauto.
Qed.

(* ===================================================================== *)
(*  §2g  Assign-SolveM: the var-base mono bridge                          *)
(* ===================================================================== *)

Lemma join_var_tyequiv : forall Ψ Θ A A',
  {{ Ψ ⨟ Θ ⊢ˢ (pskl_to_uskl (ptyp_to_pskl A)) ∼ (ptyp_to_bskl_syn A') }}ad ->
  {{ ⊢ Θ }}a ->
  mono_ptyp A ->
  mono_ptyp A' ->
  {{ Θ ⊢ A ≡ᵗ A' }}a.
Proof.
  intros Ψ Θ A A' Hc Hwf HmA HmC.
  rewrite pskl_to_uskl_ptyp in Hc.
  destruct (consis_mono_join Hc Hwf (A := A) eq_refl HmA)
    as [C' [HmC' [HeqQ Heqv]]].
  assert (HeqC : C' = A')
    by (apply ptyp_to_bskl_syn_inj; auto).
  subst C'. exact Heqv.
Qed.

(* ===================================================================== *)
(*  §2h  Assign-SolveM: OCCURS — the α-occurrence size walk                               *)
(* ===================================================================== *)

Lemma occurs_join_size_aux : forall Ψ Θ R' Q,
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall κm,
  (forall α', mono_ptyp (msubst_lookup κm α')) ->
  forall α P A Θw Δw,
    (forall α', P <> pskl_var_f α') ->
    R' = pskl_to_uskl (msubst_pskl κm P) ->
    Q = ptyp_to_bskl_syn A ->
    mono_ptyp A ->
    {{ Θw ⨟ Δw ⊢ₚₛ P }}a ->
    α `in` ftvar_in_pskl P ->
    size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α)) <= size_ptyp (⇓ᵗ[Θ] A) /\
    (P = pskl_univ_ghost (pskl_var_f α) \/
     size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α)) < size_ptyp (⇓ᵗ[Θ] A)).
Proof.
  intros Ψ Θ R' Q Hc Hwf κm Hmlk.
  induction Hc; intros α0 P0 C0 Θw Δw Hnv HeqS HeqQ HmC0 HwfP0 Hocc.
  - (* unit *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    simpl in Hocc. exfalso. clear - Hocc. fsetdec.
  - (* var *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* arrow *)
    destruct P0 as [ | | α' | P1 P2 | | | ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R1 R2.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst Q1 Q2.
    inversion HmC0; subst.
    match goal with H : mono_ptyp C1 |- _ => rename H into HmC1 end.
    match goal with H : mono_ptyp C2 |- _ => rename H into HmC2 end.
    inversion HwfP0; subst.
    match goal with H : {{ Θw ⨟ Δw ⊢ₚₛ P1 }}a |- _ => rename H into HwfP1 end.
    match goal with H : {{ Θw ⨟ Δw ⊢ₚₛ P2 }}a |- _ => rename H into HwfP2 end.
    simpl in Hocc. apply union_1 in Hocc.
    destruct Hocc as [Hocc | Hocc].
    + (* α ∈ ftv P1 *)
      assert (Hle : size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α0))
                      <= size_ptyp (⇓ᵗ[Θ] C1)).
      { destruct (pskl_var_dec P1) as [[α'1 HeqP1] | Hnv1].
        - subst P1. simpl in Hocc.
          assert (HeqX : α'1 = α0) by (clear - Hocc; fsetdec). subst α'1.
          simpl in Hc1.
          rewrite (a_tyequiv_downarrow Hwf
                     (join_var_tyequiv Hc1 Hwf (Hmlk α0) HmC1)).
          lia.
        - destruct (IHHc1 Hwf α0 P1 C1 Θw Δw Hnv1 eq_refl eq_refl
                      HmC1 HwfP1 Hocc) as [Hle1 _].
          exact Hle1. }
      split; [ | right ];
        simpl; pose proof (size_ptyp_min (⇓ᵗ[Θ] C2)); lia.
    + (* α ∈ ftv P2 *)
      assert (Hle : size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α0))
                      <= size_ptyp (⇓ᵗ[Θ] C2)).
      { destruct (pskl_var_dec P2) as [[α'2 HeqP2] | Hnv2].
        - subst P2. simpl in Hocc.
          assert (HeqX : α'2 = α0) by (clear - Hocc; fsetdec). subst α'2.
          simpl in Hc2.
          rewrite (a_tyequiv_downarrow Hwf
                     (join_var_tyequiv Hc2 Hwf (Hmlk α0) HmC2)).
          lia.
        - destruct (IHHc2 Hwf α0 P2 C2 Θw Δw Hnv2 eq_refl eq_refl
                      HmC2 HwfP2 Hocc) as [Hle2 _].
          exact Hle2. }
      split; [ | right ];
        simpl; pose proof (size_ptyp_min (⇓ᵗ[Θ] C1)); lia.
  - (* forall_inh_tagged : R' = uskl_all_tag, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_inh_untagged : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* forall_syn_tagged : R' = uskl_all_tag, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_syn : Q = bskl_all_syn, mono A refutes *)
    destruct C0; simpl in HeqQ; try discriminate. inversion HmC0.
  - (* ghostg : R' = uskl_dot_ghost, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* dot_univ_ghost : R' = uskl_dot_univ_ghost, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* ghost : P = ghost, no free variables *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    simpl in Hocc. exfalso. clear - Hocc. fsetdec.
  - (* univ_ghost : Q = bskl_univ_ghost, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* univ_ghost_inh : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* univ_ghost_drop : P = ∀◇P', same A *)
    destruct P0 as [ | | | | | | P' ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R.
    inversion HwfP0; subst.
    match goal with H : guarded_pskl P' |- _ => rename H into Hgu end.
    match goal with H : {{ _ ⨟ empty ⊢ₚₛ P' }}a |- _ => rename H into HwfP' end.
    simpl in Hocc.
    destruct (pskl_var_dec P') as [[α'' HeqP'] | Hnv'].
    + (* P = ∀◇α'' : the drop-to-var base *)
      subst P'. simpl in Hocc.
      assert (HeqX : α'' = α0) by (clear - Hocc; fsetdec). subst α''.
      simpl in Hc.
      rewrite (a_tyequiv_downarrow Hwf
                 (join_var_tyequiv Hc Hwf (Hmlk α0) HmC0)).
      split; [ lia | left; reflexivity ].
    + (* body not a var : recurse; P' = ∀◇α̂ is killed by guardedness *)
      destruct (IHHc Hwf α0 P' C0 (aenv_minus Θw Δw) empty Hnv' eq_refl eq_refl
                  HmC0 HwfP' Hocc) as [Hle Hdisj].
      split; [ exact Hle | right ].
      destruct Hdisj as [HeqP' | Hlt]; [ | exact Hlt ].
      subst P'. inversion Hgu.
  - (* flex_l : R' = uskl_var, P must be a var — excluded *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* flex_r : unfold the RHS definition, same P *)
    destruct C0 as [ | | α'0 | | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst α'0.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHc Hwf α0 P0 τ Θw Δw Hnv HeqS eq_refl Hmτ HwfP0 Hocc)
      as [Hle Hdisj].
    assert (Heqd : ⇓ᵗ[Θ] (ptyp_var_f α) = ⇓ᵗ[Θ] τ)
      by (apply a_tyequiv_downarrow;
          [ exact Hwf | apply a_tyequiv__flex_def; exact H ]).
    rewrite Heqd. split; [ exact Hle | exact Hdisj ].
Qed.

(** The wrapper: full occurs-size fact, var case included. *)
Lemma occurs_join_size : forall Ψ Θ κm α P A Θw Δw,
  {{ Ψ ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κm P)) ∼ (ptyp_to_bskl_syn A) }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α0, mono_ptyp (msubst_lookup κm α0)) ->
  mono_ptyp A ->
  {{ Θw ⨟ Δw ⊢ₚₛ P }}a ->
  α `in` ftvar_in_pskl P ->
  size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α)) <= size_ptyp (⇓ᵗ[Θ] A) /\
  (P = pskl_var_f α \/ P = pskl_univ_ghost (pskl_var_f α) \/
   size_ptyp (⇓ᵗ[Θ] (msubst_lookup κm α)) < size_ptyp (⇓ᵗ[Θ] A)).
Proof.
  intros Ψ Θ κm α P A Θw Δw Hc Hwf Hmlk HmC HwfP Hocc.
  destruct (pskl_var_dec P) as [[α0 HeqP] | Hnv].
  - (* P = var α0 *)
    subst P. simpl in Hocc.
    assert (HeqX : α0 = α) by (clear - Hocc; fsetdec). subst α0.
    simpl in Hc.
    rewrite (a_tyequiv_downarrow Hwf
               (join_var_tyequiv Hc Hwf (Hmlk α) HmC)).
    split; [ lia | left; reflexivity ].
  - destruct (occurs_join_size_aux Hc Hwf κm Hmlk Hnv eq_refl eq_refl
                HmC HwfP Hocc) as [Hle Hdisj].
    split; [ exact Hle | destruct Hdisj; auto ].
Qed.

(* ===================================================================== *)
(*  §2i  Assign-SolveM: GUESS — existence + the ζ-images from the join                   *)
(* ===================================================================== *)

(** The trivial tuple at a variable: guess keeps the variable, no fresh
    names, and the equation is the base bridge. *)
Lemma guess_witness_var_tuple : forall Θ κm α A L,
  {{ Θ ⊢ (msubst_lookup κm α) ≡ᵗ A }}a ->
  exists βs τg ζβ,
    (forall Θg,
       (forall α0, α0 `in` dom βs -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg (pskl_var_f α) βs τg) /\
    mono_ptyp τg /\
    uniq βs /\
    (forall α10, α10 `in` dom βs -> α10 `notin` L) /\
    dom ζβ [=] dom βs /\
    (forall E κE, κE ∷ E ⊑ Θ -> ζβ ++ κE ∷ (βs ++ E) ⊑ Θ) /\
    {{ Θ ⊢ (msubst_ptyp (ζβ ++ κm) τg) ≡ᵗ A }}a.
Proof.
  intros Θ κm α A L Heqv.
  exists nil, (ptyp_var_f α), (@nil (atom * ptyp)).
  split; [ intros Θg _; apply a_guess_mono__var | ].
  split; [ apply mono_ptyp__var | ].
  split; [ constructor | ].
  split; [ intros α10 Hγ0; simpl in Hγ0; exfalso; clear - Hγ0; fsetdec | ].
  split; [ simpl; reflexivity | ].
  split; [ intros E κE HE; simpl; exact HE | ].
  simpl. exact Heqv.
Qed.

Lemma guess_join_witness_aux : forall Ψ Θ R' Q,
  {{ Ψ ⨟ Θ ⊢ˢ R' ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  forall κm,
  (forall α, mono_ptyp (msubst_lookup κm α)) ->
  forall P A,
    (forall α, P <> pskl_var_f α) ->
    R' = pskl_to_uskl (msubst_pskl κm P) ->
    Q = ptyp_to_bskl_syn A ->
    mono_ptyp A ->
    a_wf_ptyp Θ A ->
    forall L, exists βs τg ζβ,
      (forall Θg,
       (forall α0, α0 `in` dom βs -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P βs τg) /\
      mono_ptyp τg /\
      uniq βs /\
      (forall α10, α10 `in` dom βs -> α10 `notin` L) /\
      dom ζβ [=] dom βs /\
      (forall E κE, κE ∷ E ⊑ Θ -> ζβ ++ κE ∷ (βs ++ E) ⊑ Θ) /\
      {{ Θ ⊢ (msubst_ptyp (ζβ ++ κm) τg) ≡ᵗ A }}a.
Proof.
  intros Ψ Θ R' Q Hc Hwf κm Hmlk.
  induction Hc; intros P0 C0 Hnv HeqS HeqQ HmC0 HwfC0 Lav.
  - (* unit *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    destruct C0; simpl in HeqQ; try discriminate.
    exists nil, ptyp_unit, (@nil (atom * ptyp)).
    split; [ intros Θg _; apply a_guess_mono__unit | ].
    split; [ apply mono_ptyp__unit | ].
    split; [ constructor | ].
    split; [ intros α10 Hγ0; simpl in Hγ0; exfalso; clear - Hγ0; fsetdec | ].
    split; [ simpl; reflexivity | ].
    split; [ intros E κE HE; simpl; exact HE | ].
    simpl. apply a_tyequiv__refl. apply lc_ptyp_unit.
  - (* var : P must be a var — excluded *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* arrow *)
    destruct P0 as [ | | α | P1 P2 | | | ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R1 R2.
    destruct C0 as [ | | | C1 C2 | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst Q1 Q2.
    inversion HmC0; subst.
    match goal with H : mono_ptyp C1 |- _ => rename H into HmC1 end.
    match goal with H : mono_ptyp C2 |- _ => rename H into HmC2 end.
    inversion HwfC0; subst.
    match goal with H : a_wf_ptyp Θ C1 |- _ => rename H into HwfC1 end.
    match goal with H : a_wf_ptyp Θ C2 |- _ => rename H into HwfC2 end.
    (* component 1, avoiding Lav ∪ ftv (P1→P2) *)
    set (L1 := Lav `union` ftvar_in_pskl (pskl_arrow P1 P2)).
    assert (Hcomp1 : exists βs1 τ1 ζ1,
        (forall Θg,
       (forall α0, α0 `in` dom βs1 -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P1 βs1 τ1) /\
        mono_ptyp τ1 /\ uniq βs1 /\
        (forall α10, α10 `in` dom βs1 -> α10 `notin` L1) /\
        dom ζ1 [=] dom βs1 /\
        (forall E κE, κE ∷ E ⊑ Θ -> ζ1 ++ κE ∷ (βs1 ++ E) ⊑ Θ) /\
        {{ Θ ⊢ (msubst_ptyp (ζ1 ++ κm) τ1) ≡ᵗ C1 }}a).
    { destruct (pskl_var_dec P1) as [[α1 HeqP1] | Hnv1].
      - subst P1. simpl in Hc1.
        apply guess_witness_var_tuple.
        apply (join_var_tyequiv Hc1 Hwf (Hmlk α1) HmC1).
      - apply (IHHc1 Hwf P1 C1 Hnv1 eq_refl eq_refl HmC1 HwfC1 L1). }
    destruct Hcomp1 as [βs1 [τ1 [ζ1 [Hg1 [Hm1 [Hu1 [Hf1 [Hd1 [Ht1 He1]]]]]]]]].
    set (L2 := L1 `union` dom βs1).
    assert (Hcomp2 : exists βs2 τ2 ζ2,
        (forall Θg,
       (forall α0, α0 `in` dom βs2 -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P2 βs2 τ2) /\
        mono_ptyp τ2 /\ uniq βs2 /\
        (forall α10, α10 `in` dom βs2 -> α10 `notin` L2) /\
        dom ζ2 [=] dom βs2 /\
        (forall E κE, κE ∷ E ⊑ Θ -> ζ2 ++ κE ∷ (βs2 ++ E) ⊑ Θ) /\
        {{ Θ ⊢ (msubst_ptyp (ζ2 ++ κm) τ2) ≡ᵗ C2 }}a).
    { destruct (pskl_var_dec P2) as [[α2 HeqP2] | Hnv2].
      - subst P2. simpl in Hc2.
        apply guess_witness_var_tuple.
        apply (join_var_tyequiv Hc2 Hwf (Hmlk α2) HmC2).
      - apply (IHHc2 Hwf P2 C2 Hnv2 eq_refl eq_refl HmC2 HwfC2 L2). }
    destruct Hcomp2 as [βs2 [τ2 [ζ2 [Hg2 [Hm2 [Hu2 [Hf2 [Hd2 [Ht2 He2]]]]]]]]].
    exists (βs1 ++ βs2), (ptyp_arrow τ1 τ2), (ζ1 ++ ζ2).
    assert (Hdisj12 : forall α10, α10 `in` dom βs2 -> α10 `notin` dom βs1).
    { intros α10 Hγ0. specialize (Hf2 α10 Hγ0).
      clear - Hf2. unfold L2 in Hf2. fsetdec. }
    (* the two msubst-agree transports *)
    (* the ftv bound is context-free; read it off at [nil], where the
       generated-name guard is vacuous *)
    pose proof (a_guess_mono_ftv (Hg1 nil ltac:(intros; simpl; solve_notin_auto)))
      as Hftv1.
    pose proof (a_guess_mono_ftv (Hg2 nil ltac:(intros; simpl; solve_notin_auto)))
      as Hftv2.
    assert (Hag1 : msubst_ptyp ((ζ1 ++ ζ2) ++ κm) τ1
                 = msubst_ptyp (ζ1 ++ κm) τ1).
    { apply msubst_ptyp_agree. intros α0 HX0.
      assert (HX0' : α0 `in` ftvar_in_pskl P1 `union` dom βs1)
        by (clear - Hftv1 HX0; fsetdec).
      rewrite app_assoc.
      destruct (AtomSetProperties.In_dec α0 (dom ζ1)) as [Hin | Hni].
      - rewrite (msubst_lookup_app_in ζ1 (ζ2 ++ κm) Hin).
        rewrite (msubst_lookup_app_in ζ1 κm Hin). reflexivity.
      - rewrite (msubst_lookup_app_notin _ _ Hni).
        rewrite (msubst_lookup_app_notin _ _ Hni).
        assert (HX0P1 : α0 `in` ftvar_in_pskl P1)
          by (rewrite Hd1 in Hni; clear - HX0' Hni; fsetdec).
        assert (Hniζ2 : α0 `notin` dom ζ2).
        { rewrite Hd2. intros Hin2.
          specialize (Hf2 α0 Hin2). clear - Hf2 HX0P1.
          unfold L2, L1 in Hf2. simpl in Hf2. fsetdec. }
        rewrite (msubst_lookup_app_notin _ _ Hniζ2). reflexivity. }
    assert (Hag2 : msubst_ptyp ((ζ1 ++ ζ2) ++ κm) τ2
                 = msubst_ptyp (ζ2 ++ κm) τ2).
    { apply msubst_ptyp_agree. intros α0 HX0.
      assert (HX0' : α0 `in` ftvar_in_pskl P2 `union` dom βs2)
        by (clear - Hftv2 HX0; fsetdec).
      rewrite app_assoc.
      assert (Hniζ1 : α0 `notin` dom ζ1).
      { rewrite Hd1.
        destruct (AtomSetProperties.In_dec α0 (dom βs2)) as [Hin2 | Hni2].
        - exact (Hdisj12 α0 Hin2).
        - assert (HX0P2 : α0 `in` ftvar_in_pskl P2)
            by (clear - HX0' Hni2; fsetdec).
          intros Hin1. specialize (Hf1 α0 Hin1).
          clear - Hf1 HX0P2. unfold L1 in Hf1. simpl in Hf1. fsetdec. }
      rewrite (msubst_lookup_app_notin _ _ Hniζ1). reflexivity. }
    split; [ intros Θg Hfrg; apply a_guess_mono__arrow;
             [ apply Hg1 | apply Hg2 ];
             intros α0 Hα0; apply Hfrg; rewrite dom_app;
             clear - Hα0; fsetdec | ].
    split; [ apply mono_ptyp__arrow; assumption | ].
    split.
    { apply uniq_app_4; auto.
      unfold disjoint. intros x Hx.
      assert (Hx1 : x `in` dom βs1) by (clear - Hx; fsetdec).
      assert (Hx2 : x `in` dom βs2) by (clear - Hx; fsetdec).
      exfalso. exact (Hdisj12 x Hx2 Hx1). }
    split.
    { intros α10 Hγ0. rewrite dom_app in Hγ0.
      apply union_1 in Hγ0. destruct Hγ0 as [Hγ0 | Hγ0].
      - specialize (Hf1 α10 Hγ0). clear - Hf1. unfold L1 in Hf1. fsetdec.
      - specialize (Hf2 α10 Hγ0). clear - Hf2. unfold L2, L1 in Hf2. fsetdec. }
    split.
    { repeat rewrite dom_app. rewrite Hd1. rewrite Hd2. reflexivity. }
    split.
    { intros E κE HE.
      rewrite app_assoc. rewrite app_assoc.
      apply Ht1. apply Ht2. exact HE. }
    simpl. apply a_tyequiv__arrow;
      [ rewrite Hag1; exact He1 | rewrite Hag2; exact He2 ].
  - (* forall_inh_tagged : R' = uskl_all_tag, unreachable *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_inh_untagged : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* forall_syn_tagged *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* forall_syn : Q = bskl_all_syn, mono A refutes *)
    destruct C0; simpl in HeqQ; try discriminate. inversion HmC0.
  - (* ghostg *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* dot_univ_ghost *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* ghost : the crux — a fresh β̂ whose ζ-image is A *)
    destruct P0; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    destruct (atom_fresh Lav) as [β Hβ].
    exists (β ~ abind_flex_mono), (ptyp_var_f β), ((β, C0) :: nil).
    split; [ intros Θg Hfrg; apply a_guess_mono__ghost;
               apply Hfrg; simpl; fsetdec | ].
    split; [ apply mono_ptyp__var | ].
    split; [ solve_uniq | ].
    split.
    { intros α10 Hγ0. simpl in Hγ0.
      assert (Heqγ : α10 = β) by (clear - Hγ0; fsetdec).
      subst α10. exact Hβ. }
    split; [ simpl; fsetdec | ].
    split.
    { intros E κE HE. simpl.
      apply a_inc__flex; [ exact HE | exact HwfC0 | exact HmC0 ]. }
    simpl. destruct (β == β) as [_ | Hne]; [ | exfalso; auto ].
    apply a_tyequiv__refl. apply mono_ptyp_lc. exact HmC0.
  - (* univ_ghost : Q = bskl_univ_ghost, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* univ_ghost_inh : Q = bskl_all_inh, never a mono syn painting *)
    destruct C0; simpl in HeqQ; discriminate.
  - (* univ_ghost_drop : P = ∀◇P', recurse on the body *)
    destruct P0 as [ | | | | | | P' ]; simpl in HeqS; try discriminate;
      try solve [ exfalso; eapply Hnv; reflexivity ].
    inversion HeqS; subst R.
    assert (Hbody : exists βs τg ζβ,
        (forall Θg,
       (forall α0, α0 `in` dom βs -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P' βs τg) /\
        mono_ptyp τg /\ uniq βs /\
        (forall α10, α10 `in` dom βs -> α10 `notin` Lav) /\
        dom ζβ [=] dom βs /\
        (forall E κE, κE ∷ E ⊑ Θ -> ζβ ++ κE ∷ (βs ++ E) ⊑ Θ) /\
        {{ Θ ⊢ (msubst_ptyp (ζβ ++ κm) τg) ≡ᵗ C0 }}a).
    { destruct (pskl_var_dec P') as [[α' HeqP'] | Hnv'].
      - subst P'. simpl in Hc. rewrite HeqQ in Hc.
        apply guess_witness_var_tuple.
        apply (join_var_tyequiv Hc Hwf (Hmlk α') HmC0).
      - apply (IHHc Hwf P' C0 Hnv' eq_refl HeqQ HmC0 HwfC0 Lav). }
    destruct Hbody as [βs [τg [ζβ [Hg [Hm [Hu [Hf [Hd [Ht He]]]]]]]]].
    exists βs, τg, ζβ.
    split; [ intros Θg Hfrg; apply a_guess_mono__univ_ghost;
               apply Hg; exact Hfrg | ].
    split; [ exact Hm | ].
    split; [ exact Hu | ].
    split; [ exact Hf | ].
    split; [ exact Hd | ].
    split; [ exact Ht | ].
    exact He.
  - (* flex_l : P must be a var — excluded *)
    destruct P0; simpl in HeqS; try discriminate;
      solve [ exfalso; eapply Hnv; reflexivity ].
  - (* flex_r : unfold the RHS definition *)
    destruct C0 as [ | | α0 | | ]; simpl in HeqQ; try discriminate.
    inversion HeqQ; subst α0.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    assert (Hwτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eauto).
    destruct (IHHc Hwf P0 τ Hnv HeqS eq_refl Hmτ Hwτ Lav)
      as [βs [τg [ζβ [Hg [Hm [Hu [Hf [Hd [Ht He]]]]]]]]].
    exists βs, τg, ζβ.
    split; [ exact Hg | ].
    split; [ exact Hm | ].
    split; [ exact Hu | ].
    split; [ exact Hf | ].
    split; [ exact Hd | ].
    split; [ exact Ht | ].
    eapply a_tyequiv__trans; [ exact He | ].
    apply a_tyequiv__sym. apply a_tyequiv__flex_def. exact H.
Qed.

(** The wrapper: var case included. *)
Lemma guess_join_witness : forall Ψ Θ κm P A,
  {{ Ψ ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κm P)) ∼ (ptyp_to_bskl_syn A) }}ad ->
  {{ ⊢ Θ }}a ->
  (forall α, mono_ptyp (msubst_lookup κm α)) ->
  mono_ptyp A ->
  a_wf_ptyp Θ A ->
  forall L, exists βs τg ζβ,
    (forall Θg,
       (forall α0, α0 `in` dom βs -> α0 `notin` ftvar_in_aenv Θg) ->
       a_guess_mono Θg P βs τg) /\
    mono_ptyp τg /\
    uniq βs /\
    (forall α10, α10 `in` dom βs -> α10 `notin` L) /\
    dom ζβ [=] dom βs /\
    (forall E κE, κE ∷ E ⊑ Θ -> ζβ ++ κE ∷ (βs ++ E) ⊑ Θ) /\
    {{ Θ ⊢ (msubst_ptyp (ζβ ++ κm) τg) ≡ᵗ A }}a.
Proof.
  intros Ψ Θ κm P A Hc Hwf Hmlk HmC HwfC L.
  destruct (pskl_var_dec P) as [[α HeqP] | Hnv].
  - subst P. simpl in Hc.
    apply guess_witness_var_tuple.
    apply (join_var_tyequiv Hc Hwf (Hmlk α) HmC).
  - eapply (guess_join_witness_aux Hc Hwf κm Hmlk Hnv eq_refl eq_refl
              HmC HwfC).
Qed.

(* ===================================================================== *)
(*  §2j  The Assign-SolveM completeness case, assembled                   *)
(* ===================================================================== *)

Lemma assign_solve_m_complete : forall (N : atoms) Θ0' Ξ α P κ Θ,
  a_decls Ξ ->
  {{ ⊢ (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') }}a ->
  {{ (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ⨟ empty ⊢ₚₛ P }}a ->
  a_non_flex (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') P ->
  P <> pskl_univ_ghost (pskl_var_f α) ->
  κ ∷ (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ⊑ Θ ->
  {{ ⊢ Θ }}a ->
  {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P))
             ∼ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α))) }}ad ->
  exists Θ1,
    {{ ((α ~ abind_flex_mono) ++ Θ0') ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a /\
    (forall γ, γ `in` dom Θ1 ->
       γ `in` dom (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') \/ γ `notin` N) /\
    (forall κ1, is_id_msubst κ1 ->
       κ1 ∷ (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') ⊑ Θ1 ->
       exists ζ, ζ ∷ Θ1 ⊑ Θ /\
         a_inc_equiv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0') κ
                     (msubst_compose ζ κ1) Θ).
Proof.
  intros N Θ0' Ξ α P κ Θ Hdecl Hwf HwfP Hnf HneP Hinc Hwfth Hjoin.
  set (τα := msubst_lookup κ α) in *.
  assert (Huq : uniq (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (Hbα : binds α abind_flex_mono (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
    by (apply binds_app_3; left; reflexivity).
  assert (Hbtα : a_binds_tvar α (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
    by (right; left; exact Hbα).
  assert (Hmτα : mono_ptyp τα) by (eapply a_inc_lookup_mono; exact Hinc).
  assert (Hwτα : a_wf_ptyp Θ τα)
    by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact Hbtα ]).
  assert (Hmlk : forall α0, mono_ptyp (msubst_lookup κ α0))
    by (intros α0; eapply a_inc_lookup_mono; exact Hinc).
  (* ---- occurs check ---- *)
  assert (Hocc : α `notin` ftvar_in_pskl P).
  { destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P))
      as [Hin | Hni]; [ exfalso | exact Hni ].
    destruct (occurs_join_size κ Hjoin Hwfth Hmlk Hmτα HwfP Hin)
      as [Hle Hdisj].
    destruct Hdisj as [HeqP | [HeqP | Hlt]].
    - subst P. destruct Hnf as [_ Hnfl].
      apply Hnfl. apply a_flex__var. exact Hbα.
    - exact (HneP HeqP).
    - exact (Nat.lt_irrefl _ Hlt). }
  (* ---- the guess witness ---- *)
  (* [ftvar_in_aenv], not [dom]: since the freshness campaign the guessed
     names must dodge everything the context MENTIONS (payloads included),
     which is what [a_guess_mono__ghost] now polices. *)
  set (L := N `union` add α (ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
              `union` ftvar_in_pskl P `union` dom Θ).
  destruct (guess_join_witness κ P Hjoin Hwfth Hmlk Hmτα Hwτα L)
    as [βs [τg [ζβ [Hg [Hmτg [Huβ [Hfβ [Hdζ [Htr Heqn]]]]]]]]].
  (* ---- the algorithmic step ---- *)
  exists ((α ~ abind_flex_mono_def τg) ++ βs ++ Ξ ++ Θ0').
  split.
  { apply a_assign__solve_m.
    - exact Hocc.
    - apply Hg.
      intros α10 Hγ0. specialize (Hfβ α10 Hγ0).
      clear - Hfβ. unfold L in Hfβ.
      rewrite ftvar_in_aenv_app in Hfβ. rewrite ftvar_in_aenv_app in Hfβ.
      fsetdec.
    - exact Hmτg.
    - exact Huβ.
    - intros α10 Hγ0. specialize (Hfβ α10 Hγ0).
      pose proof (dom_subset_ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono) ++ Θ0'))
        as Hds.
      clear - Hfβ Hds. unfold L in Hfβ. simpl_env in *. fsetdec. }
  (* ---- the avoid set: everything the node deposits is a GUESSED name,
         and the guess dodged [L], which contains [N] ---- *)
  split.
  { intros γ Hγ. simpl_env in Hγ.
    destruct (AtomSetProperties.In_dec γ (dom βs)) as [Hin | Hni].
    - right. specialize (Hfβ γ Hin). clear - Hfβ. unfold L in Hfβ. fsetdec.
    - left. simpl_env. clear - Hγ Hni. fsetdec. }
  (* ---- optimality ---- *)
  intros κ1 Hid Hinc1.
  (* strip the competing solution at the α entry *)
  destruct (@a_inc_mid_strip_flex Ξ α Θ0' κ Θ Hdecl Hinc)
    as [κa [τα' [κ0 [Heqκ [Hdκa [Hinc0 Hincs]]]]]].
  assert (Hακa : α `notin` dom κa).
  { rewrite Hdκa. clear - Huq. simpl_env in Huq. solve_uniq. }
  assert (Heqτα : τα = τα').
  { unfold τα. rewrite Heqκ.
    rewrite (msubst_lookup_app_notin _ _ Hακa). simpl.
    destruct (α == α) as [_ | Hne]; [ reflexivity | exfalso; auto ]. }
  subst τα'.
  (* the factoring ζ *)
  exists ((α, τα) :: ζβ ++ κa ++ κ0).
  assert (Hwf' : {{ ⊢ (Ξ ++ Θ0') }}a)
    by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact Hwf ]).
  assert (Hαftvτg : α `notin` ftvar_in_ptyp τg).
  { pose proof (a_guess_mono_ftv (Hg nil ltac:(intros; simpl; solve_notin_auto)))
      as Hftv.
    intros Hinτ. apply Hftv in Hinτ.
    apply union_1 in Hinτ. destruct Hinτ as [HinP | Hinβ].
    - clear - HinP Hocc. fsetdec.
    - specialize (Hfβ α Hinβ). clear - Hfβ. unfold L in Hfβ. fsetdec. }
  (* the deposited definition is ζ-consistent *)
  assert (Heqdef : {{ Θ ⊢ τα ≡ᵗ (msubst_ptyp (ζβ ++ κa ++ κ0) τg) }}a).
  { apply a_tyequiv__sym.
    assert (Hagd : msubst_ptyp (ζβ ++ κa ++ κ0) τg
                 = msubst_ptyp (ζβ ++ κ) τg).
    { apply msubst_ptyp_agree. intros α00 HX0.
      rewrite Heqκ.
      rewrite <- app_assoc. rewrite <- (app_assoc _ ζβ κa ((α, τα) :: κ0)).
      assert (HneX : α00 <> α)
        by (intros ->; exact (Hαftvτg HX0)).
      rewrite (msubst_lookup_mid_drop _ _ _ HneX). reflexivity. }
    rewrite Hagd. exact Heqn. }
  split.
  { (* ζ ∷ Θ1 ⊑ Θ *)
    simpl_env.
    apply a_inc__flex_def.
    - simpl_env. apply Htr. exact Hincs.
    - exact Hwτα.
    - exact Hmτα.
    - simpl_env. exact Heqdef. }
  (* ---- the metasubstitution equivalence ---- *)
  destruct (@a_inc_mid_strip_flex Ξ α Θ0' κ1
              ((α ~ abind_flex_mono_def τg) ++ βs ++ Ξ ++ Θ0') Hdecl Hinc1)
    as [κ1a [τid [κ1b [Heqκ1 [Hdκ1a [Hinc10 Hinc1s]]]]]].
  assert (Hidm : τid = ptyp_var_f α /\ is_id_msubst (κ1a ++ κ1b))
    by (rewrite Heqκ1 in Hid; apply is_id_msubst_mid; exact Hid).
  destruct Hidm as [Heqτid Hid'].
  subst τid.
  rewrite Heqκ1. rewrite Heqκ.
  rewrite msubst_compose_app.
  replace (msubst_compose ((α, τα) :: ζβ ++ κa ++ κ0)
             ((α, ptyp_var_f α) :: κ1b))
    with ((α, τα) :: msubst_compose ((α, τα) :: ζβ ++ κa ++ κ0) κ1b)
    by (unfold msubst_compose; simpl;
        destruct (α == α); [ reflexivity | exfalso; auto ]).
  apply a_inc_equiv_mid_insert_flex.
  - exact Hdecl.
  - clear - Huq. simpl_env in *. solve_uniq.
  - exact Hdκa.
  - rewrite dom_msubst_compose. exact Hdκ1a.
  - apply a_tyequiv__refl. apply mono_ptyp_lc. exact Hmτα.
  - (* collapse ζ ∘ (κ1a ++ κ1b) to κa ++ κ0, then reflexivity *)
    rewrite <- msubst_compose_app.
    change ((α, τα) :: ζβ ++ κa ++ κ0)
      with (((α, τα) :: ζβ) ++ κa ++ κ0).
    rewrite (msubst_compose_is_id_r_ext ((α, τα) :: ζβ) Hwf' Hid' Hinc1s Hincs).
    + apply a_inc_equiv_refl. exact Hincs.
    + intros α00 HX0. simpl in HX0.
      destruct (AtomSetProperties.In_dec α00 (dom ζβ)) as [Hinζ | Hniζ].
      * rewrite Hdζ in Hinζ. specialize (Hfβ α00 Hinζ).
        pose proof (dom_subset_ftvar_in_aenv
                      (Ξ ++ (α ~ abind_flex_mono) ++ Θ0')) as Hds.
        clear - Hfβ Hds. unfold L in Hfβ. simpl_env in *. fsetdec.
      * assert (HeqX : α00 = α) by (clear - HX0 Hniζ; fsetdec).
        subst α00. clear - Huq. simpl_env in Huq. solve_uniq.
Qed.

(** Dropping a middle entry keeps a skeleton non-flexible: a flexible
    variable of the shorter context is one of the longer. *)
Lemma a_non_flex_strip_mid : forall Ξ (x : atom) b Θ0 P,
  a_non_flex (Ξ ++ (x ~ b) ++ Θ0) P -> a_non_flex (Ξ ++ Θ0) P.
Proof.
  intros Ξ x b Θ0 P [Hlc Hnfl]. split; [ exact Hlc | ].
  intro Hfl. apply Hnfl.
  assert (Hbw : forall (β1 : atom) (bb : abind),
            binds β1 bb (Ξ ++ Θ0) -> binds β1 bb (Ξ ++ (x ~ b) ++ Θ0))
    by (intros β1 bb Hb; apply binds_weaken; exact Hb).
  inversion Hfl as [Θf β1 Hb | Θf β1 τ0 Hb]; subst.
  - apply a_flex__var; apply Hbw; exact Hb.
  - eapply a_flex__var_def; apply Hbw; exact Hb.
Qed.
Arguments a_non_flex_strip_mid {Ξ x b Θ0 P}.

(** The three nonflexible skip rules recurse below a split source
    binding. Normalize the competing solution in that target suffix and
    establish the smaller recursive problem once, independently of the
    skipped binding's payload. *)
Local Lemma assign_skip_normalize :
  forall Θ0' Ξ α α1 bd P κ Θ κa κb' Θpre Θ',
  a_decls Ξ -> dom Ξ [<=] ftvar_in_pskl P ->
  {{ ⊢ (Ξ ++ (α1 ~ bd) ++ Θ0') }}a -> {{ ⊢ Θ }}a ->
  {{ (Ξ ++ (α1 ~ bd) ++ Θ0') ⨟ empty ⊢ₚₛ P }}a ->
  a_flex_tvar Θ0' α -> κ ∷ (Ξ ++ (α1 ~ bd) ++ Θ0') ⊑ Θ ->
  {{ empty ⨟ Θ ⊢ˢ (pskl_to_uskl (msubst_pskl κ P))
      ∼ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α))) }}ad ->
  κ = κa ++ κb' -> dom κa [=] dom Ξ -> κb' ∷ Θ0' ⊑ Θ' ->
  Θpre ++ Θ' = Θ -> {{ ⊢ Θ' }}a ->
  msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0') ⊑ Θ' /\
  {{ empty ⨟ Θ' ⊢ˢ
      (pskl_to_uskl (msubst_pskl (msubst_compose (aenv_msubst Θ) κ) P))
      ∼ (pskl_to_bskl_syn (ptyp_to_pskl
          (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α))) }}ad /\
  mu_lt (mu_assign Θ' (msubst_compose (aenv_msubst Θ) κ) α P Ξ Θ0')
        (mu_assign Θ κ α P Ξ ((α1, bd) :: Θ0')).
Proof.
  intros Θ0' Ξ α α1 bd P κ Θ κa κb' Θpre Θ'
    Hdecl Hdomξ Hwf Hwfth HwfP Hfα0 Hinc Hjoin
    Heqκ Hdκa Hincb HeqW HwfΘ'.
  assert (Huqf : uniq (Ξ ++ (α1 ~ bd) ++ Θ0'))
    by (apply a_wf_aenv_uniq; exact Hwf).
  assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
  assert (Hwf0 : {{ ⊢ Θ0' }}a).
  { eapply a_wf_aenv_strip_prefix with (Ξ := Ξ ++ (α1 ~ bd)).
    simpl_env. exact Hwf. }
  assert (Hincb_n : msubst_compose (aenv_msubst Θ) κb' ∷ Θ0' ⊑ Θ').
  { pose proof (a_inc_self_downarrow Hincb Θpre) as Hs.
    rewrite HeqW in Hs. apply Hs; [exact Hwfth | exact HuqΘ | exact Hwf0]. }
  assert (Hside : forall β, β `in` ftvar_in_pskl P ->
            β `in` dom κ \/ β `notin` dom (aenv_msubst Θ))
    by (intros x Hx; eapply a_inc_downarrow_vis;
        [exact Hinc | exact Hwf | exact Hwfth
        | eapply a_wf_pskl_ftv_binds; eassumption]).
  assert (Hmona : mono_ptyp (msubst_lookup κ α))
    by (eapply a_inc_lookup_mono; exact Hinc).
  pose proof (a_flex_tvar_in_dom Hfα0) as HαΘ0.
  assert (Hακa : α `notin` dom κa)
    by (rewrite Hdκa; clear - Huqf HαΘ0; simpl_env in Huqf; solve_uniq).
  pose proof (a_flex_tvar_binds_tvar Hfα0) as Hbtα0.
  assert (Hwfα' : a_wf_ptyp Θ' (msubst_lookup κ α)).
  { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb' Hακa).
    eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | exact Hbtα0 ]. }
  assert (HO2 : ftvar_in_pskl (⇓ˢ[ Θ ] (msubst_pskl κ P)) [<=] dom Θ').
  { eapply join_pskl_downarrow_mono_scoped;
      [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
      | exact Hmona | | ].
    - intros β τ Hbβ Hβd.
      assert (Hβpre : β `notin` dom (Θpre)).
      { pose proof HuqΘ as Hu2. rewrite <- HeqW in Hu2.
        apply uniq_app_iff in Hu2. destruct Hu2 as [_ [_ Hdisj]].
        clear - Hdisj Hβd. unfold disjoint in Hdisj. fsetdec. }
      assert (Hbβ' : binds β (abind_flex_mono_def τ) Θ').
      { rewrite <- HeqW in Hbβ.
        apply binds_app_iff in Hbβ. destruct Hbβ as [Hb | Hb];
          [ | exact Hb ].
        exfalso. apply binds_In in Hb. clear - Hb Hβpre. fsetdec. }
      apply a_wf_ptyp_ftv_dom.
      eapply a_wf_aenv_binds_def_wf; [ exact HwfΘ' | exact Hbβ' ].
    - apply a_wf_ptyp_ftv_dom. exact Hwfα'. }
  assert (Hgr : forall α0, α0 `in` dom κa ->
             ftvar_in_ptyp (⇓ᵗ[ Θ ] (msubst_lookup κa α0)) [<=] dom Θ').
  { intros α0 Hα0.
    assert (HXP : α0 `in` ftvar_in_pskl P)
      by (apply Hdomξ; rewrite <- Hdκa; exact Hα0).
    assert (Hα0κ : α0 `in` dom κ)
      by (rewrite Heqκ; rewrite dom_app; clear - Hα0; fsetdec).
    assert (Heqlk : ⇓ᵗ[ Θ ] (msubst_lookup κa α0)
                   = msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α0).
    { rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hα0κ)).
      f_equal. rewrite Heqκ. symmetry.
      apply msubst_lookup_app_in; exact Hα0. }
    rewrite Heqlk.
    eapply AtomSetProperties.subset_trans;
      [ apply (msubst_pskl_ftv_lower
                 (msubst_compose (aenv_msubst Θ) κ) P HXP) | ].
    rewrite msubst_pskl_compose; [ exact HO2 | exact Hside ]. }
  assert (Hsub' : forall y c, binds y c Θ' -> binds y c Θ).
  { intros y c Hb. rewrite <- HeqW. apply binds_app_3.
    exact Hb. }
  assert (Hinc_sub0 : (msubst_compose (aenv_msubst Θ) κa)
                          ++ (msubst_compose (aenv_msubst Θ) κb') ∷ (Ξ ++ Θ0') ⊑ Θ').
  { assert (HincR : κa ++ κb' ∷ (Ξ ++ (α1 ~ bd) ++ Θ0') ⊑ Θ)
      by (rewrite <- Heqκ; exact Hinc).
    eapply a_inc_downarrow_prefix;
      [ exact Hdecl | exact HincR | exact Huqf | exact Hdκa
      | exact Hincb_n | exact Hwfth | exact HuqΘ | exact Hsub' | exact Hgr ]. }
  assert (Hinc_sub : msubst_compose (aenv_msubst Θ) κ ∷ (Ξ ++ Θ0') ⊑ Θ').
  { rewrite Heqκ. rewrite msubst_compose_app. exact Hinc_sub0. }
  (* the join over Θ' at ⇓κ *)
  assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θ')
    by (apply a_wf_ptyp_ftv_dom; exact Hwfα').
  assert (Hvisα : forall β, β `in` ftvar_in_ptyp (msubst_lookup κ α) ->
            a_binds_tvar β Θ).
  { intros β Hβ.
    assert (HbtY' : a_binds_tvar β Θ')
      by (eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfα' | exact Hβ ]).
    destruct HbtY' as [Hb | [Hb | [τ0 Hb]]];
      [ left | right; left | right; right; exists τ0 ];
      apply Hsub'; exact Hb. }
  assert (Hddα : ⇓ᵗ[ Θ ] (msubst_lookup κ α)
               = ⇓ᵗ[ Θ' ] (msubst_lookup κ α)).
  { rewrite <- HeqW.
    apply downarrow_app_agree_ptyp;
      [ rewrite HeqW; exact HuqΘ | exact Hftvα ]. }
  assert (Hj1 : ad_pat_consis empty Θ
            (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl κ P)))
            (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))).
  { eapply consis_downarrow_subject;
      [ exact Hjoin | exact Hwfth | reflexivity | reflexivity
      | exact Hmona ]. }
  assert (Heqκα : {{ Θ ⊢ (msubst_lookup κ α)
                    ≡ᵗ (⇓ᵗ[ Θ ] (msubst_lookup κ α)) }}a).
  { apply a_tyequiv_to_downarrow_mono;
      [ exact Hwfth
      | eapply a_wf_ptyp_weaken; [ exact Hsub' | exact Hwfα' ]
      | exact Hmona ]. }
  destruct (tyequiv_mono_consis_transport_q Heqκα Hwfth Hmona Hvisα)
    as [_ Hfwd].
  pose proof (Hfwd empty _ Hj1) as Hj2.
  assert (Hjstr : ad_pat_consis empty Θ'
            (pskl_to_uskl (⇓ˢ[ Θ ] (msubst_pskl κ P)))
            (pskl_to_bskl_syn (ptyp_to_pskl
               (⇓ᵗ[ Θ ] (msubst_lookup κ α))))).
  { eapply ad_pat_consis_strengthen;
      [ exact Hj2 | exact HuqΘ | exact HwfΘ' | exact Hsub' | | ].
    - intros α2 Hα2. rewrite ftvar_in_uskl_pskl in Hα2.
      clear - HO2 Hα2. fsetdec.
    - intros α2 Hα2. rewrite ftvar_in_bskl_syn in Hα2.
      rewrite ftvar_ptyp_to_pskl in Hα2.
      rewrite Hddα in Hα2.
      assert (Hwfd : a_wf_ptyp Θ' (⇓ᵗ[ Θ' ] (msubst_lookup κ α)))
        by (apply a_wf_ptyp_downarrow_mono;
            [ exact HwfΘ' | exact Hwfα' | exact Hmona ]).
      apply a_wf_ptyp_ftv_dom in Hwfd. clear - Hwfd Hα2. fsetdec. }
  assert (Hακdom : α `in` dom κ).
  { rewrite Heqκ. rewrite dom_app.
    assert (Hαb : α `in` dom κb')
      by (eapply a_inc_flex_dom;
          [ exact Hincb | exact Hwf0 | exact Hfα0 ]).
    clear - Hαb. fsetdec. }
  assert (Hjoin_sub : {{ empty ⨟ Θ' ⊢ˢ
            (pskl_to_uskl (msubst_pskl
               (msubst_compose (aenv_msubst Θ) κ) P))
          ∼ (pskl_to_bskl_syn (ptyp_to_pskl
              (msubst_lookup (msubst_compose (aenv_msubst Θ) κ) α))) }}ad).
  { rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P Hside).
    rewrite (msubst_lookup_compose (aenv_msubst Θ) κ (or_introl Hακdom)).
    exact Hjstr. }
  (* ---- the μ-IH at the truncated problem : V is exactly constant ---- *)
  assert (Hlt : mu_lt
      (mu_assign Θ' (msubst_compose (aenv_msubst Θ) κ) α P Ξ Θ0')
      (mu_assign Θ κ α P Ξ ((α1, bd) :: Θ0'))).
  { unfold mu_assign. apply mu_lt_intro. right. split.
    - unfold V_assign, Vpskl, Vvar.
      rewrite (msubst_pskl_compose (aenv_msubst Θ) κ P Hside).
      rewrite (msubst_lookup_compose (aenv_msubst Θ) κ
                 (or_introl Hακdom)).
      rewrite downarrow_idem_sub_pskl;
        [ | exact Hwfth | exact Hsub' ].
      rewrite downarrow_idem_sub_ptyp;
        [ | exact Hwfth | exact Hsub' ].
      reflexivity.
    - left. simpl. lia. }
  repeat apply conj; assumption.
Qed.

Lemma assign_complete_step : forall m,
  (forall m', mu_lt m' m -> complete_at m') ->
  assign_complete_at m.
Proof.
  intros m IH. unfold assign_complete_at.
  intros N Θ0 Ξ α P κ Θ Hm Hdecl Hwf Hfα HwfP Hnf Hdomξ Hinc Hwfth Hjoin.
  subst m.
  destruct Θ0 as [ | [α1 b] Θ0' ].
  { exfalso. destruct Hfα as [Hb | [τ Hb]]; inversion Hb. }
  destruct b as [ | A | Q | | τdef ].
  - (* head [α1 ~ tvar] RIGID. *)
    destruct (AtomSetProperties.In_dec α1 (ftvar_in_pskl P)) as [Hγin | Hγni].
    + (* α1 ∈ ftv(P) : NO RULE fires — the STUCK-CHECK (design doc §9.2,
         [paper-gap]: the paper never proves the walk cannot reach this
         head) refutes the solution.  [a_inc] peels α1 before reaching α̂
         ([a_inc_tvar_inv]), so κα̂ is wf BELOW α1; α1 survives the solution
         into κP ([rigid_survives_solution]) while the join confines the
         subject's rigid ftv to κα̂'s scope
         ([ad_pat_consis_rigid_ftv_rev_scoped]) — contradiction. *)
      exfalso.
      (* decompose the competing increment at the rigid head *)
      destruct (@a_inc_strip_decls_prefix Ξ ((α1, abind_tvar) :: Θ0') κ Θ
                  Hdecl Hinc)
        as [κa [κb [Heqκ [Hdκa Hincb]]]].
      destruct (a_inc_tvar_inv Hincb)
        as [Ξv [Θt [HeqΘ [HsufΞv Hincb']]]].
      assert (Huq : uniq (Ξ ++ (α1, abind_tvar) :: Θ0'))
        by (apply a_wf_aenv_uniq; exact Hwf).
      assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
      assert (Hbγ : binds α1 abind_tvar (Ξ ++ (α1, abind_tvar) :: Θ0')).
      { apply binds_app_3. left. reflexivity. }
      assert (HbγΘ : binds α1 abind_tvar Θ)
        by (eapply a_inc_binds_tvar; [ exact Hinc | exact Hbγ ]).
      assert (Hα1Θt : α1 `notin` dom Θt).
      { rewrite HeqΘ in HuqΘ. clear - HuqΘ.
        simpl_env in HuqΘ. solve_uniq. }
      (* κα̂ is well-formed in the truncated target Θt, below α1 *)
      pose proof (a_flex_tvar_strip_tvar Hfα) as Hfα0.
      pose proof (a_flex_tvar_binds_tvar Hfα0) as Hbtα0.
      assert (HαΘ0' : α `in` dom Θ0')
        by (destruct Hfα0 as [Hb | [? Hb]]; apply binds_In in Hb; exact Hb).
      assert (Hακa : α `notin` dom κa).
      { rewrite Hdκa. clear - Huq HαΘ0'.
        simpl_env in Huq. solve_uniq. }
      assert (Hwf2 : {{ ⊢ ((Ξ ++ (α1 ~ abind_tvar)) ++ Θ0') }}a)
        by (simpl_env; exact Hwf).
      assert (Hwf0' : {{ ⊢ Θ0' }}a)
        by (eapply a_wf_aenv_strip_prefix; exact Hwf2).
      assert (Hwfα : a_wf_ptyp Θt (msubst_lookup κ α)).
      { rewrite Heqκ. rewrite (msubst_lookup_app_notin κa κb Hακa).
        eapply a_inc_lookup_wf;
          [ exact Hincb' | exact Hwf0' | exact Hbtα0 ]. }
      assert (Hftvα : ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θt)
        by (apply a_wf_ptyp_ftv_dom; exact Hwfα).
      (* definitions visible in dom Θt are Θt's own, scoped to Θt *)
      assert (HwfΘt : {{ ⊢ Θt }}a).
      { rewrite HeqΘ in Hwfth.
        assert (Hwtmp : {{ ⊢ ((Ξv ++ (α1 ~ abind_tvar)) ++ Θt) }}a)
          by (simpl_env; simpl_env in Hwfth; exact Hwfth).
        eapply a_wf_aenv_strip_prefix; exact Hwtmp. }
      assert (Hdefs : forall β1 τ, binds β1 (abind_flex_mono_def τ) Θ ->
                β1 `in` dom Θt -> ftvar_in_ptyp τ [<=] dom Θt).
      { intros β1 τ Hb HδD.
        assert (Hbt : binds β1 (abind_flex_mono_def τ) Θt).
        { rewrite HeqΘ in Hb.
          assert (Hb2 : binds β1 (abind_flex_mono_def τ)
                    ((Ξv ++ (α1 ~ abind_tvar)) ++ Θt))
            by (simpl_env; simpl_env in Hb; exact Hb).
          apply binds_app_iff in Hb2.
          destruct Hb2 as [Hb2 | Hb2]; [ exfalso | exact Hb2 ].
          apply binds_In in Hb2.
          rewrite HeqΘ in HuqΘ.
          assert (Hu2 : uniq ((Ξv ++ (α1 ~ abind_tvar)) ++ Θt))
            by (simpl_env; simpl_env in HuqΘ; exact HuqΘ).
          apply uniq_app_iff in Hu2. destruct Hu2 as [_ [_ Hdisj]].
          clear - Hdisj Hb2 HδD. unfold disjoint in Hdisj. fsetdec. }
        apply a_wf_ptyp_ftv_dom.
        eapply a_wf_aenv_binds_def_wf; [ exact HwfΘt | exact Hbt ]. }
      (* α1 survives the solution into κP … *)
      assert (Hα1κP : α1 `in` ftvar_in_pskl (msubst_pskl κ P))
        by (eapply rigid_survives_solution;
            [ exact Hinc | exact Hwf | exact Hbγ | exact Hγin ]).
      (* … but the join confines the subject's rigid ftv to dom Θt *)
      assert (HγnS : α1 `notin`
                ftvar_in_uskl (pskl_to_uskl (msubst_pskl κ P))).
      { eapply ad_pat_consis_rigid_ftv_rev_scoped with (D := dom Θt);
          [ exact Hwfth | exact HbγΘ | exact Hα1Θt | exact Hdefs
          | exact Hjoin | ].
        pose proof (ftvar_in_bskl_syn
                      (ptyp_to_pskl (msubst_lookup κ α))) as Hf1.
        pose proof (ftvar_ptyp_to_pskl (msubst_lookup κ α)) as Hf2.
        clear - Hf1 Hf2 Hftvα. fsetdec. }
      pose proof (ftvar_in_uskl_pskl (msubst_pskl κ P)) as Hf3.
      clear - HγnS Hα1κP Hf3. fsetdec.
    + (* Assign-SkipRigid proper (α1 ∉ ftv P): the same ⇓-truncation as
           SkipTmVar, with the rigid middle re-attached verbatim (no
           semantic-middle obligation). *)
      assert (Huqf : uniq (Ξ ++ (α1 ~ abind_tvar) ++ Θ0'))
        by (apply a_wf_aenv_uniq; exact Hwf).
      assert (HwfM : {{ ⊢ (Ξ ++ (α1 ~ abind_tvar) ++ Θ0') }}a)
        by (exact Hwf).
      assert (Hwf' : {{ ⊢ (Ξ ++ Θ0') }}a)
        by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
      assert (Huq' : uniq (Ξ ++ Θ0')) by (apply a_wf_aenv_uniq; exact Hwf').
      assert (Hwf0 : {{ ⊢ Θ0' }}a) by (eapply a_wf_aenv_strip_prefix; exact Hwf').
      assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
      pose proof Hγni as Hγfr.
      assert (HwfP' : {{ (Ξ ++ Θ0') ⨟ empty ⊢ₚₛ P }}a)
        by (eapply a_wf_pskl_strip_mid; [ exact HwfP | exact Hγfr ]).
      pose proof (a_flex_tvar_strip_tvar Hfα) as Hfα0.
      pose proof (a_non_flex_strip_mid Hnf) as Hnf'.
      (* competing: strip Ξ, invert the α1-var middle *)
      destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_tvar) ++ Θ0')
                  κ Θ Hdecl Hinc) as [κa [κb' [Heqκ [Hdκa Hincxb]]]].
      destruct (a_inc_tvar_inv Hincxb)
        as [Ξv [Θ' [HeqΘ [HsufΞv Hincb]]]].
      assert (HwfΘ' : {{ ⊢ Θ' }}a).
      { rewrite HeqΘ in Hwfth.
        eapply a_wf_aenv_strip_prefix with (Ξ := Ξv ++ (α1 ~ abind_tvar)).
        simpl_env. simpl_env in Hwfth. exact Hwfth. }
      assert (HeqW : (Ξv ++ (α1 ~ abind_tvar)) ++ Θ' = Θ)
        by (rewrite HeqΘ; simpl_env; reflexivity).
      destruct (@assign_skip_normalize Θ0' Ξ α α1 (abind_tvar) P κ Θ
                  κa κb' (Ξv ++ (α1 ~ abind_tvar)) Θ'
                  Hdecl Hdomξ Hwf Hwfth HwfP Hfα0 Hinc Hjoin
                  Heqκ Hdκa Hincb HeqW HwfΘ')
        as (Hinc_sub & Hjoin_sub & Hlt).
      destruct (IH _ Hlt) as [_ [_ HaIH]].
      destruct (HaIH (add α1 N) Θ0' Ξ α P
                     (msubst_compose (aenv_msubst Θ) κ) Θ' eq_refl
                     Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hinc_sub HwfΘ'
                     Hjoin_sub)
        as [Θ1 [Ha' [Hnew Hopt'']]].
      exists ((α1 ~ abind_tvar) ++ Θ1). split.
      { apply a_assign__skip_rigid;
          [ exact Hγni | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss;
            [ exact Hnew
            | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
              simpl_env in Huq0; solve_uniq ] | exact Ha' ]. }
      split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
      (* ---- optimality : the OPT twin's two conjuncts ---- *)
      intros κ1 Hid Hinc1.
      assert (Hinc1_s : κ1 ∷ (Ξ ++ Θ0') ⊑ Θ1)
        by (eapply a_inc_tvar_mid_strip_id;
            [ exact Hdecl | exact Huqf | exact Hid | exact Hinc1 ]).
      destruct (Hopt'' κ1 Hid Hinc1_s) as [ζ' [Hζ' Hie']].
      exists ζ'. split.
      * (* ζ' ∷ ((α1~tvar)++Θ1) ⊑ Θ  via a_inc__tvar *)
        rewrite HeqΘ. apply a_inc__tvar; [ exact Hζ' | exact HsufΞv ].
      * (* factoring: mid_insert_tvar over ⇓κ, then ⇓κ→κ *)
        destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_tvar) ++ Θ0')
                    κ1 ((α1 ~ abind_tvar) ++ Θ1) Hdecl Hinc1)
          as [κ1a [κ1b' [Heqκ1' [Hdκ1a Hinc1x]]]].
        assert (Hmi : a_inc_equiv (Ξ ++ (α1 ~ abind_tvar) ++ Θ0')
                        (msubst_compose (aenv_msubst Θ) κ)
                        (msubst_compose ζ' κ1)
                        (Ξv ++ (α1 ~ abind_tvar) ++ Θ')).
        { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb').
          rewrite Heqκ1'. rewrite (msubst_compose_app ζ' κ1a κ1b').
          apply a_inc_equiv_mid_insert_tvar;
            [ exact Hdecl | exact Huq'
            | rewrite dom_msubst_compose; exact Hdκa
            | rewrite dom_msubst_compose; exact Hdκ1a
            | exact HsufΞv | ].
          rewrite Heqκ in Hie'.
          rewrite (msubst_compose_app (aenv_msubst Θ) κa κb') in Hie'.
          rewrite Heqκ1' in Hie'.
          rewrite (msubst_compose_app ζ' κ1a κ1b') in Hie'.
          exact Hie'. }
        rewrite <- HeqΘ in Hmi.
        eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
        pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
          as Hself.
        simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
  - (* head [α1 ~ var_typ A] : Assign-SkipTmVar — the EX+OPT fusion of the
       CLOSED OPT twin [skip_tm_var_case] (prop_completeness_consis.v (PART B):990):
       ⇓-normalize the competing increment below the middle, strengthen
       the join to the truncated target, recurse through the μ-IH (V is
       exactly constant by ⇓-idempotence, §1e), rebuild with the semantic
       middle. *)
    assert (Huqf : uniq (Ξ ++ (α1 ~ abind_var_typ A) ++ Θ0'))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfM : {{ ⊢ (Ξ ++ (α1 ~ abind_var_typ A) ++ Θ0') }}a)
      by (exact Hwf).
    assert (Hwf' : {{ ⊢ (Ξ ++ Θ0') }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
    assert (Huq' : uniq (Ξ ++ Θ0')) by (apply a_wf_aenv_uniq; exact Hwf').
    assert (Hwf0 : {{ ⊢ Θ0' }}a) by (eapply a_wf_aenv_strip_prefix; exact Hwf').
    assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
    pose proof (a_wf_pskl_mid_tm_notin Huqf I HwfP) as Hγfr.
    assert (HwfP' : {{ (Ξ ++ Θ0') ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; [ exact HwfP | exact Hγfr ]).
    pose proof (a_flex_tvar_cons_tm Hfα I) as Hfα0.
    pose proof (a_non_flex_strip_mid Hnf) as Hnf'.
    (* competing: strip Ξ, invert the α1-var middle *)
    destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_var_typ A) ++ Θ0')
                κ Θ Hdecl Hinc) as [κa [κb' [Heqκ [Hdκa Hincxb]]]].
    destruct (a_inc_var_inv Hincxb)
      as [Ξv [A' [Θ' [HeqΘ [HeqA' [HsufΞv Hincb]]]]]].
    assert (HwfΘ' : {{ ⊢ Θ' }}a).
    { rewrite HeqΘ in Hwfth.
      eapply a_wf_aenv_strip_prefix with (Ξ := Ξv ++ (α1 ~ abind_var_typ A')).
      simpl_env. simpl_env in Hwfth. exact Hwfth. }
    assert (HeqW : (Ξv ++ (α1 ~ abind_var_typ A')) ++ Θ' = Θ)
      by (rewrite HeqΘ; simpl_env; reflexivity).
    destruct (@assign_skip_normalize Θ0' Ξ α α1 (abind_var_typ A) P κ Θ
                κa κb' (Ξv ++ (α1 ~ abind_var_typ A')) Θ'
                Hdecl Hdomξ Hwf Hwfth HwfP Hfα0 Hinc Hjoin
                Heqκ Hdκa Hincb HeqW HwfΘ')
      as (Hinc_sub & Hjoin_sub & Hlt).
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH (add α1 N) Θ0' Ξ α P
                   (msubst_compose (aenv_msubst Θ) κ) Θ' eq_refl
                   Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hinc_sub HwfΘ'
                   Hjoin_sub)
      as [Θ1 [Ha' [Hnew Hopt'']]].
    exists ((α1 ~ abind_var_typ A) ++ Θ1). split.
    { apply a_assign__skip_tm_var; [ (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss;
            [ exact Hnew
            | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
              simpl_env in Huq0; solve_uniq ] | exact Ha' ]. }
    split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
    (* ---- optimality : the OPT twin's two conjuncts ---- *)
    intros κ1 Hid Hinc1.
    assert (Hinc1_s : κ1 ∷ (Ξ ++ Θ0') ⊑ Θ1)
      by (eapply a_inc_var_mid_strip_id;
          [ exact Hdecl | exact Hid | exact Hinc1 ]).
    destruct (Hopt'' κ1 Hid Hinc1_s) as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + (* ζ' ∷ ((α1:A)++Θ1) ⊑ Θ  via a_inc__var *)
      rewrite HeqΘ. apply a_inc__var; [ exact Hζ' | | exact HsufΞv ].
      assert (HwfaΘ0x : {{ ⊢ ((α1 ~ abind_var_typ A) ++ Θ0') }}a)
        by (eapply a_wf_aenv_strip_prefix; exact Hwf).
      destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HwfQ : a_wf_ptyp (Ξ ++ Θ0') A)
        by (eapply a_wf_ptyp_weaken;
            [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
      assert (HlcQ : lc_ptyp A) by (eapply a_wf_ptyp_lc; exact HwfQ0).
      assert (HwfΘ1 : {{ ⊢ Θ1 }}a)
        by (eapply a_assign_preserves_wf;
            [ exact Ha' | exact Hdecl | exact Hwf' | exact HwfP' ]).
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) κ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ' κ1)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
        intros a t Hin. eapply is_id_msubst_values_lc;
          [ exact Hid | exact Hin ]. }
      pose proof (a_inc_equiv_msubst_ptyp HwfQ Hie' Hwf' Hlc1 Hlc2)
        as Hmid.
      rewrite (msubst_compose_id_ptyp Hwf' HwfΘ1 Hid Hinc1_s Hζ' HwfQ)
        in Hmid.
      assert (Hag : msubst_ptyp (msubst_compose (aenv_msubst Θ) κ) A
                  = msubst_ptyp (msubst_compose (aenv_msubst Θ) κb') A).
      { apply msubst_ptyp_agree. intros α0 HXQ.
        rewrite Heqκ. rewrite msubst_compose_app.
        apply msubst_lookup_app_notin.
        rewrite dom_msubst_compose. rewrite Hdκa.
        assert (Hα0Θ0 : α0 `in` dom Θ0')
          by (apply a_wf_ptyp_ftv_dom in HwfQ0;
              clear - HwfQ0 HXQ; fsetdec).
        clear - Huqf Hα0Θ0. simpl_env in Huqf. solve_uniq. }
      rewrite Hag in Hmid.
      eapply a_tyequiv__trans; [ exact HeqA' | ].
      eapply a_tyequiv__trans; [ | exact Hmid ].
      apply a_tyequiv__sym.
      eapply msubst_compose_downarrow_tyequiv
        with (Θpre := Ξv ++ (α1 ~ abind_var_typ A'));
        [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth
        | exact HwfΘ' | eapply a_inc_msubst_lc; exact Hincb
        | intros α0 HXd;
          destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
          (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
        | exact HlcQ ].
    + (* factoring: mid_insert_var over ⇓κ, then ⇓κ→κ via self_downarrow *)
      assert (HwfaΘ0x : {{ ⊢ ((α1 ~ abind_var_typ A) ++ Θ0') }}a)
        by (eapply a_wf_aenv_strip_prefix; exact Hwf).
      destruct (a_wf_aenv_var_typ_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HlcQ : lc_ptyp A) by (eapply a_wf_ptyp_lc; exact HwfQ0).
      destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_var_typ A) ++ Θ0')
                  κ1 ((α1 ~ abind_var_typ A) ++ Θ1) Hdecl Hinc1)
        as [κ1a [κ1b' [Heqκ1' [Hdκ1a Hinc1x]]]].
      assert (Hmiddle : {{ Θ' ⊢ A' ≡ᵗ
                msubst_ptyp (msubst_compose (aenv_msubst Θ) κb') A }}a).
      { eapply a_tyequiv__trans; [ exact HeqA' | ].
        apply a_tyequiv__sym.
        eapply msubst_compose_downarrow_tyequiv
          with (Θpre := Ξv ++ (α1 ~ abind_var_typ A'));
          [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
          | eapply a_inc_msubst_lc; exact Hincb
          | intros α0 HXd;
            destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
            (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
          | exact HlcQ ]. }
      assert (Hmi : a_inc_equiv (Ξ ++ (α1 ~ abind_var_typ A) ++ Θ0')
                      (msubst_compose (aenv_msubst Θ) κ)
                      (msubst_compose ζ' κ1)
                      (Ξv ++ (α1 ~ abind_var_typ A') ++ Θ')).
      { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb').
        rewrite Heqκ1'. rewrite (msubst_compose_app ζ' κ1a κ1b').
        apply a_inc_equiv_mid_insert_var;
          [ exact Hdecl | exact Huq'
          | rewrite dom_msubst_compose; exact Hdκa
          | rewrite dom_msubst_compose; exact Hdκ1a
          | exact Hmiddle | exact HsufΞv | ].
        rewrite Heqκ in Hie'.
        rewrite (msubst_compose_app (aenv_msubst Θ) κa κb') in Hie'.
        rewrite Heqκ1' in Hie'.
        rewrite (msubst_compose_app ζ' κ1a κ1b') in Hie'.
        exact Hie'. }
      rewrite <- HeqΘ in Hmi.
      eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
      pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
        as Hself.
      simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
  - (* head [α1 ~ var_skl Q] : Assign-SkipTmSkl — as SkipTmVar with the
       ≡ˢ semantic middle throughout. *)
    assert (Huqf : uniq (Ξ ++ (α1 ~ abind_var_skl Q) ++ Θ0'))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfM : {{ ⊢ (Ξ ++ (α1 ~ abind_var_skl Q) ++ Θ0') }}a)
      by (exact Hwf).
    assert (Hwf' : {{ ⊢ (Ξ ++ Θ0') }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
    assert (Huq' : uniq (Ξ ++ Θ0')) by (apply a_wf_aenv_uniq; exact Hwf').
    assert (Hwf0 : {{ ⊢ Θ0' }}a) by (eapply a_wf_aenv_strip_prefix; exact Hwf').
    assert (HuqΘ : uniq Θ) by (apply a_wf_aenv_uniq; exact Hwfth).
    pose proof (a_wf_pskl_mid_tm_notin Huqf I HwfP) as Hγfr.
    assert (HwfP' : {{ (Ξ ++ Θ0') ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_strip_mid; [ exact HwfP | exact Hγfr ]).
    pose proof (a_flex_tvar_cons_tm Hfα I) as Hfα0.
    pose proof (a_non_flex_strip_mid Hnf) as Hnf'.
    (* competing: strip Ξ, invert the α1-var middle *)
    destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_var_skl Q) ++ Θ0')
                κ Θ Hdecl Hinc) as [κa [κb' [Heqκ [Hdκa Hincxb]]]].
    destruct (a_inc_var_skl_inv Hincxb)
      as [Ξv [Q' [Θ' [HeqΘ [HeqQ' [HsufΞv Hincb]]]]]].
    assert (HwfΘ' : {{ ⊢ Θ' }}a).
    { rewrite HeqΘ in Hwfth.
      eapply a_wf_aenv_strip_prefix with (Ξ := Ξv ++ (α1 ~ abind_var_skl Q')).
      simpl_env. simpl_env in Hwfth. exact Hwfth. }
    assert (HeqW : (Ξv ++ (α1 ~ abind_var_skl Q')) ++ Θ' = Θ)
      by (rewrite HeqΘ; simpl_env; reflexivity).
    destruct (@assign_skip_normalize Θ0' Ξ α α1 (abind_var_skl Q) P κ Θ
                κa κb' (Ξv ++ (α1 ~ abind_var_skl Q')) Θ'
                Hdecl Hdomξ Hwf Hwfth HwfP Hfα0 Hinc Hjoin
                Heqκ Hdκa Hincb HeqW HwfΘ')
      as (Hinc_sub & Hjoin_sub & Hlt).
    destruct (IH _ Hlt) as [_ [_ HaIH]].
    destruct (HaIH (add α1 N) Θ0' Ξ α P
                   (msubst_compose (aenv_msubst Θ) κ) Θ' eq_refl
                   Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hinc_sub HwfΘ'
                   Hjoin_sub)
      as [Θ1 [Ha' [Hnew Hopt'']]].
    exists ((α1 ~ abind_var_skl Q) ++ Θ1). split.
    { apply a_assign__skip_tm_skl; [ (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss;
            [ exact Hnew
            | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
              simpl_env in Huq0; solve_uniq ] | exact Ha' ]. }
    split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
    (* ---- optimality : the OPT twin's two conjuncts ---- *)
    intros κ1 Hid Hinc1.
    assert (Hinc1_s : κ1 ∷ (Ξ ++ Θ0') ⊑ Θ1)
      by (eapply a_inc_var_skl_mid_strip_id;
          [ exact Hdecl | exact Hid | exact Hinc1 ]).
    destruct (Hopt'' κ1 Hid Hinc1_s) as [ζ' [Hζ' Hie']].
    exists ζ'. split.
    + (* ζ' ∷ ((α1:A)++Θ1) ⊑ Θ  via a_inc__var *)
      rewrite HeqΘ. apply a_inc__var_skl; [ exact Hζ' | | exact HsufΞv ].
      assert (HwfaΘ0x : {{ ⊢ ((α1 ~ abind_var_skl Q) ++ Θ0') }}a)
        by (eapply a_wf_aenv_strip_prefix; exact Hwf).
      destruct (a_wf_aenv_var_skl_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HwfQ : {{ (Ξ ++ Θ0') ⨟ empty ⊢ₚₛ Q }}a)
        by (eapply a_wf_pskl_weaken;
            [ intros ? ? Hb; apply binds_app_3; exact Hb | exact HwfQ0 ]).
      assert (HlcQ : lc_pskl Q) by (eapply a_wf_pskl_lc; eauto).
      assert (HwfΘ1 : {{ ⊢ Θ1 }}a)
        by (eapply a_assign_preserves_wf;
            [ exact Ha' | exact Hdecl | exact Hwf' | exact HwfP' ]).
      assert (Hlc1 : msubst_lc (msubst_compose (aenv_msubst Θ) κ))
        by (eapply a_inc_msubst_lc; exact Hinc_sub).
      assert (Hlc2 : msubst_lc (msubst_compose ζ' κ1)).
      { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
        intros a t Hin. eapply is_id_msubst_values_lc;
          [ exact Hid | exact Hin ]. }
      pose proof (a_inc_equiv_msubst_pskl (a_scope_pskl_of_wf HwfQ) Hie' Hwf'
                   Hlc1 Hlc2)
        as Hmid.
      rewrite (msubst_compose_id_pskl Hwf' HwfΘ1 Hid Hinc1_s Hζ'
                 (a_scope_pskl_of_wf HwfQ))
        in Hmid.
      assert (Hag : msubst_pskl (msubst_compose (aenv_msubst Θ) κ) Q
                  = msubst_pskl (msubst_compose (aenv_msubst Θ) κb') Q).
      { apply msubst_pskl_agree. intros α0 HXQ.
        rewrite Heqκ. rewrite msubst_compose_app.
        apply msubst_lookup_app_notin.
        rewrite dom_msubst_compose. rewrite Hdκa.
        assert (Hα0Θ0 : α0 `in` dom Θ0')
          by (pose proof (a_scope_pskl_ftv_dom (a_scope_pskl_of_wf HwfQ0))
                as HwfQ0';
              clear - HwfQ0' HXQ; fsetdec).
        clear - Huqf Hα0Θ0. simpl_env in Huqf. solve_uniq. }
      rewrite Hag in Hmid.
      eapply a_pskl_tyequiv__trans; [ exact HeqQ' | ].
      eapply a_pskl_tyequiv__trans; [ | exact Hmid ].
      apply a_pskl_tyequiv__sym.
      eapply msubst_pskl_compose_downarrow_tyequiv
        with (Θpre := Ξv ++ (α1 ~ abind_var_skl Q'));
        [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth
        | exact HwfΘ' | eapply a_inc_msubst_lc; exact Hincb
        | intros α0 HXd;
          destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
          (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
          [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
        | exact HlcQ ].
    + (* factoring: mid_insert_var over ⇓κ, then ⇓κ→κ via self_downarrow *)
      assert (HwfaΘ0x : {{ ⊢ ((α1 ~ abind_var_skl Q) ++ Θ0') }}a)
        by (eapply a_wf_aenv_strip_prefix; exact Hwf).
      destruct (a_wf_aenv_var_skl_inv HwfaΘ0x) as [_ [HwfQ0 _]].
      assert (HlcQ : lc_pskl Q) by (eapply a_wf_pskl_lc; eauto).
      destruct (@a_inc_strip_decls_prefix Ξ ((α1 ~ abind_var_skl Q) ++ Θ0')
                  κ1 ((α1 ~ abind_var_skl Q) ++ Θ1) Hdecl Hinc1)
        as [κ1a [κ1b' [Heqκ1' [Hdκ1a Hinc1x]]]].
      assert (Hmiddle : {{ Θ' ⊢ Q' ≡ˢ
                msubst_pskl (msubst_compose (aenv_msubst Θ) κb') Q }}a).
      { eapply a_pskl_tyequiv__trans; [ exact HeqQ' | ].
        apply a_pskl_tyequiv__sym.
        eapply msubst_pskl_compose_downarrow_tyequiv
          with (Θpre := Ξv ++ (α1 ~ abind_var_skl Q'));
          [ exact (eq_sym HeqW) | exact HuqΘ | exact Hwfth | exact HwfΘ'
          | eapply a_inc_msubst_lc; exact Hincb
          | intros α0 HXd;
            destruct (a_inc_dom_flex Hincb HXd) as [Hb | [τ0 Hb]];
            (eapply a_inc_lookup_wf; [ exact Hincb | exact Hwf0 | ]);
            [ right; left; exact Hb | right; right; exists τ0; exact Hb ]
          | exact HlcQ ]. }
      assert (Hmi : a_inc_equiv (Ξ ++ (α1 ~ abind_var_skl Q) ++ Θ0')
                      (msubst_compose (aenv_msubst Θ) κ)
                      (msubst_compose ζ' κ1)
                      (Ξv ++ (α1 ~ abind_var_skl Q') ++ Θ')).
      { rewrite Heqκ. rewrite (msubst_compose_app (aenv_msubst Θ) κa κb').
        rewrite Heqκ1'. rewrite (msubst_compose_app ζ' κ1a κ1b').
        apply a_inc_equiv_mid_insert_var_skl;
          [ exact Hdecl | exact Huq'
          | rewrite dom_msubst_compose; exact Hdκa
          | rewrite dom_msubst_compose; exact Hdκ1a
          | exact Hmiddle | exact HsufΞv | ].
        rewrite Heqκ in Hie'.
        rewrite (msubst_compose_app (aenv_msubst Θ) κa κb') in Hie'.
        rewrite Heqκ1' in Hie'.
        rewrite (msubst_compose_app ζ' κ1a κ1b') in Hie'.
        exact Hie'. }
      rewrite <- HeqΘ in Hmi.
      eapply a_inc_equiv_trans; [ | exact Hwfth | exact Hmi ].
      pose proof (a_inc_equiv_self_downarrow Hinc (@nil (atom * abind)))
        as Hself.
      simpl in Hself. apply Hself; [ exact Hwfth | exact HuqΘ | exact Hwf ].
  - (* head [α1̂] undefined flexible *)
    destruct (α1 == α) as [-> | Hα1α].
    + (* the head IS the subject α̂ *)
      destruct (pskl_eq_dec P (pskl_univ_ghost (pskl_var_f α))) as [-> | HneP].
      * (* Assign-UnivGhost-Id : axiom, Θ1 = Θ0, Ξ forced nil. *)
        assert (HΞnil : Ξ = nil).
        { destruct Ξ as [ | [ξ bξ] Ξ' ]; [ reflexivity | exfalso ].
          assert (Hξ : ξ `in` ftvar_in_pskl (pskl_univ_ghost (pskl_var_f α)))
            by (apply Hdomξ; simpl; fsetdec).
          simpl in Hξ.
          assert (Heqξ : ξ = α) by (clear - Hξ; fsetdec). subst ξ.
          pose proof (a_wf_aenv_uniq Hwf) as Hu.
          clear - Hu. simpl_env in Hu. solve_uniq. }
        subst Ξ. simpl_env in *.
        exists ((α ~ abind_flex_mono) ++ Θ0'). split.
        { apply a_assign__univ_ghost_id. }
        split; [ intros γ Hγ; left; simpl_env in *; exact Hγ | ].
        intros κ1 Hid Hinc1. exists κ.
        exact (opt_axiom_factor Hwf Hid Hinc1 Hinc).
      * (* Assign-SolveM : the standalone lemma above supplies the two
           premises the paper leaves implicit (design doc §9.2) — the
           occurs check and the mono guess witness — plus the ζ-factoring. *)
        apply (assign_solve_m_complete N Θ0' Hdecl Hwf HwfP Hnf HneP Hinc
                 Hwfth Hjoin).
    + (* α1̂ ≠ α̂ : Assign-Depend (α1 ∈ ftv P) / Assign-Skip (α1 ∉ ftv P) *)
      assert (Hαα1 : α <> α1) by auto.
      assert (Hwfmid : {{ ⊢ ((α1 ~ abind_flex_mono) ++ Θ0') }}a)
        by (eapply a_wf_aenv_strip_prefix; exact Hwf).
      inversion Hwfmid as [ | γh Θh Hnd Hwf0 | | | | ]; subst.
      assert (Hfα0 : a_flex_tvar Θ0' α)
        by (eapply (proj1 (a_flex_tvar_cons_other _ _ Hαα1)); exact Hfα).
      destruct (AtomSetProperties.In_dec α1 (ftvar_in_pskl P)) as [Hγin | Hγni].
      * (* Assign-Depend : α1̂ moves to the tail of Ξ; pure re-association. *)
        assert (Hdecl' : a_decls (Ξ ++ (α1 ~ abind_flex_mono)))
          by (apply a_decls_app;
              [ exact Hdecl | apply (a_decls__cons α1); apply a_decls__nil ]).
        assert (Hdomξ' : dom (Ξ ++ (α1 ~ abind_flex_mono)) [<=] ftvar_in_pskl P)
          by (rewrite dom_app; simpl; clear - Hdomξ Hγin; fsetdec).
        assert (Hwf2 : {{ ⊢ ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0') }}a)
          by (simpl_env; exact Hwf).
        assert (HwfP2 : {{ ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0') ⨟ empty ⊢ₚₛ P }}a)
          by (simpl_env; exact HwfP).
        assert (Hnf2 : a_non_flex ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0') P)
          by (simpl_env; exact Hnf).
        assert (Hinc2 : κ ∷ ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0') ⊑ Θ)
          by (simpl_env; exact Hinc).
        assert (Hlt : mu_lt (mu_assign Θ κ α P (Ξ ++ (α1 ~ abind_flex_mono)) Θ0')
                            (mu_assign Θ κ α P Ξ ((α1 ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_assign. apply mu_lt_intro. right. split; [ reflexivity | ].
          right. split.
          - rewrite length_app. simpl. lia.
          - right. split; [ reflexivity | simpl; lia ]. }
        destruct (IH _ Hlt) as [_ [_ HaIH]].
        destruct (HaIH N Θ0' (Ξ ++ (α1 ~ abind_flex_mono)) α P κ Θ eq_refl
                       Hdecl' Hwf2 Hfα0 HwfP2 Hnf2 Hdomξ' Hinc2 Hwfth Hjoin)
          as [Θ1 [Ha' [Hnew Hopt']]].
        exists Θ1. split.
        { apply a_assign__depend; [ exact Hαα1 | exact Hγin | exact Ha' ]. }
        split;
          [ intros γ Hγ; destruct (Hnew γ Hγ) as [Hin | Hni];
            [ left; simpl_env in *; exact Hin | right; exact Hni ] | ].
        intros κ1 Hid Hinc1.
        assert (Hinc1' : κ1 ∷ ((Ξ ++ (α1 ~ abind_flex_mono)) ++ Θ0') ⊑ Θ1)
          by (simpl_env; exact Hinc1).
        destruct (Hopt' κ1 Hid Hinc1') as [ζ [Hζ Hie]].
        exists ζ. split; [ exact Hζ | ].
        simpl_env in Hie. exact Hie.
      * (* Assign-Skip : α1̂ dropped from the walked context (mid-strip). *)
        destruct (a_inc_mid_strip_flex α1 Θ0' Hdecl Hinc)
          as [κa [τα1 [κb [Heqκ [Hdκa [Hincb Hincab]]]]]].
        assert (Hwf' : {{ ⊢ (Ξ ++ Θ0') }}a)
          by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact Hwf ]).
        assert (HwfP' : {{ (Ξ ++ Θ0') ⨟ empty ⊢ₚₛ P }}a)
          by (eapply a_wf_pskl_strip_mid; [ exact HwfP | exact Hγni ]).
        pose proof (a_non_flex_strip_mid Hnf) as Hnf'.
        assert (HeqP : msubst_pskl (κa ++ κb) P = msubst_pskl κ P).
        { rewrite Heqκ. apply msubst_pskl_agree. intros α0 Hα0.
          symmetry. apply msubst_lookup_mid_drop.
          clear - Hα0 Hγni. intro; subst α0; contradiction. }
        assert (Hlkα : msubst_lookup (κa ++ κb) α = msubst_lookup κ α)
          by (rewrite Heqκ; symmetry; apply msubst_lookup_mid_drop; exact Hαα1).
        assert (Hjoin' : {{ empty ⨟ Θ ⊢ˢ
                  (pskl_to_uskl (msubst_pskl (κa ++ κb) P))
                ∼ (pskl_to_bskl_syn (ptyp_to_pskl
                     (msubst_lookup (κa ++ κb) α))) }}ad)
          by (rewrite HeqP, Hlkα; exact Hjoin).
        assert (Hlt : mu_lt (mu_assign Θ (κa ++ κb) α P Ξ Θ0')
                            (mu_assign Θ κ α P Ξ
                                       ((α1 ~ abind_flex_mono) ++ Θ0'))).
        { unfold mu_assign. apply mu_lt_intro. right. split.
          - unfold V_assign, Vpskl, Vvar. rewrite HeqP, Hlkα. reflexivity.
          - left. simpl. lia. }
        destruct (IH _ Hlt) as [_ [_ HaIH]].
        destruct (HaIH (add α1 N) Θ0' Ξ α P (κa ++ κb) Θ eq_refl
                       Hdecl Hwf' Hfα0 HwfP' Hnf' Hdomξ Hincab Hwfth Hjoin')
          as [Θ1' [Ha' [Hnew Hopt']]].
        exists ((α1 ~ abind_flex_mono) ++ Θ1'). split.
        { apply a_assign__skip;
            [ exact Hαα1 | exact Hγni | (* the popped head misses the sub-run's output: the
             relayed avoid set [add α1 N] says so *)
          eapply avoid_head_miss;
            [ exact Hnew
            | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
              simpl_env in Huq0; solve_uniq ] | exact Ha' ]. }
        split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
        intros κ1 Hid Hinc1.
        destruct (a_inc_mid_strip_flex α1 Θ0' Hdecl Hinc1)
          as [κ1a [τ1 [κ1b [Heqκ1 [Hdκ1a [Hinc1b Hinc1ab]]]]]].
        rewrite Heqκ1 in Hid.
        apply Forall_app in Hid as [Hida Hidtail].
        pose proof (Forall_inv Hidtail) as Heγ1.
        pose proof (Forall_inv_tail Hidtail) as Hidb.
        unfold is_id_entry in Heγ1; simpl in Heγ1; subst τ1.
        assert (Hidab : is_id_msubst (κ1a ++ κ1b))
          by (apply Forall_app; split; assumption).
        destruct (a_assign_sound Ha' Hdecl Hwf' HwfP')
          as [[[w [Hidw Hincw]] _] _].
        assert (Hweq : w = κ1a ++ κ1b)
          by (eapply is_id_inc_unique;
              [ exact Hincw | exact Hidw | exact Hinc1ab | exact Hidab ]).
        subst w.
        destruct (Hopt' (κ1a ++ κ1b) Hidab Hincw) as [ζ' [Hζ' Hie']].
        (* facts about the dropped image τα1 *)
        assert (Huqf : uniq (Ξ ++ (α1 ~ abind_flex_mono) ++ Θ0'))
          by (apply a_wf_aenv_uniq; exact Hwf).
        assert (Hα1κa : α1 `notin` dom κa)
          by (rewrite Hdκa; clear - Huqf; simpl_env in Huqf; solve_uniq).
        assert (Hlkγ : msubst_lookup κ α1 = τα1)
          by (rewrite Heqκ; rewrite msubst_lookup_app_notin by exact Hα1κa;
              apply msubst_lookup_cons_eq).
        assert (Hmτα1 : mono_ptyp τα1)
          by (rewrite <- Hlkγ; eapply a_inc_lookup_mono; exact Hinc).
        assert (Hbtγ : a_binds_tvar α1 (Ξ ++ (α1 ~ abind_flex_mono) ++ Θ0'))
          by (right; left; unfold binds; apply in_or_app; right; left;
              reflexivity).
        assert (Hwfτα1 : a_wf_ptyp Θ τα1)
          by (rewrite <- Hlkγ;
              eapply a_inc_lookup_wf;
              [ exact Hinc | exact Hwf | exact Hbtγ ]).
        assert (Hα1κ1a : α1 `notin` dom κ1a)
          by (rewrite Hdκ1a; clear - Huqf; simpl_env in Huqf; solve_uniq).
        assert (Hα1κ1b : α1 `notin` dom κ1b)
          by (pose proof (a_inc_dom_sub Hinc1b) as Hs;
              clear - Hs Hnd; fsetdec).
        exists ((α1, τα1) :: ζ'). split.
        -- apply a_inc__flex; [ exact Hζ' | exact Hwfτα1 | exact Hmτα1 ].
        -- (* compute ζ ∘ κ1 = (ζ' ∘ κ1a) ++ (α1,τα1) :: (ζ' ∘ κ1b), then
              mid-insert the matching flex pair *)
           assert (Heqc : msubst_compose ((α1, τα1) :: ζ')
                            (κ1a ++ (α1, ptyp_var_f α1) :: κ1b)
                        = msubst_compose ζ' κ1a
                          ++ (α1, τα1) :: msubst_compose ζ' κ1b).
           { rewrite msubst_compose_app. f_equal.
             - apply (msubst_compose_cons_l_id τα1 ζ' Hida Hα1κ1a).
             - change (msubst_compose ((α1, τα1) :: ζ')
                         ((α1, ptyp_var_f α1) :: κ1b))
                 with ((α1, msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                       :: msubst_compose ((α1, τα1) :: ζ') κ1b).
               rewrite (msubst_compose_cons_l_id τα1 ζ' Hidb Hα1κ1b).
               change (msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                 with (msubst_lookup ((α1, τα1) :: ζ') α1).
               rewrite msubst_lookup_cons_eq. reflexivity. }
           rewrite Heqκ1, Heqκ, Heqc.
           apply a_inc_equiv_mid_insert_flex;
             [ exact Hdecl
             | apply a_wf_aenv_uniq; exact Hwf'
             | exact Hdκa
             | rewrite dom_msubst_compose; exact Hdκ1a
             | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτα1
             | ].
           rewrite <- msubst_compose_app. exact Hie'.
  - (* head [α1̂ ≔ τdef] DEFINED : Assign-Assign, the back-edge into part 1
       over the merged context Ξ ++ Θ0' with both sides substituted by
       [τdef/α1̂].  The competing solution strips its (α1,τα1)-entry
       ([a_inc_mid_strip_flex_def]); the substituted subject/input images
       are ≡ˢ to the node's ([msubst_pskl_subst] + the pointwise-≡ᵗ
       transport over an artificial source), so the sub-call's join is
       the REFLEXIVITY on the monotype κα̂ and both ∅-refinements follow
       by the mono bridges.  V is exactly constant ([Vpskl_backedge]);
       n drops by one (design doc §5.4, A3). *)
    assert (Huqf : uniq (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0'))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (HwfM : {{ ⊢ (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0') }}a)
      by exact Hwf.
    assert (Hwf' : {{ ⊢ (Ξ ++ Θ0') }}a)
      by (eapply a_wf_aenv_strip_mid; [ exact Hdecl | exact HwfM ]).
    assert (Hwf0 : {{ ⊢ Θ0' }}a) by (eapply a_wf_aenv_strip_prefix; exact Hwf').
    assert (Hmidwf : {{ ⊢ ((α1 ~ abind_flex_mono_def τdef) ++ Θ0') }}a)
      by (eapply a_wf_aenv_strip_prefix; exact HwfM).
    assert (Hwfτd : a_wf_ptyp Θ0' τdef) by (inversion Hmidwf; assumption).
    assert (Hmτd : mono_ptyp τdef) by (inversion Hmidwf; assumption).
    assert (Hγd : α1 `notin` dom Θ0') by (inversion Hmidwf; assumption).
    (* strip the defined mid off the competing increment *)
    destruct (a_inc_mid_strip_flex_def α1 τdef Θ0' Hdecl Hinc)
      as [κa [τα1 [κb [Heqκ [Hdκa [Hincb [Hincab [Hwfτα1 [Hmτα1 Heqτα1]]]]]]]]].
    assert (Hα1κa : α1 `notin` dom κa)
      by (rewrite Hdκa; clear - Huqf; simpl_env in Huqf; solve_uniq).
    assert (Hfτd : ftvar_in_ptyp τdef [<=] dom Θ0')
      by (apply a_wf_ptyp_ftv_dom; exact Hwfτd).
    assert (Hα1τd : α1 `notin` ftvar_in_ptyp τdef)
      by (clear - Hfτd Hγd; fsetdec).
    assert (Hagτd : msubst_ptyp (κa ++ κb) τdef = msubst_ptyp κb τdef).
    { apply msubst_ptyp_agree. intros α0 Hα0.
      apply msubst_lookup_app_notin.
      rewrite Hdκa.
      assert (HXd : α0 `in` dom Θ0') by (clear - Hfτd Hα0; fsetdec).
      clear - Huqf HXd. simpl_env in Huqf. solve_uniq. }
    assert (Heqτα1' : {{ Θ ⊢ τα1 ≡ᵗ (msubst_ptyp (κa ++ κb) τdef) }}a)
      by (rewrite Hagτd; exact Heqτα1).
    assert (Hlcκ : msubst_lc (κa ++ κb))
      by (eapply a_inc_msubst_lc; exact Hincab).
    assert (Hlcm1 : lc_ptyp (msubst_ptyp (κa ++ κb) τdef))
      by (apply msubst_ptyp_lc_lc;
          [ exact Hlcκ | eapply a_wf_ptyp_lc; exact Hwfτd ]).
    (* the pointwise-≡ᵗ transport over the artificial source *)
    assert (HwfArt : {{ ⊢ ((α1 ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0') }}a).
    { apply a_wf_aenv__flex_def.
      - clear - Huqf. simpl_env in Huqf. rewrite dom_app. solve_uniq.
      - eapply a_wf_ptyp_weaken;
          [ intros x b Hb; apply binds_app_3; exact Hb | exact Hwfτd ].
      - exact Hmτd.
      - exact Hwf'. }
    assert (Hlcc1 : msubst_lc
              ((α1, msubst_ptyp (κa ++ κb) τdef) :: κa ++ κb)).
    { intros α0. simpl.
      destruct_if; [ exact Hlcm1 | apply Hlcκ ]. }
    assert (Hlcc2 : msubst_lc ((α1, τα1) :: κa ++ κb)).
    { intros α0. simpl.
      destruct_if;
        [ apply mono_ptyp_lc; exact Hmτα1 | apply Hlcκ ]. }
    assert (Hartsub : forall β2,
              a_scope_pskl ((α1 ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0') β2 ->
              {{ Θ ⊢ (msubst_pskl
                     ((α1, msubst_ptyp (κa ++ κb) τdef) :: κa ++ κb) β2)
                ≡ˢ (msubst_pskl ((α1, τα1) :: κa ++ κb) β2) }}a).
    { intros β2 HwfW.
      eapply a_inc_equiv_msubst_pskl;
        [ exact HwfW | | exact HwfArt | exact Hlcc1 | exact Hlcc2 ].
      apply a_inc_equiv__flex_def.
      - apply a_inc_equiv_refl. exact Hincab.
      - apply a_tyequiv__sym. exact Heqτα1'.
      - apply a_tyequiv__refl. exact Hlcm1. }
    (* the reorder agreement : κ = (α1,τα1) :: (κa ++ κb) pointwise *)
    assert (Hreo : forall (β2 : pskl),
              msubst_pskl κ β2 = msubst_pskl ((α1, τα1) :: κa ++ κb) β2).
    { intro β2. apply msubst_pskl_agree. intros α0 Hα0.
      rewrite Heqκ. destruct (α0 == α1) as [-> | Hne].
      - rewrite msubst_lookup_app_notin by exact Hα1κa.
        rewrite msubst_lookup_cons_eq.
        rewrite msubst_lookup_cons_eq. reflexivity.
      - rewrite msubst_lookup_mid_drop by exact Hne.
        rewrite msubst_lookup_cons_neq by exact Hne. reflexivity. }
    (* wf of the substituted pieces at the stripped context *)
    assert (HbγM : binds α1 (abind_flex_mono_def τdef)
              (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0'))
      by (apply binds_app_3; left; reflexivity).
    assert (Hsubup : forall (β2 : pskl),
              ftvar_in_pskl
                (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 β2)
              [<=] ftvar_in_ptyp τdef `union`
                   remove α1 (ftvar_in_pskl β2)).
    { intro β2.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                    β2 (ptyp_to_pskl τdef) α1) as Hup.
      pose proof (ftvar_ptyp_to_pskl τdef) as Hfe.
      clear - Hup Hfe. fsetdec. }
    assert (HwfP0s : {{ (Ξ ++ Θ0') ⨟ empty ⊢ₚₛ
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P) }}a).
    { eapply a_wf_pskl_strip_mid.
      - eapply a_wf_pskl_mono_subst;
          [ exact HwfP | exact HwfM | exact HbγM | exact Hmτd ].
      - pose proof (Hsubup P). clear - H Hα1τd. fsetdec. }
    assert (HwfSα : {{ (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0')
              ⨟ empty ⊢ₚₛ (pskl_var_f α) }}a).
    { apply a_wf_pskl__var.
      destruct Hfα as [Hb | [τ0 Hb]];
        [ right; left | right; right; exists τ0 ];
        unfold binds in *; apply in_or_app; right; exact Hb. }
    assert (HwfSs : {{ (Ξ ++ Θ0') ⨟ empty ⊢ₚₛ
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α)) }}a).
    { eapply a_wf_pskl_strip_mid.
      - eapply a_wf_pskl_mono_subst;
          [ exact HwfSα | exact HwfM | exact HbγM | exact Hmτd ].
      - pose proof (Hsubup (pskl_var_f α)). simpl in H.
        clear - H Hα1τd. fsetdec. }
    (* wf of the pieces as a_scope_pskl over the artificial source *)
    assert (HwfPart : a_scope_pskl
              ((α1 ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0') P).
    { eapply a_scope_pskl_weaken;
        [ | exact (a_scope_pskl_of_wf HwfP) ].
      intros x b Hb. unfold binds in *.
      apply in_app_or in Hb. apply in_or_app.
      destruct Hb as [Hb | Hb];
        [ right; apply in_or_app; left; exact Hb | ].
      destruct Hb as [Hb | Hb];
        [ left; left; exact Hb
        | right; apply in_or_app; right; exact Hb ]. }
    assert (HwfVart : a_scope_pskl
              ((α1 ~ abind_flex_mono_def τdef) ++ Ξ ++ Θ0')
              (pskl_var_f α)).
    { apply a_scope_pskl_var.
      destruct Hfα as [Hb | [τ0 Hb]].
      - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'];
          [ discriminate | ].
        right; left. apply binds_cons_3. apply binds_app_3. exact Hb'.
      - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[He1 He2] | Hb'].
        + inversion He2; subst.
          right; right. eexists. unfold binds. left. reflexivity.
        + right; right. exists τ0.
          apply binds_cons_3. apply binds_app_3. exact Hb'. }
    (* the two ≡ˢ facts (subject and input) *)
    assert (HeqP : {{ Θ ⊢ (msubst_pskl (κa ++ κb)
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P))
              ≡ˢ (msubst_pskl κ P) }}a).
    { rewrite msubst_pskl_subst. rewrite (Hreo P).
      apply Hartsub. exact HwfPart. }
    assert (HeqS : {{ Θ ⊢ (msubst_pskl (κa ++ κb)
              (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α)))
              ≡ˢ (msubst_pskl κ (pskl_var_f α)) }}a).
    { rewrite msubst_pskl_subst. rewrite (Hreo (pskl_var_f α)).
      apply Hartsub. exact HwfVart. }
    (* the sub-call's competing data : the monotype κα̂ *)
    assert (HbtαM : a_binds_tvar α
              (Ξ ++ (α1 ~ abind_flex_mono_def τdef) ++ Θ0')).
    { destruct Hfα as [Hb | [τ0 Hb]];
        [ right; left | right; right; exists τ0 ];
        unfold binds in *; apply in_or_app; right; exact Hb. }
    assert (HwfC : a_wf_ptyp Θ (msubst_lookup κ α))
      by (eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | exact HbtαM ]).
    assert (HmC : mono_ptyp (msubst_lookup κ α))
      by (eapply a_inc_lookup_mono; exact Hinc).
    assert (HvisC : forall β, β `in` ftvar_in_ptyp (msubst_lookup κ α) ->
              a_binds_tvar β Θ)
      by (intros β Hβ; eapply a_wf_ptyp_ftv_tvarish;
          [ exact HwfC | exact Hβ ]).
    (* sub-join : reflexivity on κα̂, transported to the subject image *)
    assert (Hjrefl : {{ empty ⨟ Θ ⊢ˢ
              (pskl_to_uskl (msubst_pskl κ (pskl_var_f α)))
              ∼ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α))) }}ad).
    { cbn [msubst_pskl].
      rewrite pskl_to_uskl_ptyp.
      eapply ad_pat_consis_psi_cong;
        [ apply consis_mono_refl; [ exact HmC | exact HvisC ]
        | clear; fsetdec ]. }
    destruct (skl_tyequiv_consis_transport HeqS Hwfth
                (fun x b Hb => Hb)) as [_ Hjback].
    pose proof (Hjback _ _ Hjrefl) as Hjsub.
    (* sub-refinements : transport the join and monotype reflexivity *)
    assert (Hrssub : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl (κa ++ κb)
                 (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P))) ⊳ (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α))) }}ad).
    { destruct (skl_tyequiv_refine_syn_transport HeqP Hwfth
                  (fun x b Hb => Hb)) as [_ Hback].
      apply Hback.
      replace (msubst_pskl κ P)
        with (uskl_to_pskl (pskl_to_uskl (msubst_pskl κ P)))
        by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      eapply ad_pat_consis_refine_syn_mono;
        [ exact Hjoin | exact Hwfth
        | apply mono_ptyp_to_bskl_syn; exact HmC
        | clear; fsetdec
        | intros β τ Hb; clear; fsetdec ]. }
    assert (Hrpsub : {{ Θ ⨟ empty ⊢ᵣₚ (msubst_pskl (κa ++ κb)
                 (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α))) ⊳ (bskl_to_pskl (pskl_to_bskl_syn
                 (ptyp_to_pskl (msubst_lookup κ α)))) }}ad).
    { destruct (skl_tyequiv_refine_pskl_transport HeqS Hwfth
                  (fun x b Hb => Hb)) as [_ Hback].
      apply Hback.
      cbn [msubst_pskl]. rewrite bskl_to_pskl_pskl_to_bskl_syn.
      apply ad_refine_pskl_mono_refl; [exact HmC | exact HwfC]. }
    (* the measure : V exactly constant, n drops by one *)
    assert (Hlt : mu_lt
        (mu_consis Θ (κa ++ κb)
           (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P)
           (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α))
           (Ξ ++ Θ0'))
        (mu_assign Θ κ α P Ξ ((α1, abind_flex_mono_def τdef) :: Θ0'))).
    { unfold mu_consis, mu_assign. apply mu_lt_intro. right. split.
      - unfold V_consis, V_assign.
        erewrite Vpskl_backedge; [ | exact Hwfth | exact Heqτα1' ].
        erewrite Vpskl_backedge; [ | exact Hwfth | exact Heqτα1' ].
        unfold Vpskl, Vvar.
        rewrite <- !Hreo.
        cbn [msubst_pskl].
        rewrite msubst_pskl_embed_ptyp.
        rewrite size_pskl_ptyp_to_pskl. lia.
      - left. rewrite length_app. simpl. lia. }
    destruct (IH _ Hlt) as [HcIH _].
    destruct (HcIH (add α1 N) empty empty (Ξ ++ Θ0')
                (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 P)
                (subst_pskl_in_pskl (ptyp_to_pskl τdef) α1 (pskl_var_f α))
                (κa ++ κb) Θ empty
                (pskl_to_bskl_syn (ptyp_to_pskl (msubst_lookup κ α)))
                eq_refl Hwf' HwfP0s HwfSs
                ltac:(intros α0 Hα0; exfalso; clear - Hα0; solve_notin_auto)
                ltac:(intros β τ Hb; clear; solve_notin_auto)
                ltac:(intros Θa β b Θb Heqx Hne; clear; solve_notin_auto)
                Hincab Hwfth
                ltac:(intros β τ Hb; clear; solve_notin_auto)
                ltac:(reflexivity)
                Hjsub Hrssub Hrpsub
                ltac:(rewrite bskl_to_pskl_pskl_to_bskl_syn;
                      apply a_wf_ptyp_to_wf_pskl;
                      eapply a_inc_lookup_wf; [ exact Hinc | exact Hwf | ];
                      destruct Hfα as [Hb | [τ0 Hb]];
                        [ right; left | right; right; exists τ0 ];
                        apply binds_app_3; exact Hb))
      as [Q' [Θ1' [Hc [Hnew Hopt']]]].
    exists ((α1 ~ abind_flex_mono_def τdef) ++ Θ1'). split.
    { eapply a_assign__assign; [ exact Hfα | | exact Hc ].
      (* the walked definition is in the relayed avoid set [add α1 N] and
         fresh for the merged input, so it misses the output *)
      eapply avoid_head_miss;
        [ exact Hnew
        | pose proof (a_wf_aenv_uniq Hwf) as Huq0; clear - Huq0;
          simpl_env in Huq0; solve_uniq ]. }
    split; [ eapply avoid_relay_cons_mid; exact Hnew | ].
    (* ---- optimality ---- *)
    intros κ1 Hid Hinc1.
    destruct (a_inc_mid_strip_flex_def α1 τdef Θ0' Hdecl Hinc1)
      as [κ1a [τ1γ [κ1b [Heqκ1 [Hdκ1a [Hinc1b [Hinc1ab _]]]]]]].
    rewrite Heqκ1 in Hid.
    apply Forall_app in Hid as [Hida Hidtail].
    pose proof (Forall_inv Hidtail) as Heγ1.
    pose proof (Forall_inv_tail Hidtail) as Hidb.
    unfold is_id_entry in Heγ1; simpl in Heγ1; subst τ1γ.
    assert (Hidab : is_id_msubst (κ1a ++ κ1b))
      by (apply Forall_app; split; assumption).
    destruct (proj2 (proj2 a_assign_unify_consis_sound) _ _ _ _ _ _ _ Hc Hwf' HwfP0s HwfSs
                ltac:(intros α0 Hα0; exfalso; clear - Hα0; solve_notin_auto)
                ltac:(intros β τ Hb; clear; solve_notin_auto)
                ltac:(intros Θa β b Θb Heqx Hne; clear; solve_notin_auto))
      as [Hle1 [HwfΘ1' _]].
    destruct Hle1 as [[w [Hidw Hincw]] _].
    assert (Hweq : w = κ1a ++ κ1b)
      by (eapply is_id_inc_unique;
          [ exact Hincw | exact Hidw | exact Hinc1ab | exact Hidab ]).
    subst w.
    destruct (Hopt' (κ1a ++ κ1b) Hidab Hincw)
      as [ζ' [Hζ' [Hie' Hprec']]].
    (* the final ζ re-conses the dropped (α1, τα1) entry *)
    assert (Hα1κ1a : α1 `notin` dom κ1a)
      by (rewrite Hdκ1a; clear - Huqf; simpl_env in Huqf; solve_uniq).
    assert (Hα1κ1b : α1 `notin` dom κ1b)
      by (pose proof (a_inc_dom_sub Hinc1b) as Hs; clear - Hs Hγd; fsetdec).
    (* τα1 ≡ᵗ msubst ζ' τdef *)
    assert (Hwfτd' : a_wf_ptyp (Ξ ++ Θ0') τdef)
      by (eapply a_wf_ptyp_weaken;
          [ intros x b Hb; apply binds_app_3; exact Hb | exact Hwfτd ]).
    assert (Hlc2' : msubst_lc (msubst_compose ζ' (κ1a ++ κ1b))).
    { apply msubst_lc_compose; [ eapply a_inc_msubst_lc; exact Hζ' | ].
      intros a t Hin. eapply is_id_msubst_values_lc;
        [ exact Hidab | exact Hin ]. }
    assert (Heqζτd : {{ Θ ⊢ (msubst_ptyp (κa ++ κb) τdef)
                       ≡ᵗ (msubst_ptyp ζ' τdef) }}a).
    { pose proof (a_inc_equiv_msubst_ptyp Hwfτd' Hie' Hwf' Hlcκ Hlc2')
        as Hmid.
      rewrite (msubst_compose_id_ptyp Hwf' HwfΘ1' Hidab Hincw Hζ'
                 Hwfτd') in Hmid.
      exact Hmid. }
    exists ((α1, τα1) :: ζ'). split.
    + apply a_inc__flex_def;
        [ exact Hζ' | exact Hwfτα1 | exact Hmτα1 | ].
      eapply a_tyequiv__trans; [ exact Heqτα1' | exact Heqζτd ].
    + (* factoring : mid-insert the matching defined pair *)
      assert (Heqc : msubst_compose ((α1, τα1) :: ζ')
                       (κ1a ++ (α1, ptyp_var_f α1) :: κ1b)
                   = msubst_compose ζ' κ1a
                     ++ (α1, τα1) :: msubst_compose ζ' κ1b).
      { rewrite msubst_compose_app. f_equal.
        - apply (msubst_compose_cons_l_id τα1 ζ' Hida Hα1κ1a).
        - change (msubst_compose ((α1, τα1) :: ζ')
                    ((α1, ptyp_var_f α1) :: κ1b))
            with ((α1, msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
                  :: msubst_compose ((α1, τα1) :: ζ') κ1b).
          rewrite (msubst_compose_cons_l_id τα1 ζ' Hidb Hα1κ1b).
          change (msubst_ptyp ((α1, τα1) :: ζ') (ptyp_var_f α1))
            with (msubst_lookup ((α1, τα1) :: ζ') α1).
          rewrite msubst_lookup_cons_eq. reflexivity. }
      rewrite Heqκ1, Heqκ, Heqc.
      apply a_inc_equiv_mid_insert_flex_def;
        [ exact Hdecl
        | apply a_wf_aenv_uniq; exact Hwf'
        | exact Hdκa
        | rewrite dom_msubst_compose; exact Hdκ1a
        | apply a_tyequiv__refl; apply mono_ptyp_lc; exact Hmτα1
        | exact Heqτα1
        | ].
      rewrite <- msubst_compose_app. exact Hie'.
Qed.
