(** P6-Ss — completeness of subtyping CONSTRAINT COLLECTION AND SOLVING
    (paper [lemma:complete-constraint-collection-solving],
    subtyping-proofs.tex:2202).  The subtyping twin of the closed P6-Cs
    ([a_lookeq_solve_complete], prop_look_complete_cstr.v).

    ⚠️ THE PAPER'S STATEMENT INHERITS P6-Sv'S FALSITY.  Its first special
    case ("if P = α then S = α") applies P6-Sv WITH THE IDENTITY
    substitution, i.e. at Δρ = ∅ — exactly the configuration of
    [cex/cex_p6sv_forall_flex.v].  The witness transports directly: with
    the lookup variable α and S = R' = α the subject (κS)[ψa/α] IS ψa, and
    since [a_looksub] has NO FlexR rule, LS-Var is FORCED, so 𝒞 is the
    single subtyping constraint whose solving the counterexample refutes.
    This file therefore carries the SAME repair as P6-Sv; see
    docs/PAPER-GAPS.md and DESIGN-completeness-subtyping.md §8.

    THE REPAIR HERE IS A P0-ONLY WALK.  P6-Sv's [flex_shield] pairs P0 and
    ψa positionally, both descending together.  P6-Ss's recursion is
    different: ψa is FIXED (it is the single guess for α) while P0
    descends, so the pairing at a leaf is (P0-subterm, the WHOLE ψa).  Only
    two cases move P0 — Sub-Arrow takes the RIGHT component (the left one
    goes to P6-Cs, which needs no shield: consistency has no ForallL, so
    tags never become dirt there) and Sub-ForallR opens the body — and
    [flex_shield] supports only the second ([fsh_all_l]); [fsh_arrow]
    descends BOTH sides at once.  So the closure under those two descents
    is threaded, exactly as P6-Sv threads [flex_apart_walk]. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_decorate_sub.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_consis_precise.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_sub_complete.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_look_complete_var.

Set Implicit Arguments.

Require Import src.frost.algo.prop_look_complete_cstr.
Require Import src.frost.algo.prop_look_complete_sub_var.

(* ===================================================================== *)
(*  The P0-only descents of P6-Ss, and the shield closed under them       *)
(* ===================================================================== *)

(** Sub-Arrow keeps the RIGHT component; Sub-ForallR opens the body.  Every
    other case of P6-Ss leaves P0 alone.

    The walk carries an AVOID SET [A], and Sub-ForallR's binder must miss
    it.  Without that the walk reaches states mentioning an ARBITRARY γ, and
    [sub_shield] could then not be transported across a flexible prefix at
    all: [fsh_flexfree] is anti-monotone in the context, so its transport
    needs [ftv P0' ∩ dom Ξ = ∅], which only holds if the opened binders miss
    [dom Ξ].  [sub_shield] instantiates [A := dom Θ0], and every call site
    picks its binder fresh for the context anyway — so the condition costs
    nothing and buys [sub_shield_weaken_flex_prefix], which P6-Ss's Sub-Arrow
    row needs for its right branch. *)
Inductive ss_step (A : atoms) : pskl -> pskl -> Prop :=
| sss_arrow_r : forall P1 P2,                     (* Sub-Arrow *)
    ss_step A (pskl_arrow P1 P2) P2
| sss_all : forall P0 γ,                          (* Sub-ForallR *)
    γ `notin` A ->
    ss_step A (pskl_all_syn P0) (open_pskl_wrt_pskl P0 (pskl_var_f γ)).

Inductive ss_walk (A : atoms) : pskl -> pskl -> Prop :=
| ssw_refl : forall P0, ss_walk A P0 P0
| ssw_step : forall P0 P1 P2,
    ss_step A P0 P1 -> ss_walk A P1 P2 -> ss_walk A P0 P2.

(** Shrinking the avoid set only admits MORE walks, so a walk at the larger
    set is one at the smaller — the direction the transport needs. *)
Lemma ss_walk_mono : forall A A' P0 P1,
  ss_walk A P0 P1 -> A' [<=] A -> ss_walk A' P0 P1.
Proof.
  intros A A' P0 P1 H; induction H; intros Hsub; [ apply ssw_refl | ].
  eapply ssw_step; [ | apply IHss_walk; exact Hsub ].
  destruct H; [ apply sss_arrow_r | apply sss_all; clear - H Hsub; fsetdec ].
Qed.

(** …and the free variables a walk can introduce are bounded by the start's
    plus the avoid set's complement — all we need is that they MISS [A]. *)
Lemma ss_walk_ftv : forall A P0 P1,
  ss_walk A P0 P1 -> (ftvar_in_pskl P0) ∩ A [=] empty ->
  (ftvar_in_pskl P1) ∩ A [=] empty.
Proof.
  intros A P0 P1 H; induction H; intros Hfr; [ exact Hfr | ].
  apply IHss_walk. destruct H.
  - simpl in Hfr; clear - Hfr; fsetdec.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f γ)) as Hup.
    simpl in Hup, Hfr. clear - Hup Hfr H; fsetdec.
Qed.

(** The P6-Ss repair premise: at EVERY P0-subterm the recursion can reach,
    P6-Sv's two premises hold against the fixed guess.  Both are needed:
    P6-Cs discharges P6-Cv's [flex_apart] with [fa_clean] at Δρ = ∅, but
    [fsh_clean] additionally demands TAG-freeness, which a tagged ψa does
    not have, so the two cannot be merged.

    THE Δρ QUANTIFIER IS PART OF THE PREMISE, not a lemma.  Sub-ForallL
    absorbs its guess into ρ and so runs the recursion at [add β Δρ] for a
    FRESH β — but ψa itself does NOT move in that row (P6-Ss's ∀ comes from
    the SUBJECT, and ψa is the fixed guess for α), so neither
    [fastep_all_r] nor [fsh_all_r] applies and there is nothing to descend.
    Growing Δρ by variables that ψa does not mention is harmless for both
    predicates — [fa_clean] / [fsh_clean] only ever ask that ψa avoid Δρ —
    but proving that as a lemma means simulating the [fa_walk] whose own
    steps grow Δρ.  Quantifying here instead makes [sub_shield_add_fresh]
    free, exactly as the [ss_walk] quantifier makes [sub_shield_step] free;
    the obligation moves to the call site, which is the honest reading
    ("the shield holds along everything the recursion does"). *)
Definition sub_shield (Θ0 : aenv) (Ψ' : atoms) (Δρ : atoms) (P0 : pskl)
  (ψa : uskl) : Prop :=
  forall P0' Δρ', ss_walk (dom Θ0) P0 P0' ->
    Δρ [<=] Δρ' -> Δρ' ∩ ftvar_in_uskl ψa [<=] Δρ ->
    flex_apart_walk Θ0 Δρ' P0' ψa /\ flex_shield Θ0 Ψ' Δρ' P0' ψa.

Lemma ss_walk_trans : forall A P0 P1 P2,
  ss_walk A P0 P1 -> ss_walk A P1 P2 -> ss_walk A P0 P2.
Proof.
  intros A P0 P1 P2 H; induction H; intros Hw; [ exact Hw | ].
  eapply ssw_step; [ exact H | apply IHss_walk; exact Hw ].
Qed.

(** The leaf: P6-Sv's premises, read off by the reflexive walk at Δρ. *)
Lemma sub_shield_here : forall Θ0 Ψ' Δρ P0 ψa,
  sub_shield Θ0 Ψ' Δρ P0 ψa ->
  flex_apart_walk Θ0 Δρ P0 ψa /\ flex_shield Θ0 Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa H;
    apply H; [ apply ssw_refl | clear; fsetdec | clear; fsetdec ].
Qed.

(** …and the three closures, all free by construction. *)
Lemma sub_shield_step : forall Θ0 Ψ' Δρ P0 P0' ψa,
  sub_shield Θ0 Ψ' Δρ P0 ψa ->
  ss_step (dom Θ0) P0 P0' ->
  sub_shield Θ0 Ψ' Δρ P0' ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 P0' ψa H Hs P0'' Δρ' Hw Hle Hcl.
  apply H; [ eapply ssw_step; [ exact Hs | exact Hw ] | exact Hle | exact Hcl ].
Qed.

(** Sub-ForallL's Δρ growth: β is fresh for the whole context, hence for ψa. *)
Lemma sub_shield_add_fresh : forall Θ0 Ψ' Δρ P0 ψa β,
  sub_shield Θ0 Ψ' Δρ P0 ψa ->
  β `notin` ftvar_in_uskl ψa ->
  sub_shield Θ0 Ψ' (add β Δρ) P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa β H Hβ P0' Δρ' Hw Hle Hcl.
  apply H;
    [ exact Hw | clear - Hle; fsetdec | clear - Hcl Hβ; fsetdec ].
Qed.

(** …and the context growth the same row needs ([rho_fresh] insists every
    ρ-replaced variable be a rigid OF the context, so Θ0 gains β too). *)
Lemma sub_shield_weaken_tvar : forall Θ0 Ψ' Δρ P0 ψa β,
  sub_shield Θ0 Ψ' Δρ P0 ψa ->
  sub_shield ((β ~ abind_tvar) ++ Θ0) Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa β H P0' Δρ' Hw Hle Hcl.
  (* PIN the avoid set with a named [assert]: inline, [ss_walk_mono]'s
     [A'] is still an evar when the [⊆] side goal runs, and an evar-[fsetdec]
     does not terminate. *)
  assert (Hw0 : ss_walk (dom Θ0) P0 P0')
    by (eapply ss_walk_mono; [ exact Hw | simpl; clear; fsetdec ]).
  destruct (H P0' Δρ' Hw0 Hle Hcl) as [Hap Hfs].
  split;
    [ apply flex_apart_walk_weaken_tvar; exact Hap
    | apply flex_shield_weaken_tvar; exact Hfs ].
Qed.

(** …and the FLEXIBLE-prefix growth Sub-Arrow's right branch needs: it runs
    at [Ξ,Θ0] with the left branch's collected flexibles.  [flex_apart] is
    plain binds-monotone; [flex_shield] is not (see
    [flex_shield_weaken_flex_prefix]), so the prefix must miss the walk's
    free variables — which the avoid set delivers, since the walk is taken at
    [dom (Ξ ++ Θ0)] and P0 is Θ0-scoped. *)
Lemma sub_shield_weaken_flex_prefix : forall Θ0 Ψ' Δρ P0 ψa Ξ,
  sub_shield Θ0 Ψ' Δρ P0 ψa ->
  (ftvar_in_pskl P0) ∩ (dom Ξ) [=] empty ->
  sub_shield (Ξ ++ Θ0) Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ P0 ψa Ξ H HfrP0 P0' Δρ' Hw Hle Hcl.
  (* every [ss_walk_mono] instance is PINNED by a named [assert] — inline,
     its [A'] is an evar when the [⊆] side goal runs and [fsetdec] hangs. *)
  assert (HwΞ : ss_walk (dom Ξ) P0 P0')
    by (eapply ss_walk_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  assert (Hw0 : ss_walk (dom Θ0) P0 P0')
    by (eapply ss_walk_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  (* the walk misses [dom Ξ] throughout, so its endpoint does too *)
  assert (HfrP0' : (ftvar_in_pskl P0') ∩ (dom Ξ) [=] empty)
    by (eapply ss_walk_ftv; [ exact HwΞ | exact HfrP0 ]).
  destruct (H P0' Δρ' Hw0 Hle Hcl) as [Hap Hfs].
  split;
    [ eapply flex_apart_walk_weaken;
        [ exact Hap | intros x b Hb; apply binds_app_3; exact Hb ]
    | eapply flex_shield_weaken_flex_prefix; [ exact Hfs | exact HfrP0' ] ].
Qed.

(* ===================================================================== *)
(*  Δ-SHRINKING for partial precision                                     *)
(* ===================================================================== *)

(** The mirror of [ad_partial_precise_delta_weaken_fresh]
    (prop_look_complete.v): a Δ-entry the TARGET does not mention can be
    dropped again.  Sub-ForallL needs both directions — it hands the IH the
    precision premise at [add β Δ] (β joins Δρ, and [Δρ ⊆ Δ]) and must
    return the IH's conclusion at plain Δ.

    Only two rows read Δ: [ad_ppre__var]'s disjunct, whose variable IS the
    target, so a target-fresh Δ-entry is never the one used; and
    [ad_ppre__hole]'s disjointness side condition, which is ANTITONE in Δ
    and so only gets easier.  (Unrestricted Δ-shrinking is of course fine
    for the □ row and false for the var row — hence the freshness.) *)
Lemma ad_partial_precise_delta_shrink_fresh : forall Θ Δf Ψ P ψ,
  Θ ⨟ Δf ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Δ Δ', Δf [=] Δ `union` Δ' ->
  Δ' ∩ ftvar_in_uskl ψ [=] empty ->
  delta_def_fresh Δ' Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δf Ψ P ψ H; induction H; intros Δ0 Δ' Heq HΔ' Hdf.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb];
      [ left; cbn [ftvar_in_uskl] in HΔ'; clear - HΔ Heq HΔ'; fsetdec
      | right; assumption ] end.
  - cbn [ftvar_in_uskl] in HΔ'.
    eapply ad_ppre__arrow;
      [ eapply (IHad_partial_precise1 Δ0 Δ');
          [ exact Heq | clear - HΔ'; fsetdec | exact Hdf ]
      | eapply (IHad_partial_precise2 Δ0 Δ');
          [ exact Heq | clear - HΔ'; fsetdec | exact Hdf ]
      | assumption ].
  - (* forall *)
    cbn [ftvar_in_uskl] in HΔ'.
    eapply ad_ppre__forall with (L := L `union` Δ'); [ | eassumption ].
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      cbn [ftvar_in_uskl] in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    (* Δ and Δ' MUST be pinned: left as evars the [=] goal below is an
       evar-fsetdec and does not terminate *)
    eapply (H0 α0 ltac:(clear - Hα0; fsetdec) (add α0 Δ0) Δ');
      [ clear - Heq; fsetdec | exact HSX | exact Hdf ].
  - (* hole : the side condition is antitone in Δ *)
    apply ad_ppre__hole; [ assumption | ].
    match goal with Hint : _ ∩ _ [=] empty |- _ =>
      clear - Hint Heq; fsetdec end.
  - apply ad_ppre__tophole_remove.
    eapply (IHad_partial_precise Δ0 Δ'); [ exact Heq | exact HΔ' | exact Hdf ].
  - (* tophole_fill *)
    eapply ad_ppre__tophole_fill with (L := L `union` Δ').
    intros α0 Hα0.
    assert (HSX : Δ' ∩
              (ftvar_in_uskl (open_uskl_wrt_uskl ψ (uskl_var_f α0)))
              [=] empty).
    { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0))
        as Hup.
      cbn [ftvar_in_uskl] in Hup. clear - HΔ' Hα0 Hup. fsetdec. }
    assert (Hdf' : delta_def_fresh Δ' ((α0 ~ abind_tvar) ++ Θ)).
    { intros β0 α3 τ3 Hβ0 Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
        [ discriminate Hc | exact (Hdf β0 α3 τ3 Hβ0 Hb') ]. }
    eapply (H0 α0 ltac:(clear - Hα0; fsetdec) Δ0 Δ');
      [ exact Heq | exact HSX | exact Hdf' ].
  - (* tophole_keep *)
    cbn [ftvar_in_uskl] in HΔ'.
    apply ad_ppre__tophole_keep.
    eapply (IHad_partial_precise Δ0 Δ');
      [ exact Heq | clear - HΔ'; fsetdec | exact Hdf ].
  - eapply ad_ppre__flex_l; [ eassumption | ].
    eapply (IHad_partial_precise Δ0 Δ'); [ exact Heq | exact HΔ' | exact Hdf ].
  - (* flex_r : the target hops to the definition's paint — this is the row
       [delta_def_fresh] is for, exactly as in the weakening twin *)
    eapply ad_ppre__flex_r; [ eassumption | ].
    eapply (IHad_partial_precise Δ0 Δ'); [ exact Heq | | exact Hdf ].
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
    apply atoms_inter_empty_pointwise.
    intros y Hy. eapply Hdf; [ exact Hy | eassumption ].
Qed.

(* ===================================================================== *)
(*  wf preservation for [a_solve_sub]                                     *)
(* ===================================================================== *)

(** A prefix of RIGID binders, the only context growth [a_solve_sub_wf]
    needs (SS-ForallR opens the target under one). *)
Fixpoint all_tvar (Ξ : aenv) : Prop :=
  match Ξ with
  | nil => True
  | (_, b) :: Ξ' => b = abind_tvar /\ all_tvar Ξ'
  end.

Lemma a_solve_eq_weaken_tvars : forall Ξ Θ P P0 P',
  all_tvar Ξ ->
  Θ ⊢ₑ P ∼ P0 ⤳ P' ->
  (Ξ ++ Θ) ⊢ₑ P ∼ P0 ⤳ P'.
Proof.
  intros Ξ; induction Ξ as [ | [α b] Ξ' IH ]; intros Θ P P0 P' Ha H;
    [ exact H | ].
  destruct Ha as [-> Ha'].
  apply a_solve_eq_weaken_tvar. apply IH; assumption.
Qed.

(** wf preservation for [a_solve_sub] — the sub-half twin of
    [a_solve_eq_wf], and NOT its mechanical mirror.

    ⚠️ THE Δ-UNIFORM STATEMENT IS FALSE.  With Δ = {β}:
    [∀◇(□→⟨⟩)] and [β→⟨⟩] are both well-formed, and SS-UnivGhostL,
    SS-Check, SE-Arrow with SE-GhostL on the left derive
    [∀◇(□→⟨⟩) ≼[TC] β→⟨⟩ ⤳ ∀◇(β→⟨⟩)] — whose output is NOT well-formed at
    Δ = {β}, since [a_wf_pskl__tophole] types a ghost body at the EMPTY Δ
    and this one mentions a Δ-variable.  The eq half has no such row (its
    only ∀◇ output, SE-UnivGhost, has ∀◇ on BOTH sides, so the body stays
    Θ-scoped); SS-UnivGhostL strips the ghost on the LEFT only and wraps
    target material back up.  Hence the side condition [Δ ∩ ftv P0 = ∅].

    That side condition is what forces the [Ξ] prefix: SS-ForallR opens the
    TARGET, so its binder cannot go into Δ (it would break the condition it
    is meant to preserve) and must go into the CONTEXT instead — where
    [a_wf_pskl_strip_tvar] removes it again, the output being β-free. *)
Lemma a_solve_sub_wf : forall Θ m P P0 P',
  Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' ->
  forall Ξ Δ, all_tvar Ξ ->
  (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P ->
  (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P0 ->
  Δ ∩ ftvar_in_pskl P0 [=] empty ->
  (Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ P'.
Proof.
  intros Θ m P P0 P' H; induction H; intros Ξ Δ Hall HwfP HwfQ Hdisj.
  - (* SS-Var *) exact HwfP.
  - (* SS-ForallL : the SUBJECT's binder goes into Δ *)
    inversion HwfP as [ | | | L1 ? ? ? HbP | | ]; subst.
    apply a_wf_pskl__all
      with (L := L `union` L1 `union` ftvar_in_pskl Q `union` Δ).
    intros α Hα.
    eapply H0;
      [ clear - Hα; fsetdec | exact Hall
      | apply HbP; clear - Hα; fsetdec
      | eapply a_wf_pskl_delta_mono; [ exact HwfQ | clear; fsetdec ]
      | clear - Hdisj Hα; fsetdec ].
  - (* SS-UnivGhostL : the target must be Θ-scoped — this is the row the
       Δ-uniform statement gets wrong *)
    destruct (a_wf_pskl_tophole_inv HwfP) as [HgP HwfP0].
    assert (HwfQe : (Ξ ++ Θ) ⨟ empty ⊢ₚₛᵃ Q)
      by (eapply a_wf_pskl_delta_shrink;
            [ exact HwfQ | intros α0 Hα0 Hin; clear - Hdisj Hα0 Hin; fsetdec ]).
    apply a_wf_pskl__tophole.
    + eapply a_solve_sub_guarded;
        [ exact H | eapply a_wf_pskl_lc; exact HwfP0
        | eapply a_wf_pskl_lc; exact HwfQe | exact HgP ].
    + eapply IHa_solve_sub;
        [ exact Hall | exact HwfP0 | exact HwfQe | clear; fsetdec ].
  - (* SS-Vacuous *) exact HwfP.
  - (* SS-Check *)
    eapply a_solve_eq_wf;
      [ apply a_solve_eq_weaken_tvars; [ exact Hall | exact H1 ]
      | exact HwfP | exact HwfQ ].
  - (* SS-ForallR : the TARGET's binder goes into the CONTEXT *)
    inversion HwfQ as [ | | | L2 ? ? ? HbQ | | ]; subst.
    pick fresh β for
      (L `union` L2 `union` Δ `union` dom Θ `union` dom Ξ
         `union` ftvar_in_pskl P' `union` ftvar_in_pskl B).
    assert (Hall' : all_tvar ((β ~ abind_tvar) ++ Ξ))
      by (simpl; split; [ reflexivity | exact Hall ]).
    eapply a_wf_pskl_strip_tvar with (Θ1 := nil) (α := β) (Θ2 := Ξ ++ Θ);
      [ | clear - Fr; solve_notin ].
    change ((β ~ abind_tvar) ++ Ξ ++ Θ)
      with (((β ~ abind_tvar) ++ Ξ) ++ Θ).
    assert (HwfPβ : ((β ~ abind_tvar) ++ Ξ ++ Θ) ⨟ Δ ⊢ₚₛᵃ A)
      by (eapply a_wf_pskl_weaken;
            [ intros x b Hb; unfold binds; simpl; right; exact Hb
            | exact HwfP ]).
    assert (HwfQβ : ((β ~ abind_tvar) ++ Ξ ++ Θ) ⨟ Δ
              ⊢ₚₛᵃ (open_pskl_wrt_pskl B (pskl_var_f β)))
      by (eapply a_wf_pskl_delta_to_tvar_mid
            with (α1 := β) (Θ1 := nil) (Θ2 := Ξ ++ Θ) (Δ' := Δ);
            [ apply (HbQ β ltac:(clear - Fr; solve_notin))
            | reflexivity | clear; fsetdec ]).
    assert (HdisjΒ : Δ ∩ ftvar_in_pskl (open_pskl_wrt_pskl B (pskl_var_f β))
              [=] empty).
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β))
        as Hup.
      cbn [ftvar_in_pskl] in Hup, Hdisj.
      assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
      clear - Hdisj Hup HβΔ; fsetdec. }
    exact (H0 β ltac:(clear - Fr; solve_notin) ((β ~ abind_tvar) ++ Ξ) Δ
             Hall' HwfPβ HwfQβ HdisjΒ).
  - (* SS-Arrow *)
    inversion HwfP; subst; inversion HwfQ; subst.
    cbn [ftvar_in_pskl] in Hdisj.
    apply a_wf_pskl__arrow.
    + eapply a_solve_eq_wf;
        [ apply a_solve_eq_weaken_tvars; [ exact Hall | exact H ]
        | assumption | assumption ].
    + eapply IHa_solve_sub;
        [ exact Hall | assumption | assumption
        | clear - Hdisj; fsetdec ].
  - (* SS-GhostLF *)
    inversion HwfQ; subst.
    cbn [ftvar_in_pskl] in Hdisj.
    assert (HQ1 : (Ξ ++ Θ) ⨟ empty ⊢ₚₛᵃ Q1)
      by (eapply a_wf_pskl_delta_shrink;
            [ eassumption
            | intros α0 Hα0 Hin; clear - Hdisj Hα0 Hin; fsetdec ]).
    assert (HQ2 : (Ξ ++ Θ) ⨟ empty ⊢ₚₛᵃ Q2)
      by (eapply a_wf_pskl_delta_shrink;
            [ eassumption
            | intros α0 Hα0 Hin; clear - Hdisj Hα0 Hin; fsetdec ]).
    assert (HP1 : (Ξ ++ Θ) ⨟ empty ⊢ₚₛᵃ P1')
      by (eapply a_solve_eq_wf;
            [ apply a_solve_eq_weaken_tvars; [ exact Hall | exact H ]
            | apply a_wf_pskl__hole | exact HQ1 ]).
    assert (HP2 : (Ξ ++ Θ) ⨟ empty ⊢ₚₛᵃ P2')
      by (eapply IHa_solve_sub;
            [ exact Hall | apply a_wf_pskl__hole | exact HQ2
            | clear; fsetdec ]).
    apply a_wf_pskl__tophole;
      [ apply guarded_pskl__arrow;
          [ eapply a_wf_pskl_lc; exact HP1 | eapply a_wf_pskl_lc; exact HP2 ]
      | apply a_wf_pskl__arrow; assumption ].
  - (* SS-GhostL *)
    apply a_wf_pskl__tophole;
      [ exact H
      | eapply a_wf_pskl_delta_shrink;
          [ exact HwfQ
          | intros α0 Hα0 Hin; clear - Hdisj Hα0 Hin; fsetdec ] ].
Qed.

(** NB the auxiliary fact behind the ForallL row below — an ABSENT subject
    collects nothing — is [a_looksub_lookeq_absent_nil] (prop_looksub.v §4),
    and the REVERSE of [lemma:constraint-collection-stable-substitution] it
    feeds is [a_looksub_subst_stable_rev] (prop_looksub.v §4b, Qed). *)

(** The two SPECIAL CASES of P6-Ss, factored out.  They are needed as a
    standalone lemma, not just at the top of the theorem: the main proof
    inducts on the SUBTYPING DERIVATION (P6-Cs's measure is unusable — see
    the theorem's header), and a recursive row can land on a special case
    (e.g. Sub-UnivGhostL at [R' = ∀◇α], whose erasure ∀◇α is not α, so the
    level above is NOT special while the level below is).  A measure
    induction would re-run the dispatch at every recursive use; a
    derivation induction cannot, because the derivation is consumed.  So
    every recursive site dispatches through this lemma instead. *)
(** The looksub twin of [a_lookeq_all_flex_mono]: [a_looksub] collects
    flexibles only through LS-Check and LS-Arrow's left premise, both of
    which are [a_lookeq]. *)
Lemma a_looksub_all_flex_mono : forall α m P P0 Ξ 𝒞,
  P ≼[ α , m ] P0 ⤳ Ξ ⨾ 𝒞 -> all_flex_mono Ξ.
Proof.
  intros α m P P0 Ξ 𝒞 H; unfold all_flex_mono; induction H.
  - constructor.                                       (* LS-Var *)
  - constructor.                                       (* LS-Absent *)
  - constructor.                                       (* LS-Vacuous *)
  - eapply a_lookeq_all_flex_mono; eassumption.        (* LS-Check *)
  - match goal with Hb : forall β, β `notin` ?L -> _ |- _ =>
      pick fresh β for L; exact (Hb β ltac:(auto)) end. (* LS-ForallR *)
  - apply Forall_app; split;
      [ eapply a_lookeq_all_flex_mono; eassumption | assumption ]. (* LS-Arrow *)
  - match goal with Hb : forall β, β `notin` ?L -> _ |- _ =>
      pick fresh β for L; exact (Hb β ltac:(auto)) end. (* LS-ForallL *)
  - assumption.                                        (* LS-UnivGhostL *)
Qed.

Lemma a_looksub_solve_complete_leaf :
  forall n NM M Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->                            (* erase R' = P (R' is κ-FREE) *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->       (* the paper's "Ψ disjoint from Ψ'" *)
  Ψi `union` Ψa [=] Ψ' ->                   (* the paper's Ψi,Ψa = Ψ' *)
  delta_def_fresh Δ Θ ->
  sub_shield Θ0 Ψ' Δρ P0 ψa ->              (* ⇐ THE REPAIR (see the header) *)
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* subject = the ρ-IMAGE of the paper's (κR')[ψa/α] (ρ = id ⇒ the paper's) *)
  ad_pat_sub_g n NM M Ψsub Θ Rsub Q ->
  Θ ⨟ empty ⊢ₚₛᵃ (uskl_to_pskl Rsub) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  (* --- the ρ pack (all vacuous at ρ = identity) --- *)
  uskl_rho NM Θ Δρ Ψρ Rsub
    (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
  Ψρ ∩ Ψ' [=] empty ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  (α `notin` ftvar_in_pskl P \/ P = pskl_var_f α) ->
  exists 𝒞 Ξc Pa κc,
    (P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞) /\             (* looksub α P P0 𝒞 Ξc *)
    (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Pa /\               (* solve 𝒞 Pi Pa *)
    (Ξc ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa /\
    a_wf_aenv (Ξc ++ Θ0) /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (* NB no [ftvar_in_cstrs] conjunct: the STRUCTURAL bound
       [ftv 𝒞 ⊆ ftv P0 ∪ dom Ξc] is already available to every consumer as
       [a_looksub_ftv] (prop_looksub.v).  P6-Cs carries a ψa-RELATIVE bound
       instead, because its ∀ rows need the collected constraints to avoid a
       fresh binder; whether P6-Ss's Sub-ForallR row can re-derive that is
       the open design point recorded at the [P = α] case below. *)
    (κc ++ κ) ∷ (Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc -> α0 `notin` add α (dom Θ0 `union` dom Θ)) /\
    Θ ⨟ Δ ⊢ (msubst_pskl (κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros n NM M Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' Rsub α.
  intros HwfΘ HwfΘ0 HwfP0 HwfPi HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR
         HscopeR HlcR Htags Hdisj Hsub Hdfresh Hshield Hpre HΨs1 HΨs2
         Hsubty HwfSubj Hrefine Hrho HΨρ Hrfr HΔρΔ HΔρPi Hspecial.
  destruct Hspecial as [Hnin | Heqα].
  - (* α ∉ ftv P : LS-Absent *)
  { assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
      { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
        clear - HαΘ Hb; fsetdec. }
      assert (HαMS : α `notin` ftvar_in_uskl (msubst_uskl_syn κ R')).
      { rewrite <- ftvar_in_pskl_uskl_to_pskl.
        rewrite uskl_to_pskl_msubst_uskl_syn. rewrite HeraseR.
        apply msubst_pskl_ftv_avoid; [ exact Hκav | exact Hnin ]. }
      (* under ρ the tag bound reads off the IMAGE, so ρ's own tags join it —
         and they are ⊥ Ψ' by [HΨρ], as R'-tags are by [Hdisj] *)
      rewrite (subst_bskl_in_uskl_fresh_eq (msubst_uskl_syn κ R') ψa α HαMS)
        in Hrho.
      assert (HΨsR : Ψsub [<=] ftag_in_uskl Rsub)
        by (apply (ad_pat_sub_g_ftag_sub Hsubty)).
      pose proof (uskl_rho_ftag_sub Hrho) as Hftr.
      rewrite ftag_in_uskl_msubst_uskl_syn in Hftr.
      assert (HΨa0 : Ψa [=] empty)
        by (clear - HΨs2 HΨsR Hftr Hdisj Hsub HΨρ; fsetdec).
      exists nil, nil, Pi, (@nil (atom * ptyp)).
      repeat split.
      - apply a_looksub__absent; exact Hnin.
      - simpl. apply a_solve_cstr__empty.
      - simpl. exact HwfPi.
      - simpl. exact HwfΘ0.
      - simpl; clear; fsetdec.
      - apply Forall_nil.
      - simpl. exact Hκ.
      - simpl. apply a_inc_equiv_refl; exact Hκ.
      - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
      - simpl. eapply ad_partial_precise_psi_cong;
          [ exact Hpre | clear - HΨa0; fsetdec ]. }
  - (* P = α : LS-Var, then P6-Sv at ρ = IDENTITY.  NB not [subst P]: the
       erase-tie [⌊R'⌋ˢ = P] is also an equation on P, and [subst] would
       orient it the wrong way and discard it. *)
    rewrite Heqα in HeraseR |- *.
  { assert (Hlk : msubst_lookup κ α = ptyp_var_f α).
    { apply msubst_lookup_notin_dom.
      intro Hc. apply (a_inc_dom_sub Hκ) in Hc. contradiction. }
    assert (HR : R' = uskl_var_f α).
    { destruct R'; simpl in HeraseR; try discriminate HeraseR.
      injection HeraseR as ->. reflexivity. }
    subst R'.
    assert (Hms : msubst_uskl_syn κ (uskl_var_f α) = uskl_var_f α)
      by (cbn; rewrite Hlk; apply ptyp_to_uskl_syn_var).
    (* under ρ it is the IDEAL side of [Hrho] that collapses to ψa —
       [Hsubty] / [HwfSubj] are already in the shape P6-Sv wants *)
    rewrite Hms in Hrho.
    assert (Hsubj : subst_bskl_in_uskl ψa α (uskl_var_f α) = ψa).
    { cbn. match goal with |- context [if ?c then _ else _] => destruct c end;
        [ reflexivity | contradiction ]. }
    rewrite Hsubj in Hrho.
    cbn in HΨs1.        (* ftag_in_uskl (uskl_var_f α) = empty *)
    assert (Hlcψa : lc_uskl ψa)
      by (apply is_tskl_lc; inversion Htags; assumption).
    destruct (sub_shield_here Hshield) as [Hapart Hfsh].
    assert (Hsv : exists Pa, Θ0 ⊢ₛ Pi ≼[ M ] P0 ⤳ Pa /\
                    Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa).
    { eapply a_solve_sub_complete_var
        with (Δρ := Δρ) (Ψρ := Ψρ) (ψsub := Rsub) (Ψsub := Ψsub)
             (Θs := Θ);
      [ exact HwfΘ | exact HwfΘ0 | exact HwfPi | exact HwfP0
      | exact HmodSK | exact HmodTY | exact Hκ
      | exact Hrho
      | exact Htags | exact HwfSubj | exact Hsub | exact HΨρ
      | exact Hrfr
      | exact HΔρΔ
      | exact HΔρPi
      | exact Hdfresh | exact Hapart | exact Hfsh | exact Hpre
      | clear - HΨs1; fsetdec | exact HΨs2
      | intros x b Hb; exact Hb | exact Hsubty | exact Hrefine ]. }
    destruct Hsv as (Pa & Hsolve & Hprec).
    exists (a_cstr_sub M P0 :: nil), nil, Pa, (@nil (atom * ptyp)).
    repeat split.
    - apply a_looksub__var.
    - simpl. apply a_solve_cstr__sub; exact Hsolve.
    - simpl. eapply (a_solve_sub_wf Hsolve nil);
        [ exact I | exact HwfPi | exact HwfP0 | clear; fsetdec ].
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    - simpl. exact Hκ.
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - simpl. exact Hprec. }
Qed.

(** The ρ = IDENTITY instance of the leaf, i.e. its interface BEFORE the
    ρ-generalization.  The rows of P6-Ss call this one while the theorem
    itself is still ρ-free; each will switch to the general lemma as the
    ρ-generalization reaches it. *)
Lemma a_looksub_solve_complete_leaf_id :
  forall n NM M Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->
  Ψi `union` Ψa [=] Ψ' ->
  delta_def_fresh Δ Θ ->
  sub_shield Θ0 Ψ' empty P0 ψa ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->
  Ψa [<=] Ψsub ->
  ad_pat_sub_g n NM M Ψsub Θ
    (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  Θ ⨟ empty ⊢ₚₛᵃ
    (uskl_to_pskl (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R'))) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  (α `notin` ftvar_in_pskl P \/ P = pskl_var_f α) ->
  exists 𝒞 Ξc Pa κc,
    (P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞) /\
    (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Pa /\
    (Ξc ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa /\
    a_wf_aenv (Ξc ++ Θ0) /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (κc ++ κ) ∷ (Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc -> α0 `notin` add α (dom Θ0 `union` dom Θ)) /\
    Θ ⨟ Δ ⊢ (msubst_pskl (κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros n NM M Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α.
  intros HwfΘ HwfΘ0 HwfP0 HwfPi HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR
         HscopeR HlcR Htags Hdisj Hsub Hdfresh Hshield Hpre HΨs1 HΨs2
         Hsubty HwfSubj Hrefine Hspecial.
  eapply (@a_looksub_solve_complete_leaf n NM M Θ0 Θ κ Δ empty empty Ψ'
            Ψi Ψa Ψsub ψa Q P P0 Pi R'
            (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R')) α);
    [ exact HwfΘ | exact HwfΘ0 | exact HwfP0 | exact HwfPi
    | exact HmodSK | exact HmodTY | exact Hκ | exact HαΘ | exact HαΘ0
    | exact HeraseR | exact HscopeR | exact HlcR | exact Htags | exact Hdisj
    | exact Hsub | exact Hdfresh | exact Hshield | exact Hpre
    | clear - HΨs1; fsetdec | exact HΨs2
    | exact Hsubty | exact HwfSubj | exact Hrefine
    | apply urho__refl;
        [ apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact HwfSubj
        | clear; fsetdec ]
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | exact Hspecial ].
Qed.

(* ===================================================================== *)
(*  P6-Ss — THE REPAIRED STATEMENT                                        *)
(*  [lemma:complete-constraint-collection-solving]                        *)
(* ===================================================================== *)

(** The premise set is P6-Cs's, plus the mode data ([M], [skmod]) that the
    subtyping side carries and the [sub_shield] repair.  Everything else —
    the erase-tie [⌊R'⌋ˢ = P], the scoping and tag-flow bounds, the
    subject's well-formedness (load-bearing: without it P6-Cs is FALSE,
    cex/cex_p6cs_subject_wf.v), and the conclusion's
    [𝒞 / Ξc / Pa / κc] bundle with its [keys] / [Forall] /
    [ftvar_in_cstrs] side conditions — is verbatim P6-Cs. *)
Theorem a_looksub_solve_complete :
  forall n NM M Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->                            (* erase R' = P (R' is κ-FREE) *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->       (* the paper's "Ψ disjoint from Ψ'" *)
  Ψi `union` Ψa [=] Ψ' ->                   (* the paper's Ψi,Ψa = Ψ' *)
  delta_def_fresh Δ Θ ->
  sub_shield Θ0 Ψ' empty P0 ψa ->           (* ⇐ THE REPAIR (see the header) *)
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* subject = (κR')[ψa/α], EXACTLY the paper's form *)
  ad_pat_sub_g n NM M Ψsub Θ
    (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  Θ ⨟ empty ⊢ₚₛᵃ
    (uskl_to_pskl (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R'))) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  exists 𝒞 Ξc Pa κc,
    (P ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞) /\             (* looksub α P P0 𝒞 Ξc *)
    (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Pa /\               (* solve 𝒞 Pi Pa *)
    (Ξc ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa /\
    a_wf_aenv (Ξc ++ Θ0) /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (* NB no [ftvar_in_cstrs] conjunct: the STRUCTURAL bound
       [ftv 𝒞 ⊆ ftv P0 ∪ dom Ξc] is already available to every consumer as
       [a_looksub_ftv] (prop_looksub.v).  P6-Cs carries a ψa-RELATIVE bound
       instead, because its ∀ rows need the collected constraints to avoid a
       fresh binder; whether P6-Ss's Sub-ForallR row can re-derive that is
       the open design point recorded at the [P = α] case below. *)
    (κc ++ κ) ∷ (Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc -> α0 `notin` add α (dom Θ0 `union` dom Θ)) /\
    Θ ⨟ Δ ⊢ (msubst_pskl (κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros n NM M Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α.
  intros HwfΘ HwfΘ0 HwfP0 HwfPi HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR
         HscopeR HlcR Htags Hdisj Hsub Hdfresh Hshield Hpre HΨs1 HΨs2
         Hsubty HwfSubj Hrefine.
  (* ---------------------------------------------------------------- *)
  (* The two special cases go through [a_looksub_solve_complete_leaf],   *)
  (* which every recursive row of the induction below also calls.        *)
  (* ---------------------------------------------------------------- *)
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P)) as [Hin | Hnin];
    [ | eapply a_looksub_solve_complete_leaf_id;
        solve [ eassumption | left; exact Hnin ] ].
  destruct (pskl_var_dec P α) as [Heqα | HPnα];
    [ eapply a_looksub_solve_complete_leaf_id;
        solve [ eassumption | right; exact Heqα ] | ].
  (* ---------------------------------------------------------------- *)
  (* Main induction: P ≠ α, α ∈ ftv P, and P is not a flexible variable  *)
  (* (that is the absent case).  Induct on the SUBTYPING DERIVATION —    *)
  (* NOT on P6-Cs's measure [size R' + size P0]: consistency's ∀ rules   *)
  (* open with a VARIABLE, but Sub-ForallL opens with the GUESS ψ_b, so  *)
  (* the subject can grow.  The subject being the compound              *)
  (* [(κR')[ψa/α]], it is [remember]ed and R' (with everything that      *)
  (* depends on it) generalized; each case then reads R''s shape off the *)
  (* equation — α ∈ ftv R' rules out the leaf shapes and R' = var α is   *)
  (* the special case already discharged.                               *)
  (* ---------------------------------------------------------------- *)
  assert (Hακdom : α `notin` dom κ)
    by (intro Hc; apply (a_inc_dom_sub Hκ) in Hc; contradiction).
  assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
  { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
    clear - HαΘ Hb; fsetdec. }
  assert (HαR : α `in` ftvar_in_uskl R').
  { rewrite <- HeraseR in Hin. rewrite ftvar_in_pskl_uskl_to_pskl in Hin.
    exact Hin. }
  remember (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R')) as Sub0
    eqn:HeqSub.
  (* Θ0 and κ are GENERALIZED too: Sub-Arrow's right branch runs at
     [Ξc1,Θ0] with [κc1,κ], because the two constraint sets are solved in
     SEQUENCE (LS-Arrow pairs [Ξ1,Ξ2] with [𝒞1++𝒞2], and [a_solve_cstr_app]
     feeds the left branch's [Pa1] to the right one).  Every other row
     instantiates them at the incoming [Θ0] / [κ]. *)
  revert Θ0 κ HwfΘ0 HαΘ0 Hκ Hακdom Hκav
         R' P P0 Pi Ψi Ψa HeraseR HscopeR HlcR Hdisj HwfP0 HwfPi
         HmodSK HmodTY Hsub HΨs1 HΨs2 Hshield Hpre Hrefine HeqSub HPnα
         Hin HαR HwfSubj.
  (* the lemma's [P] comes back as [P'']: [P] is a BINDER NAME of the
     Ghost rule, so [induction] has already claimed it *)
  induction Hsubty; intros
    Θ0 κ HwfΘ0 HαΘ0 Hκ Hακdom Hκav
    R' P'' P0 Pi Ψi Ψa HeraseR HscopeR HlcR Hdisj HwfP0 HwfPi
    HmodSK HmodTY Hsub HΨs1 HΨs2 Hshield Hpre Hrefine HeqSub HPnα
    Hin HαR HwfSubj.
  (* R' is NEVER a variable here: a var erases to [P = α] (the special
     case) or has α ∉ ftv, so the subject's top constructor is R''s. *)
  all: assert (HRnv : forall β, R' <> uskl_var_f β);
    [ intros β Heq; subst R'; cbn in HαR;
      assert (Heqβ : β = α) by (clear - HαR; fsetdec); subst β;
      cbn in HeraseR; contradiction (HPnα (eq_sym HeraseR)) | ].
  - (* Infer : M = TI, so [skmod] forces P0 = □; LS-Vacuous collects
       nothing and the identity solve returns Pi.  The rule's Ψ = ∅ gives
       Ψa = ∅, so the conclusion's precision is the premise's. *)
    assert (HP0 : P0 = pskl_hole).
    { destruct NM;
        [ pose proof (HmodTY eq_refl) as Hm
        | pose proof (HmodSK eq_refl) as Hm ];
        inversion Hm; reflexivity. }
    subst P0.
    exists nil, nil, Pi, (@nil (atom * ptyp)).
    repeat split.
    + apply a_looksub__vacuous.
    + simpl. apply a_solve_cstr__empty.
    + simpl. exact HwfPi.
    + simpl. exact HwfΘ0.
    + simpl; clear; fsetdec.
    + apply Forall_nil.
    + simpl. exact Hκ.
    + simpl. apply a_inc_equiv_refl; exact Hκ.
    + intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    + simpl. eapply ad_partial_precise_psi_cong;
        [ exact Hpre | assert (HΨae : Ψa [=] empty)
                         by (clear - HΨs2 H; fsetdec);
          clear - HΨae; fsetdec ].
  - (* Check : delegates WHOLE to P6-Cs ([a_lookeq_solve_complete]) on the
       consistency premise, then re-wraps with LS-Check.  LS-Check's side
       conditions: P ≠ α (HPnα) and P, P0 guarded. *)
    assert (HgP0 : guarded_pskl P0).
    { pose proof (HmodTY eq_refl) as Hmod.
      inversion Hmod as [ | A HeqA | ]; subst.
      destruct A as [ | nA | αA | A1 A2 | A0 ]; cbn [ptyp_to_pskl] in *.
      - apply guarded_pskl__unit.
      - inversion HwfP0.
      - apply guarded_pskl__var.
      - pose proof (a_wf_pskl_lc HwfP0) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption.
      - (* ∀ : its inherited painting is a [bskl_all_inh], and the target is
           the inherited painting of a GUARDED B — which is never one *)
        exfalso.
        assert (HgQ : guarded_bskl (pskl_to_bskl_inh B))
          by (apply guarded_pskl_to_bskl_inh; exact H0).
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        destruct B; cbn [pskl_to_bskl_inh] in Hrefine, HgQ;
          try solve [ inversion HgQ ];
          inversion Hrefine; subst;
          solve [ eapply ad_refine_allinh_lhs_mono_absurd;
                    [ exact HwfΘ | eassumption | reflexivity | reflexivity
                    | eapply a_wf_aenv_binds_def_mono;
                        [ exact HwfΘ | eassumption ] ] ]. }
    (* the SUBJECT's guardedness transports to its erasure: R' is not a
       variable ([HRnv]), so its top constructor is the subject's, and a
       non-guarded shape contradicts the rule's [guarded_uskl T] *)
    assert (HgP : guarded_pskl P'').
    { rewrite <- HeraseR. rewrite HeqSub in H.
      destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
        cbn in H |- *;
        try solve [ inversion H | contradiction (HRnv _ eq_refl)
                  | inversion HlcR ].
      - apply guarded_pskl__unit.
      - inversion HlcR; subst.
        apply guarded_pskl__arrow; apply lc_uskl_to_pskl_local; assumption. }
    (* this [⊆] must be discharged OUTSIDE the [edestruct]: as a bullet it
       runs while Ψi and Ψa are still EVARS (the goal does not constrain the
       lemma's conclusion), and [fsetdec] on an evar goal does not
       terminate *)
    assert (Hsub' : Ψi `union` Ψa [<=] Ψ') by (clear - Hsub; fsetdec).
    (* P6-Cs is ρ-generalized, but P6-Ss is not (yet), so this call goes to the
       PAPER-FAITHFUL corollary [a_lookeq_solve_complete] — the ρ = identity
       instance, whose premises are exactly the ones below. *)
    edestruct a_lookeq_solve_complete
      as (𝒞 & Ξc & Pa & κc & Hlook & Hsolve & HwfPa & HwfΞ & HαΞ & Hkeys
          & HFor & Hftv & Hinc & Heqv & Hκcfresh & Hprec);
      [ exact HwfΘ | exact HwfΘ0 | exact HwfP0
      | exact HwfPi | exact Hκ | exact HαΘ | exact HαΘ0 | exact HeraseR
      | exact HscopeR | exact HlcR | exact Htags | exact Hdisj
      | exact Hsub' | exact Hdfresh | exact Hpre | exact HΨs1
      | exact HΨs2 | rewrite <- HeqSub; exact H1
      | rewrite <- HeqSub; exact HwfSubj
      | exact Hrefine | ].
    exists 𝒞, Ξc, Pa, κc.
    split;
      [ apply a_looksub__check;
          [ exact HPnα | exact HgP | exact HgP0 | exact Hlook ] | ].
    repeat split; assumption.
  - (* ForallR : the refinement premise forces P0 = ∀β.P0'; descend with
       [sss_all] + [sub_shield_step], run the IH at Θ,β, rebuild with
       LS-ForallR, then strip β.

       THE β ∉ ftv 𝒞 OBLIGATION IS A MECH-ENCODING ARTEFACT, NOT A PAPER
       GAP (author resolution, 2026-07-29).  Constraint collection is
       deliberately scoping-AGNOSTIC; the scope check is the SEPARATE
       [Θ0,Ξ ⊢ P1] premise at the EXTRACT use site.  So \lslab{ForallR}
       carries no side condition and the paper's proof owes nothing.  The
       locally nameless [a_looksub__forall_r] is COFINITE in β with one
       [Ξ ⨾ 𝒞], which IS that side condition, so the mech rule is strictly
       narrower — KEEP IT: completeness of a NARROWER algorithm is a
       STRONGER theorem, and soundness is unaffected.

       Do NOT justify the cofinite rule by "the wf check catches a
       β-mentioning 𝒞 anyway" — the two encodings are NOT literally
       equivalent.  [a_solve_sub__var] is [α̂ ≼[m] Q ⤳ α̂]: it DISCARDS the
       target, so a 𝒞 mentioning β can solve to a β-FREE P1 that
       [Θ0,Ξ ⊢ P1] happily accepts.  The lax rule admits strictly more.

       WHAT THE ROW ACTUALLY NEEDS: re-acquire the ψa-RELATIVE bound P6-Cs
       carries as a conclusion,
         ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ,
       which this statement dropped; β is fresh for all four.  That route
       was thought closed ("Sub-ForallL instantiates with a GUESS bounded
       only by ftv ψb ⊆ dom Θ") — the ρ-GENERALIZED INDUCTION dissolves the
       objection: under ρ the lookup side never sees a guess, every ForallL
       opens with a fresh RIGID, and the constraints stay ψa-bounded exactly
       as on the consistency side.  ρ's binders live in Δρ; ForallR's β is a
       genuine context rigid, never a Δρ entry.  ⇒ ForallL and ForallR are
       fixed by the SAME change.  docs/PAPER-GAPS.md carries the record. *)
    admit.
  - (* UnivGhostR : NM = SK at M = TC, so [skmod] forces P0 = □ again and
       the case closes exactly like Infer. *)
    assert (HP0 : P0 = pskl_hole)
      by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
    subst P0.
    exists nil, nil, Pi, (@nil (atom * ptyp)).
    repeat split.
    + apply a_looksub__vacuous.
    + simpl. apply a_solve_cstr__empty.
    + simpl. exact HwfPi.
    + simpl. exact HwfΘ0.
    + simpl; clear; fsetdec.
    + apply Forall_nil.
    + simpl. exact Hκ.
    + simpl. apply a_inc_equiv_refl; exact Hκ.
    + intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    + simpl. eapply ad_partial_precise_psi_cong;
        [ exact Hpre | assert (HΨae : Ψa [=] empty)
                         by (clear - HΨs2 H; fsetdec);
          clear - HΨae; fsetdec ].
  - (* Arrow : [skmod] forces P0 = P01→P02 and the refinement splits.  The
       LEFT premise is a consistency judgment and goes to P6-Cs; the RIGHT
       one is the IH, with [sss_arrow_r] + [sub_shield_step].  The two
       constraint sets concatenate (LS-Arrow) and the two solves compose —
       note P6-Cs's 𝒞1 holds no SUBTYPING constraint, which is what lets
       [a_solve_cstr] run them in sequence. *)
    (* R' is an arrow: its shape is read off [HeqSub] *)
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in HeqSub, HαR, HeraseR;
      try solve [ discriminate HeqSub | contradiction (HRnv _ eq_refl) ].
    injection HeqSub as HeqSubA HeqSubB.
    (* [skmod] forces P0's arrow shape, in either sort *)
    assert (HP0arr : exists P01 P02, P0 = pskl_arrow P01 P02 /\
              (NM = a_sub_mode_sk -> a_sk_mode_compat M P02) /\
              (NM = a_sub_mode_ty -> a_ty_mode_compat M P02)).
    { destruct NM.
      - specialize (HmodTY eq_refl); inversion HmodTY; subst.
        match goal with |- exists _ _, pskl_arrow ?A ?B = _ /\ _ =>
          exists A, B end.
        repeat split; [ intros Habs; discriminate Habs | intros _; assumption ].
      - specialize (HmodSK eq_refl); inversion HmodSK; subst.
        match goal with |- exists _ _, pskl_arrow ?A ?B = _ /\ _ =>
          exists A, B end.
        repeat split; [ intros _; assumption | intros Habs; discriminate Habs ]. }
    destruct HP0arr as (P01 & P02 & HP0eq & HmodSK2 & HmodTY2).
    subst P0.
    destruct (a_wf_pskl_arrow_inv HwfP0) as [HwfP01 HwfP02].
    (* the refinement splits with P0 *)
    cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
    destruct (ad_refine_arrow_arrow_inv Hrefine) as [Href1 Href2].
    (* the subject's wf splits too *)
    cbn [uskl_to_pskl] in HwfSubj.
    destruct (a_wf_pskl_arrow_inv HwfSubj) as [HwfSubjA HwfSubjB].
    destruct (lc_uskl_arrow_inv HlcR) as [HlcRa HlcRb].
    (* --- tag algebra: Ψa = (Ψ1∩Ψ') ∪ (Ψ2∩Ψ') --- *)
    pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
    assert (HΨa : Ψa [=] union (Ψ1 ∩ Ψ') (Ψ2 ∩ Ψ'))
      by (clear - HΨs1 HΨs2 Hsub H0 Hdisj; fsetdec).
    assert (HΨ1sub : Ψ1 [<=] union (ftag_in_uskl Ra) Ψ').
    { pose proof (ad_pat_consis_ftag_sub H) as Hf1.
      rewrite HeqSubA in Hf1.
      pose proof (ftag_in_uskl_subst_bskl_in_uskl ψa α
                    (msubst_uskl_syn κ Ra)) as Hb1.
      pose proof (ftag_in_uskl_msubst_uskl_syn κ Ra) as Hm1.
      clear - Hf1 Hb1 Hm1 Hψatag; fsetdec. }
    assert (HΨ2sub : Ψ2 [<=] union (ftag_in_uskl Rb) Ψ').
    { pose proof (ad_pat_sub_g_ftag_sub Hsubty) as Hf2.
      rewrite HeqSubB in Hf2.
      pose proof (ftag_in_uskl_subst_bskl_in_uskl ψa α
                    (msubst_uskl_syn κ Rb)) as Hb2.
      pose proof (ftag_in_uskl_msubst_uskl_syn κ Rb) as Hm2.
      clear - Hf2 Hb2 Hm2 Hψatag; fsetdec. }
    (* --- LEFT branch: the consistency premise, straight to P6-Cs --- *)
    assert (HsubL : Ψi `union` (Ψ1 ∩ Ψ') [<=] Ψ') by (clear - Hsub; fsetdec).
    assert (HΨs1L : Ψ1 [<=] union (ftag_in_uskl Ra) (Ψ1 ∩ Ψ'))
      by (clear - HΨ1sub; fsetdec).
    assert (HΨs2L : Ψ1 ∩ Ψ' [<=] Ψ1) by (clear; fsetdec).
    assert (HconsL : Ψ1 ⨟ Θ ⊢ₛᵃ
              (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ Ra)) ∼ Q1)
      by (rewrite <- HeqSubA; exact H).
    assert (HwfSubjA' : Θ ⨟ empty ⊢ₚₛᵃ
              (uskl_to_pskl (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ Ra))))
      by (rewrite <- HeqSubA; exact HwfSubjA).
    edestruct (@a_lookeq_solve_complete NM Θ0 Θ κ Δ Ψ' Ψi (Ψ1 ∩ Ψ') Ψ1 ψa Q1
                 (uskl_to_pskl Ra) P01 Pi Ra α)
      as (C1 & Ξc1 & Pa1 & κc1 & HLK1 & HSolve1 & HwfPa1 & HwfΞ1 & HαΞ1
          & Hmap1 & Himg1 & HftvC1 & Hinc1 & Hinceq1 & Hκf1 & Hpre1);
      [ exact HwfΘ | exact HwfΘ0 | exact HwfP01 | exact HwfPi | exact Hκ
      | exact HαΘ | exact HαΘ0 | reflexivity
      | clear - HscopeR; cbn in HscopeR; fsetdec
      | exact HlcRa | exact Htags
      | clear - Hdisj; cbn in Hdisj; fsetdec
      | exact HsubL | exact Hdfresh | exact Hpre | exact HΨs1L | exact HΨs2L
      | exact HconsL | exact HwfSubjA' | exact Href1 | ].
    (* --- transports for the RIGHT branch (Θ0 → Ξc1,Θ0 and κ → κc1,κ) --- *)
    pose proof (@keys_eq_dom _ _ κc1 Ξc1 Hmap1) as Hd1.
    assert (Hαr : α `notin` dom (Ξc1 ++ Θ0))
      by (rewrite dom_app; clear - HαΞ1 HαΘ0; fsetdec).
    assert (Hακdom' : α `notin` dom (κc1 ++ κ)).
    { intro Hc. apply (a_inc_dom_sub Hinc1) in Hc. contradiction. }
    assert (Hκav' : forall p, In p (κc1 ++ κ) ->
              α `notin` ftvar_in_ptyp (snd p)).
    { intros p Hp. pose proof (a_inc_image_ftv_dom Hinc1 p Hp) as Hb.
      clear - HαΘ Hb; fsetdec. }
    assert (HscopeRb : ftvar_in_uskl Rb
              [<=] add α (dom (Ξc1 ++ Θ0) `union` dom Θ))
      by (rewrite dom_app; clear - HscopeR; cbn in HscopeR; fsetdec).
    assert (HwfP02R : (Ξc1 ++ Θ0) ⨟ empty ⊢ₚₛᵃ P02)
      by (eapply a_wf_pskl_weaken;
            [ intros x b Hb; apply binds_app_3; exact Hb | exact HwfP02 ]).
    assert (Htr_c : msubst_uskl_syn (κc1 ++ κ) Rb = msubst_uskl_syn κ Rb).
    { apply msubst_uskl_syn_prepend_fresh. intros α0 Hα0.
      specialize (Hκf1 α0 Hα0).
      clear - Hκf1 HscopeR; cbn in HscopeR; fsetdec. }
    assert (Htr_r : msubst_pskl (κc1 ++ κ) P02 = msubst_pskl κ P02).
    { apply msubst_pskl_prepend_fresh. intros α0 Hα0.
      specialize (Hκf1 α0 Hα0).
      pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
      clear - Hκf1 Hfd; fsetdec. }
    assert (HeqSubB' : R2 = subst_bskl_in_uskl ψa α
                              (msubst_uskl_syn (κc1 ++ κ) Rb))
      by (rewrite Htr_c; exact HeqSubB).
    assert (Href2' : Θ ⨟ empty ⊢ᵣᵃ
              (pskl_to_bskl_inh (msubst_pskl (κc1 ++ κ) P02)) ⊳ Q2)
      by (rewrite Htr_r; exact Href2).
    (* the shield descends with [sss_arrow_r] and then crosses Ξc1, whose
       names are fresh for the Θ0-scoped P02 *)
    assert (HfrΞ1 : (ftvar_in_pskl P02) ∩ (dom Ξc1) [=] empty).
    { pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
      intros x; split; intros Hx; [ exfalso | clear - Hx; fsetdec ].
      assert (Hx1 : x `in` ftvar_in_pskl P02) by (clear - Hx; fsetdec).
      assert (Hx2 : x `in` dom Ξc1) by (clear - Hx; fsetdec).
      rewrite <- Hd1 in Hx2. specialize (Hκf1 x Hx2).
      clear - Hκf1 Hfd Hx1; fsetdec. }
    assert (HshieldR : sub_shield (Ξc1 ++ Θ0) Ψ' empty P02 ψa).
    { apply sub_shield_weaken_flex_prefix; [ | exact HfrΞ1 ].
      eapply sub_shield_step; [ exact Hshield | apply sss_arrow_r ]. }
    assert (HsubR : (Ψi `union` (Ψ1 ∩ Ψ')) `union` (Ψ2 ∩ Ψ') [=] Ψ')
      by (clear - Hsub HΨa; fsetdec).
    assert (HΨs1R : Ψ2 [<=] union (ftag_in_uskl Rb) (Ψ2 ∩ Ψ'))
      by (clear - HΨ2sub; fsetdec).
    assert (HΨs2R : Ψ2 ∩ Ψ' [<=] Ψ2) by (clear; fsetdec).
    assert (HdisjRb : (ftag_in_uskl Rb) ∩ Ψ' [=] empty)
      by (clear - Hdisj; cbn in Hdisj; fsetdec).
    (* --- RIGHT branch: the IH, dispatching through the leaf lemma exactly
       as every other recursive row does (Rb may itself be [var α]) --- *)
    assert (REC : exists 𝒞 Ξc Pa κc,
      (⌊ Rb ⌋ˢ ≼[ α , M ] P02 ⤳ Ξc ⨾ 𝒞) /\
      (Ξc ++ (Ξc1 ++ Θ0)) ⊩ 𝒞 ⨾ Pa1 ⤳ Pa /\
      (Ξc ++ (Ξc1 ++ Θ0)) ⨟ empty ⊢ₚₛᵃ Pa /\
      a_wf_aenv (Ξc ++ (Ξc1 ++ Θ0)) /\
      α `notin` dom Ξc /\
      keys κc = keys Ξc /\
      Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
      (κc ++ (κc1 ++ κ)) ∷ (Ξc ++ (Ξc1 ++ Θ0)) ⊑ Θ /\
      a_inc_equiv (Ξc1 ++ Θ0) (κc1 ++ κ) (κc1 ++ κ) Θ /\
      (forall α0, α0 `in` dom κc ->
         α0 `notin` add α (dom (Ξc1 ++ Θ0) `union` dom Θ)) /\
      Θ ⨟ Δ ⊢ (msubst_pskl (κc ++ (κc1 ++ κ)) Pa)
        ⊑ᵖ[ (Ψi `union` (Ψ1 ∩ Ψ')) `union` (Ψ2 ∩ Ψ') ] ψa).
    { destruct (AtomSetProperties.In_dec α (ftvar_in_pskl ⌊ Rb ⌋ˢ))
        as [Hin0 | Hnin0].
      - destruct (pskl_var_dec ⌊ Rb ⌋ˢ α) as [Heq0 | Hne0].
        + (* leaf, var *)
          eapply (@a_looksub_solve_complete_leaf_id n NM M (Ξc1 ++ Θ0) Θ
                    (κc1 ++ κ) Δ Ψ' (Ψi `union` (Ψ1 ∩ Ψ')) (Ψ2 ∩ Ψ') Ψ2 ψa Q2
                    (uskl_to_pskl Rb) P02 Pa1 Rb α
                    HwfΘ HwfΞ1 HwfP02R HwfPa1 HmodSK2 HmodTY2 Hinc1
                    HαΘ Hαr eq_refl HscopeRb HlcRb Htags HdisjRb HsubR
                    Hdfresh HshieldR Hpre1 HΨs1R HΨs2R);
            [ rewrite <- HeqSubB'; exact Hsubty
            | rewrite <- HeqSubB'; exact HwfSubjB
            | exact Href2'
            | right; exact Heq0 ].
        + (* recurse *)
          assert (HαRb : α `in` ftvar_in_uskl Rb)
            by (rewrite <- ftvar_in_pskl_uskl_to_pskl; exact Hin0).
          eapply (IHHsubty HwfΘ HαΘ Htags Hdfresh (Ξc1 ++ Θ0) (κc1 ++ κ)
                    HwfΞ1 Hαr Hinc1 Hακdom' Hκav'
                    Rb (uskl_to_pskl Rb) P02 Pa1
                    (Ψi `union` (Ψ1 ∩ Ψ')) (Ψ2 ∩ Ψ')
                    eq_refl HscopeRb HlcRb HdisjRb HwfP02R HwfPa1
                    HmodSK2 HmodTY2 HsubR HΨs1R HΨs2R HshieldR Hpre1 Href2'
                    HeqSubB' Hne0 Hin0 HαRb HwfSubjB).
      - (* leaf, absent *)
        eapply (@a_looksub_solve_complete_leaf_id n NM M (Ξc1 ++ Θ0) Θ
                  (κc1 ++ κ) Δ Ψ' (Ψi `union` (Ψ1 ∩ Ψ')) (Ψ2 ∩ Ψ') Ψ2 ψa Q2
                  (uskl_to_pskl Rb) P02 Pa1 Rb α
                  HwfΘ HwfΞ1 HwfP02R HwfPa1 HmodSK2 HmodTY2 Hinc1
                  HαΘ Hαr eq_refl HscopeRb HlcRb Htags HdisjRb HsubR
                  Hdfresh HshieldR Hpre1 HΨs1R HΨs2R);
          [ rewrite <- HeqSubB'; exact Hsubty
          | rewrite <- HeqSubB'; exact HwfSubjB
          | exact Href2'
          | left; exact Hnin0 ]. }
    destruct REC as (C2 & Ξc2 & Pa2 & κc2 & HLK2 & HSolve2 & HwfPa2 & HwfΞ2
                     & HαΞ2 & Hmap2 & Himg2 & Hinc2 & Hinceq2 & Hκf2 & Hpre2).
    (* --- ASSEMBLY: LS-Arrow pairs [Ξc1,Ξc2] with [C1++C2], and the two
       solves compose because C1 (a LOOKEQ's output) holds no subtyping
       constraint.  Identical to P6-Cs's Arrow assembly. --- *)
    pose proof (a_lookeq_all_flex_mono HLK1) as HfmΞ1.
    pose proof (a_looksub_all_flex_mono HLK2) as HfmΞ2.
    destruct (@a_inc_flex_prefix_split Ξc1 κc1 Θ0 κ Θ HfmΞ1 Hmap1 Hinc1)
      as [Hwm1 _].
    destruct (@a_inc_flex_prefix_split Ξc2 κc2 (Ξc1 ++ Θ0) (κc1 ++ κ) Θ
                HfmΞ2 Hmap2 Hinc2) as [Hwm2 _].
    pose proof (@keys_eq_dom _ _ κc2 Ξc2 Hmap2) as Hd2.
    assert (Hmapc : keys (κc1 ++ κc2) = keys (Ξc1 ++ Ξc2))
      by (rewrite !keys_app; rewrite Hmap1, Hmap2; reflexivity).
    assert (Hdisj12 : forall β0, β0 `in` dom κc1 -> β0 `notin` dom κc2).
    { intros β0 Hβ0 Hin2. pose proof (Hκf2 β0 Hin2) as Hf2.
      rewrite dom_app in Hf2. rewrite Hd1 in Hβ0. clear - Hf2 Hβ0; fsetdec. }
    assert (HΞ2disj : forall x, x `in` dom Ξc2 -> x `notin` dom (Ξc1 ++ Θ0)).
    { intros x Hx. rewrite <- Hd2 in Hx. pose proof (Hκf2 x Hx) as Hf.
      clear - Hf; fsetdec. }
    exists (C1 ++ C2), (Ξc1 ++ Ξc2), Pa2, (κc1 ++ κc2).
    repeat split.
    -- (* a_looksub : LS-Arrow *)
       rewrite <- HeraseR. apply a_looksub__arrow; [ exact HLK1 | exact HLK2 ].
    -- (* solve *)
       rewrite (@app_assoc _ Ξc1 Ξc2 Θ0).
       eapply a_solve_cstr_app;
         [ exact (a_lookeq_cstr_eq HLK1)
         | apply a_solve_cstr_weaken_mid_flex;
             [ exact HfmΞ2 | exact HΞ2disj
             | intros x Hx; pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfd;
                 specialize (HΞ2disj x Hx); rewrite dom_app in HΞ2disj;
                 simpl in Hfd; clear - Hfd HΞ2disj; fsetdec
             | intros x Hx;
                 pose proof ((proj2 a_looksub_lookeq_ftv) _ _ _ _ _ HLK1) as Hcf;
                 pose proof (a_wf_pskl_ftv_dom HwfP01) as Hpf;
                 specialize (HΞ2disj x Hx); rewrite dom_app in HΞ2disj;
                 simpl in Hpf; clear - Hcf Hpf HΞ2disj; fsetdec
             | exact HSolve1 ]
         | eapply a_solve_cstr_ctx_change;
             [ exact HSolve2
             | intros α1 Hg; destruct Hg as [Hb | [τ Hb]];
                 [ left | right; exists τ ]; apply binds_swap_app; exact Hb
             | intros P0 Hf; inversion Hf; subst;
                 [ apply a_flex__var with (α := α0)
                 | apply a_flex__var_def with (α := α0) (τ := τ) ];
                 apply binds_swap_app; assumption ] ].
    -- (* wf Pa2 *)
       rewrite (@app_assoc _ Ξc1 Ξc2 Θ0).
       apply a_wf_pskl_swap_app; exact HwfPa2.
    -- (* a_wf_aenv *)
       apply a_wf_aenv_flex_prefix;
         [ apply all_flex_mono_app; assumption
         | pose proof (a_wf_aenv_uniq_local HwfΞ2) as Huq;
           clear - Huq; solve_uniq
         | exact HwfΘ0 ].
    -- (* α ∉ dom (Ξc1++Ξc2) *)
       rewrite dom_app; clear - HαΞ1 HαΞ2; fsetdec.
    -- (* keys *) exact Hmapc.
    -- (* κc images ⊆ ftv ψa *) apply Forall_app; split; assumption.
    -- (* a_inc *)
       apply a_inc_flex_prefix_build;
         [ apply all_flex_mono_app; assumption
         | exact Hmapc
         | apply Forall_app; split; assumption
         | exact Hκ ].
    -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
    -- (* κc fresh *)
       intros α0 Hα0. rewrite dom_app in Hα0.
       apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0].
       ++ apply Hκf1; exact Hα0.
       ++ pose proof (Hκf2 α0 Hα0) as Hf. rewrite dom_app in Hf.
          clear - Hf; fsetdec.
    -- (* precision *)
       rewrite (@app_assoc _ κc1 κc2 κ).
       rewrite (@msubst_pskl_app_swap κc1 κc2 κ Pa2 Hdisj12).
       eapply ad_partial_precise_psi_cong;
         [ exact Hpre2 | clear - HΨa; fsetdec ].
  - (* ForallL, tagged : the subject's ∀ is instantiated, so the IH must run
       at [open R' ψb] — this is why the induction is on the DERIVATION and
       not on P6-Cs's measure.

       PREREQUISITE — DONE.  The REVERSE of
       [lemma:constraint-collection-stable-substitution] is now
       [a_looksub_subst_stable_rev] (prop_looksub.v §4b, Qed, axiom-free):

         (subst Pg βg Pu) ≼[α,m] P' ⤳ Ξ ⨾ 𝒞 ->
         βg <> α -> α ∉ ftv Pg -> lc Pg -> lc Pu ->
         Pu ≼[α,m] P' ⤳ Ξ ⨾ 𝒞.

       BLOCKER — THE PAPER'S IH INSTANCE DOES NOT TYPE-CHECK IN THIS
       ENCODING.  subtyping-proofs.tex:2600–2643 applies the IH with
       [S := S'[ψ_b/β]] and, in passing from \refb to \refe, uses

           θ (S'[ψ_b/β])  =  (θ S')[ψ_b/β],

       which holds ONLY IF [θ ψ_b = ψ_b].  Here the subject is written
       EXACTLY as the paper writes it, [(κ R')[ψa/α]] with R' κ-FREE and
       Θ0-scoped, so choosing [R'' := open R0 ψ] forces

           msubst_uskl_syn κ (open R0 ψ) = open (msubst_uskl_syn κ R0) ψ,

       i.e. [msubst_uskl_syn κ ψ = ψ] — and NOTHING in the premises gives
       it.  ψ is the ForallL rule's guess, constrained only by
       [Θ ⨟ empty ⊢ₚₛᵃ ⌊ψ⌋ˢ], so [ftv ψ ⊆ dom Θ]; and [a_inc]'s flexible
       rows ([a_inc__flex], [a_inc__flex_def]) leave the TARGET arbitrary,
       so a Θ-scoped ψ may perfectly well mention a [dom κ] variable.  Nor
       can a pre-image be manufactured: κ's images are MONOTYPES
       ([metasubst = list (atom * ptyp)] + [mono_ptyp]) while ψ is a
       general tagged skeleton, so extending κ (or Θ0) to name ψ is not an
       option either.

       ⚠️ AND NO PREMISE ON κ RESCUES THAT STEP — three machine-checked
       facts, all in cex/cex_p6ss_inc_compat.v (two rounds of review):

       - Barendregt disjointness [dom κ ∩ dom Θ = ∅] is UNSATISFIABLE at
         identity metasubstitutions, whose flexible entries are all
         PRESERVED in the target (algorithmic.tex:135-140) — and identity
         is what the pipeline supplies ([id_inc_dom_overlap]).
       - Syntactic compatibility [∀ α̂ ∈ dom κ ∩ dom Θ, κα̂ = α̂] EXCLUDES a
         legitimate θ: at Θ = [α̂ := ⟨⟩], the θ with θα̂ = ⟨⟩ substitutes a
         DEFINED survivor's definition — licensed by the paper's own
         "preserved ... but possibly with more monomorphic information" —
         and is inc-EQUIVALENT to ι ([def_subst_theta_is_legit]).
       - The strongest defensible invariant — SEMANTIC compatibility,
         [α̂ ∈ dom Θ ⟹ Θ ⊢ κα̂ ≡ᵗ α̂], which kills the junk θ that moves
         an UNDEFINED survivor ([inc_moves_survivor], derivable only
         because the figure's flex rule demands nothing but wf of the
         image) while keeping the definition-substituting θ — STILL leaves
         [κψ_b ≠ ψ_b] on that legitimate θ (third conjunct of
         [def_subst_theta_is_legit]).  The written step holds essentially
         only at ι-like κ; the lemma quantifies over general κ.

       REPAIR (decided after review; NOT yet built): PROOF-side, statement
       UNCHANGED — restructure the induction the way P6-Sv already does.
       Generalize the motive over an accumulated rigid substitution ρ: each
       ForallL opens with a FRESH RIGID β and the guess rides OUTSIDE κ as
       ρ := ρ ∘ [ψ/β], so the subject is ρ((κR'')[ψa/α]) with β ∉ dom κ ∪
       dom Θ0 and κ's images β-free — no κ/ψ commutation ever arises.  The
       theorem is the ρ = identity instance.  The looksub side then runs on
       var-opened subjects, so LS-ForallL rebuilds via its cofinite family
       directly ([a_looksub_lookeq_rename_tvar]); the reverse-substitution
       lemma [a_looksub_subst_stable_rev] is NOT needed on this route (it
       stays in prop_looksub.v as a true, independently useful fact).  The
       [P = α] leaf calls [a_solve_sub_complete_var] at the ACCUMULATED ρ —
       the general-ρ interface P6-Sv was built with, which the current
       identity-ρ leaf leaves unused.  Cost: the aux lemma carries P6-Sv's
       ρ premise kit ([uskl_rho], [rho_fresh] via the binds-monotone
       Θs-generalization, [flex_apart_walk]/[flex_shield] at Δρ — so
       [sub_shield] generalizes to carry Δρ) and the eight closed rows are
       re-dispatched under the generalized motive (mechanical).  The tag
       bookkeeping (the instantiated binder's ε, previously an open
       sub-question) is expected to follow P6-Sv's Ψρ treatment — the
       guesses' tags accumulate in Ψρ, with [Ψρ ∩ Ψ' = ∅] from the rule's
       own freshness premises; verify when executing.

       The SCOPE-premise relaxation ([ftv R' ⊆ add α (dom Θ0 ∪ dom Θ)],
       done here and in P6-Cs with the dual κc-freshness conclusion
       strengthened) predates this decision and is kept: it is harmless,
       and the Arrow row wants the strengthened conclusion anyway.  (It is
       also all that is needed on the scope side: β enters Θ0 AND Θ as a
       rigid — [rho_fresh] insists every ρ-replaced variable be a rigid of
       the context — so [ftv (open R0 (var β))] stays inside the bound.)

       SCOPE OF THE REPAIR, MEASURED.  The Check row hands its WHOLE
       subject to P6-Cs, and a ForallL can sit above a Check, so **P6-Cs
       must be ρ-generalized too**.  That is threading, not new theory:
       P6-Cv ([a_solve_eq_complete_var_gen], prop_look_complete_var.v:505)
       ALREADY takes [uskl_rho NM Θ Δρ Ψρ ψsub ψa]; the [uskl_rho_*_l_inv]
       kit exists; P6-Cs's measure ([size R' + size P0], on the ρ-FREE
       ideal subject) is unaffected; its ∀ rows open with fresh VARIABLES
       so ρ never grows inside it; and its leaf passes the real ρ down
       instead of [urho__refl].

       READY HERE for that step: [sub_shield] already carries Δρ (the
       statement below instantiates it at [empty], so nothing has moved
       yet) with [sub_shield_add_fresh] / [_weaken_tvar], and
       [ad_partial_precise_delta_shrink_fresh] is the Δ-return the row
       needs.  P6-Sv's ForallL row (prop_look_complete_sub_var.v:2308) is
       the line-by-line template for the rest — with one simplification:
       P6-Ss's ∀ comes from the SUBJECT, so ψa, P0, Pi, Ψi and Ψa do NOT
       move, and only Θ0/Θ/Δ/Δρ grow by β. *)
    admit.
  - (* ForallL, untagged : identical to the tagged row; the mech splits the
       paper's single rule by the subject's POTENTIAL tag. *)
    admit.
  - (* Ghost : IMPOSSIBLE — the subject is [uskl_hole], so R' is □ and has
       no free variables, contradicting α ∈ ftv R'. *)
    exfalso.
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in HeqSub, HαR;
      solve [ discriminate HeqSub
            | contradiction (HRnv _ eq_refl)
            | clear - HαR; fsetdec ].
  - (* GhostG : IMPOSSIBLE for the same reason (subject [uskl_holeg]). *)
    exfalso.
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in HeqSub, HαR;
      solve [ discriminate HeqSub
            | contradiction (HRnv _ eq_refl)
            | clear - HαR; fsetdec ].
  - (* UnivGhostL : R' = ∀◇R0; the IH runs at the body with P0 UNCHANGED
       (so [sub_shield] is threaded as is), then LS-UnivGhostL rebuilds.

       RECIPE (the structural point that used to block this is SOLVED —
       [a_looksub_solve_complete_leaf] above).  A recursive row can land on
       a special case: here R0 may be [var α], and then R' = ∀◇α, whose
       erasure is ∀◇α ≠ α, so THIS level is not special while the level
       below is.  The IH cannot serve it — it demands [HPnα] and [Hin],
       which were reverted into the induction — and a derivation induction
       cannot re-run the dispatch the way P6-Cs's measure induction does.
       So every recursive site dispatches:

         destruct (In_dec α (ftv ⌊R0⌋ˢ)) as [Hin0 | Hnin0];
           [ destruct (pskl_var_dec ⌊R0⌋ˢ α) as [Heq0 | Hne0];
               [ (* leaf, var  *) eapply a_looksub_solve_complete_leaf …
               | (* recurse    *) eapply IHHsubty … ]
           | (* leaf, absent *) eapply a_looksub_solve_complete_leaf … ].

       Then rebuild with LS-UnivGhostL: the conclusion at R0 is about
       [⌊R0⌋ˢ], and [a_looksub__univ_ghost_l] lifts it to [∀◇⌊R0⌋ˢ] = ⌊R'⌋ˢ
       with 𝒞, Ξc, Pa, κc ALL UNCHANGED — P0 does not move, so [sub_shield]
       threads as is and every other conjunct of the conclusion is
       literally the recursive one.  R''s shape comes from [HeqSub] by
       [destruct R']: every branch but [tophole] discriminates, and the
       variable branch is [HRnv]. *)
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in HeqSub, HαR, HeraseR;
      try solve [ discriminate HeqSub | contradiction (HRnv _ eq_refl) ].
    injection HeqSub as HeqSub0.
    assert (REC : exists 𝒞 Ξc Pa κc,
      (⌊ R0 ⌋ˢ ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞) /\
      (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Pa /\
      (Ξc ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa /\
      a_wf_aenv (Ξc ++ Θ0) /\
      α `notin` dom Ξc /\
      keys κc = keys Ξc /\
      Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
      (κc ++ κ) ∷ (Ξc ++ Θ0) ⊑ Θ /\
      a_inc_equiv Θ0 κ κ Θ /\
      (forall α0, α0 `in` dom κc -> α0 `notin` add α (dom Θ0 `union` dom Θ)) /\
      Θ ⨟ Δ ⊢ (msubst_pskl (κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa).
    { assert (HlcR0 : lc_uskl R0) by (inversion HlcR; assumption).
      assert (HwfSubj0 : Θ ⨟ empty ⊢ₚₛᵃ
                (uskl_to_pskl (subst_bskl_in_uskl ψa α
                                 (msubst_uskl_syn κ R0)))).
      { cbn [msubst_uskl_syn subst_bskl_in_uskl uskl_to_pskl] in HwfSubj.
        rewrite <- HeqSub0.
        eapply a_wf_pskl_tophole_inv; exact HwfSubj. }
      destruct (AtomSetProperties.In_dec α (ftvar_in_pskl ⌊ R0 ⌋ˢ))
        as [Hin0 | Hnin0].
      - destruct (pskl_var_dec ⌊ R0 ⌋ˢ α) as [Heq0 | Hne0].
        + (* leaf, var *)
          eapply a_looksub_solve_complete_leaf_id;
            solve [ eassumption | reflexivity | assumption
                | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption | assumption
                  | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption
                  | clear - HscopeR; cbn in HscopeR; fsetdec
                  | exact HlcR0
                  | clear - Hdisj; cbn in Hdisj; fsetdec
                  | clear - HΨs1; cbn in HΨs1; fsetdec
                  | rewrite <- HeqSub0; exact Hsubty
                  | exact HwfSubj0
                  | right; exact Heq0 ].
        + (* recurse *)
          eapply IHHsubty;
            solve [ eassumption | reflexivity | assumption
                | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption | assumption
                  | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption
                  | clear - HscopeR; cbn in HscopeR; fsetdec
                  | exact HlcR0
                  | clear - Hdisj; cbn in Hdisj; fsetdec
                  | clear - HΨs1; cbn in HΨs1; fsetdec
                  | exact HeqSub0
                  | exact Hne0 | exact Hin0
                  | clear - HαR; cbn in HαR; fsetdec
                  | exact HwfSubj0 ].
      - (* leaf, absent *)
        eapply a_looksub_solve_complete_leaf_id;
          solve [ eassumption | reflexivity | assumption
                | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption
                | clear - HscopeR; cbn in HscopeR; fsetdec
                | exact HlcR0
                | clear - Hdisj; cbn in Hdisj; fsetdec
                | clear - HΨs1; cbn in HΨs1; fsetdec
                | rewrite <- HeqSub0; exact Hsubty
                | exact HwfSubj0
                | left; exact Hnin0 ]. }
    destruct REC as (𝒞 & Ξc & Pa & κc & Hlook & Hrest).
    exists 𝒞, Ξc, Pa, κc.
    split; [ rewrite <- HeraseR; apply a_looksub__univ_ghost_l; exact Hlook
           | exact Hrest ].
  - (* UnivGhostLG : identical, for the dotted ghost — both ∀◇ and ∀◈
       ERASE to [pskl_tophole], so the very same LS-UnivGhostL rebuild
       applies and only the surviving [destruct R'] branch differs. *)
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in HeqSub, HαR, HeraseR;
      try solve [ discriminate HeqSub | contradiction (HRnv _ eq_refl) ].
    injection HeqSub as HeqSub0.
    assert (REC : exists 𝒞 Ξc Pa κc,
      (⌊ R0 ⌋ˢ ≼[ α , M ] P0 ⤳ Ξc ⨾ 𝒞) /\
      (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Pa /\
      (Ξc ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa /\
      a_wf_aenv (Ξc ++ Θ0) /\
      α `notin` dom Ξc /\
      keys κc = keys Ξc /\
      Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
      (κc ++ κ) ∷ (Ξc ++ Θ0) ⊑ Θ /\
      a_inc_equiv Θ0 κ κ Θ /\
      (forall α0, α0 `in` dom κc -> α0 `notin` add α (dom Θ0 `union` dom Θ)) /\
      Θ ⨟ Δ ⊢ (msubst_pskl (κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa).
    { assert (HlcR0 : lc_uskl R0) by (inversion HlcR; assumption).
      assert (HwfSubj0 : Θ ⨟ empty ⊢ₚₛᵃ
                (uskl_to_pskl (subst_bskl_in_uskl ψa α
                                 (msubst_uskl_syn κ R0)))).
      { cbn [msubst_uskl_syn subst_bskl_in_uskl uskl_to_pskl] in HwfSubj.
        rewrite <- HeqSub0.
        eapply a_wf_pskl_tophole_inv; exact HwfSubj. }
      destruct (AtomSetProperties.In_dec α (ftvar_in_pskl ⌊ R0 ⌋ˢ))
        as [Hin0 | Hnin0].
      - destruct (pskl_var_dec ⌊ R0 ⌋ˢ α) as [Heq0 | Hne0].
        + (* leaf, var *)
          eapply a_looksub_solve_complete_leaf_id;
            solve [ eassumption | reflexivity | assumption
                | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption | assumption
                  | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption
                  | clear - HscopeR; cbn in HscopeR; fsetdec
                  | exact HlcR0
                  | clear - Hdisj; cbn in Hdisj; fsetdec
                  | clear - HΨs1; cbn in HΨs1; fsetdec
                  | rewrite <- HeqSub0; exact Hsubty
                  | exact HwfSubj0
                  | right; exact Heq0 ].
        + (* recurse *)
          eapply IHHsubty;
            solve [ eassumption | reflexivity | assumption
                | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption | assumption
                  | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption
                  | clear - HscopeR; cbn in HscopeR; fsetdec
                  | exact HlcR0
                  | clear - Hdisj; cbn in Hdisj; fsetdec
                  | clear - HΨs1; cbn in HΨs1; fsetdec
                  | exact HeqSub0
                  | exact Hne0 | exact Hin0
                  | clear - HαR; cbn in HαR; fsetdec
                  | exact HwfSubj0 ].
      - (* leaf, absent *)
        eapply a_looksub_solve_complete_leaf_id;
          solve [ eassumption | reflexivity | assumption
                | cbn; eassumption | rewrite <- HeqSub0; eassumption | rewrite HeqSub0; eassumption
                | clear - HscopeR; cbn in HscopeR; fsetdec
                | exact HlcR0
                | clear - Hdisj; cbn in Hdisj; fsetdec
                | clear - HΨs1; cbn in HΨs1; fsetdec
                | rewrite <- HeqSub0; exact Hsubty
                | exact HwfSubj0
                | left; exact Hnin0 ]. }
    destruct REC as (𝒞 & Ξc & Pa & κc & Hlook & Hrest).
    exists 𝒞, Ξc, Pa, κc.
    split; [ rewrite <- HeraseR; apply a_looksub__univ_ghost_l; exact Hlook
           | exact Hrest ].
  - (* FlexMono : IMPOSSIBLE — the subject is a bare flexible variable, so
       R' would have to be a variable, which [HRnv] excludes. *)
    exfalso.
    destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
      cbn in HeqSub, HαR;
      solve [ discriminate HeqSub
            | contradiction (HRnv _ eq_refl)
            | clear - HαR; fsetdec ].
Admitted.  (* TODO[P6-Ss]: statement + [sub_shield] machinery are in place
    and the plan is DESIGN-completeness-subtyping.md §8; the case analysis
    is not started.  The statement is believed TRUE (it is P6-Cs's, with the
    mode data and the same repair P6-Sv needed); what remains is the work.

    Order to execute:
      1. the two SPECIAL CASES before the induction — P = α (LS-Var, then
         [a_solve_sub_complete_var] at ρ = identity, whose [flex_shield] /
         [flex_apart_walk] come from [sub_shield_here]) and P = a flexible
         (LS-Absent, Ψa = ∅);
      2. Infer / UnivGhostR / Ghost / GhostG — [skmod] forces P0 = □, so
         LS-Vacuous and the identity solve close them, as in P6-Cs;
      3. Check — delegates WHOLE to P6-Cs ([a_lookeq_solve_complete]) and
         re-wraps with LS-Check;
      4. UnivGhostL / LG — IH at the body, LS-UnivGhostL;
      5. ForallR — P0 = ∀.P0', descend with [sss_all] + [sub_shield_step],
         IH at Θ,β, then strip β (P6-Cs's ∀-binder kit);
      6. Arrow — P0 = P01→P02: LEFT to P6-Cs, RIGHT to the IH with
         [sss_arrow_r] + [sub_shield_step]; the two constraint sets
         concatenate (LS-Arrow) and the two solves compose;
      7. ForallL — the subject's ∀ is instantiated, so the IH runs at
         [open R' ψb]; the paper closes it with the REVERSE direction of
         [lemma:constraint-collection-stable-substitution].

    DONE so far: [a_solve_sub_wf] (Qed — read its header before touching
    it, the Δ-uniform statement is FALSE and its side condition is
    load-bearing), BOTH special cases before the induction, i.e.
    α ∉ ftv P (LS-Absent, Ψa = ∅) and P = α (LS-Var, then P6-Sv at
    ρ = IDENTITY with [sub_shield_here] supplying its two repair premises),
    and EIGHT of the twelve rows: Infer, Check, UnivGhostR, UnivGhostL,
    UnivGhostLG, Ghost, GhostG, FlexMono.

    2026-07-29 (this session): the ForallL PREREQUISITE is closed —
    [a_looksub_subst_stable_rev] (prop_looksub.v §4b, Qed, axiom-free) — and
    the SCOPE premise / κc-freshness conclusion were relaxed here and in
    P6-Cs from [dom Θ0] to [dom Θ0 ∪ dom Θ].  The paper's ForallL step
    needs [θψ_b = ψ_b], which fails even for legitimate θ (three
    machine-checked facts in cex/cex_p6ss_inc_compat.v) — a PROOF-STEP
    gap, and no premise on κ repairs it.  DECIDED REPAIR (not yet built):
    the ρ-generalized induction, statement UNCHANGED — see the block at
    the [ForallL, tagged] admit and docs/PAPER-GAPS.md.

    OPEN DESIGN POINT for Sub-ForallR — and a [paper-gap].  Rebuilding
    with LS-ForallR needs the SAME [Ξ ⨾ 𝒞] for every β, i.e. β ∉ ftv 𝒞.
    P6-Cs gets that from the ψa-RELATIVE bound it carries as a conclusion
    (β is fresh for ψa, dom κ and def_ftv Θ); the STRUCTURAL bound
    [a_looksub_ftv] gives only ftv 𝒞 ⊆ ftv P0 ∪ dom Ξc, which still admits
    β.  P6-Cs's route does not transport: it comes from
    [ad_pat_consis_target_ftv], and consistency's ForallInh opens with a
    fresh VARIABLE, whereas Sub-ForallL instantiates with a GUESS bounded
    only by ftv ψ_b ⊆ dom Θ.  The paper (subtyping-proofs.tex:2412) applies
    \lslab{ForallR} to a SINGLE IH instance and never establishes this —
    see docs/PAPER-GAPS.md.  When the row is reached: do NOT chase the
    target-ftv bound; the guess is UNDONE by the reverse direction of
    [lemma:constraint-collection-stable-substitution], so ψ_b's variables
    never enter 𝒞, and the bound to prove ties P0 to ψa through the
    PRECISION and REFINEMENT premises, which Sub-ForallL leaves untouched.

    MEASURE: NOT P6-Cs's [size_uskl R' + size_pskl P0].  Consistency's ∀
    rules open with a VARIABLE (size-preserving), but Sub-ForallL opens with
    the GUESS ψb, so the subject can GROW.  Induct on the [ad_pat_sub_g]
    derivation instead, as P6-Sv does. *)
