(** ext_algo — THE FOUR REL-TRANSPORTS (campaign §8c.9, the extract
    level's option (b); docs/HANDOFF-extractable-algo-encoding.md §8c.9).

    A solve-layer derivation on side-1 data transports to any
    [rel_pskl ρ V]-related side-2 data over any context that flex-AGREES
    on ρ's pairs and V ([flex_agree_rel], §2) and whose ftvar covers the
    motive sets.  Side 1 is NEVER rebound (the §8c.9 second-pass design):
    a binder row opens side 2 at its OWN fresh witness, PAIRS the two
    openers into ρ ([rel_pskl_open_pair]), and a closing row re-closes by
    [rel_pskl_close_pair] (both prop_solve_det.v §1) — so none of the
    det-template's swap-chain bookkeeping exists here at all.

    §1  shape predicates (lc / nonghost / guarded / ghost-free / nonflex)
        transport along the rel;
    §2  [flex_agree_rel ρ V Θ1 Θ2] — the context interface: id-agreement
        on V plus pairwise agreement on ρ — and its push kit (rigid PAIR,
        common rigid, aligned flex-pair blocks);
    §3  [a_guess_mono_rel]   — guess^TY (no agreement needed: the guess
        never reads flexibility, the context is only an avoid-set);
    §4  [a_solve_eq_rel]     — the eq layer (SE-FlexR consumes §2 + §3);
    §5  [a_solve_sub_rel]    — the sub layer.  ⭐ The conclusion adds
        [ρx]: SS-ForallR's opener pairs, which never re-close (the rule's
        yield passes through, the leak is BY DESIGN) and stay in the
        yield relation as RIGID pairs, fresh on their own sides;
    §6  [a_solve_cstr_rel]   — the fold, pointwise on [rel_a_cstrs]
        (the HYGIENIC-REDERIVATION consumer; the b-core is fused and
        must NOT be stated through a list rel — §8c.9).

    Every side-2 generated name additionally dodges the caller's
    avoid-set [L] — the supply discipline's relational rendering. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_coercions.
Require Import src.frost.prop_ln.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.ext_algo.prop_solve_det.

(* the ∀-quantified inputs are inferable from the derivation and relation
   arguments — applications read [lemma Hd L Hrel …] with the target
   context inferred from the [flex_agree_rel] argument *)
Set Implicit Arguments.

Open Scope frost_a_scope.

(* ===================================================================== *)
(*  §1  Shape predicates transport along the rel                          *)
(* ===================================================================== *)

Lemma rel_pskl_degree : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  forall k, degree_pskl_wrt_pskl k P1 -> degree_pskl_wrt_pskl k P2.
Proof.
  intros * Hrel; induction Hrel; intros k Hd; inversion Hd; subst;
    constructor; auto.
Qed.

Lemma rel_pskl_lc : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> lc_pskl P1 -> lc_pskl P2.
Proof.
  intros * Hrel Hlc.
  apply lc_pskl_of_degree.
  eapply rel_pskl_degree; [ exact Hrel | ].
  apply degree_pskl_wrt_pskl_of_lc_pskl. exact Hlc.
Qed.

Lemma rel_pskl_nonghost : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> nonghost_pskl P1 -> nonghost_pskl P2.
Proof.
  intros * Hrel Hng; inversion Hng; subst; inversion Hrel; subst;
    constructor.
Qed.

Lemma rel_pskl_guarded : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> guarded_pskl P1 -> guarded_pskl P2.
Proof.
  intros * Hrel Hg; inversion Hg; subst; inversion Hrel; subst;
    constructor; eauto using rel_pskl_lc.
Qed.

Lemma rel_pskl_ghost_free : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> pskl_ghost_free P1 -> pskl_ghost_free P2.
Proof.
  intros * Hrel; induction Hrel; simpl; intros; try tauto.
Qed.

(* ===================================================================== *)
(*  §2  Flex-agreement on a rel pair list                                 *)
(*                                                                        *)
(*  ⚙ The three [a_flex_tvar] context-plumbing lemmas below are MOVED     *)
(*  from prop_run_complete.v §3a/§5a (2026-08-16: this file sits below    *)
(*  it; one fact, one name, one file).                                    *)
(* ===================================================================== *)

Lemma a_flex_tvar_notin_app : forall (Ξ Θ : aenv) α,
  α `notin` dom Ξ ->
  (a_flex_tvar (Ξ ++ Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros * Hn. split.
  - intros [Hb | [τ Hb]]; unfold binds in *;
      apply in_app_or in Hb; destruct Hb as [Hb | Hb];
      try solve [ exfalso; apply Hn; eapply binds_In; exact Hb ];
      [ left; exact Hb | right; eexists; exact Hb ].
  - intros [Hb | [τ Hb]]; unfold binds in *;
      [ left | right; eexists ]; apply in_or_app; right; eassumption.
Qed.

Lemma a_flex_tvar_cons_tvar_other : forall β (Θ : aenv) α,
  α <> β ->
  (a_flex_tvar ((β ~ abind_tvar) ++ Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros * Hne. split.
  - intros [Hb | [τ Hb]]; unfold binds in Hb; simpl in Hb;
      (destruct Hb as [Hb | Hb]; [ solve [ inversion Hb; congruence ] | ]);
      [ left; exact Hb | right; eexists; exact Hb ].
  - intros [Hb | [τ Hb]]; [ left | right; eexists ];
      unfold binds in *; simpl; right; eassumption.
Qed.

Lemma a_flex_tvar_cons_flex_other : forall b (Θ : aenv) α,
  α <> b ->
  (a_flex_tvar ((b, abind_flex_mono) :: Θ) α <-> a_flex_tvar Θ α).
Proof.
  intros * Hne. split.
  - intros [Hb | [τ Hb]]; unfold binds in Hb; simpl in Hb;
      (destruct Hb as [Hb | Hb]; [ solve [ inversion Hb; congruence ] | ]);
      [ left; exact Hb | right; eexists; exact Hb ].
  - intros [Hb | [τ Hb]]; [ left | right; eexists ];
      unfold binds in *; simpl; right; eassumption.
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

(** ⭐ [flex_agree_rel ρ V Θ1 Θ2] — §8c.9's context interface for the four
    REL-TRANSPORTS: identity agreement on the support [V] (exactly
    [flex_agree], prop_run_complete.v §3a), extended to ρ's PAIRS —
    a paired name has the same flex-status on its own side as its partner
    has on the other. *)
Definition flex_agree_rel (ρ : list (atom * atom)) (V : atoms)
    (Θ1 Θ2 : aenv) : Prop :=
  (forall α, α `in` V -> (a_flex_tvar Θ1 α <-> a_flex_tvar Θ2 α)) /\
  (forall a b, In (a, b) ρ -> (a_flex_tvar Θ1 a <-> a_flex_tvar Θ2 b)).

Lemma flex_agree_rel_weaken : forall ρ ρ' V V' Θ1 Θ2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  (forall a b, In (a, b) ρ' -> In (a, b) ρ) ->
  V' [<=] V ->
  flex_agree_rel ρ' V' Θ1 Θ2.
Proof.
  intros * [HagV Hagp] Hincl Hsub. split.
  - intros α Hα. apply HagV. fsetdec.
  - intros a b Hin. apply Hagp. apply Hincl. exact Hin.
Qed.

(** Pushing one RIGID entry per side, the two names PAIRED into ρ — the
    binder rows' move (both entries are non-flex, so the new pair's
    agreement is False ↔ False). *)
Lemma flex_agree_rel_push_tvar_pair : forall ρ V Θ1 Θ2 β1 β2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  β1 `notin` dom Θ1 ∪ V ∪ cols_l ρ ->
  β2 `notin` dom Θ2 ∪ V ∪ cols_r ρ ->
  flex_agree_rel ((β1, β2) :: ρ) V
    ((β1 ~ abind_tvar) ++ Θ1) ((β2 ~ abind_tvar) ++ Θ2).
Proof.
  intros * [HagV Hagp] Hb1 Hb2. split.
  - intros α Hα.
    destruct (α == β1) as [-> | Hne1];
      [ exfalso; clear - Hb1 Hα; fsetdec | ].
    destruct (α == β2) as [-> | Hne2];
      [ exfalso; clear - Hb2 Hα; fsetdec | ].
    rewrite (a_flex_tvar_cons_tvar_other Θ1 Hne1).
    rewrite (a_flex_tvar_cons_tvar_other Θ2 Hne2).
    apply HagV; exact Hα.
  - intros a b Hin. destruct Hin as [E | Hin].
    + inversion E; subst.
      split; intros Hf; exfalso;
        [ eapply a_flex_tvar_cons_tvar_self;
          [ | exact Hf ]; clear - Hb1; fsetdec
        | eapply a_flex_tvar_cons_tvar_self;
          [ | exact Hf ]; clear - Hb2; fsetdec ].
    + pose proof (cols_l_in _ _ _ Hin) as Hcl.
      pose proof (cols_r_in _ _ _ Hin) as Hcr.
      assert (Hne1 : a <> β1) by (clear - Hb1 Hcl; fsetdec).
      assert (Hne2 : b <> β2) by (clear - Hb2 Hcr; fsetdec).
      rewrite (a_flex_tvar_cons_tvar_other Θ1 Hne1).
      rewrite (a_flex_tvar_cons_tvar_other Θ2 Hne2).
      apply Hagp. exact Hin.
Qed.

(** Pushing one COMMON rigid entry, growing the support — kept for
    consumers that open both sides at one name. *)
Lemma flex_agree_rel_push_tvar : forall ρ V Θ1 Θ2 c,
  flex_agree_rel ρ V Θ1 Θ2 ->
  c `notin` dom Θ1 ∪ dom Θ2 ∪ cols_l ρ ∪ cols_r ρ ->
  flex_agree_rel ρ (add c V)
    ((c ~ abind_tvar) ++ Θ1) ((c ~ abind_tvar) ++ Θ2).
Proof.
  intros * [HagV Hagp] Hc. split.
  - intros α Hα.
    destruct (α == c) as [-> | Hne].
    + split; intros Hf; exfalso;
        eapply a_flex_tvar_cons_tvar_self; try exact Hf;
        clear - Hc; fsetdec.
    + rewrite (a_flex_tvar_cons_tvar_other Θ1 Hne).
      rewrite (a_flex_tvar_cons_tvar_other Θ2 Hne).
      apply HagV. clear - Hα Hne. fsetdec.
  - intros a b Hin.
    pose proof (cols_l_in _ _ _ Hin) as Hcl.
    pose proof (cols_r_in _ _ _ Hin) as Hcr.
    assert (Hne1 : a <> c) by (clear - Hc Hcl; fsetdec).
    assert (Hne2 : b <> c) by (clear - Hc Hcr; fsetdec).
    rewrite (a_flex_tvar_cons_tvar_other Θ1 Hne1).
    rewrite (a_flex_tvar_cons_tvar_other Θ2 Hne2).
    apply Hagp. exact Hin.
Qed.

Lemma binds_flex_pairs_l : forall ρ a b,
  In (a, b) ρ -> binds a abind_flex_mono (flex_pairs_l ρ).
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros * Hin; simpl in *;
    [ contradiction | ].
  destruct Hin as [E | Hin].
  - inversion E; subst. unfold binds. simpl. auto.
  - unfold binds. simpl. right. apply (IH _ _ Hin).
Qed.

Lemma binds_flex_pairs_r : forall ρ a b,
  In (a, b) ρ -> binds b abind_flex_mono (flex_pairs_r ρ).
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros * Hin; simpl in *;
    [ contradiction | ].
  destruct Hin as [E | Hin].
  - inversion E; subst. unfold binds. simpl. auto.
  - unfold binds. simpl. right. apply (IH _ _ Hin).
Qed.

(** ⭐ Extension by an aligned pair of FLEX blocks — the generative steps'
    move (SE-FlexR's guess): the new pairs are flexible on BOTH sides by
    construction, and the old data rides provided the new domains avoid
    it. *)
Lemma flex_agree_rel_push_pairs : forall ρn ρ V Θ1 Θ2,
  flex_agree_rel ρ V Θ1 Θ2 ->
  cols_l ρn ∩ (V ∪ cols_l ρ) [=] empty ->
  cols_r ρn ∩ (V ∪ cols_r ρ) [=] empty ->
  flex_agree_rel (ρn ++ ρ) V
    (flex_pairs_l ρn ++ Θ1) (flex_pairs_r ρn ++ Θ2).
Proof.
  intros * [HagV Hagp] Hdl Hdr. split.
  - intros α Hα.
    rewrite (a_flex_tvar_notin_app (flex_pairs_l ρn))
      by (rewrite dom_flex_pairs_l; clear - Hdl Hα; fsetdec).
    rewrite (a_flex_tvar_notin_app (flex_pairs_r ρn))
      by (rewrite dom_flex_pairs_r; clear - Hdr Hα; fsetdec).
    apply HagV; exact Hα.
  - intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + split; intros _; left;
        [ pose proof (@binds_flex_pairs_r ρn a b Hin) as Hb
        | pose proof (@binds_flex_pairs_l ρn a b Hin) as Hb ];
        unfold binds in *; apply in_or_app; left; exact Hb.
    + pose proof (cols_l_in _ _ _ Hin) as Hcl.
      pose proof (cols_r_in _ _ _ Hin) as Hcr.
      rewrite (a_flex_tvar_notin_app (flex_pairs_l ρn))
        by (rewrite dom_flex_pairs_l; clear - Hdl Hcl; fsetdec).
      rewrite (a_flex_tvar_notin_app (flex_pairs_r ρn))
        by (rewrite dom_flex_pairs_r; clear - Hdr Hcr; fsetdec).
      apply Hagp. exact Hin.
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

(** [a_non_flex] transports along the rel: flex-status of a paired (or
    supported) variable agrees across the two contexts. *)
Lemma rel_pskl_non_flex : forall ρ V Θ1 Θ2 P1 P2,
  rel_pskl ρ V P1 P2 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  a_non_flex Θ1 P1 -> a_non_flex Θ2 P2.
Proof.
  intros * Hrel Hagr [Hlc Hnf].
  split; [ eauto using rel_pskl_lc | ].
  intros Hf. apply Hnf.
  inversion Hf; subst;
    match goal with
    | Hb : binds ?b _ Θ2 |- _ =>
        inversion Hrel; subst;
        match goal with
        | Ha : rel_atom _ _ ?a b |- _ =>
            apply a_flex_var_iff_tvar;
            assert (Hf2 : a_flex_tvar Θ2 b)
              by (first [ left; assumption
                        | right; eexists; eassumption ]);
            inversion Ha; subst;
            [ apply (proj2 (Hagr) _ _ ltac:(eassumption)); exact Hf2
            | apply (proj1 (Hagr) _ ltac:(eassumption)); exact Hf2 ]
        end
    end.
Qed.

(* ===================================================================== *)
(*  §3  Transport 1 — guess^TY along the rel                              *)
(* ===================================================================== *)

(** List bookkeeping: a pair invented by a binder row bubbles to the head
    of the pair list ([In] is order-insensitive). *)
Lemma rel_pskl_bubble_pair : forall ρn ρ V β1 β2 P1 P2,
  rel_pskl (ρn ++ (β1, β2) :: ρ) V P1 P2 ->
  rel_pskl ((β1, β2) :: ρn ++ ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - right. apply in_or_app. left. exact Hin.
  - destruct Hin as [E | Hin];
      [ left; exact E | right; apply in_or_app; right; exact Hin ].
Qed.

(** ⭐ TRANSPORT 1 — [guess^TY]: a guess on side 1 transports to any
    rel-related subject over any context whose ftvar covers the motive
    sets; the two fresh blocks PAIR into ρ's extension, and side 2's
    names additionally dodge the caller's avoid-set [L]. *)
Lemma a_guess_mono_rel : forall Θ1 P1 Ξ1 A1,
  a_guess_mono Θ1 P1 Ξ1 A1 ->
  forall Θ2 (L : atoms) P2 ρ V,
  rel_pskl ρ V P1 P2 ->
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  V ∪ cols_r ρ [<=] ftvar_in_aenv Θ2 ->
  exists ρn Ξ2 A2,
    a_guess_mono Θ2 P2 Ξ2 A2
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ uniq Ξ2 /\ dom Ξ2 ∩ L [=] empty
    /\ rel_pskl (ρn ++ ρ) V (ptyp_to_pskl A1) (ptyp_to_pskl A2).
Proof.
  intros Θ1 P1 Ξ1 A1 HG.
  induction HG; intros Θ2 L P2 ρ V Hrel Hscp1 Hscp2.
  - (* hole ↦ a fresh flexible on each side, PAIRED *)
    inversion Hrel; subst.
    destruct (atom_fresh (ftvar_in_aenv Θ2 ∪ L)) as [α2 Hα2].
    exists ((α, α2) :: nil), ((α2 ~ abind_flex_mono) ++ nil),
      (ptyp_var_f α2).
    split; [ apply a_guess_mono__hole; clear - Hα2; fsetdec | ].
    split; [ reflexivity | ].
    split; [ reflexivity | ].
    split; [ solve_uniq | ].
    split; [ simpl; clear - Hα2; fsetdec | ].
    simpl. constructor. apply rel_atom__pair. left. reflexivity.
  - (* tophole: pass-through *)
    inversion Hrel; subst.
    match goal with
    | Hb : rel_pskl ρ V P ?X |- _ => rename Hb into Hbody; rename X into Q0
    end.
    destruct (IHHG Θ2 L Q0 ρ V Hbody Hscp1 Hscp2)
      as (ρn & Ξ2 & A2 & HG2 & E1 & E2 & Hu & HL & Hrel').
    exists ρn, Ξ2, A2.
    split; [ apply a_guess_mono__tophole; exact HG2 | ].
    split; [ assumption | ].
    split; [ assumption | ].
    split; [ assumption | ].
    split; [ assumption | ].
    assumption.
  - (* var: answers itself on both sides *)
    inversion Hrel; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into β0
    end.
    exists nil, nil, (ptyp_var_f β0).
    split; [ apply a_guess_mono__var | ].
    split; [ reflexivity | ].
    split; [ reflexivity | ].
    split; [ solve_uniq | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor. exact Hat.
  - (* unit *)
    inversion Hrel; subst.
    exists nil, nil, ptyp_unit.
    split; [ apply a_guess_mono__unit | ].
    split; [ reflexivity | ].
    split; [ reflexivity | ].
    split; [ solve_uniq | ].
    split; [ simpl; clear; fsetdec | ].
    simpl. constructor.
  - (* arrow: both halves at the SAME Θ; the right block dodges the left *)
    inversion Hrel; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?X, Hb : rel_pskl ρ V Q ?Y |- _ =>
        rename Ha into HrelA; rename Hb into HrelB;
        rename X into Q0a; rename Y into Q0b
    end.
    destruct (IHHG1 Θ2 L Q0a ρ V HrelA Hscp1 Hscp2)
      as (ρnA & Ξ2a & A2a & HG2a & E1a & E2a & Hua & HLa & HrelA').
    destruct (IHHG2 Θ2 (L ∪ dom Ξ2a) Q0b ρ V HrelB Hscp1 Hscp2)
      as (ρnB & Ξ2b & B2b & HG2b & E1b & E2b & Hub & HLb & HrelB').
    exists (ρnA ++ ρnB), (Ξ2a ++ Ξ2b), (ptyp_arrow A2a B2b).
    split; [ apply a_guess_mono__arrow; assumption | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split;
      [ apply uniq_app_4; [ assumption | assumption | ];
        unfold disjoint; clear - HLb; fsetdec | ].
    split; [ rewrite dom_app; clear - HLa HLb; fsetdec | ].
    simpl. constructor.
      * eapply rel_pskl_mono;
          [ exact HrelA' | | intros x Hx; exact Hx ].
        intros a b Hin. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [Hin | Hin];
          [ left; apply in_or_app; left; exact Hin | right; exact Hin ].
      * eapply rel_pskl_mono;
          [ exact HrelB' | | intros x Hx; exact Hx ].
        intros a b Hin. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [Hin | Hin];
          [ left; apply in_or_app; right; exact Hin | right; exact Hin ].
  - (* forall: side 2 opens at ITS fresh witness; the openers PAIR *)
    inversion Hrel; subst.
    match goal with
    | Hb : rel_pskl ρ V P ?X |- _ => rename Hb into Hbody; rename X into Q0
    end.
    destruct (atom_fresh (ftvar_in_aenv Θ2 ∪ ftvar_in_pskl Q0 ∪ L))
      as [β2 Hβ2].
    assert (Hrelo : rel_pskl ((β, β2) :: ρ) V
                      (open_pskl_wrt_pskl P (pskl_var_f β))
                      (open_pskl_wrt_pskl Q0 (pskl_var_f β2)))
      by (apply rel_pskl_open_pair; exact Hbody).
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2))
      by (simpl; clear - Hscp2; fsetdec).
    destruct (IHHG ((β2 ~ abind_tvar) ++ Θ2) L
                (open_pskl_wrt_pskl Q0 (pskl_var_f β2))
                ((β, β2) :: ρ) V Hrelo Hscp1' Hscp2')
      as (ρn & Ξ2 & A2 & HG2 & E1 & E2 & Hu & HL & Hrel').
    exists ρn, Ξ2, (ptyp_all (close_ptyp_wrt_ptyp β2 A2)).
    (* the two openers leave the block domains *)
    assert (HβΞ1 : β `notin` dom Ξ).
    { intros Hin.
      pose proof (a_guess_mono_generated_fresh HG Hin) as Hgf.
      simpl in Hgf. clear - Hgf. fsetdec. }
    assert (Hβ2Ξ2 : β2 `notin` dom Ξ2).
    { intros Hin.
      pose proof (a_guess_mono_generated_fresh HG2 Hin) as Hgf.
      simpl in Hgf. clear - Hgf. fsetdec. }
    split;
      [ apply a_guess_mono__forall with (β := β2);
        [ clear - Hβ2; fsetdec | exact HG2 ] | ].
    split; [ assumption | ].
    split; [ assumption | ].
    split; [ assumption | ].
    split; [ assumption | ].
    simpl. rewrite ! ptyp_to_pskl_close.
      constructor.
      apply rel_pskl_close_pair.
      * apply rel_pskl_bubble_pair. exact Hrel'.
      * match goal with
        | Hf : β `notin` union _ _ |- _ => clear - Hf Hscp1; fsetdec
        end.
      * rewrite cols_l_app.
        rewrite <- ! dom_flex_pairs_l. rewrite <- E1.
        rewrite dom_flex_pairs_l.
        match goal with
        | Hf : β `notin` union _ _ |- _ => clear - Hf Hscp1 HβΞ1; fsetdec
        end.
      * clear - Hβ2 Hscp2. fsetdec.
      * rewrite cols_r_app.
        rewrite <- ! dom_flex_pairs_r. rewrite <- E2.
        rewrite dom_flex_pairs_r.
        clear - Hβ2 Hscp2 Hβ2Ξ2. fsetdec.
Qed.

(* ===================================================================== *)
(*  §4  Transport 2 — the eq-solve along the rel                          *)
(* ===================================================================== *)

Lemma rel_pskl_widen_hd : forall ρb ρa ρ V P1 P2,
  rel_pskl (ρa ++ ρ) V P1 P2 ->
  rel_pskl ((ρb ++ ρa) ++ ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. apply in_app_or in Hin. apply in_or_app.
  destruct Hin as [Hin | Hin];
    [ left; apply in_or_app; right; exact Hin | right; exact Hin ].
Qed.

Lemma rel_pskl_app_assoc : forall ρa ρb ρ V P1 P2,
  rel_pskl (ρa ++ ρb ++ ρ) V P1 P2 ->
  rel_pskl ((ρa ++ ρb) ++ ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. apply in_app_or in Hin. apply in_or_app.
  destruct Hin as [Hin | Hin].
  - left. apply in_or_app. left. exact Hin.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin];
      [ left; apply in_or_app; right; exact Hin | right; exact Hin ].
Qed.

Lemma rel_pskl_widen : forall ρn ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  rel_pskl (ρn ++ ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. apply in_or_app. right. exact Hin.
Qed.

Lemma rel_pskl_extend_pair : forall β1 β2 ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ((β1, β2) :: ρ) V P1 P2.
Proof.
  intros * Hrel.
  eapply rel_pskl_mono; [ exact Hrel | | intros x Hx; exact Hx ].
  intros a b Hin. right. exact Hin.
Qed.

(** ⭐ TRANSPORT 2 — the eq-solve.  Binder rows never rebind side 1: side 2
    opens at its OWN fresh witness, the two openers PAIR into ρ
    ([rel_pskl_open_pair]) and the yields re-close by
    [rel_pskl_close_pair]. *)
Lemma a_solve_eq_rel : forall Θ1 P1 Q1 Ξ1 P1',
  {{ Θ1 ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}a ->
  forall Θ2 (L : atoms) P2 Q2 ρ V,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ V Q1 Q2 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  V ∪ cols_r ρ [<=] ftvar_in_aenv Θ2 ->
  exists ρn Ξ2 P2',
    {{ Θ2 ⊢ₑ P2 ∼ Q2 ⤳ Ξ2 ⨾ P2' }}a
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ uniq Ξ2 /\ dom Ξ2 ∩ L [=] empty
    /\ rel_pskl (ρn ++ ρ) V P1' P2'.
Proof.
  intros Θ1 P1 Q1 Ξ1 P1' HD.
  induction HD; intros Θ2 L P3 Q3 ρ V HrelP HrelQ Hagr Hscp1 Hscp2.
  - (* SE-Unit *)
    inversion HrelP; subst. inversion HrelQ; subst.
    exists nil, nil, pskl_unit.
    split; [ apply a_solve_eq__unit | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    simpl. constructor.
  - (* SE-Var: a variable subject answers itself *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into β0
    end.
    exists nil, nil, (pskl_var_f β0).
    split; [ apply a_solve_eq__var | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    simpl. constructor. exact Hat.
  - (* SE-FlexR: the guess fires on side 2's paired flexible *)
    inversion HrelQ; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into β0
    end.
    match goal with
    | Hf : a_flex_tvar Θ α |- _ => rename Hf into Hflex1
    end.
    assert (Hflex2 : a_flex_tvar Θ2 β0).
    { inversion Hat; subst.
      - exact (proj1 ((proj2 Hagr) _ _ ltac:(eassumption)) Hflex1).
      - exact (proj1 ((proj1 Hagr) _ ltac:(eassumption)) Hflex1). }
    match goal with
    | HG : a_guess_mono Θ P Ξ ?AA |- _ => rename HG into Hguess
    end.
    destruct (a_guess_mono_rel Hguess Θ2 L HrelP Hscp1 Hscp2)
      as (ρn & Ξ2g & A2 & HG2 & E1 & E2 & Hu & HL & Hrel').
    exists ρn, Ξ2g, (ptyp_to_pskl A2).
    split.
    { apply a_solve_eq__flex_r.
      - exact Hflex2.
      - eapply rel_pskl_non_flex; [ exact HrelP | exact Hagr | ].
        assumption.
      - eapply rel_pskl_nonghost; [ exact HrelP | assumption ].
      - exact HG2. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    exact Hrel'.
  - (* SE-GhostL: ghost subject answers the target *)
    inversion HrelP; subst.
    exists nil, nil, Q3.
    split; [ apply a_solve_eq__hole_l | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    simpl. exact HrelQ.
  - (* SE-VacuousR: ghost target answers the subject *)
    inversion HrelQ; subst.
    exists nil, nil, P3.
    split; [ apply a_solve_eq__hole_r | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    simpl. exact HrelP.
  - (* SE-Arrow: the right half threads the left block *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P1 ?xa, Hb : rel_pskl ρ V P2 ?xb,
      Hc : rel_pskl ρ V Q1 ?xc, Hd : rel_pskl ρ V Q2 ?xd |- _ =>
        rename Ha into HrPa; rename Hb into HrPb;
        rename Hc into HrQa; rename Hd into HrQb;
        rename xa into P2a; rename xb into P2b;
        rename xc into Q2a; rename xd into Q2b
    end.
    destruct (IHHD1 Θ2 L P2a Q2a ρ V HrPa HrQa Hagr Hscp1 Hscp2)
      as (ρnA & Ξ2a & P2a' & D2a & E1a & E2a & Hua & HLa & HrelA').
    (* the two head blocks dodge the motive sets *)
    assert (Hd1a : dom Ξ1 ∩ ftvar_in_aenv Θ [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD1)).
    assert (Hd2a : dom Ξ2a ∩ ftvar_in_aenv Θ2 [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ D2a)).
    pose proof (dom_flex_pairs_l ρnA) as Hdfl. rewrite <- E1a in Hdfl.
    pose proof (dom_flex_pairs_r ρnA) as Hdfr. rewrite <- E2a in Hdfr.
    assert (Hagr' : flex_agree_rel (ρnA ++ ρ) V (Ξ1 ++ Θ) (Ξ2a ++ Θ2)).
    { rewrite E1a, E2a. apply flex_agree_rel_push_pairs.
      - exact Hagr.
      - clear - Hd1a Hscp1 Hdfl. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V ∪ cols_l (ρnA ++ ρ)
                       [<=] ftvar_in_aenv (Ξ1 ++ Θ)).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      clear - Hscp1 Hdfl Hds. fsetdec. }
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ)
                       [<=] ftvar_in_aenv (Ξ2a ++ Θ2)).
    { rewrite cols_r_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ2a) as Hds.
      clear - Hscp2 Hdfr Hds. fsetdec. }
    assert (HrPb' : rel_pskl (ρnA ++ ρ) V P2 P2b)
      by (apply rel_pskl_widen; exact HrPb).
    assert (HrQb' : rel_pskl (ρnA ++ ρ) V Q2 Q2b)
      by (apply rel_pskl_widen; exact HrQb).
    destruct (IHHD2 (Ξ2a ++ Θ2) (L ∪ dom Ξ2a) P2b Q2b (ρnA ++ ρ) V
                HrPb' HrQb' Hagr' Hscp1' Hscp2')
      as (ρnB & Ξ2b & P2b' & D2b & E1b & E2b & Hub & HLb & HrelB').
    exists (ρnB ++ ρnA), (Ξ2b ++ Ξ2a), (pskl_arrow P2a' P2b').
    split; [ apply a_solve_eq__arrow; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { apply uniq_app_4; [ exact Hub | exact Hua | ].
      unfold disjoint. clear - HLb. fsetdec. }
    split; [ rewrite dom_app; clear - HLa HLb; fsetdec | ].
    constructor.
    + apply rel_pskl_widen_hd. exact HrelA'.
    + apply rel_pskl_app_assoc. exact HrelB'.
  - (* SE-Forall: side 2 opens at its own witness; openers PAIR *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa, Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh (ftvar_in_aenv Θ2 ∪ ftvar_in_pskl P2b
                          ∪ ftvar_in_pskl Q2b ∪ L)) as [β2 Hβ2].
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    pose proof (dom_subset_ftvar_in_aenv Θ2) as Hds2.
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 Hscp2 Hds2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2))
      by (simpl; clear - Hscp2; fsetdec).
    destruct (IHHD ((β2 ~ abind_tvar) ++ Θ2) L
                (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_open_pair; exact HrP0)
                ltac:(apply rel_pskl_open_pair; exact HrQ0)
                Hagr' Hscp1' Hscp2')
      as (ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hrel').
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
    assert (Hd2p : dom Ξ2 ∩ ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2)
                     [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ D2p)).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    exists ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
    split.
    { apply a_solve_eq__forall with (β := β2);
        [ clear - Hβ2; fsetdec | exact D2p ]. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    constructor.
    apply rel_pskl_close_pair.
    + apply rel_pskl_bubble_pair. exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + rewrite cols_l_app. simpl in Hd1p.
      clear - Hβ1 Hscp1 Hd1p Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite cols_r_app. simpl in Hd2p.
      clear - Hβ2 Hscp2 Hd2p Hdfr. fsetdec.
  - (* SE-UnivGhost: ⫯ on both sides passes through *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa, Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    destruct (IHHD Θ2 L P2b Q2b ρ V HrP0 HrQ0 Hagr Hscp1 Hscp2)
      as (ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hrel').
    exists ρn, Ξ2, (pskl_tophole Y2).
    split; [ apply a_solve_eq__tophole_both; exact D2p | ].
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    constructor. exact Hrel'.
  - (* SE-GhostForall: the TARGET opens; the subject stays whole *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa, Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh (ftvar_in_aenv Θ2 ∪ ftvar_in_pskl P2b
                          ∪ ftvar_in_pskl Q2b ∪ L)) as [β2 Hβ2].
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    pose proof (dom_subset_ftvar_in_aenv Θ2) as Hds2.
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 Hscp2 Hds2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2))
      by (simpl; clear - Hscp2; fsetdec).
    destruct (IHHD ((β2 ~ abind_tvar) ++ Θ2) L
                (pskl_tophole P2b)
                (open_pskl_wrt_pskl Q2b (pskl_var_f β2))
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_extend_pair; constructor; exact HrP0)
                ltac:(apply rel_pskl_open_pair; exact HrQ0)
                Hagr' Hscp1' Hscp2')
      as (ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hrel').
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
    assert (Hd2p : dom Ξ2 ∩ ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2)
                     [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ D2p)).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    exists ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
    split.
    { apply a_solve_eq__tophole_l_all with (β := β2);
        [ clear - Hβ2; fsetdec | exact D2p ]. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    constructor.
    apply rel_pskl_close_pair.
    + apply rel_pskl_bubble_pair. exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + rewrite cols_l_app. simpl in Hd1p.
      clear - Hβ1 Hscp1 Hd1p Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite cols_r_app. simpl in Hd2p.
      clear - Hβ2 Hscp2 Hd2p Hdfr. fsetdec.
  - (* SE-GhostGuarded: the subject strips its ⫯ *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa |- _ =>
        rename Ha into HrP0; rename xa into P2b
    end.
    destruct (IHHD Θ2 L P2b Q3 ρ V HrP0 HrelQ Hagr Hscp1 Hscp2)
      as (ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hrel').
    exists ρn, Ξ2, Y2.
    split.
    { apply a_solve_eq__tophole_l_guarded;
        [ eapply rel_pskl_guarded; [ exact HrelQ | assumption ]
        | exact D2p ]. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    exact Hrel'.
  - (* SE-ForallGhost: the SUBJECT opens; the target stays whole *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa, Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Ha into HrP0; rename Hb into HrQ0;
        rename xa into P2b; rename xb into Q2b
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh (ftvar_in_aenv Θ2 ∪ ftvar_in_pskl P2b
                          ∪ ftvar_in_pskl Q2b ∪ L)) as [β2 Hβ2].
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    pose proof (dom_subset_ftvar_in_aenv Θ2) as Hds2.
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 Hscp2 Hds2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2))
      by (simpl; clear - Hscp2; fsetdec).
    destruct (IHHD ((β2 ~ abind_tvar) ++ Θ2) L
                (open_pskl_wrt_pskl P2b (pskl_var_f β2))
                (pskl_tophole Q2b)
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_open_pair; exact HrP0)
                ltac:(apply rel_pskl_extend_pair; constructor; exact HrQ0)
                Hagr' Hscp1' Hscp2')
      as (ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hrel').
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HD)).
    assert (Hd2p : dom Ξ2 ∩ ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2)
                     [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ D2p)).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    exists ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
    split.
    { apply a_solve_eq__all_l_tophole with (β := β2);
        [ clear - Hβ2; fsetdec | exact D2p ]. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    constructor.
    apply rel_pskl_close_pair.
    + apply rel_pskl_bubble_pair. exact Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + rewrite cols_l_app. simpl in Hd1p.
      clear - Hβ1 Hscp1 Hd1p Hdfl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite cols_r_app. simpl in Hd2p.
      clear - Hβ2 Hscp2 Hd2p Hdfr. fsetdec.
  - (* SE-GuardedGhost: the target strips its ⫯ *)
    inversion HrelQ; subst.
    match goal with
    | Hb : rel_pskl ρ V Q ?xb |- _ =>
        rename Hb into HrQ0; rename xb into Q2b
    end.
    destruct (IHHD Θ2 L P3 Q2b ρ V HrelP HrQ0 Hagr Hscp1 Hscp2)
      as (ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hrel').
    exists ρn, Ξ2, Y2.
    split.
    { apply a_solve_eq__tophole_r_guarded;
        [ eapply rel_pskl_guarded; [ exact HrelP | assumption ]
        | exact D2p ]. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    exact Hrel'.
Qed.

(* ===================================================================== *)
(*  §5  Transport 3 — the sub-solve along the rel                         *)
(* ===================================================================== *)

Lemma cols_l_fresh : forall (ρx : list (atom * atom)) x,
  (forall a b, In (a, b) ρx -> a <> x) ->
  x `notin` cols_l ρx.
Proof.
  induction ρx as [ | [a b] ρx IH ]; intros x H; simpl;
    [ clear; fsetdec | ].
  pose proof (H a b (or_introl eq_refl)) as Hne.
  pose proof (IH x ltac:(intros a' b' Hin'; apply (H a' b');
                         right; exact Hin')) as Htl.
  clear - Hne Htl. fsetdec.
Qed.

Lemma cols_r_fresh : forall (ρx : list (atom * atom)) x,
  (forall a b, In (a, b) ρx -> b <> x) ->
  x `notin` cols_r ρx.
Proof.
  induction ρx as [ | [a b] ρx IH ]; intros x H; simpl;
    [ clear; fsetdec | ].
  pose proof (H a b (or_introl eq_refl)) as Hne.
  pose proof (IH x ltac:(intros a' b' Hin'; apply (H a' b');
                         right; exact Hin')) as Htl.
  clear - Hne Htl. fsetdec.
Qed.

(** Re-shuffle a pair list by any [In]-preserving permutation. *)
Local Ltac rel_perm H :=
  eapply rel_pskl_mono;
    [ exact H
    | let a0 := fresh "a0" in let b0 := fresh "b0" in
      let Hi := fresh "Hi" in
      intros a0 b0 Hi; revert Hi;
      rewrite ? in_app_iff; simpl; rewrite ? in_app_iff; tauto
    | let x0 := fresh "x0" in let Hx0 := fresh "Hx0" in
      intros x0 Hx0; exact Hx0 ].

(** ⭐ TRANSPORT 3 — the sub-solve.  Beyond the eq shape, the conclusion
    carries [ρx]: the pairs of SS-ForallR openers, which never re-close
    (the rule's yield passes through, the leak is BY DESIGN — see the rule's
    box) and so stay in the yield relation as RIGID pairs, fresh on their
    own sides. *)
Lemma a_solve_sub_rel : forall Θ1 m P1 Q1 Ξ1 P1',
  {{ Θ1 ⊢ₛ P1 ≼[ m ] Q1 ⤳ Ξ1 ⨾ P1' }}a ->
  forall Θ2 (L : atoms) P3 Q3 ρ V,
  rel_pskl ρ V P1 P3 ->
  rel_pskl ρ V Q1 Q3 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  V ∪ cols_r ρ [<=] ftvar_in_aenv Θ2 ->
  exists ρx ρn Ξ2 P3',
    {{ Θ2 ⊢ₛ P3 ≼[ m ] Q3 ⤳ Ξ2 ⨾ P3' }}a
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ uniq Ξ2 /\ dom Ξ2 ∩ L [=] empty
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1
          /\ b `notin` ftvar_in_aenv Θ2 ∪ L)
    /\ rel_pskl (ρx ++ ρn ++ ρ) V P1' P3'.
Proof.
  intros Θ1 m P1 Q1 Ξ1 P1' HD.
  induction HD; intros Θ2 L P3 Q3 ρ V HrelP HrelQ Hagr Hscp1 Hscp2.
  - (* SS-Var *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_atom ρ V α ?b |- _ => rename Ha into Hat; rename b into β0
    end.
    exists nil, nil, nil, (pskl_var_f β0).
    split; [ apply a_solve_sub__var | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    simpl. constructor. exact Hat.
  - (* SS-ForallL: the subject opens; openers PAIR; the yield re-closes *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa |- _ =>
        rename Ha into HrP0; rename xa into P3b
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh (ftvar_in_aenv Θ2 ∪ ftvar_in_pskl P3b
                          ∪ ftvar_in_pskl Q3 ∪ L)) as [β2 Hβ2].
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    pose proof (dom_subset_ftvar_in_aenv Θ2) as Hds2.
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 Hscp2 Hds2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2))
      by (simpl; clear - Hscp2; fsetdec).
    destruct (IHHD ((β2 ~ abind_tvar) ++ Θ2) L
                (open_pskl_wrt_pskl P3b (pskl_var_f β2)) Q3
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_open_pair; exact HrP0)
                ltac:(apply rel_pskl_extend_pair; exact HrelQ)
                Hagr' Hscp1' Hscp2')
      as (ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hρx & Hrel').
    assert (Hd1p : dom Ξ ∩ ftvar_in_aenv ((β ~ abind_tvar) ++ Θ) [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ HD)).
    assert (Hd2p : dom Ξ2 ∩ ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2)
                     [=] empty)
      by (exact ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ D2p)).
    pose proof (dom_flex_pairs_l ρn) as Hdfl. rewrite <- E1 in Hdfl.
    pose proof (dom_flex_pairs_r ρn) as Hdfr. rewrite <- E2 in Hdfr.
    assert (Hβcl : β `notin` cols_l ρx).
    { apply cols_l_fresh. intros a b Hin.
      destruct (Hρx a b Hin) as [Ha _]. simpl in Ha.
      intros ->. clear - Ha. fsetdec. }
    assert (Hβ2cr : β2 `notin` cols_r ρx).
    { apply cols_r_fresh. intros a b Hin.
      destruct (Hρx a b Hin) as [_ Hb]. simpl in Hb.
      intros ->. clear - Hb. fsetdec. }
    exists ρx, ρn, Ξ2, (pskl_all_syn (close_pskl_wrt_pskl β2 Y2)).
    split.
    { apply a_solve_sub__forall_l with (β := β2);
        [ clear - Hβ2; fsetdec | exact D2p ]. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      simpl in Ha, Hb. split; [ clear - Ha; fsetdec | clear - Hb; fsetdec ]. }
    constructor.
    apply rel_pskl_close_pair.
    + rel_perm Hrel'.
    + clear - Hβ1 Hscp1. fsetdec.
    + rewrite ! cols_l_app. simpl in Hd1p.
      clear - Hβ1 Hscp1 Hd1p Hdfl Hβcl. fsetdec.
    + clear - Hβ2 Hscp2. fsetdec.
    + rewrite ! cols_r_app. simpl in Hd2p.
      clear - Hβ2 Hscp2 Hd2p Hdfr Hβ2cr. fsetdec.
  - (* SS-UnivGhostL: the subject strips its ⫯; the yield re-wraps *)
    inversion HrelP; subst.
    match goal with
    | Ha : rel_pskl ρ V P ?xa |- _ =>
        rename Ha into HrP0; rename xa into P3b
    end.
    destruct (IHHD Θ2 L P3b Q3 ρ V HrP0 HrelQ Hagr Hscp1 Hscp2)
      as (ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hρx & Hrel').
    exists ρx, ρn, Ξ2, (pskl_tophole Y2).
    split; [ apply a_solve_sub__univ_ghost_l; exact D2p | ].
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    split; [ exact Hρx | ].
    constructor. exact Hrel'.
  - (* SS-Vacuous *)
    inversion HrelQ; subst.
    exists nil, nil, nil, P3.
    split; [ apply a_solve_sub__vacuous | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    simpl. exact HrelP.
  - (* SS-Check: drops into the finished eq transport *)
    match goal with
    | He : a_solve_eq _ _ _ _ _ |- _ => rename He into HDeq0
    end.
    destruct (a_solve_eq_rel HDeq0 L HrelP HrelQ Hagr Hscp1 Hscp2)
      as (ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hrel').
    exists nil, ρn, Ξ2, Y2.
    split.
    { apply a_solve_sub__check.
      - eapply rel_pskl_ghost_free; [ exact HrelQ | assumption ].
      - eapply rel_pskl_guarded; [ exact HrelP | assumption ].
      - eapply rel_pskl_guarded; [ exact HrelQ | assumption ].
      - exact D2p. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    split; [ intros a b Hin; inversion Hin | ].
    simpl. exact Hrel'.
  - (* SS-ForallR: the TARGET opens; the pair LEAKS into ρx *)
    inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V B ?xa |- _ =>
        rename Ha into HrB0; rename xa into B3
    end.
    match goal with
    | Hf : β `notin` union _ _ |- _ => rename Hf into Hβ1
    end.
    destruct (atom_fresh (ftvar_in_aenv Θ2 ∪ ftvar_in_pskl P3
                          ∪ ftvar_in_pskl B3 ∪ L)) as [β2 Hβ2].
    pose proof (dom_subset_ftvar_in_aenv Θ) as Hds1.
    pose proof (dom_subset_ftvar_in_aenv Θ2) as Hds2.
    assert (Hagr' : flex_agree_rel ((β, β2) :: ρ) V
                      ((β ~ abind_tvar) ++ Θ) ((β2 ~ abind_tvar) ++ Θ2)).
    { apply flex_agree_rel_push_tvar_pair; [ exact Hagr | | ].
      - clear - Hβ1 Hscp1 Hds1. fsetdec.
      - clear - Hβ2 Hscp2 Hds2. fsetdec. }
    assert (Hscp1' : V ∪ cols_l ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β ~ abind_tvar) ++ Θ))
      by (simpl; clear - Hscp1; fsetdec).
    assert (Hscp2' : V ∪ cols_r ((β, β2) :: ρ)
                       [<=] ftvar_in_aenv ((β2 ~ abind_tvar) ++ Θ2))
      by (simpl; clear - Hscp2; fsetdec).
    destruct (IHHD ((β2 ~ abind_tvar) ++ Θ2) L
                P3 (open_pskl_wrt_pskl B3 (pskl_var_f β2))
                ((β, β2) :: ρ) V
                ltac:(apply rel_pskl_extend_pair; exact HrelP)
                ltac:(apply rel_pskl_open_pair; exact HrB0)
                Hagr' Hscp1' Hscp2')
      as (ρx & ρn & Ξ2 & Y2 & D2p & E1 & E2 & Hu & HL & Hρx & Hrel').
    exists (ρx ++ (β, β2) :: nil), ρn, Ξ2, Y2.
    split.
    { apply a_solve_sub__forall_r with (β := β2).
      - eapply rel_pskl_ghost_free; [ exact HrelQ | assumption ].
      - clear - Hβ2; fsetdec.
      - exact D2p. }
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    split.
    { intros a b Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      - destruct (Hρx a b Hin) as [Ha Hb]. simpl in Ha, Hb.
        split; [ clear - Ha; fsetdec | clear - Hb; fsetdec ].
      - destruct Hin as [E | Hin]; [ inversion E; subst | inversion Hin ].
        split; [ clear - Hβ1; fsetdec | clear - Hβ2; fsetdec ]. }
    rel_perm Hrel'.
  - (* SS-Arrow: the eq half feeds the threaded sub half *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Ha : rel_pskl ρ V P1 ?xa, Hb : rel_pskl ρ V P2 ?xb,
      Hc : rel_pskl ρ V Q1 ?xc, Hd : rel_pskl ρ V Q2 ?xd |- _ =>
        rename Ha into HrPa; rename Hb into HrPb;
        rename Hc into HrQa; rename Hd into HrQb;
        rename xa into P3a; rename xb into P3b;
        rename xc into Q3a; rename xd into Q3b
    end.
    match goal with
    | He : a_solve_eq Θ P1 Q1 ?x ?y |- _ => rename He into HDeq
    end.
    destruct (a_solve_eq_rel HDeq L HrPa HrQa Hagr Hscp1 Hscp2)
      as (ρnA & Ξ2a & P2a' & D2a & E1a & E2a & Hua & HLa & HrelA').
    assert (Hd1a : dom Ξ1 ∩ ftvar_in_aenv Θ [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HDeq)).
    assert (Hd2a : dom Ξ2a ∩ ftvar_in_aenv Θ2 [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ D2a)).
    pose proof (dom_flex_pairs_l ρnA) as Hdfl. rewrite <- E1a in Hdfl.
    pose proof (dom_flex_pairs_r ρnA) as Hdfr. rewrite <- E2a in Hdfr.
    assert (Hagr' : flex_agree_rel (ρnA ++ ρ) V (Ξ1 ++ Θ) (Ξ2a ++ Θ2)).
    { rewrite E1a, E2a. apply flex_agree_rel_push_pairs.
      - exact Hagr.
      - clear - Hd1a Hscp1 Hdfl. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V ∪ cols_l (ρnA ++ ρ)
                       [<=] ftvar_in_aenv (Ξ1 ++ Θ)).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      clear - Hscp1 Hdfl Hds. fsetdec. }
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ)
                       [<=] ftvar_in_aenv (Ξ2a ++ Θ2)).
    { rewrite cols_r_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ2a) as Hds.
      clear - Hscp2 Hdfr Hds. fsetdec. }
    destruct (IHHD (Ξ2a ++ Θ2) (L ∪ dom Ξ2a) P3b Q3b (ρnA ++ ρ) V
                ltac:(apply rel_pskl_widen; exact HrPb)
                ltac:(apply rel_pskl_widen; exact HrQb)
                Hagr' Hscp1' Hscp2')
      as (ρx & ρnB & Ξ2b & P2b' & D2b & E1b & E2b & Hub & HLb & Hρx & HrelB').
    exists ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a), (pskl_arrow P2a' P2b').
    split; [ apply a_solve_sub__arrow; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { apply uniq_app_4; [ exact Hub | exact Hua | ].
      unfold disjoint. clear - HLb. fsetdec. }
    split; [ rewrite dom_app; clear - HLa HLb; fsetdec | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha, Hb.
      split; [ clear - Ha; fsetdec | clear - Hb; fsetdec ]. }
    constructor.
    + rel_perm HrelA'.
    + rel_perm HrelB'.
  - (* SS-GhostLF: a ghost subject against an arrow target *)
    inversion HrelP; subst. inversion HrelQ; subst.
    match goal with
    | Hc : rel_pskl ρ V Q1 ?xc, Hd : rel_pskl ρ V Q2 ?xd |- _ =>
        rename Hc into HrQa; rename Hd into HrQb;
        rename xc into Q3a; rename xd into Q3b
    end.
    match goal with
    | He : a_solve_eq Θ pskl_hole Q1 ?x ?y |- _ => rename He into HDeq
    end.
    destruct (a_solve_eq_rel HDeq L
                (rel_pskl__hole ρ V) HrQa Hagr Hscp1 Hscp2)
      as (ρnA & Ξ2a & P2a' & D2a & E1a & E2a & Hua & HLa & HrelA').
    assert (Hd1a : dom Ξ1 ∩ ftvar_in_aenv Θ [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HDeq)).
    assert (Hd2a : dom Ξ2a ∩ ftvar_in_aenv Θ2 [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ D2a)).
    pose proof (dom_flex_pairs_l ρnA) as Hdfl. rewrite <- E1a in Hdfl.
    pose proof (dom_flex_pairs_r ρnA) as Hdfr. rewrite <- E2a in Hdfr.
    assert (Hagr' : flex_agree_rel (ρnA ++ ρ) V (Ξ1 ++ Θ) (Ξ2a ++ Θ2)).
    { rewrite E1a, E2a. apply flex_agree_rel_push_pairs.
      - exact Hagr.
      - clear - Hd1a Hscp1 Hdfl. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V ∪ cols_l (ρnA ++ ρ)
                       [<=] ftvar_in_aenv (Ξ1 ++ Θ)).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      clear - Hscp1 Hdfl Hds. fsetdec. }
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ)
                       [<=] ftvar_in_aenv (Ξ2a ++ Θ2)).
    { rewrite cols_r_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ2a) as Hds.
      clear - Hscp2 Hdfr Hds. fsetdec. }
    destruct (IHHD (Ξ2a ++ Θ2) (L ∪ dom Ξ2a) pskl_hole Q3b (ρnA ++ ρ) V
                (rel_pskl__hole (ρnA ++ ρ) V)
                ltac:(apply rel_pskl_widen; exact HrQb)
                Hagr' Hscp1' Hscp2')
      as (ρx & ρnB & Ξ2b & P2b' & D2b & E1b & E2b & Hub & HLb & Hρx & HrelB').
    exists ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a),
      (pskl_tophole (pskl_arrow P2a' P2b')).
    split; [ apply a_solve_sub__ghost_l_fn; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { apply uniq_app_4; [ exact Hub | exact Hua | ].
      unfold disjoint. clear - HLb. fsetdec. }
    split; [ rewrite dom_app; clear - HLa HLb; fsetdec | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha, Hb.
      split; [ clear - Ha; fsetdec | clear - Hb; fsetdec ]. }
    constructor. constructor.
    + rel_perm HrelA'.
    + rel_perm HrelB'.
  - (* SS-GhostL: no premise; the target passes as the pattern *)
    inversion HrelP; subst.
    exists nil, nil, nil, (pskl_tophole Q3).
    split.
    { apply a_solve_sub__ghost_l.
      - eapply rel_pskl_ghost_free; [ exact HrelQ | assumption ].
      - eapply rel_pskl_guarded; [ exact HrelQ | assumption ]. }
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    simpl. constructor. exact HrelQ.
Qed.

(* ===================================================================== *)
(*  §6  Transport 4 — the constraint fold along the rel                   *)
(* ===================================================================== *)

(** Pointwise rel on constraints.  ⚠️ This serves the FOLD TRANSPORT only
    (the hygienic-rederivation consumer, where the two collections are
    same-rule and hence aligned); the b-core pair induction must NOT be
    stated through it (§8c.9: the two looks' collections may differ in
    LENGTH — ◇-emission slack — so the fused motive is the design). *)
Inductive rel_a_cstr (ρ : list (atom * atom)) (V : atoms)
    : a_cstr -> a_cstr -> Prop :=
| rel_a_cstr__sub : forall m Q1 Q2,
    rel_pskl ρ V Q1 Q2 ->
    rel_a_cstr ρ V (a_cstr_sub m Q1) (a_cstr_sub m Q2)
| rel_a_cstr__eq : forall Q1 Q2,
    rel_pskl ρ V Q1 Q2 ->
    rel_a_cstr ρ V (a_cstr_eq Q1) (a_cstr_eq Q2).

Definition rel_a_cstrs (ρ : list (atom * atom)) (V : atoms)
    : a_cstrs -> a_cstrs -> Prop :=
  List.Forall2 (rel_a_cstr ρ V).

Lemma rel_a_cstr_widen : forall ρn ρ V c1 c2,
  rel_a_cstr ρ V c1 c2 -> rel_a_cstr (ρn ++ ρ) V c1 c2.
Proof.
  intros * H; inversion H; subst; constructor;
    apply rel_pskl_widen; assumption.
Qed.

Lemma rel_a_cstrs_widen : forall ρn ρ V C1 C2,
  rel_a_cstrs ρ V C1 C2 -> rel_a_cstrs (ρn ++ ρ) V C1 C2.
Proof.
  intros * H; induction H; constructor;
    eauto using rel_a_cstr_widen.
Qed.

(** ⭐ TRANSPORT 4 — the fold: eq-cons via transport 2 + the IH at the
    extended contexts, the terminal sub singleton via transport 3. *)
Lemma a_solve_cstr_rel : forall Θ1 C1 P1 Ξ1 P1',
  {{ Θ1 ⊩ C1 ⨾ P1 ⤳ Ξ1 ⨾ P1' }}a ->
  forall (L : atoms) Θ2 C2 P3 ρ V,
  rel_pskl ρ V P1 P3 ->
  rel_a_cstrs ρ V C1 C2 ->
  flex_agree_rel ρ V Θ1 Θ2 ->
  V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1 ->
  V ∪ cols_r ρ [<=] ftvar_in_aenv Θ2 ->
  exists ρx ρn Ξ2 P3',
    {{ Θ2 ⊩ C2 ⨾ P3 ⤳ Ξ2 ⨾ P3' }}a
    /\ Ξ1 = flex_pairs_l ρn /\ Ξ2 = flex_pairs_r ρn
    /\ uniq Ξ2 /\ dom Ξ2 ∩ L [=] empty
    /\ (forall a b, In (a, b) ρx ->
          a `notin` ftvar_in_aenv Θ1 /\ b `notin` ftvar_in_aenv Θ2 ∪ L)
    /\ rel_pskl (ρx ++ ρn ++ ρ) V P1' P3'.
Proof.
  intros Θ1 C1 P1 Ξ1 P1' HD.
  induction HD; intros L Θ2 C2 P3 ρ V HrelP HrelC Hagr Hscp1 Hscp2.
  - (* SC-Empty *)
    inversion HrelC; subst.
    exists nil, nil, nil, P3.
    split; [ apply a_solve_cstr__empty | ].
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ solve_uniq | ]. split; [ simpl; clear; fsetdec | ].
    split; [ intros a b Hin; inversion Hin | ].
    simpl. exact HrelP.
  - (* SC-Sub: the terminal singleton, transport 3 *)
    inversion HrelC; subst.
    match goal with
    | Hc : rel_a_cstr ρ V (a_cstr_sub m Q) ?y,
      Ht : Forall2 _ nil ?l |- _ =>
        inversion Hc; subst; inversion Ht; subst
    end.
    match goal with
    | Hq : rel_pskl ρ V Q ?x |- _ => rename Hq into HrelQ; rename x into Q2c
    end.
    match goal with
    | Hs : a_solve_sub _ _ _ _ _ _ |- _ => rename Hs into HDsub
    end.
    destruct (a_solve_sub_rel HDsub L HrelP HrelQ Hagr Hscp1 Hscp2)
      as (ρx & ρn & Ξ2 & Y2 & D2s & E1 & E2 & Hu & HL & Hρx & Hrel').
    exists ρx, ρn, Ξ2, Y2.
    split; [ apply a_solve_cstr__sub; exact D2s | ].
    split; [ exact E1 | ]. split; [ exact E2 | ].
    split; [ exact Hu | ]. split; [ exact HL | ].
    split; [ exact Hρx | ].
    exact Hrel'.
  - (* SC-Eq: head via transport 2, tail via the IH at the grown state *)
    inversion HrelC; subst.
    match goal with
    | Hc : rel_a_cstr ρ V (a_cstr_eq Q) ?y |- _ =>
        inversion Hc; subst
    end.
    match goal with
    | Hq : rel_pskl ρ V Q ?x, Ht : Forall2 _ C ?l |- _ =>
        rename Hq into HrelQ; rename x into Q2c;
        rename Ht into HrelC'; rename l into C2'
    end.
    match goal with
    | He : a_solve_eq _ _ _ _ _ |- _ => rename He into HDeq
    end.
    destruct (a_solve_eq_rel HDeq L HrelP HrelQ Hagr Hscp1 Hscp2)
      as (ρnA & Ξ2a & Pmid2 & D2a & E1a & E2a & Hua & HLa & HrelM).
    assert (Hd1a : dom Ξ1 ∩ ftvar_in_aenv Θ [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ HDeq)).
    assert (Hd2a : dom Ξ2a ∩ ftvar_in_aenv Θ2 [=] empty)
      by (exact ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ D2a)).
    pose proof (dom_flex_pairs_l ρnA) as Hdfl. rewrite <- E1a in Hdfl.
    pose proof (dom_flex_pairs_r ρnA) as Hdfr. rewrite <- E2a in Hdfr.
    assert (Hagr' : flex_agree_rel (ρnA ++ ρ) V (Ξ1 ++ Θ) (Ξ2a ++ Θ2)).
    { rewrite E1a, E2a. apply flex_agree_rel_push_pairs.
      - exact Hagr.
      - clear - Hd1a Hscp1 Hdfl. fsetdec.
      - clear - Hd2a Hscp2 Hdfr. fsetdec. }
    assert (Hscp1' : V ∪ cols_l (ρnA ++ ρ)
                       [<=] ftvar_in_aenv (Ξ1 ++ Θ)).
    { rewrite cols_l_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ1) as Hds.
      clear - Hscp1 Hdfl Hds. fsetdec. }
    assert (Hscp2' : V ∪ cols_r (ρnA ++ ρ)
                       [<=] ftvar_in_aenv (Ξ2a ++ Θ2)).
    { rewrite cols_r_app. rewrite ftvar_in_aenv_app.
      pose proof (dom_subset_ftvar_in_aenv Ξ2a) as Hds.
      clear - Hscp2 Hdfr Hds. fsetdec. }
    destruct (IHHD (L ∪ dom Ξ2a) (Ξ2a ++ Θ2) C2' Pmid2 (ρnA ++ ρ) V
                HrelM
                ltac:(apply rel_a_cstrs_widen; exact HrelC')
                Hagr' Hscp1' Hscp2')
      as (ρx & ρnB & Ξ2b & P3' & D2b & E1b & E2b & Hub & HLb & Hρx & HrelB').
    exists ρx, (ρnB ++ ρnA), (Ξ2b ++ Ξ2a), P3'.
    split; [ eapply a_solve_cstr__eq; [ exact D2a | exact D2b ] | ].
    split;
      [ rewrite flex_pairs_l_app; rewrite <- E1a, <- E1b; reflexivity | ].
    split;
      [ rewrite flex_pairs_r_app; rewrite <- E2a, <- E2b; reflexivity | ].
    split.
    { apply uniq_app_4; [ exact Hub | exact Hua | ].
      unfold disjoint. clear - HLb. fsetdec. }
    split; [ rewrite dom_app; clear - HLa HLb; fsetdec | ].
    split.
    { intros a b Hin. destruct (Hρx a b Hin) as [Ha Hb].
      rewrite ftvar_in_aenv_app in Ha, Hb.
      split; [ clear - Ha; fsetdec | clear - Hb; fsetdec ]. }
    rel_perm HrelB'.
Qed.
