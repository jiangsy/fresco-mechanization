(** ⚠️ DO NOT MERGE THIS INTO [prop_inc.v].  It shares that file's topic but
    NOT its layer: this one needs [prop_flex], [prop_compose] and
    [prop_normal], and all three import [prop_inc] — so folding it back is an
    import CYCLE, not a tidy-up.  Checked 2026-08-09 during the file-reorg
    pass; the [_strengthen] suffix marks the layer, not a size accident. *)

(** Increment strengthening / mid-strip infrastructure for the OPTIMALITY
    walk cases (algo/prop_consis_complete.v, Blocker-2).

    The assign walk sandwiches the skipped binding as [Ξ ++ [β] ++ Θ0]
    (unlike Flex-Flex-Skip's clean head-flex).  [a_inc_peel_suffix] only peels
    an all-flex suffix; here we need to peel the suffix AND the mid flex binding
    together, then RE-INSERT the suffix over the smaller tail — producing the
    sub-node's competing increment [κ1 ++ κ2 ∷ (Ξ ++ Θ0) ⊑ Θ].

    The suffix here is [a_decls Ξ] (every entry an UNDEFINED flexible), the
    algorithm's own invariant on the pending suffix (full-algo-spec.tex:1508).
    That is what keeps the re-insertion clean: with no [flex_mono_def] entry in
    Ξ there is no definition whose image depends on the dropped [β], so the
    reconstructed increment's premises transport unchanged.  (With a general
    [a_suffix] Ξ a def entry [a ≔ τd] could have [β ∈ ftv τd], and dropping
    β's metasubst entry would change [msubst τd] — the flex_def premise
    [τa' ≡ᵗ msubst (κ1++κ2) τd] would then be false.) *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_normal.

Set Implicit Arguments.

(** MID-STRIP of a flexible binding sandwiched under an [a_decls] suffix.
    Peels the suffix Ξ and the mid flex [β] off a competing increment
    [κ ∷ (Ξ ++ β̂ ++ Θ0) ⊑ Θ], returning
      - the split [κ = κ1 ++ (β,τ) :: κ2] (κ1 = the Ξ-part, dom κ1 = dom Ξ),
      - the tail increment [κ2 ∷ Θ0 ⊑ Θ], and
      - the RE-INSERTED increment [κ1 ++ κ2 ∷ (Ξ ++ Θ0) ⊑ Θ] with β dropped.
    The target [Θ] is UNCHANGED (flex/suffix entries do not extend it). *)
Lemma a_inc_mid_strip_flex : forall Ξ β Θ0 κ Θ,
  a_decls Ξ ->
  κ ∷ (Ξ ++ (β ~ abind_flex_mono) ++ Θ0) ⊑ Θ ->
  exists κ1 τ κ2,
    κ = κ1 ++ (β, τ) :: κ2 /\
    dom κ1 [=] dom Ξ /\
    κ2 ∷ Θ0 ⊑ Θ /\
    κ1 ++ κ2 ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros β Θ0 κ Θ Hdec Hinc.
  - (* Ξ = nil : head is the mid flex β itself *)
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqκ] Heqt
                      | | | | ]; subst.
    exists (@nil (atom * ptyp)), τ, κs. simpl.
    split; [ reflexivity | ].
    split; [ clear; fsetdec | ].
    split; [ exact Hinc' | exact Hinc' ].
  - (* Ξ = (a ~ flex) ++ Ξ' : peel the head flex a, recurse *)
    inversion Hdec as [ | α1 Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs κs Θt as' τ Hinc' Hwfτ Hmτ [Heqa Heqκ] Heqt
                      | | | | ]; subst.
    destruct (IH _ _ _ _ Hdec' Hinc')
      as [κ1 [τ2 [κ2 [Heqκ [Hdom [Hinc2 Hrec]]]]]].
    exists ((a, τ) :: κ1), τ2, κ2. simpl.
    split; [ rewrite Heqκ; reflexivity | ].
    split; [ clear - Hdom; simpl_env; fsetdec | ].
    split; [ exact Hinc2 | ].
    apply a_inc__flex; auto.
Qed.

(* ===================================================================== *)
(*  FLEX-KIND PRESERVATION over the algorithm.                             *)
(*                                                                        *)
(*  The algorithm never rigidifies a flexible variable: every [a_assign]/  *)
(*  [a_unify]/[a_consis] step maps a flexible (defined or not) of its      *)
(*  source to a flexible of its target.  NOT derivable from soundness's    *)
(*  [⊴] alone — [a_inc__flex]'s image [α̂ ↦ α] only forces [α] to be SOME   *)
(*  tvar in the target, and the relation tolerates a rigid one.  Needed by  *)
(*  the optimality walk cases: the ζ-override must know that a Θ0-flexible  *)
(*  free in a walked-past term binding still has a ζ-entry (i.e. is still   *)
(*  flexible in the algorithm's output).                                    *)
(* ===================================================================== *)

(** [a_flex_tvar], packaged through the flex-kind predicate
    [a_suffix_binding] (exactly the two flexible binding forms). *)
Lemma a_flex_tvar_alt : forall Θ α1,
  a_flex_tvar Θ α1 <-> exists b, a_suffix_binding b /\ binds α1 b Θ.
Proof.
  intros Θ α1; split.
  - intros [Hb | [τ Hb]];
      [ exists abind_flex_mono | exists (abind_flex_mono_def τ) ];
      split; solve [ constructor | exact Hb ].
  - intros [b [Hs Hb]]; inversion Hs; subst;
      [ left; exact Hb | right; eexists; exact Hb ].
Qed.

(** Split a binding at an explicit middle entry. *)
Lemma binds_split_mid : forall α1 (b : abind) (a : atom) (bm : abind) Ξ Θ,
  binds α1 b (Ξ ++ (a ~ bm) ++ Θ) ->
  binds α1 b (Ξ ++ Θ) \/ (α1 = a /\ b = bm).
Proof.
  intros * Hb. unfold binds in *. apply in_app_or in Hb.
  destruct Hb as [H | [H | H]];
    [ left; apply in_or_app; auto
    | right; inversion H; auto
    | left; apply in_or_app; auto ].
Qed.

Lemma a_assign_unify_consis_flex_preserve :
  (forall Θ0 Ξ α P Θ1,
     {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
     forall α1, a_flex_tvar (Ξ ++ Θ0) α1 -> a_flex_tvar Θ1 α1) /\
  (forall Θ0 α β Θ1,
     {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
     forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1) /\
  (forall Δ1 Δ2 Θ0 P0 P P' Θ1,
     {{ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ P' ⊣ Θ1 }}a ->
     forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun Θ0 Ξ α P Θ1 _ =>
              forall α1, a_flex_tvar (Ξ ++ Θ0) α1 -> a_flex_tvar Θ1 α1)
           (fun Θ0 α β Θ1 _ =>
              forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1)
           (fun Δ1 Δ2 Θ0 P0 P P' Θ1 _ =>
              forall α1, a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1)).
  (* ---------- a_assign ---------- *)
  - (* univ_ghost_id : identity *)
    intros Θ0 α α1 Hα1. simpl_env in Hα1. exact Hα1.
  - (* solve_m : Ξ ++ (α̂) ++ Θ0  →  (α̂≔τ) ++ β̄ ++ Ξ ++ Θ0 *)
    intros Θ0 Ξ α P βs τ Hαn Hg Hm Hu Hfr α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]].
    + apply a_flex_tvar_alt; exists b; split; [ exact Hs | ].
      unfold binds in *. simpl. right.
      apply in_or_app; right. apply in_or_app. apply in_app_or in Hb. exact Hb.
    + subst. right; exists τ. unfold binds; left; reflexivity.
  - (* assign : Ξ ++ (β̂≔τ) ++ Θ0  →  (β̂≔τ) ++ Θ1, premise Ξ ++ Θ0 → Θ1 *)
    intros Θ0 Θ1 Ξ α β τ P P' Hfα Hβd Hc IH α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]].
    + assert (Hγ' : a_flex_tvar Θ1 α1)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb'.
    + subst. right; exists τ. unfold binds; left; reflexivity.
  - (* depend : reassociate *)
    intros Θ0 Θ1 Ξ α β P Hne Hβ Ha IH α1 Hα1.
    apply IH. simpl_env in *. exact Hα1.
  - (* skip : Ξ ++ (β̂) ++ Θ0  →  (β̂) ++ Θ1 *)
    intros Θ0 Θ1 Ξ α β P Hne Hβn Hβd Ha IH α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]].
    + assert (Hγ' : a_flex_tvar Θ1 α1)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb'.
    + subst. left. unfold binds; left; reflexivity.
  - (* skip_rigid : mid is rigid, kind mismatch *)
    intros Θ0 Θ1 Ξ α β P Hβn Hβd Ha IH α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]];
      [ | subst; inversion Hs ].
    assert (Hγ' : a_flex_tvar Θ1 α1)
      by (apply IH; apply a_flex_tvar_alt; eauto).
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
    apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
    unfold binds in *; simpl; right; exact Hb'.
  - (* skip_tm_var *)
    intros Θ0 Θ1 Ξ α x P' P Hxd Ha IH α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]];
      [ | subst; inversion Hs ].
    assert (Hγ' : a_flex_tvar Θ1 α1)
      by (apply IH; apply a_flex_tvar_alt; eauto).
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
    apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
    unfold binds in *; simpl; right; exact Hb'.
  - (* skip_tm_skl *)
    intros Θ0 Θ1 Ξ α x P' P Hxd Ha IH α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]];
      [ | subst; inversion Hs ].
    assert (Hγ' : a_flex_tvar Θ1 α1)
      by (apply IH; apply a_flex_tvar_alt; eauto).
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
    apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
    unfold binds in *; simpl; right; exact Hb'.
  (* ---------- a_unify ---------- *)
  - (* flex_id : identity *)
    intros Θ0 α Hfα α1 Hα1. exact Hα1.
  - (* flex_l : (α̂) ++ Θ0 → (α̂≔β) ++ Θ0 *)
    intros Θ0 α β Hne Hfβ α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'].
    + subst. right; eexists. unfold binds; left; reflexivity.
    + apply a_flex_tvar_alt; exists b; split; [ exact Hs | ].
      unfold binds in *; simpl; right; exact Hb'.
  - (* flex_r : symmetric *)
    intros Θ0 α β Hne Hfα α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'].
    + subst. right; eexists. unfold binds; left; reflexivity.
    + apply a_flex_tvar_alt; exists b; split; [ exact Hs | ].
      unfold binds in *; simpl; right; exact Hb'.
  - (* flex_assign : (α1̂≔τ) ++ Θ0 → (α1̂≔τ) ++ Θ1, consis premise Θ0 → Θ1 *)
    intros Θ0 Θ1 α10 τ α β P' Hfα Hfβ Hα1d Hc IH α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'].
    + subst. right; eexists. unfold binds; left; reflexivity.
    + assert (Hγ' : a_flex_tvar Θ1 α1)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb'']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb''.
  - (* flex_skip : (α1̂) ++ Θ0 → (α1̂) ++ Θ1 *)
    intros Θ0 Θ1 α10 α β Hα1α Hα1β Hα1d Hu IH α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'].
    + subst. left. unfold binds; left; reflexivity.
    + assert (Hγ' : a_flex_tvar Θ1 α1)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb'']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb''.
  - (* skip_other : (c~b) ++ Θ0 → (c~b) ++ Θ1, b non-flex *)
    intros Θ0 Θ1 c b α β Hbshape Hcd Hu IH α1 Hα1.
    apply a_flex_tvar_alt in Hα1; destruct Hα1 as [b0 [Hs Hb0]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb0) as [[Heqγ Heqb] | Hb'].
    + subst. exfalso.
      destruct Hbshape as [Hb1 | [[Q1 Hb1] | [Q1 Hb1]]]; subst; inversion Hs.
    + assert (Hγ' : a_flex_tvar Θ1 α1)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb'']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb''.
  (* ---------- a_consis ---------- *)
  - (* ghost : identity *) intros; auto.
  - (* unit : identity *) intros; auto.
  - (* rigid : identity *) intros; auto.
  - (* arrow : compose the two IHs *)
    intros Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2 α1 Hα1.
    apply IH2, IH1, Hα1.
  - (* forall_inh : cofinite, rigid head both sides *)
    (* cluster 4: the premise is a single instance at the rule's own
       binder, so there is no representative to pick *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hco IH α1 Hα1.
    assert (Hγ' : a_flex_tvar ((α ~ abind_tvar) ++ Θ1) α1).
    { apply IH. apply a_flex_tvar_weaken_prefix. exact Hα1. }
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'];
      [ subst; inversion Hs | ].
    apply a_flex_tvar_alt; eauto.
  - (* forall_syn : cofinite *)
    (* cluster 4: the premise is a single instance at the rule's own
       binder, so there is no representative to pick *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hco IH α1 Hα1.
    assert (Hγ' : a_flex_tvar ((α ~ abind_tvar) ++ Θ1) α1).
    { apply IH. apply a_flex_tvar_weaken_prefix. exact Hα1. }
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'];
      [ subst; inversion Hs | ].
    apply a_flex_tvar_alt; eauto.
  - (* univ_ghost : direct IH *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hc IH α1 Hα1. apply IH, Hα1.
  - (* univ_ghost1 : cofinite *)
    (* cluster 4: the premise is a single instance at the rule's own
       binder, so there is no representative to pick *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' α Hfr Hco IH α1 Hα1.
    assert (Hγ' : a_flex_tvar ((α ~ abind_tvar) ++ Θ1) α1).
    { apply IH. apply a_flex_tvar_weaken_prefix. exact Hα1. }
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'];
      [ subst; inversion Hs | ].
    apply a_flex_tvar_alt; eauto.
  - (* univ_ghost2 : direct IH *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH α1 Hα1. apply IH, Hα1.
  - (* flex : unify IH *)
    intros Δ1 Δ2 Θ0 Θ1 α β Hu IH α1 Hα1. apply IH, Hα1.
  - (* flex_l : assign IH at Ξ = nil *)
    intros Δ1 Δ2 Θ0 Θ1 α P0 Hnf Ha IH α1 Hα1. apply IH. simpl_env. exact Hα1.
  - (* flex_r : assign IH at Ξ = nil *)
    intros Δ1 Δ2 Θ0 Θ1 α P Hnf Ha IH α1 Hα1. apply IH. simpl_env. exact Hα1.
  - (* ghost_r : identity *) intros; auto.
  - (* univ_ghost_r : direct IH *)
    intros Δ1 Δ2 Θ0 Θ1 P0 P P' Hg Hnf Hc IH α1 Hα1. apply IH, Hα1.
Qed.

(** Packaged corollaries. *)
Corollary a_unify_flex_preserve : forall Θ0 α β Θ1 α1,
  {{ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}a ->
  a_flex_tvar Θ0 α1 -> a_flex_tvar Θ1 α1.
Proof.
  intros * Hu Hα1.
  exact (proj1 (proj2 a_assign_unify_consis_flex_preserve) _ _ _ _ Hu α1 Hα1).
Qed.

Corollary a_assign_flex_preserve : forall Θ0 Ξ α P Θ1 α1,
  {{ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}a ->
  a_flex_tvar (Ξ ++ Θ0) α1 -> a_flex_tvar Θ1 α1.
Proof.
  intros * Ha Hα1.
  exact (proj1 a_assign_unify_consis_flex_preserve _ _ _ _ _ Ha α1 Hα1).
Qed.

(* ===================================================================== *)
(*  Pointwise inversion of substitution agreement (converse of              *)
(*  [msubst_ptyp_agree] / [msubst_pskl_agree]).                             *)
(* ===================================================================== *)

Lemma msubst_ptyp_agree_inv : forall κ ζ A,
  msubst_ptyp κ A = msubst_ptyp ζ A ->
  forall α', α' `in` ftvar_in_ptyp A ->
  msubst_lookup κ α' = msubst_lookup ζ α'.
Proof.
  intros κ ζ A; induction A; intros Heq α' Hα; simpl in *;
    try solve [ exfalso; clear - Hα; fsetdec ].
  - (* var_f *)
    assert (HXY : α' = α) by (clear - Hα; fsetdec). subst. exact Heq.
  - (* arrow *)
    injection Heq as Heq1 Heq2.
    apply union_1 in Hα; destruct Hα; eauto.
  - (* all *)
    injection Heq as Heq0. eauto.
Qed.

(** [ptyp_to_pskl] is injective (structural embedding). *)
Lemma ptyp_to_pskl_inj : forall A B,
  ptyp_to_pskl A = ptyp_to_pskl B -> A = B.
Proof.
  induction A; destruct B; simpl; intros Heq; try discriminate;
    try reflexivity; injection Heq; intros; f_equal; auto.
Qed.

Lemma msubst_pskl_agree_inv : forall κ ζ P,
  msubst_pskl κ P = msubst_pskl ζ P ->
  forall α', α' `in` ftvar_in_pskl P ->
  msubst_lookup κ α' = msubst_lookup ζ α'.
Proof.
  intros κ ζ P; induction P; intros Heq α' Hα; simpl in *;
    try solve [ exfalso; clear - Hα; fsetdec ].
  - (* var_f *)
    assert (HXY : α' = α) by (clear - Hα; fsetdec). subst.
    apply ptyp_to_pskl_inj. exact Heq.
  - (* arrow *)
    injection Heq as Heq1 Heq2.
    apply union_1 in Hα; destruct Hα; eauto.
  - (* all_syn *)
    injection Heq as Heq0. eauto.
  - (* tophole *)
    injection Heq as Heq0. eauto.
Qed.

(* ===================================================================== *)
(*  ftv of a bound entry lives in the context's domain.                    *)
(* ===================================================================== *)

Lemma a_wf_ptyp_ftv_dom' : forall Θ A,
  a_wf_ptyp Θ A -> ftvar_in_ptyp A [<=] dom Θ.
Proof.
  intros Θ A H α Hα.
  apply (a_wf_ptyp_ftv_tvarish H) in Hα.
  destruct Hα as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

Lemma a_scope_pskl_ftv_dom' : forall Θ P,
  a_scope_pskl Θ P -> ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros Θ P H α Hα.
  apply (a_scope_pskl_ftv_tvarish H) in Hα.
  destruct Hα as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

(** In a wf context, a term binding's payload draws its variables from the
    context's domain.  (Applied at a TAIL context to separate a fresh head.) *)
Lemma a_wf_aenv_binds_var_typ_ftv : forall Θ x A,
  {{ ⊢ Θ }}a -> binds x (abind_var_typ A) Θ ->
  ftvar_in_ptyp A [<=] dom Θ.
Proof.
  intros Θ x A Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    try discriminate;
    try solve [ pose proof (IHHwf Hb') as Hs; simpl; clear - Hs; fsetdec ].
  (* var_typ head : A is wf in the tail *)
  injection Heq2 as Heq2. subst.
  pose proof (a_wf_ptyp_ftv_dom' H0) as Hs. simpl. clear - Hs. fsetdec.
Qed.

(** ⭐ A well-formed context's term entry is DISCIPLINED-well-formed in the
    WHOLE context.  [a_wf_aenv__var] stores it in the entry's TAIL (2026-08-09);
    this weakens that to the full context, which is the form every consumer
    wants.  It is what retired the two
    [binds y (abind_var_skl Ps) Θ -> {{ Θ ⨟ ∅ ⊢ₚₛ Ps }}a] hypotheses from
    [a_pat_complete] / [a_typing_complete] — before the constructor was
    strengthened they were EXTERNAL side conditions (docs/WF-SIDE-CONDITIONS.md),
    and now they are theorems. *)
Lemma a_wf_aenv_binds_var_skl_wf : forall Θ x P,
  {{ ⊢ Θ }}a -> binds x (abind_var_skl P) Θ ->
  {{ Θ ⨟ empty ⊢ₚₛ P }}a.
Proof.
  intros Θ x P Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    try discriminate;
    try solve [ eapply a_wf_pskl_weaken;
                  [ intros ? ? Hb2; apply binds_cons_3; exact Hb2
                  | exact (IHHwf Hb') ] ].
  (* var_skl head : the entry's own stored wf, weakened past the entry *)
  injection Heq2 as Heq2. subst.
  eapply a_wf_pskl_weaken;
    [ intros ? ? Hb2; apply binds_cons_3; exact Hb2 | exact H0 ].
Qed.

Lemma a_wf_aenv_binds_var_skl_ftv : forall Θ x P,
  {{ ⊢ Θ }}a -> binds x (abind_var_skl P) Θ ->
  ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros Θ x P Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    try discriminate;
    try solve [ pose proof (IHHwf Hb') as Hs; simpl; clear - Hs; fsetdec ].
  (* var_skl head : P is wf in the tail *)
  injection Heq2 as Heq2. subst.
  pose proof (a_scope_pskl_ftv_dom' (a_scope_pskl_of_wf H0)) as Hs. simpl. clear - Hs. fsetdec.
Qed.

(* ===================================================================== *)
(*  Term bindings transport along increments (both directions).            *)
(* ===================================================================== *)

Lemma a_suffix_no_var_typ : forall Ξ x A,
  a_suffix Ξ -> binds x (abind_var_typ A) Ξ -> False.
Proof.
  intros Ξ x A Hsuf; induction Hsuf; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    [ subst; inversion H | auto ].
Qed.

Lemma a_suffix_no_var_skl : forall Ξ x P,
  a_suffix Ξ -> binds x (abind_var_skl P) Ξ -> False.
Proof.
  intros Ξ x P Hsuf; induction Hsuf; intros Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    [ subst; inversion H | auto ].
Qed.

(** pskl twin of [msubst_ptyp_cons_notin]. *)
Lemma msubst_pskl_cons_notin : forall α0 τ0 ζ P,
  α0 `notin` ftvar_in_pskl P ->
  msubst_pskl ((α0, τ0) :: ζ) P = msubst_pskl ζ P.
Proof.
  intros α0 τ0 ζ P HP.
  apply msubst_pskl_agree. intros α Hα. simpl.
  destruct (α == α0) as [->|Hne]; [ exfalso; auto | reflexivity ].
Qed.

(* NB the forward/backward SYNTACTIC binding transports that lived here
   (a_inc_binds_var_typ/skl and their _src converses) were deleted with the
   move to GMM-style SEMANTIC entries in [a_inc] (def_meta.v): the target's
   binder payload is now only ≡ᵗ/≡ˢ-related to the substituted source
   payload, and the ζ-override machinery they supported is gone (see
   algo/cex/cex_assign_optimal_syn_middle.v for why it had to go). *)


