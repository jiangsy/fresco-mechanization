(** Increment strengthening / mid-strip infrastructure for the OPTIMALITY
    walk cases (algo/prop_consis_complete.v, Blocker-2).

    The assign walk sandwiches the skipped binding as [Ξ ++ [β] ++ Θ0]
    (unlike Flex-Flex-Skip's clean head-flex).  [a_inc_peel_suffix] only peels
    an all-flex suffix; here we need to peel the suffix AND the mid flex binding
    together, then RE-INSERT the suffix over the smaller tail — producing the
    sub-node's competing increment [ρ1 ++ ρ2 ∷ (Ξ ++ Θ0) ⊑ Θ].

    The suffix here is [a_decls Ξ] (every entry an UNDEFINED flexible), the
    algorithm's own invariant on the pending suffix (full-algo-spec.tex:1508).
    That is what keeps the re-insertion clean: with no [flex_mono_def] entry in
    Ξ there is no definition whose image depends on the dropped [β], so the
    reconstructed increment's premises transport unchanged.  (With a general
    [a_suffix] Ξ a def entry [a ≔ τd] could have [β ∈ ftv τd], and dropping
    β's metasubst entry would change [msubst τd] — the flex_def premise
    [τa' ≡ᵗ msubst (ρ1++ρ2) τd] would then be false.) *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_normal.

Set Implicit Arguments.

(** MID-STRIP of a flexible binding sandwiched under an [a_decls] suffix.
    Peels the suffix Ξ and the mid flex [β] off a competing increment
    [ρ ∷ (Ξ ++ β̂ ++ Θ0) ⊑ Θ], returning
      - the split [ρ = ρ1 ++ (β,τ) :: ρ2] (ρ1 = the Ξ-part, dom ρ1 = dom Ξ),
      - the tail increment [ρ2 ∷ Θ0 ⊑ Θ], and
      - the RE-INSERTED increment [ρ1 ++ ρ2 ∷ (Ξ ++ Θ0) ⊑ Θ] with β dropped.
    The target [Θ] is UNCHANGED (flex/suffix entries do not extend it). *)
Lemma a_inc_mid_strip_flex : forall Ξ β Θ0 ρ Θ,
  a_decls Ξ ->
  ρ ∷ (Ξ ++ (β ~ abind_flex_mono) ++ Θ0) ⊑ Θ ->
  exists ρ1 τ ρ2,
    ρ = ρ1 ++ (β, τ) :: ρ2 /\
    dom ρ1 [=] dom Ξ /\
    ρ2 ∷ Θ0 ⊑ Θ /\
    ρ1 ++ ρ2 ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  induction Ξ as [ | [a b] Ξ' IH ]; intros β Θ0 ρ Θ Hdec Hinc.
  - (* Ξ = nil : head is the mid flex β itself *)
    simpl in Hinc.
    inversion Hinc as [ | Θs ρs Θt βs τ Hinc' Hwfτ Hmτ [Heqβ Heqρ] Heqt
                      | | | | ]; subst.
    exists (@nil (atom * ptyp)), τ, ρs. simpl.
    split; [ reflexivity | ].
    split; [ clear; fsetdec | ].
    split; [ exact Hinc' | exact Hinc' ].
  - (* Ξ = (a ~ flex) ++ Ξ' : peel the head flex a, recurse *)
    inversion Hdec as [ | γ Ξ'' Hdec' [Heqγ HeqΞ] ]; subst.
    simpl in Hinc.
    inversion Hinc as [ | Θs ρs Θt as' τ Hinc' Hwfτ Hmτ [Heqa Heqρ] Heqt
                      | | | | ]; subst.
    destruct (IH _ _ _ _ Hdec' Hinc')
      as [ρ1 [τ2 [ρ2 [Heqρ [Hdom [Hinc2 Hrec]]]]]].
    exists ((a, τ) :: ρ1), τ2, ρ2. simpl.
    split; [ rewrite Heqρ; reflexivity | ].
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
Lemma a_flex_tvar_alt : forall Θ γ,
  a_flex_tvar Θ γ <-> exists b, a_suffix_binding b /\ binds γ b Θ.
Proof.
  intros Θ γ; split.
  - intros [Hb | [τ Hb]];
      [ exists abind_flex_mono | exists (abind_flex_mono_def τ) ];
      split; solve [ constructor | exact Hb ].
  - intros [b [Hs Hb]]; inversion Hs; subst;
      [ left; exact Hb | right; eexists; exact Hb ].
Qed.

(** Split a binding at an explicit middle entry. *)
Lemma binds_split_mid : forall γ (b : abind) (a : atom) (bm : abind) Ξ Θ,
  binds γ b (Ξ ++ (a ~ bm) ++ Θ) ->
  binds γ b (Ξ ++ Θ) \/ (γ = a /\ b = bm).
Proof.
  intros * Hb. unfold binds in *. apply in_app_or in Hb.
  destruct Hb as [H | [H | H]];
    [ left; apply in_or_app; auto
    | right; inversion H; auto
    | left; apply in_or_app; auto ].
Qed.

Lemma a_assign_unify_consis_flex_preserve :
  (forall F Θ0 Ξ α P Θ1,
     Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
     forall γ, a_flex_tvar (Ξ ++ Θ0) γ -> a_flex_tvar Θ1 γ) /\
  (forall F Θ0 α β Θ1,
     Θ0 ⊲[ F ] α ≈ᵘ β ⊣ Θ1 ->
     forall γ, a_flex_tvar Θ0 γ -> a_flex_tvar Θ1 γ) /\
  (forall F Δ1 Δ2 Θ0 P0 P Q Θ1,
     Θ0 ⊢ₐ[ F ][ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 ->
     forall γ, a_flex_tvar Θ0 γ -> a_flex_tvar Θ1 γ).
Proof.
  apply (a_assign_unify_consis_mutind
           (fun F Θ0 Ξ α P Θ1 _ =>
              forall γ, a_flex_tvar (Ξ ++ Θ0) γ -> a_flex_tvar Θ1 γ)
           (fun F Θ0 α β Θ1 _ =>
              forall γ, a_flex_tvar Θ0 γ -> a_flex_tvar Θ1 γ)
           (fun F Δ1 Δ2 Θ0 P0 P Q Θ1 _ =>
              forall γ, a_flex_tvar Θ0 γ -> a_flex_tvar Θ1 γ)).
  (* ---------- a_assign ---------- *)
  - (* univ_ghost_id : identity *)
    intros F Θ0 α γ Hγ. simpl_env in Hγ. exact Hγ.
  - (* solve_m : Ξ ++ (α̂) ++ Θ0  →  (α̂≔τ) ++ β̄ ++ Ξ ++ Θ0 *)
    intros F Θ0 Ξ α P βs τ Hαn Hg Hm Hu Hfr γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]].
    + apply a_flex_tvar_alt; exists b; split; [ exact Hs | ].
      unfold binds in *. simpl. right.
      apply in_or_app; right. apply in_or_app. apply in_app_or in Hb. exact Hb.
    + subst. right; exists τ. unfold binds; left; reflexivity.
  - (* assign : Ξ ++ (β̂≔τ) ++ Θ0  →  (β̂≔τ) ++ Θ1, premise Ξ ++ Θ0 → Θ1 *)
    intros F Θ0 Θ1 Ξ α β τ P Q Hfα Hc IH γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]].
    + assert (Hγ' : a_flex_tvar Θ1 γ)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb'.
    + subst. right; exists τ. unfold binds; left; reflexivity.
  - (* depend : reassociate *)
    intros F Θ0 Θ1 Ξ α β P Hne Hβ Ha IH γ Hγ.
    apply IH. simpl_env in *. exact Hγ.
  - (* skip : Ξ ++ (β̂) ++ Θ0  →  (β̂) ++ Θ1 *)
    intros F Θ0 Θ1 Ξ α β P Hne Hβn Ha IH γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]].
    + assert (Hγ' : a_flex_tvar Θ1 γ)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb'.
    + subst. left. unfold binds; left; reflexivity.
  - (* skip_rigid : mid is rigid, kind mismatch *)
    intros F Θ0 Θ1 Ξ α β P Hβn Ha IH γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]];
      [ | subst; inversion Hs ].
    assert (Hγ' : a_flex_tvar Θ1 γ)
      by (apply IH; apply a_flex_tvar_alt; eauto).
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
    apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
    unfold binds in *; simpl; right; exact Hb'.
  - (* skip_tm_var *)
    intros F Θ0 Θ1 Ξ α x Q P Ha IH γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]];
      [ | subst; inversion Hs ].
    assert (Hγ' : a_flex_tvar Θ1 γ)
      by (apply IH; apply a_flex_tvar_alt; eauto).
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
    apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
    unfold binds in *; simpl; right; exact Hb'.
  - (* skip_tm_skl *)
    intros F Θ0 Θ1 Ξ α x Q P Ha IH γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    apply binds_split_mid in Hb; destruct Hb as [Hb | [Heqγ Heqb]];
      [ | subst; inversion Hs ].
    assert (Hγ' : a_flex_tvar Θ1 γ)
      by (apply IH; apply a_flex_tvar_alt; eauto).
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb']].
    apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
    unfold binds in *; simpl; right; exact Hb'.
  (* ---------- a_unify ---------- *)
  - (* flex_id : identity *)
    intros F Θ0 α Hfα γ Hγ. exact Hγ.
  - (* flex_l : (α̂) ++ Θ0 → (α̂≔β) ++ Θ0 *)
    intros F Θ0 α β Hne Hfβ γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'].
    + subst. right; eexists. unfold binds; left; reflexivity.
    + apply a_flex_tvar_alt; exists b; split; [ exact Hs | ].
      unfold binds in *; simpl; right; exact Hb'.
  - (* flex_r : symmetric *)
    intros F Θ0 α β Hne Hfα γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'].
    + subst. right; eexists. unfold binds; left; reflexivity.
    + apply a_flex_tvar_alt; exists b; split; [ exact Hs | ].
      unfold binds in *; simpl; right; exact Hb'.
  - (* flex_assign : (γ̂≔τ) ++ Θ0 → (γ̂≔τ) ++ Θ1, consis premise Θ0 → Θ1 *)
    intros F Θ0 Θ1 γ0 τ α β Q Hfα Hfβ Hc IH γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'].
    + subst. right; eexists. unfold binds; left; reflexivity.
    + assert (Hγ' : a_flex_tvar Θ1 γ)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb'']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb''.
  - (* flex_skip : (γ̂) ++ Θ0 → (γ̂) ++ Θ1 *)
    intros F Θ0 Θ1 γ0 α β Hγα Hγβ Hu IH γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'].
    + subst. left. unfold binds; left; reflexivity.
    + assert (Hγ' : a_flex_tvar Θ1 γ)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb'']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb''.
  - (* skip_other : (c~b) ++ Θ0 → (c~b) ++ Θ1, b non-flex *)
    intros F Θ0 Θ1 c b α β Hbshape Hu IH γ Hγ.
    apply a_flex_tvar_alt in Hγ; destruct Hγ as [b0 [Hs Hb0]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb0) as [[Heqγ Heqb] | Hb'].
    + subst. exfalso.
      destruct Hbshape as [Hb1 | [[Q1 Hb1] | [Q1 Hb1]]]; subst; inversion Hs.
    + assert (Hγ' : a_flex_tvar Θ1 γ)
        by (apply IH; apply a_flex_tvar_alt; eauto).
      apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b' [Hs' Hb'']].
      apply a_flex_tvar_alt; exists b'; split; [ exact Hs' | ].
      unfold binds in *; simpl; right; exact Hb''.
  (* ---------- a_consis ---------- *)
  - (* ghost : identity *) intros; auto.
  - (* unit : identity *) intros; auto.
  - (* rigid : identity *) intros; auto.
  - (* arrow : compose the two IHs *)
    intros F Δ1 Δ2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc1 IH1 Hc2 IH2 γ Hγ.
    apply IH2, IH1, Hγ.
  - (* forall_inh : cofinite, rigid head both sides *)
    intros L F Δ1 Δ2 Θ0 Θ1 P0 P Q Hco IH γ Hγ.
    destruct (atom_fresh L) as [X HX].
    assert (Hγ' : a_flex_tvar ((X ~ abind_tvar) ++ Θ1) γ).
    { apply (IH X HX). apply a_flex_tvar_weaken_prefix. exact Hγ. }
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'];
      [ subst; inversion Hs | ].
    apply a_flex_tvar_alt; eauto.
  - (* forall_syn : cofinite *)
    intros L F Δ1 Δ2 Θ0 Θ1 P0 P Q Hco IH γ Hγ.
    destruct (atom_fresh L) as [X HX].
    assert (Hγ' : a_flex_tvar ((X ~ abind_tvar) ++ Θ1) γ).
    { apply (IH X HX). apply a_flex_tvar_weaken_prefix. exact Hγ. }
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'];
      [ subst; inversion Hs | ].
    apply a_flex_tvar_alt; eauto.
  - (* univ_ghost : direct IH *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P Q Hc IH γ Hγ. apply IH, Hγ.
  - (* univ_ghost1 : cofinite *)
    intros L F Δ1 Δ2 Θ0 Θ1 P0 P Q Hco IH γ Hγ.
    destruct (atom_fresh L) as [X HX].
    assert (Hγ' : a_flex_tvar ((X ~ abind_tvar) ++ Θ1) γ).
    { apply (IH X HX). apply a_flex_tvar_weaken_prefix. exact Hγ. }
    apply a_flex_tvar_alt in Hγ'; destruct Hγ' as [b [Hs Hb]].
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heqγ Heqb] | Hb'];
      [ subst; inversion Hs | ].
    apply a_flex_tvar_alt; eauto.
  - (* univ_ghost2 : direct IH *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH γ Hγ. apply IH, Hγ.
  - (* flex : unify IH *)
    intros F Δ1 Δ2 Θ0 Θ1 α β Hu IH γ Hγ. apply IH, Hγ.
  - (* flex_l : assign IH at Ξ = nil *)
    intros F Δ1 Δ2 Θ0 Θ1 α P0 Hnf Ha IH γ Hγ. apply IH. simpl_env. exact Hγ.
  - (* flex_r : assign IH at Ξ = nil *)
    intros F Δ1 Δ2 Θ0 Θ1 α P Hnf Ha IH γ Hγ. apply IH. simpl_env. exact Hγ.
  - (* ghost_r : identity *) intros; auto.
  - (* univ_ghost_r : direct IH *)
    intros F Δ1 Δ2 Θ0 Θ1 P0 P Q Hg Hnf Hc IH γ Hγ. apply IH, Hγ.
Qed.

(** Packaged corollaries. *)
Corollary a_unify_flex_preserve : forall F Θ0 α β Θ1 γ,
  Θ0 ⊲[ F ] α ≈ᵘ β ⊣ Θ1 ->
  a_flex_tvar Θ0 γ -> a_flex_tvar Θ1 γ.
Proof.
  intros * Hu Hγ.
  exact (proj1 (proj2 a_assign_unify_consis_flex_preserve) _ _ _ _ _ Hu γ Hγ).
Qed.

Corollary a_assign_flex_preserve : forall F Θ0 Ξ α P Θ1 γ,
  Θ0 ⊲[ F ][ Ξ ] α ≔ P ⊣ Θ1 ->
  a_flex_tvar (Ξ ++ Θ0) γ -> a_flex_tvar Θ1 γ.
Proof.
  intros * Ha Hγ.
  exact (proj1 a_assign_unify_consis_flex_preserve _ _ _ _ _ _ Ha γ Hγ).
Qed.

(* ===================================================================== *)
(*  Pointwise inversion of substitution agreement (converse of              *)
(*  [msubst_ptyp_agree] / [msubst_pskl_agree]).                             *)
(* ===================================================================== *)

Lemma msubst_ptyp_agree_inv : forall θ ζ A,
  msubst_ptyp θ A = msubst_ptyp ζ A ->
  forall X, X `in` ftvar_in_ptyp A ->
  msubst_lookup θ X = msubst_lookup ζ X.
Proof.
  intros θ ζ A; induction A; intros Heq X HX; simpl in *;
    try solve [ exfalso; clear - HX; fsetdec ].
  - (* var_f *)
    assert (HXY : X = α) by (clear - HX; fsetdec). subst. exact Heq.
  - (* arrow *)
    injection Heq as Heq1 Heq2.
    apply union_1 in HX; destruct HX; eauto.
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

Lemma msubst_pskl_agree_inv : forall θ ζ P,
  msubst_pskl θ P = msubst_pskl ζ P ->
  forall X, X `in` ftvar_in_pskl P ->
  msubst_lookup θ X = msubst_lookup ζ X.
Proof.
  intros θ ζ P; induction P; intros Heq X HX; simpl in *;
    try solve [ exfalso; clear - HX; fsetdec ].
  - (* var_f *)
    assert (HXY : X = α) by (clear - HX; fsetdec). subst.
    apply ptyp_to_pskl_inj. exact Heq.
  - (* arrow *)
    injection Heq as Heq1 Heq2.
    apply union_1 in HX; destruct HX; eauto.
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
  intros Θ A H X HX.
  apply (a_wf_ptyp_ftv_tvarish H) in HX.
  destruct HX as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

Lemma a_scope_pskl_ftv_dom' : forall Θ P,
  a_scope_pskl Θ P -> ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros Θ P H X HX.
  apply (a_scope_pskl_ftv_tvarish H) in HX.
  destruct HX as [Hb | [Hb | [t Hb]]]; apply binds_In in Hb; exact Hb.
Qed.

(** In a wf context, a term binding's payload draws its variables from the
    context's domain.  (Applied at a TAIL context to separate a fresh head.) *)
Lemma a_wf_aenv_binds_var_typ_ftv : forall Θ x A,
  a_wf_aenv Θ -> binds x (abind_var_typ A) Θ ->
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

Lemma a_wf_aenv_binds_var_skl_ftv : forall Θ x P,
  a_wf_aenv Θ -> binds x (abind_var_skl P) Θ ->
  ftvar_in_pskl P [<=] dom Θ.
Proof.
  intros Θ x P Hwf; induction Hwf; intros Hb; try solve [ inversion Hb ];
    destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq1 Heq2] | Hb'];
    try discriminate;
    try solve [ pose proof (IHHwf Hb') as Hs; simpl; clear - Hs; fsetdec ].
  (* var_skl head : P is wf in the tail *)
  injection Heq2 as Heq2. subst.
  pose proof (a_scope_pskl_ftv_dom' H0) as Hs. simpl. clear - Hs. fsetdec.
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
  apply msubst_pskl_agree. intros X HX. simpl.
  destruct (X == α0) as [->|Hne]; [ exfalso; auto | reflexivity ].
Qed.

(* NB the forward/backward SYNTACTIC binding transports that lived here
   (a_inc_binds_var_typ/skl and their _src converses) were deleted with the
   move to GMM-style SEMANTIC entries in [a_inc] (def_meta.v): the target's
   binder payload is now only ≡ᵗ/≡ˢ-related to the substituted source
   payload, and the ζ-override machinery they supported is gone (see
   algo/cex/cex_assign_optimal_syn_middle.v for why it had to go). *)


