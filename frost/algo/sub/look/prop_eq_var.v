(* P6-Cv: completeness of consistency-constraint solving for the variable
   case — [a_solve_eq_complete_var] (consistency-proofs.tex:1180), CLOSED
   axiom-free and PREMISE-FAITHFUL to the paper (the earlier mech-only
   [pskl_no_hole P0] side condition was removed by the [aenv_split] bag
   rework, 2026-07-27).  Extends sub/look/prop_rho_relation.v with the ForallSyn
   machinery (the bag-split generalized theorem, the aenv-tvar precision
   rename, and the three ForallGhost / GhostL / UnivGhost rows). *)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.decorated_algo.prop_decorate.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.consis.prop_consis_precise.
Require Import src.frost.algo.sub.prop_looksub.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.algo.sub.prop_completeness_sub_precise.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_compose.   (* a_inc_lookup_mono, a_inc_dom_flex *)
Require Import src.frost.algo.sub.look.prop_rho_relation.
Require Import src.frost.algo.sub.look.prop_solve_ext.
Require Import src.frost.algo.sub.look.prop_flex_apart.

Set Implicit Arguments.

(* Most P6-Cv leaf/absurd helpers live in sub/look/prop_rho_relation.v; this file
   adds the ForallSyn-specific kit and the main induction over the whole
   consistency judgment. *)



(** [MECH-ONLY kit] Moving a Δ-entry of skeleton well-formedness into the
    aenv as a rigid tvar (mid-insertion general; the ∀◇-body stays at
    empty Δ and only needs binds-weakening).  No paper counterpart: the
    paper writes every descent binder as "Θ,β" and never distinguishes
    the aenv from the skeleton-scope Δ, so these transports are implicit
    there. *)
Lemma a_wf_pskl_delta_to_tvar_mid : forall Θfull Δ P,
  Θfull ⨟ Δ ⊢ₚₛᵃ P ->
  forall α1 Θ1 Θ2 Δ', Θfull = Θ1 ++ Θ2 ->
  Δ [<=] add α1 Δ' ->
  (Θ1 ++ (α1 ~ abind_tvar) ++ Θ2) ⨟ Δ' ⊢ₚₛᵃ P.
Proof.
  intros Θfull Δ P H; induction H; intros α1 Θ1 Θ2 Δ' HeqΘ Hsub; subst.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    match goal with Hor : _ \/ a_binds_tvar ?α0 _ |- _ =>
      destruct Hor as [HΔ | Hbt];
      [ destruct (α0 == α1) as [-> | Hne];
        [ right; left; unfold binds;
          apply in_or_app; right; left; reflexivity
        | left; clear - HΔ Hsub Hne; fsetdec ]
      | right;
        destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        [ left; apply binds_weaken; exact Hb
        | right; left; apply binds_weaken; exact Hb
        | right; right; exists τ0; apply binds_weaken; exact Hb ] ]
    end.
  - apply a_wf_pskl__arrow; eauto.
  - apply a_wf_pskl__all with (L := L).
    intros α Hα.
    apply (H0 α Hα α1 Θ1 Θ2 (add α Δ') eq_refl).
    clear - Hsub; fsetdec.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; [ assumption | ].
    eapply a_wf_pskl_weaken;
      [ intros x b Hb; apply binds_weaken; exact Hb | eassumption ].
Qed.

(* ⚙ [a_wf_pskl_delta_to_tvar] deleted 2026-08-09 (cleanup audit §8.1): an alpha-variant of the
   one in prop_completeness_consis.v, which this file imports. *)

(** a_inc images are Θ-scoped (the prose wf side-condition, pointwise). *)
Lemma a_inc_image_ftv_dom : forall Θ0 κ Θ,
  κ ∷ Θ0 ⊑ Θ ->
  forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ.
Proof.
  intros Θ0 κ Θ H; induction H; intros p Hp; simpl in Hp.
  - contradiction.
  - destruct Hp as [<- | Hp];
      [ simpl; apply a_wf_ptyp_ftv_dom'; assumption | eauto ].
  - destruct Hp as [<- | Hp];
      [ simpl; apply a_wf_ptyp_ftv_dom'; assumption | eauto ].
  - pose proof (IHa_inc p Hp) as Hb.
    repeat rewrite dom_app. clear - Hb; fsetdec.
  - pose proof (IHa_inc p Hp) as Hb.
    repeat rewrite dom_app. clear - Hb; fsetdec.
  - pose proof (IHa_inc p Hp) as Hb.
    repeat rewrite dom_app. clear - Hb; fsetdec.
Qed.

(* The paper-form statement is now the COROLLARY of the generalized
   theorem below (Θtv := [], Δr := ∅, R := ∅); the paper mapping is
   documented on the corollary [a_solve_eq_complete_var]. *)


(* ===================================================================== *)
(*  THE GENERALIZED STATEMENT (repair architecture, DESIGN §6(m), bag     *)
(*  form).  Θ splits as a binds-level BAG [aenv_split Θ Θtv Θr] (Θtv =    *)
(*  the ForallInh descent binders, all rigid; Θr = the original context   *)
(*  PLUS the refinement-visible ForallSyn binders); the refinement        *)
(*  premise lives at (Θr, Δr) with Δr [=] dom Θtv, so □-fills stay wf     *)
(*  away from the Θtv binders; the conclusion returns a fresh-extension   *)
(*  FAMILY of precisions, which is what lets the ForallInh/ForallSyn □-   *)
(*  and ∀◇-fill-rows fold their bodies at (add α Δ).  The paper's         *)
(*  statement is the Θtv := [] / R := ∅ corollary.                        *)
(* ===================================================================== *)
(*  ForallSyn kit: flex_apart TARGET descent through an all_etag binder    *)
(*  (the ∀◇-body is guarded, which excludes the all_syn source that would  *)
(*  otherwise block the descent).  [MECH-ONLY: maintenance lemmas for the  *)
(*  mech-only flex_apart premise — the paper has no counterpart because    *)
(*  its proof never states the FlexR-freshening reachability invariant.]   *)
(* ===================================================================== *)

(** Guarded source: descend the all_etag target one binder. *)
Lemma flex_apart_guarded_all_etag_descent : forall Θ0 Δρ P0 ε ψ,
  guarded_pskl P0 ->
  flex_apart Θ0 Δρ P0 (uskl_all_etag ε ψ) ->
  forall α, α `notin` Δρ ->
  flex_apart Θ0 Δρ P0 (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros Θ0 Δρ P0 ε ψ Hg Hfa α Hα; inversion Hg; subst.
  - (* unit *) apply fa_unit.
  - (* var *)
    inversion Hfa; subst.
    + apply fa_clean.
      match goal with Hc : _ ∩ _ [=] empty |- _ =>
        pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                      (uskl_var_f α)) as Hup;
        simpl in *; clear - Hc Hup Hα; fsetdec end.
    + apply fa_var_rigid; assumption.
    + (* fa_flexfree : the payload is untouched *)
      apply fa_flexfree; assumption.
  - (* arrow *)
    inversion Hfa; subst;
      [ | (* fa_flexfree : the payload is untouched *)
          apply fa_flexfree; assumption ].
    apply fa_clean.
    match goal with Hc : _ ∩ _ [=] empty |- _ =>
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                    (uskl_var_f α)) as Hup;
      simpl in *; clear - Hc Hup Hα; fsetdec end.
Qed.

(** ∀◇ source (guarded body): descend the all_etag target one binder. *)
Lemma flex_apart_tophole_all_etag_descent : forall Θ0 Δρ P0' ε ψ,
  guarded_pskl P0' ->
  flex_apart Θ0 Δρ (pskl_tophole P0') (uskl_all_etag ε ψ) ->
  forall α, α `notin` Δρ ->
  flex_apart Θ0 Δρ (pskl_tophole P0') (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof.
  intros Θ0 Δρ P0' ε ψ Hg Hfa α Hα.
  inversion Hfa; subst.
  - (* fa_clean *)
    apply fa_clean.
    match goal with Hc : _ ∩ _ [=] empty |- _ =>
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α))
        as Hup;
      simpl in *; clear - Hc Hup Hα; fsetdec end.
  - (* fa_tophole: descend the guarded body *)
    apply fa_tophole.
    eapply flex_apart_guarded_all_etag_descent;
      [ exact Hg | eassumption | exact Hα ].
  - (* fa_flexfree : the payload is untouched *)
    apply fa_flexfree; assumption.
Qed.

(* RESTART NOTE (no-hole removal rework): the "ForallSyn kit (2)" that
   lived here — [bskl_no_hole] + [ad_refine_syn_aenv_to_delta(_mid)], the
   aenv→Δr transport of the refinement premise, valid only for hole-free
   sources — was DELETED as dead.  The bag split [aenv_split] lets the
   ForallSyn binder join Θr, so the tophole_fill body is the IH's
   refinement premise VERBATIM and no transport (hence no pskl_no_hole
   premise) is needed. *)


(* ===================================================================== *)
(*  ForallSyn kit (4): rename a tvar α2↦β2 in the AENV of a precision       *)
(*  derivation.  Needed to build the ad_ppre__tophole_fill cofinite       *)
(*  family (binder in the aenv) from a SINGLE IHα instance.               *)
(*  [PAPER: implicit — the paper's "removing β as necessary" α-renames    *)
(*  the fill binder without comment; a cofinite-quantified rule needs     *)
(*  the rename made explicit.  The solve output is NOT deterministic, so  *)
(*  re-running the IH per family member would return unrelated Pa's —     *)
(*  renaming the single run is the only route.]                           *)
(* ===================================================================== *)

Lemma binds_swap_mid : forall (α : atom) (b : abind) Θ1 Θ0 α1 β1 c c',
  binds α b (Θ1 ++ (α1 ~ c) ++ Θ0) -> α <> α1 ->
  binds α b (Θ1 ++ (β1 ~ c') ++ Θ0).
Proof.
  intros α b Θ1 Θ0 α1 β1 c c' Hb Hne.
  unfold binds in *.
  apply in_app_or in Hb. apply in_or_app.
  destruct Hb as [Hb | Hb]; [ left; exact Hb | right ].
  simpl in Hb. destruct Hb as [Heq | Hb].
  - inversion Heq; subst. contradiction.
  - simpl. right. exact Hb.
Qed.

Lemma ad_partial_precise_rename_tvar : forall Θfull Δ Ψ P ψ,
  Θfull ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall α1 β1 Θ1 Θ0,
  uniq Θfull ->
  Θfull = Θ1 ++ (α1 ~ abind_tvar) ++ Θ0 ->
  β1 `notin` dom Θfull ->
  β1 `notin` Δ ->
  β1 `notin` ftvar_in_pskl P ->
  β1 `notin` ftvar_in_uskl ψ ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θfull ->
     α1 `notin` ftvar_in_ptyp τ /\ β1 `notin` ftvar_in_ptyp τ) ->
  (Θ1 ++ (β1 ~ abind_tvar) ++ Θ0) ⨟ Δ ⊢
    (subst_pskl_in_pskl (pskl_var_f β1) α1 P)
    ⊑ᵖ[ Ψ ] (subst_bskl_in_uskl (uskl_var_f β1) α1 ψ).
Proof.
  intros Θfull Δ Ψ P ψ H; induction H;
    intros α1 β1 Θ1 Θ0 Hu Heq HWd Hβ2Δ HWP Hβ2ψ Hdefs; subst; simpl in *.
  - (* unit *) apply ad_ppre__unit; assumption.
  - (* var α *)
    destruct (eq_var α α1) as [-> | Hne].
    + repeat (destruct_if as [_ | Hc]; [ | exfalso; apply Hc; reflexivity ]).
      apply ad_ppre__var; [ assumption | ].
      right. left. unfold binds; apply in_or_app; right; left; reflexivity.
    + repeat (destruct_if as [Hc | _]; [ exfalso; apply Hne; exact Hc | ]).
      apply ad_ppre__var; [ assumption | ].
      destruct H0 as [HΔ | Hbt]; [ left; exact HΔ | right ].
      destruct Hbt as [Hb | [Hb | [τ Hb]]];
        [ left | right; left | right; right; exists τ ];
        eapply binds_swap_mid; try exact Hb; exact Hne.
  - (* arrow *)
    eapply ad_ppre__arrow;
      [ apply IHad_partial_precise1;
          [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
          | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ]
      | apply IHad_partial_precise2;
          [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
          | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ]
      | assumption ].
  - (* forall: binder β into Δ, aenv unchanged *)
    eapply ad_ppre__forall with
      (L := L `union` singleton α1 `union` singleton β1
              `union` Δ `union` dom (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0));
      [ | eassumption ].
    intros β Hβ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) α1 β1 Θ1 Θ0 Hu eq_refl HWd);
      [ clear - Hβ2Δ Hβ; fsetdec
      | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P
                      (pskl_var_f β)) as Hup;
        simpl in Hup; clear - HWP Hβ Hup; fsetdec
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                      (uskl_var_f β)) as Hup;
        simpl in Hup; clear - Hβ2ψ Hβ Hup; fsetdec
      | exact Hdefs ].
  - (* hole *)
    assert (Hα2ψ : α1 `notin` ftvar_in_uskl ψ \/ α1 `in` ftvar_in_uskl ψ)
      by (destruct (AtomSetProperties.In_dec α1 (ftvar_in_uskl ψ));
          [ right | left ]; assumption).
    apply ad_ppre__hole; [ assumption | ].
    pose proof (ftvar_in_uskl_subst_bskl_in_uskl_upper ψ (uskl_var_f β1) α1)
      as Hup. simpl in Hup.
    match goal with Hint : Δ ∩ _ [=] empty |- _ =>
      clear - Hint Hβ2Δ Hup; fsetdec end.
  - (* tophole_remove *)
    apply ad_ppre__tophole_remove.
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ].
  - (* tophole_fill: binder α into the AENV front *)
    eapply ad_ppre__tophole_fill with
      (L := L `union` singleton α1 `union` singleton β1
              `union` Δ `union` dom (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0)).
    intros β Hβ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    replace (pskl_tophole (subst_pskl_in_pskl (pskl_var_f β1) α1 P))
      with (subst_pskl_in_pskl (pskl_var_f β1) α1 (pskl_tophole P))
      by reflexivity.
    assert (Hu' : uniq ((β ~ abind_tvar) ++ Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
      by (apply uniq_push; [ exact Hu | clear - Hβ; solve_notin ]).
    apply (H0 β ltac:(clear - Hβ; solve_notin_auto) α1 β1
             ((β ~ abind_tvar) ++ Θ1) Θ0 Hu' eq_refl);
      [ simpl; clear - HWd Hβ; solve_notin
      | exact Hβ2Δ
      | simpl; clear - HWP; solve_notin
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ
                      (uskl_var_f β)) as Hup;
        simpl in Hup; clear - Hβ2ψ Hβ Hup; fsetdec
      | intros αd τ Hb;
        apply Hdefs with (α := αd);
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Hc] | Hb'];
          [ discriminate Hc | exact Hb' ] ].
  - (* tophole_keep *)
    apply ad_ppre__tophole_keep.
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | clear - HWP; solve_notin | clear - Hβ2ψ; solve_notin | exact Hdefs ].
  - (* flex_l: α ≠ α1 (uniq); the def τ is α1-free (Hdefs) *)
    assert (Hne : α <> α1).
    { intro; subst.
      assert (Hbz : binds α1 abind_tvar (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbz Hu) as Hc; discriminate Hc. }
    destruct_if as [Hc | _]; [ exfalso; apply Hne; exact Hc | ].
    destruct (Hdefs _ _ H) as [Hα2τ Hβ2τ].
    eapply ad_ppre__flex_l;
      [ eapply binds_swap_mid; [ exact H | exact Hne ] | ].
    assert (Hfr : α1 `notin` ftvar_in_pskl (ptyp_to_pskl τ))
      by (rewrite ftvar_ptyp_to_pskl; exact Hα2τ).
    rewrite <- (subst_pskl_in_pskl_fresh_eq (ptyp_to_pskl τ)
                  (pskl_var_f β1) α1 Hfr).
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | rewrite ftvar_ptyp_to_pskl; exact Hβ2τ
      | clear - Hβ2ψ; solve_notin | exact Hdefs ].
  - (* flex_r: α ≠ α1 (uniq); the def τ is α1-free (Hdefs) *)
    assert (Hne : α <> α1).
    { intro; subst.
      assert (Hbz : binds α1 abind_tvar (Θ1 ++ (α1 ~ abind_tvar) ++ Θ0))
        by (unfold binds; apply in_or_app; right; left; reflexivity).
      pose proof (binds_unique _ _ _ _ _ H Hbz Hu) as Hc; discriminate Hc. }
    destruct_if as [Hc | _]; [ exfalso; apply Hne; exact Hc | ].
    destruct (Hdefs _ _ H) as [Hα2τ Hβ2τ].
    eapply ad_ppre__flex_r;
      [ eapply binds_swap_mid; [ exact H | exact Hne ] | ].
    assert (Hfr : α1 `notin` ftvar_in_uskl (ptyp_to_uskl_syn τ))
      by (rewrite ftvar_in_uskl_ptyp_to_uskl_syn; exact Hα2τ).
    rewrite <- (subst_bskl_in_uskl_fresh_eq (ptyp_to_uskl_syn τ)
               (uskl_var_f β1) α1 Hfr).
    apply IHad_partial_precise;
      [ exact Hu | reflexivity | exact HWd | exact Hβ2Δ
      | clear - HWP; solve_notin
      | rewrite ftvar_in_uskl_ptyp_to_uskl_syn; exact Hβ2τ | exact Hdefs ].
Qed.

(* ===================================================================== *)
(*  The BAG split  [aenv_split Θf Θtv Θr]  (no-hole-removal rework).      *)
(*  The old split was the LIST equation Θ = Θtv ++ Θr, which cannot put   *)
(*  the ForallSyn binder INTO Θr (the consistency rule prepends it to Θ,  *)
(*  so the equation forces it into Θtv) — that forced the aenv→Δr         *)
(*  transport [ad_refine_syn_aenv_to_delta], which is false for holey     *)
(*  sources and hence forced the pskl_no_hole premise.  A binds-level     *)
(*  split has no order, so ForallSyn can use Θr_ih := (α~tvar)++Θr and    *)
(*  take the tophole_fill body as the IH's refinement premise VERBATIM.   *)
(*  Θr's defs are no longer "a suffix of Θ", so their self-containedness  *)
(*  is carried as an explicit a_wf_aenv Θr premise.                       *)
(* ===================================================================== *)

Definition aenv_split (Θf Θtv Θr : aenv) : Prop :=
  (forall x (b : abind), binds x b Θf <-> binds x b Θtv \/ binds x b Θr) /\
  dom Θf [=] dom Θtv `union` dom Θr /\
  (dom Θtv) ∩ dom Θr [=] empty.

Lemma aenv_split_nil : forall Θf, aenv_split Θf nil Θf.
Proof.
  intros Θf; split; [ | split ].
  - intros x b; split; intros Hb;
      [ right; exact Hb
      | destruct Hb as [Hb | Hb]; [ inversion Hb | exact Hb ] ].
  - simpl. clear; fsetdec.
  - simpl. clear; fsetdec.
Qed.

Lemma aenv_split_cons_tv : forall Θf Θtv Θr α,
  aenv_split Θf Θtv Θr -> α `notin` dom Θf ->
  aenv_split ((α ~ abind_tvar) ++ Θf) ((α ~ abind_tvar) ++ Θtv) Θr.
Proof.
  intros Θf Θtv Θr α (Hbs & Hdom & Hdisj) Hα; split; [ | split ].
  - intros x b; split.
    + intros Hb.
      unfold binds in Hb; simpl in Hb.
      destruct Hb as [Heq | Hb];
        [ left; unfold binds; simpl; left; exact Heq | ].
      apply Hbs in Hb.
      destruct Hb as [Hb | Hb];
        [ left; unfold binds; simpl; right; exact Hb | right; exact Hb ].
    + intros Hor.
      unfold binds; simpl.
      destruct Hor as [Hb | Hb];
        [ unfold binds in Hb; simpl in Hb;
          destruct Hb as [Heq | Hb];
          [ left; exact Heq | right; apply Hbs; left; exact Hb ]
        | right; apply Hbs; right; exact Hb ].
  - simpl. clear - Hdom; fsetdec.
  - simpl. clear - Hdisj Hdom Hα; fsetdec.
Qed.

Lemma aenv_split_cons_r : forall Θf Θtv Θr α,
  aenv_split Θf Θtv Θr -> α `notin` dom Θf ->
  aenv_split ((α ~ abind_tvar) ++ Θf) Θtv ((α ~ abind_tvar) ++ Θr).
Proof.
  intros Θf Θtv Θr α (Hbs & Hdom & Hdisj) Hα; split; [ | split ].
  - intros x b; split.
    + intros Hb.
      unfold binds in Hb; simpl in Hb.
      destruct Hb as [Heq | Hb];
        [ right; unfold binds; simpl; left; exact Heq | ].
      apply Hbs in Hb.
      destruct Hb as [Hb | Hb];
        [ left; exact Hb | right; unfold binds; simpl; right; exact Hb ].
    + intros Hor.
      unfold binds; simpl.
      destruct Hor as [Hb | Hb];
        [ right; apply Hbs; left; exact Hb
        | unfold binds in Hb; simpl in Hb;
          destruct Hb as [Heq | Hb];
          [ left; exact Heq | right; apply Hbs; right; exact Hb ] ].
  - simpl. clear - Hdom; fsetdec.
  - simpl. clear - Hdisj Hdom Hα; fsetdec.
Qed.

Lemma aenv_split_sub_r : forall Θf Θtv Θr,
  aenv_split Θf Θtv Θr ->
  forall x (b : abind), binds x b Θr -> binds x b Θf.
Proof.
  intros Θf Θtv Θr (Hbs & _ & _) x b Hb. apply Hbs. right; exact Hb.
Qed.

Lemma aenv_split_dom_r : forall Θf Θtv Θr,
  aenv_split Θf Θtv Θr -> dom Θr [<=] dom Θf.
Proof.
  intros Θf Θtv Θr (_ & Hdom & _). clear - Hdom; fsetdec.
Qed.

(** Non-tvar bindings of the full context live on the Θr side. *)
Lemma aenv_split_binds_def_r : forall Θf Θtv Θr α τ,
  aenv_split Θf Θtv Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  binds α (abind_flex_mono_def τ) Θf ->
  binds α (abind_flex_mono_def τ) Θr.
Proof.
  intros Θf Θtv Θr α τ (Hbs & _ & _) Htvs Hb.
  apply Hbs in Hb.
  destruct Hb as [Hb | Hb]; [ | exact Hb ].
  pose proof (Htvs _ _ Hb) as Hc; discriminate Hc.
Qed.

(** [refine_primary_to_plain], bag-split form: weaken Θr into the full
    context and absorb Δr (= dom Θtv, all rigid there). *)
Lemma refine_primary_to_plain_split : forall Θf Θtv Θr Δr Q' Q,
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  aenv_split Θf Θtv Θr ->
  Δr [=] dom Θtv ->
  Θr ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  Θf ⨟ empty ⊢ᵣᵃ Q' ⊳ Q.
Proof.
  intros Θf Θtv Θr Δr Q' Q Htvs Hsp HΔr H.
  eapply ad_refine_syn_delta_absorb with (Δr := Δr).
  - eapply ad_refine_syn_weaken;
      [ exact H | intros x b Hb; eapply aenv_split_sub_r; eassumption ].
  - intros α2 Hα2. right.
    assert (HZd : α2 `in` dom Θtv) by (clear - Hα2 HΔr; fsetdec).
    apply binds_In_inv in HZd; destruct HZd as [b Hb].
    pose proof (Htvs _ _ Hb) as Heqb; subst b.
    destruct Hsp as (Hbs & _ & _). apply Hbs. left; exact Hb.
Qed.

(** [consis_subject_ftv_split_bound], bag-split form (Θr's defs are
    self-contained by its OWN wf, not by suffix position). *)
Lemma consis_subject_ftv_bag_bound : forall Ψ Θf R Q Θtv Θr,
  Ψ ⨟ Θf ⊢ₛᵃ R ∼ Q ->
  aenv_split Θf Θtv Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  a_wf_aenv Θr ->
  ftvar_in_uskl R [<=] ftvar_in_bskl Q `union` dom Θr.
Proof.
  intros Ψ Θf R Q Θtv Θr H Hsp Htvs HwfΘr.
  intros x Hx.
  destruct (ad_pat_consis_ftv_bound H Hx) as [Hin | (α & τ & Hb & Hor)].
  - clear - Hin; fsetdec.
  - assert (Hbr : binds α (abind_flex_mono_def τ) Θr)
      by (eapply aenv_split_binds_def_r; eassumption).
    destruct Hor as [-> | Hτ].
    + pose proof (binds_In _ _ _ _ Hbr) as Hd. clear - Hd; fsetdec.
    + assert (Hd : ftvar_in_ptyp τ [<=] dom Θr)
        by (eapply a_wf_aenv_def_ftv_dom; [ exact HwfΘr | exact Hbr ]).
      clear - Hτ Hd; fsetdec.
Qed.

(* ===================================================================== *)
(*  ⭐ THE CONCLUSION CARRIES THE κ-EXTENSION (2026-08-04, the SolE-FlexR  *)
(*  repair).  [solve_ext] (sub/look/prop_rho_relation.v) supplies the six          *)
(*  components every P6 statement now shares — the solve, its generated    *)
(*  block [Ξ], and the aligned extension [κ'] of the metasubstitution      *)
(*  over that block; P6-Cv's own post-condition is the Δ'-FAMILY of        *)
(*  precisions it always had, now read under [κ' ++ κ].                    *)
(*                                                                        *)
(*  The extension is REAL here and not bookkeeping: at [P0 = β̂] the        *)
(*  repaired SE-FlexR returns [guess^TY(Pi)], which invents a flexible for *)
(*  every ghost inside [Pi], and the output is only interpretable under a  *)
(*  metasubstitution that knows what those flexibles stand for.            *)
(* ===================================================================== *)
Definition p6cv_post (Θ Θr : aenv) (κ : metasubst) (Δ Ψi Ψa : atoms)
    (ψa : uskl) (κ' : metasubst) (Pa : pskl) : Prop :=
  forall Δ',
    Δ' ∩ Δ [=] empty ->
    Δ' ∩ dom Θr [=] empty ->
    delta_def_fresh Δ' Θ ->
    Θ ⨟ (Δ `union` Δ') ⊢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.

(* ⭐ [Θw] IS THE WELL-FORMEDNESS CONTEXT OF THE EXTENSION AND IT STAYS FIXED
   AS THE INDUCTION GOES UNDER BINDERS (2026-08-04).  A ∀ row runs its body at
   [(α ~ tvar) ++ Θ], but the block the body generates is emitted OUTSIDE the
   ∀ — the solve's ∀ rows pass [Ξ] through unchanged — so a payload mentioning
   the bound rigid would be ill-scoped.  Passing [Θw] down untouched is what
   makes the construction compose; see [a_guess_ty_witness_mono]. *)
Definition p6cv_concl (Θ0 Θ Θw Θr : aenv) (κ : metasubst) (Δ Ψi Ψa : atoms)
    (ψa : uskl) (Pi P0 : pskl) (L : atoms) : Prop :=
  solve_ext Θ0 Θw Pi P0 L (p6cv_post Θ Θr κ Δ Ψi Ψa ψa).

(** The PASS-THROUGH rows (every ∀◇ peel): the solve strips a constructor
    and the whole package — block, extension, freshness, precision — rides
    along unchanged. *)
(** SE-UnivGhost: the premise's output is RE-WRAPPED in a [∀◇], so the
    package is rebuilt by hand — but the block and the extension still pass
    through untouched. *)
Lemma p6cv_tophole_both : forall Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi' P0' L,
  p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi' P0' L ->
  p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa (pskl_tophole Pi') (pskl_tophole P0') L.
Proof.
  intros Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi' P0' L
         (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hq).
  exists Ξ, (pskl_tophole Pa), κ'.
  split; [ apply a_solve_eq__tophole_both; exact Hs | ].
  repeat (split; [ solve [ exact Hfm | exact Hu | exact Hk | exact Hfr
                         | exact HF ] | ]).
  intros Δ' HS1 HS2 HS3. cbn [msubst_pskl].
  apply ad_ppre__tophole_remove. exact (Hq Δ' HS1 HS2 HS3).
Qed.

Lemma p6cv_step : forall Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi P0 Pi' P0' L,
  (forall Ξ Pa, Θ0 ⊢ₑ Pi' ∼ P0' ⤳ Ξ ⨾ Pa -> Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa) ->
  p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi' P0' L ->
  p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi P0 L.
Proof.
  intros Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi P0 Pi' P0' L Hstep H.
  eapply solve_ext_step;
    [ exact Hstep | intros κ0 Pa0 Hq; exact Hq | exact H ].
Qed.

Theorem a_solve_eq_complete_var_gen :
  forall NM Θ Θ0 Θw Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  (* the context split, as a BINDS-LEVEL bag (see the block above): the
     consistency induction keeps a variable aenv index, and the ForallSyn
     binder can join Θr (refinement-visible) instead of Θtv *)
  aenv_split Θ Θtv Θr ->
  aenv_split Θ0 Θtv Θ0r ->
  a_wf_aenv Θr ->
  (forall x b, binds x b Θtv -> b = abind_tvar) ->
  Δr [=] dom Θtv ->
  Δρ ∩ dom Θtv [=] empty ->
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  (* ⭐ the FIXED wf context of the κ-extension: [Θ] is [Θw] under a stack of
     rigid binders (identical at the top-level call) *)
  a_wf_aenv Θw ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (* the converse for NON-rigid entries: [Θ] adds only rigid binders *)
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (* ⭐ EVERY κ-IMAGE LIVES OUTSIDE THE BINDERS THE INDUCTION OPENS
     (2026-08-04).  At the top-level call this is [a_inc_lookup_wf] on [Hκ]
     with [Θ = Θw]; and it is INVARIANT, because a ∀ row leaves κ alone and
     adds only a RIGID to [Θ0], which no flexible lookup can see.  Compare
     [κ ∷ Θ0 ⊑ Θw], which is NOT invariant: the ∀ row's binder is rigid in
     the extended [Θ0] but absent from [Θw].  This is what shuts the
     SE-FlexR node's payload-scope obligation — see the FLEX block. *)
  (forall α, a_flex_tvar Θ0 α ->
     ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θw) ->
  uskl_rho NM Θ Δρ Ψρ ψsub ψa ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  Ψρ ∩ Ψ' [=] empty ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  Ψsub ⨟ Θ ⊢ₛᵃ ψsub ∼ Q ->
  Θr ⨟ Δr ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa ψa Pi P0 L.
Proof.
  intros NM Θ Θ0 Θw Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv HwfΘ HwfΘ0 HwfΘw Hmon Hnr
         HwfPi HwfP0 Hκ Hκw Hrho Htags
         Hsub Hinter Hfresh Hdelta Hapart Hdfresh Hpre
         Hsubeq1 Hsubeq2 Hconsis Hrefine.
  revert NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa ψa Pi P0
         HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv HwfΘ HwfΘ0 Hmon Hnr
         HwfPi HwfP0 Hκ Hκw Hrho Htags
         Hsub Hinter Hfresh Hdelta Hapart Hdfresh Hpre
         Hsubeq1 Hsubeq2 Hrefine.
  induction Hconsis; intros
    NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ Ψ' Ψi Ψa ψa Pi P0
    HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv HwfΘ HwfΘ0 Hmon Hnr
    HwfPi HwfP0 Hκ Hκw Hrho Htags
    Hsub Hinter Hfresh Hdelta Hapart Hdfresh Hpre
    (* ⚙️ [Lav], not [L]: the consistency rules' own cofinite binder is [L] in
       several rows, and [intros] runs in all of them. *)
    Hsubeq1 Hsubeq2 Hrefine Lav HLav;
  (* the definition-only form the solve kit asks for, in EVERY row *)
  assert (Hdefs : forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
                    binds α0 (abind_flex_mono_def τ0) Θw)
    by (intros α0 τ0 Hb; destruct (Hnr _ _ Hb) as [Hb' | Hc];
        [ exact Hb' | discriminate Hc ]).
  - (* unit *)
    assert (Hrefine' : Θ ⨟ empty ⊢ᵣᵃ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_unit)
      by (eapply refine_primary_to_plain_split; eassumption).
    destruct (uskl_rho_unit_l_inv Hrho) as [[-> HΨρ] | Hleaf].
    + assert (HΨ'e : Ψ' [=] empty)
        by (exact (d_tags_skl_unit_inv (a_tags_sort_d_tags Htags))).
      assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
      assert (Hsz : size_pskl Pi + size_pskl P0
                      <= size_pskl Pi + size_pskl P0) by lia.
      destruct (a_solve_eq_cv_unit (Θ := Θ) (Δ := Δ)
                  Hsz HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine')
        as (Pa & Hsolve & Hprec).
      eapply solve_ext_nil; [ exact Hsolve | ].
      intros Δ' HS1 HS2 HS3. cbn [app].
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_partial_precise_delta_weaken_fresh;
            [ exact Hprec | simpl; clear; fsetdec | exact HS3 ]
        | clear - HΨae; fsetdec ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. cbn [app]. apply Hq. clear; fsetdec.
  - (* var: the target is [var α]; the Δ'-extension splits on where α
       lives — Θr-side (Δ' avoids it) vs binder-side (the primary
       refinement forces a hole-free P0, and solve preserves it) *)
    assert (Hrefine' : Θ ⨟ empty ⊢ᵣᵃ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (bskl_var_f α))
      by (eapply refine_primary_to_plain_split; eassumption).
    (* ⭐ [a_binds_tvar α Θ] is [ad_pat_consis__var]'s OWN premise.  It gives
       the RIGHT disjunct of the wf side condition when α is a rigid of [Θ]
       — which is the case a ∀ row produces, where α is the bound variable
       and is not in [Θw] at all — and the left one otherwise, by
       strengthening.  Either way nothing new is assumed. *)
    assert (Hbα : a_binds_tvar α Θw \/ binds α abind_tvar Θ).
    { match goal with Hb : a_binds_tvar α Θ |- _ =>
        destruct Hb as [Hrig | [Hfm | (τx & Hfd)]];
          [ right; exact Hrig
          | destruct (Hnr _ _ Hfm) as [Hb' | Hc];
              [ left; right; left; exact Hb' | discriminate Hc ]
          | destruct (Hnr _ _ Hfd) as [Hb' | Hc];
              [ left; right; right; exists τx; exact Hb' | discriminate Hc ] ]
      end. }
    destruct (uskl_rho_var_l_inv Hrho) as [[-> HΨρ] | Hleaf].
    + assert (HΨ'e : Ψ' [=] empty)
        by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
      assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
      assert (Hsz : size_pskl Pi + size_pskl P0
                      <= size_pskl Pi + size_pskl P0) by lia.
      eapply solve_ext_post_solve;
        (* ⚙️ [L] is IMPLICIT ([Set Implicit Arguments] — it is inferable from
           the avoid-set premise's type), so only [HLav] is passed. *)
        [ | exact (a_solve_eq_cv_var (Θ := Θ) (Θw := Θw) (Δ := Δ)
                     Hsz HwfΘ HwfΘ0 HwfΘw Hmon Hdefs
                     HwfPi HwfP0 Hκ Hbα Hdfresh Hpre Hrefine' HLav) ].
      intros Ξ0 κ' Pa Hsolve Hprec Δ' HS1 HS2 HS3.
      destruct (AtomSetProperties.In_dec α (dom Θr)) as [HinR | HninR].
      * (* Θr-side: Δ' avoids the target variable *)
        eapply ad_partial_precise_psi_cong;
          [ eapply ad_partial_precise_delta_weaken_fresh;
              [ exact Hprec
              | simpl; clear - HS2 HinR; fsetdec
              | exact HS3 ]
          | clear - HΨae; fsetdec ].
      * (* binder-side: the primary refinement forces a hole-free P0
           (the □-fill would have to BE the Δr-binder variable, which is
           not Θr-wf), and solve preserves it — precision is Δ-monotone *)
        assert (HnhP0d : pskl_no_hole P0).
        { eapply msubst_pskl_no_hole_inv with (κ := κ).
          eapply ad_refine_inh_deltar_var_rhs_no_hole;
            [ exact Hrefine | reflexivity | reflexivity | exact HninR ]. }
        assert (HnhPa : pskl_no_hole Pa)
          by (eapply a_solve_eq_no_hole_p0; [ exact Hsolve | exact HnhP0d ]).
        eapply ad_partial_precise_psi_cong;
          [ eapply ad_ppre_no_hole_subject_delta_mono;
              [ exact Hprec | apply msubst_pskl_no_hole; exact HnhPa
              | clear; fsetdec ]
          | clear - HΨae; fsetdec ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil; [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. cbn [app]. apply Hq. clear; fsetdec.
  - (* arrow: KEY continuation; CORE grid on size Pi + size P0 at the
       fixed arrow target, with the PRIMARY (Θr, Δr) refinement threaded
       through the recursion and ∀Δ' families out of every row. *)
    assert (HwfΘr2 := HwfΘr).
    assert (KEY : forall ψa1 ψa2 Ψρ1 Ψρ2,
      uskl_rho NM Θ Δρ Ψρ1 R1 ψa1 ->
      uskl_rho NM Θ Δρ Ψρ2 R2 ψa2 ->
      Ψρ [=] Ψρ1 `union` Ψρ2 ->
      a_tags_sort NM Ψ' (uskl_arrow ψa1 ψa2) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_arrow ψa1 ψa2) ->
      p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa (uskl_arrow ψa1 ψa2) Pi P0 Lav).
    { intros ψa1 ψa2 Ψρ1 Ψρ2 Hrho1 Hrho2 HΨρs Htags0 Hpre0.
      destruct (a_tags_sort_arrow_inv Htags0)
        as (Ψ'1 & Ψ'2 & Htags1 & Htags2 & HΨ'disj & HΨ's).
      (* branch tag-flow facts, fixed for the whole grid *)
      assert (Hft1 : Ψ1 [<=] Ψρ1 `union` Ψ'1).
      { pose proof (ad_pat_consis_ftag_sub Hconsis1) as Ha.
        pose proof (uskl_rho_ftag_sub Hrho1) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags1)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hft2 : Ψ2 [<=] Ψρ2 `union` Ψ'2).
      { pose proof (ad_pat_consis_ftag_sub Hconsis2) as Ha.
        pose proof (uskl_rho_ftag_sub Hrho2) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags2)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      (* the branch solved-tag split Ψa_k := Ψ_k ∩ Ψ'_k *)
      assert (Hbs1 : Ψ1 [<=] Ψρ1 `union` (Ψ1 ∩ Ψ'1))
        by (clear - Hft1; fsetdec).
      assert (Hbs2 : Ψ2 [<=] Ψρ2 `union` (Ψ2 ∩ Ψ'2))
        by (clear - Hft2; fsetdec).
      assert (Hba1 : Ψ1 ∩ Ψ'1 [<=] Ψ1) by (clear; fsetdec).
      assert (Hba2 : Ψ2 ∩ Ψ'2 [<=] Ψ2) by (clear; fsetdec).
      assert (Hint1 : Ψρ1 ∩ Ψ'1 [=] empty)
        by (clear - Hinter HΨρs HΨ's; fsetdec).
      assert (Hint2 : Ψρ2 ∩ Ψ'2 [=] empty)
        by (clear - Hinter HΨρs HΨ's; fsetdec).
      assert (HΨaeq : Ψa [=] (Ψ1 ∩ Ψ'1)
                        `union` (Ψ2 ∩ Ψ'2)).
      { clear - Hsubeq1 Hsubeq2 H Hsub Hinter HΨρs HΨ's Hft1 Hft2; fsetdec. }
      (* the P0=□ rows' target bound *)
      assert (HψaB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr ->
                ftvar_in_uskl (uskl_arrow ψa1 ψa2)
                  [<=] dom Θr `union` Δρ).
      { intros HQB.
        assert (HftR : ftvar_in_uskl (uskl_arrow R1 R2) [<=]
                  ftvar_in_bskl (bskl_arrow Q1 Q2) `union` dom Θr)
          by (eapply consis_subject_ftv_bag_bound;
                [ eapply ad_pat_consis__arrow; eassumption
                | exact HspΘ | exact Htvs | exact HwfΘr ]).
        assert (HftA : ftvar_in_uskl (uskl_arrow ψa1 ψa2) [<=]
                  ftvar_in_uskl (uskl_arrow R1 R2) `union` Δρ).
        { apply uskl_rho_ftv_target_bound with (NM := NM) (Θ := Θ)
            (Ψρ := Ψρ).
          eapply urho__arrow; [ exact Hrho1 | exact Hrho2 | exact HΨρs ]. }
        clear - HQB HftR HftA; fsetdec. }
      (* P0 = □ ⇒ Q synthesized ⇒ the consistency solves no tags *)
      assert (VACR : Θr ⨟ Δr ⊢ᵣᵃ bskl_hole ⊳ (bskl_arrow Q1 Q2) ->
                     Ψa [=] empty).
      { intros Hrh.
        pose proof (ad_refine_syn_hole_sskl Hrh eq_refl) as Hss.
        assert (HskQ1 : is_sskl Q1) by (inversion Hss; subst; assumption).
        assert (HskQ2 : is_sskl Q2) by (inversion Hss; subst; assumption).
        assert (HΨ1e : Ψ1 [=] empty)
          by (eapply ad_pat_consis_sskl_tags;
                [ exact Hconsis1 | exact HwfΘ | exact HskQ1 ]).
        assert (HΨ2e : Ψ2 [=] empty)
          by (eapply ad_pat_consis_sskl_tags;
                [ exact Hconsis2 | exact HwfΘ | exact HskQ2 ]).
        clear - Hsubeq2 H HΨ1e HΨ2e; fsetdec. }
      (* the repaired flexible-P0 discharge chain, Δ-universal via B2 *)
      (* ⚙️ (2026-08-05) the first premise WAS
         [flex_apart Θ0 Δρ β̂ (ψa1 → ψa2)].  At a FLEXIBLE P0 against an ARROW
         guess that predicate has exactly one satisfiable row — [fa_clean] —
         so its whole content is "the guess is Δρ-clean", and taking THAT
         directly is what frees the block.  The one row that still calls
         [FLEX] is SE-GhostL, where [Pi = ◇] and [ad_ppre__hole]'s own side
         condition supplies the cleanliness for nothing. *)
      assert (FLEX : forall β,
        (ftvar_in_uskl (uskl_arrow ψa1 ψa2)) ∩ Δρ [=] empty ->
        a_flex_tvar Θ0 β ->
        Θr ⨟ Δr ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β)))
             ⊳ (bskl_arrow Q1 Q2) ->
        Ψa [=] empty /\
        (* ⭐ the counterpart monotype's WELL-FORMEDNESS is new (2026-08-04):
           the repaired SE-FlexR's κ-extension sends each invented flexible
           to the monotype standing at that ghost's position, and
           [a_inc__flex] admits only a monotype wf IN THE TARGET.  It is not
           a new assumption — the counterpart is a consistency SUBJECT here,
           and consistency's own var/flex_l rows carry the binding.
           ⭐ And it is reported at [Θw], NOT at [Θ]: the block is emitted
           OUTSIDE every ∀ the induction has opened, so a payload naming a
           bound rigid would be ill-scoped.  See the derivation below. *)
        (exists τa1 τa2, mono_ptyp τa1 /\ mono_ptyp τa2 /\
           ψa1 = ptyp_to_uskl_syn τa1 /\ ψa2 = ptyp_to_uskl_syn τa2 /\
           a_wf_ptyp Θw (ptyp_arrow τa1 τa2)) /\
        forall Δx,
          Θ ⨟ Δx ⊢ (msubst_pskl κ (pskl_var_f β)) ⊑ᵖ[ empty ]
            (uskl_arrow ψa1 ψa2)).
      { intros β Hclean Hflxβ Hrefβ.
        simpl in Hclean.
        destruct (uskl_rho_clean_eq Hrho1 ltac:(clear - Hclean; solve_notin_auto))
          as [HeqR1 HΨρ1e].
        destruct (uskl_rho_clean_eq Hrho2 ltac:(clear - Hclean; solve_notin_auto))
          as [HeqR2 HΨρ2e].
        subst R1 R2.
        assert (Hml : mono_ptyp (msubst_lookup κ β))
          by (eapply a_inc_lookup_mono; eauto).
        simpl in Hrefβ.
        rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefβ.
        assert (Hmi : bskl_monoish (bskl_arrow Q1 Q2))
          by (eapply ad_refine_mono_paint_rhs_monoish;
                [ exact HwfΘr | exact Hrefβ | reflexivity | exact Hml ]).
        assert (Hmi1 : bskl_monoish Q1) by (inversion Hmi; assumption).
        assert (Hmi2 : bskl_monoish Q2) by (inversion Hmi; assumption).
        assert (Htsk1 : is_tskl ψa1) by (inversion Htags1; assumption).
        assert (Htsk2 : is_tskl ψa2) by (inversion Htags2; assumption).
        destruct (ad_pat_consis_monoish_counterpart Hconsis1 HwfΘ Htsk1 Hmi1)
          as (HΨ1e & τa1 & Hma1 & Heqψ1).
        destruct (ad_pat_consis_monoish_counterpart Hconsis2 HwfΘ Htsk2 Hmi2)
          as (HΨ2e & τa2 & Hma2 & Heqψ2).
        assert (Hcons' : Ψ ⨟ Θ ⊢ₛᵃ (uskl_arrow ψa1 ψa2)
                           ∼ (bskl_arrow Q1 Q2))
          by (eapply ad_pat_consis__arrow; eassumption).
        assert (Hrefβ' : Θ ⨟ empty ⊢ᵣᵃ (ptyp_to_bskl_syn (msubst_lookup κ β))
                           ⊳ (bskl_arrow Q1 Q2))
          by (eapply refine_primary_to_plain_split; eassumption).
        (* ⭐⭐ THE PAYLOAD-SCOPE DERIVATION (2026-08-04).  The κ-extension the
           repaired SE-FlexR needs is reported well-formed in [Θw], the FIXED
           context; here we only have [a_wf_ptyp Θ], and under a ∀ row [Θ] is
           [Θw] plus the bound rigids.  The counterpart is nevertheless apart
           from every one of them, and the reason is that BOTH bounds below are
           over the context's DEFINITIONS, never over its domain — a rigid
           binder carries no definition.  (Routing through [dom Θr] instead
           would FAIL: the [forall_syn_tagged] row puts its binder on the Θr
           side.  [dom Θw] is what both bounds actually land in.) *)
        assert (Hdefw : forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
                  α0 `in` dom Θw /\ ftvar_in_ptyp τ0 [<=] dom Θw).
        { intros α0 τ0 Hb.
          pose proof (Hdefs _ _ Hb) as Hbw.
          split; [ eapply binds_In; exact Hbw
                 | eapply a_wf_aenv_def_ftv_dom;
                     [ exact HwfΘw | exact Hbw ] ]. }
        assert (HftQ : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θw).
        { eapply ad_refine_mono_paint_ftv_bound;
            [ exact HwfΘ | exact Hrefβ' | reflexivity | exact Hml
            | exact (Hκw β Hflxβ) | exact Hdefw ]. }
        assert (Hftψ : ftvar_in_uskl (uskl_arrow ψa1 ψa2) [<=] dom Θw).
        { pose proof (consis_subject_ftv_defs_bound Hcons' Hdefw) as Ht.
          clear - Ht HftQ; fsetdec. }
        assert (Hwfar : a_wf_ptyp Θw (ptyp_arrow τa1 τa2)).
        { eapply a_wf_ptyp_mono_strengthen_dom;
            [ exact HwfΘ | exact Hmon | apply mono_ptyp__arrow; assumption
            | eapply ad_pat_consis_mono_subject_wf;
                [ exact Hcons' | rewrite Heqψ1, Heqψ2; reflexivity
                | apply mono_ptyp__arrow; assumption ]
            | ].
          rewrite Heqψ1, Heqψ2 in Hftψ. simpl in Hftψ |- *.
          rewrite !ftvar_in_uskl_ptyp_to_uskl_syn in Hftψ. exact Hftψ. }
        split; [ clear - Hsubeq2 H HΨ1e HΨ2e; fsetdec | ].
        split; [ exists τa1, τa2; repeat split; assumption | ].
        intros Δx.
        simpl.
        rewrite Heqψ1, Heqψ2.
        change (uskl_arrow (ptyp_to_uskl_syn τa1) (ptyp_to_uskl_syn τa2))
          with (ptyp_to_uskl_syn (ptyp_arrow τa1 τa2)).
        eapply mono_paint_paint_refine_consis_ppre with (Δr := empty);
          [ exact Hcons' | exact HwfΘ | rewrite Heqψ1, Heqψ2; reflexivity
          | apply mono_ptyp__arrow; assumption
          | clear; fsetdec | exact Hml | exact Hrefβ' ]. }
      (* ⭐⭐ THE ρ-DIRTY COMPANION OF [FLEX] (2026-08-05, the SolE-FlexR
         repair).  Everything the SE-FlexR row below actually needs — the
         counterpart monotype, its well-formedness and its scope — is
         available WITHOUT [FLEX]'s cleanliness step, hence without reading
         the [flex_apart] premise at all.

         [FLEX] argues "the guess is Δρ-CLEAN, so ρ is the identity on it, so
         the consistency SUBJECT *is* the guess".  That detour existed because
         the OLD row answered a flexible counterpart with the FLEXIBLE, and
         the obligation then compared the whole guess against a κ-image — a
         whole-object comparison with no position-wise escape.  The repaired
         row answers [guess^TY(Pi)], so we may instead read the monotype off
         the SUBJECT and lift it to the GUESS: ρ is CONGRUENT at every
         constructor and non-trivial only at a bare VARIABLE ([urho__leaf]),
         and a bare variable is itself a monotype ([uskl_rho_mono_target]).

         The one thing that does NOT survive is [Θw]-scope of the whole guess:
         a ρ-replaced variable is a rigid the fixed [Θw] need not have.  It
         survives up to [Δρ ⊆ Δ], which is exactly the slack
         [a_guess_ty_witness_mono_gen] takes — and at the only positions that
         invent a payload, [Pi]'s HOLES, [ad_ppre__hole] closes the gap
         ([ppre_hole_payload_wf]). *)
      assert (FLEXMONO : forall β,
        a_flex_tvar Θ0 β ->
        Θr ⨟ Δr ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β)))
             ⊳ (bskl_arrow Q1 Q2) ->
        Ψa [=] empty /\
        (exists τa1 τa2, mono_ptyp τa1 /\ mono_ptyp τa2 /\
           ψa1 = ptyp_to_uskl_syn τa1 /\ ψa2 = ptyp_to_uskl_syn τa2 /\
           a_wf_ptyp Θ (ptyp_arrow τa1 τa2) /\
           ftvar_in_ptyp (ptyp_arrow τa1 τa2) [<=] dom Θw `union` Δ)).
      { intros β Hflxβ Hrefβ.
        assert (Hml : mono_ptyp (msubst_lookup κ β))
          by (eapply a_inc_lookup_mono; eauto).
        simpl in Hrefβ.
        rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefβ.
        assert (Hmi : bskl_monoish (bskl_arrow Q1 Q2))
          by (eapply ad_refine_mono_paint_rhs_monoish;
                [ exact HwfΘr | exact Hrefβ | reflexivity | exact Hml ]).
        assert (Hmi1 : bskl_monoish Q1) by (inversion Hmi; assumption).
        assert (Hmi2 : bskl_monoish Q2) by (inversion Hmi; assumption).
        (* the SUBJECT is decorated because the GUESS is *)
        assert (Htsk1 : is_tskl R1)
          by (eapply uskl_rho_is_tskl;
                [ exact Hrho1 | inversion Htags1; assumption ]).
        assert (Htsk2 : is_tskl R2)
          by (eapply uskl_rho_is_tskl;
                [ exact Hrho2 | inversion Htags2; assumption ]).
        destruct (ad_pat_consis_monoish_counterpart Hconsis1 HwfΘ Htsk1 Hmi1)
          as (HΨ1e & τ1' & Hm1' & HeqR1).
        destruct (ad_pat_consis_monoish_counterpart Hconsis2 HwfΘ Htsk2 Hmi2)
          as (HΨ2e & τ2' & Hm2' & HeqR2).
        (* …and the GUESS is a mono paint because its ρ-IMAGE is *)
        destruct (uskl_rho_mono_target Hrho1 HeqR1 Hm1')
          as (τa1 & Heq1 & Hma1).
        destruct (uskl_rho_mono_target Hrho2 HeqR2 Hm2')
          as (τa2 & Heq2 & Hma2).
        assert (Hcons' : Ψ ⨟ Θ ⊢ₛᵃ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2))
          by (eapply ad_pat_consis__arrow; eassumption).
        assert (Hrefβ' : Θ ⨟ empty ⊢ᵣᵃ
                  (ptyp_to_bskl_syn (msubst_lookup κ β)) ⊳ (bskl_arrow Q1 Q2))
          by (eapply refine_primary_to_plain_split; eassumption).
        (* the SUBJECT's monotype is well-formed where the consistency lives *)
        assert (Hwfsub : a_wf_ptyp Θ (ptyp_arrow τ1' τ2')).
        { eapply ad_pat_consis_mono_subject_wf;
            [ exact Hcons' | rewrite HeqR1, HeqR2; reflexivity
            | apply mono_ptyp__arrow; assumption ]. }
        (* both bounds below are over the context's DEFINITIONS, never over a
           domain — a rigid binder carries no definition (see [FLEX]) *)
        assert (Hdefw : forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
                  α0 `in` dom Θw /\ ftvar_in_ptyp τ0 [<=] dom Θw).
        { intros α0 τ0 Hb.
          pose proof (Hdefs _ _ Hb) as Hbw.
          split; [ eapply binds_In; exact Hbw
                 | eapply a_wf_aenv_def_ftv_dom;
                     [ exact HwfΘw | exact Hbw ] ]. }
        assert (HftQ : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θw).
        { eapply ad_refine_mono_paint_ftv_bound;
            [ exact HwfΘ | exact Hrefβ' | reflexivity | exact Hml
            | exact (Hκw β Hflxβ) | exact Hdefw ]. }
        assert (HftR : (ftvar_in_uskl R1) `union` (ftvar_in_uskl R2)
                       [<=] dom Θw).
        { pose proof (consis_subject_ftv_defs_bound Hcons' Hdefw) as Ht.
          cbn [ftvar_in_uskl ftvar_in_bskl] in Ht, HftQ.
          clear - Ht HftQ; fsetdec. }
        (* …and the GUESS adds only ρ-REPLACED variables on top of it *)
        assert (Hftar : (ftvar_in_ptyp τa1) `union` (ftvar_in_ptyp τa2)
                        [<=] (ftvar_in_uskl R1) `union` (ftvar_in_uskl R2)
                             `union` Δρ).
        { pose proof (uskl_rho_ftv_target_bound
                        (urho__arrow Hrho1 Hrho2 HΨρs)) as Hb.
          rewrite Heq1, Heq2 in Hb.
          cbn [ftvar_in_uskl] in Hb.
          rewrite !ftvar_in_uskl_ptyp_to_uskl_syn in Hb.
          clear - Hb; fsetdec. }
        assert (Hwfar : a_wf_ptyp Θ (ptyp_arrow τa1 τa2)).
        { apply mono_ptyp_wf; [ apply mono_ptyp__arrow; assumption | ].
          intros α0 Hα0. cbn [ftvar_in_ptyp] in Hα0.
          destruct (mem α0 Δρ) eqn:Em;
            [ apply mem_iff in Em; rename Em into Hin
            | apply not_mem_iff in Em; rename Em into Hnin ].
          - (* a ρ-replaced variable is a RIGID of Θ *)
            destruct (Hfresh α0 Hin) as (Hb & _ & _). left; exact Hb.
          - (* otherwise it is one of the SUBJECT's, which is wf in Θ *)
            eapply a_wf_ptyp_ftv_tvarish; [ exact Hwfsub | ].
            assert (Hin' : α0 `in` (ftvar_in_uskl R1) `union`
                                   (ftvar_in_uskl R2))
              by (clear - Hftar Hα0 Hnin; fsetdec).
            rewrite HeqR1, HeqR2 in Hin'.
            rewrite !ftvar_in_uskl_ptyp_to_uskl_syn in Hin'.
            cbn [ftvar_in_ptyp]. clear - Hin'; fsetdec. }
        split; [ clear - Hsubeq2 H HΨ1e HΨ2e; fsetdec | ].
        exists τa1, τa2. repeat split; try assumption.
        cbn [ftvar_in_ptyp]. clear - Hftar HftR Hdelta; fsetdec. }
      (* CORE: the grid, by strong induction on the sizes *)
      assert (CORE : forall n Pi P0 Ψi,
        size_pskl Pi + size_pskl P0 <= n ->
        Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
        Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
        (forall α, α `in` Δρ ->
           α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
        Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_arrow ψa1 ψa2) ->
        Θr ⨟ Δr ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0))
              ⊳ (bskl_arrow Q1 Q2) ->
        p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa (uskl_arrow ψa1 ψa2) Pi P0 Lav).
      { intros n; induction n as [ | n IHn ];
          intros Pi0 P00 Ψi0 Hn HwfPi0 HwfP00 Hapart0 Hpre1
            Hrefine1.
        { pose proof (size_pskl_min Pi0); pose proof (size_pskl_min P00);
          lia. }
        destruct Pi0 as [ | nb | β | Pi1 Pi2 | Pib | | Pi' ].
        - (* Pi = unit: no precision into an arrow *)
          simpl in Hpre1. inversion Hpre1.
        - (* Pi = var_b *) inversion HwfPi0.
        - (* Pi = var β: SE-Var; a mono-paint subject forces Ψ' = ∅ *)
          assert (HΨ'e : Ψ' [=] empty).
          { eapply ad_ppre_mono_subject_target_tags_empty
              with (τ := msubst_lookup κ β);
              [ exact HwfΘ | exact Hpre1 | reflexivity
              | eapply a_inc_lookup_mono; eauto
              | exact (a_tags_sort_d_tags Htags0) ]. }
          assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
          eapply solve_ext_nil with (Pa := (pskl_var_f β)); [ apply a_solve_eq__var | ].
          intros Δ' HS1 HS2 HS3.
          eapply ad_partial_precise_psi_cong;
            [ eapply ad_ppre_no_hole_subject_delta_mono;
                [ exact Hpre1
                | apply msubst_pskl_no_hole; simpl; exact I
                | clear; fsetdec ]
            | clear - HΨae; fsetdec ].
        - (* Pi = arrow Pi1 Pi2 *)
          assert (HwfPi1 : Θ0 ⨟ empty ⊢ₚₛᵃ Pi1)
            by (inversion HwfPi0; assumption).
          assert (HwfPi2 : Θ0 ⨟ empty ⊢ₚₛᵃ Pi2)
            by (inversion HwfPi0; assumption).
          destruct P00 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          + (* P0 = unit: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = var_b *) inversion HwfP00.
          + (* P0 = var β: rigid absurd / flexible = the repaired subcase *)
            inversion HwfP00; subst;
            match goal with Hor : _ \/ a_binds_tvar β _ |- _ =>
              destruct Hor as [Hemp | Habt] end;
              [ clear - Hemp; fsetdec | ].
            destruct Habt as [Hrig | Hflx].
            * (* rigid: no refinement into an arrow *)
              exfalso.
              assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
                by (eapply msubst_pskl_tvar_id;
                    [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
              rewrite Hmid in Hrefine1. simpl in Hrefine1.
              eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hrefine1);
                [ intros x b Hb; eapply aenv_split_sub_r;
                    [ exact HspΘ | exact Hb ]
                | apply a_wf_aenv_uniq; exact HwfΘ
                | eapply a_inc_binds_tvar; eauto
                | intros β0 Hcc; discriminate Hcc ].
            * (* flexible: SE-FlexR + the discharge chain *)
              (* ⭐⭐ [FLEXMONO], not [FLEX] (2026-08-05): this row needs the
                 counterpart monotype and its SCOPE, and neither needs the
                 [flex_apart] cleanliness step.  See the block's header. *)
              destruct (FLEXMONO β Hflx Hrefine1)
                as (HΨae
                    & (τa1 & τa2 & Hma1 & Hma2 & Heq1 & Heq2 & Hwfar
                       & Hftar)).
              assert (HΨie : Ψi0 [=] empty).
              { rewrite Heq1, Heq2 in Hpre1.
                eapply ad_ppre_mono_tags_empty
                  with (τ := ptyp_arrow τa1 τa2);
                  [ exact HwfΘ | exact Hpre1 | reflexivity
                  | apply mono_ptyp__arrow; assumption ]. }
              (* ⭐ SE-FlexR, REPAIRED.  The output is [guess^TY(P_i)] — the
                 pattern the collection has accumulated — not the flexible,
                 so the witness is the guess and the κ-extension is the one
                 [a_guess_ty_witness_mono] builds alongside it.  The old
                 proof went the other way: its witness was [β̂] and the
                 obligation was discharged by [FLEX]'s [Hqf], the mono-paint
                 bridge through the refinement.  Here the precision
                 obligation IS the witness's own output — [Hqf] survives only
                 as the source of the counterpart monotype [τa1 → τa2]. *)
              assert (Hmar : mono_ptyp (ptyp_arrow τa1 τa2))
                by (apply mono_ptyp__arrow; assumption).
              assert (Hpre1' : Θ ⨟ Δ ⊢ (msubst_pskl κ (pskl_arrow Pi1 Pi2))
                        ⊑ᵖ[ Ψi0 ] (ptyp_to_uskl_syn (ptyp_arrow τa1 τa2))).
              { change (ptyp_to_uskl_syn (ptyp_arrow τa1 τa2))
                  with (uskl_arrow (ptyp_to_uskl_syn τa1)
                                   (ptyp_to_uskl_syn τa2)).
                rewrite <- Heq1, <- Heq2. exact Hpre1. }
              (* ⭐⭐ THE PAYLOAD SCOPE IS POSITION-WISE (2026-08-05).  The
                 witness reports its payloads well-formed in [Θw], the context
                 that stays FIXED under binders — and a ρ-DIRTY guess is not
                 [Θw]-scoped: a ρ-replaced variable is a rigid [Θw] need not
                 have.  It IS scoped up to [Δρ ⊆ Δ], and that is all the
                 general witness asks, because the flexibles [guess^TY]
                 invents sit exactly at [Pi]'s HOLES and [ad_ppre__hole]'s own
                 side condition keeps the target facing a hole apart from Δ
                 ([ppre_hole_payload_wf]). *)
              destruct (@a_guess_ty_witness_mono_gen
                          (size_pskl (pskl_arrow Pi1 Pi2)) Θ0 Θ Θw κ Δ Ψi0
                          (ptyp_arrow τa1 τa2) (pskl_arrow Pi1 Pi2)
                          ltac:(reflexivity) HwfΘ HwfΘw Hmon Hdefs
                          HwfPi0 Hmar Hwfar Hftar Hpre1' Lav)
                as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
              exists Ξg, (ptyp_to_pskl Ag), κg.
              split; [ apply a_solve_eq__flex_r;
                         [ exact Hflx
                         | split; [ eapply a_wf_pskl_lc; exact HwfPi0
                                  | intros Hf; inversion Hf ]
                         | apply nonghost_pskl__arrow
                         | apply Hgu; exact HLav ] | ].
              split; [ exact Hfmg | ].
              split; [ exact Hug | ].
              split; [ exact Hkg | ].
              split; [ exact Hfrg | ].
              split; [ exact HFg | ].
              intros Δ' HS1 HS2 HS3.
              rewrite Heq1, Heq2.
              change (uskl_arrow (ptyp_to_uskl_syn τa1)
                                 (ptyp_to_uskl_syn τa2))
                with (ptyp_to_uskl_syn (ptyp_arrow τa1 τa2)).
              (* ⭐ NO Δ-freshness needed: [guess^TY]'s output is a PAINT,
                 hence HOLE-FREE, and precision with a hole-free subject is
                 Δ-MONOTONE.  (The old proof had to be Δ-universal instead,
                 via FLEX's [Hqf] — the flexible it returned carried no such
                 structure.)  This is the same reason the repair leaves
                 [a_solve_eq_no_hole_p0] true. *)
              eapply ad_partial_precise_psi_cong;
                [ eapply ad_ppre_no_hole_subject_delta_mono;
                    [ exact Hqg
                    | apply msubst_pskl_no_hole; apply ptyp_to_pskl_no_hole
                    | clear; fsetdec ]
                | clear - HΨie HΨae; fsetdec ].
          + (* P0 = arrow P01 P02: componentwise via the branch main IHs *)
            assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01)
              by (inversion HwfP00; assumption).
            assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02)
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            destruct (ad_refine_arrow_arrow_inv Hrefine1) as [Hrb1 Hrb2].
            simpl in Hpre1.
            destruct (ad_ppre_arrow_arrow_inv Hpre1)
              as (Ψib1 & Ψib2 & Hpb1 & Hpb2 & HΨis).
            assert (Hsubk1 : Ψib1 `union` (Ψ1 ∩ Ψ'1)
                               [<=] Ψ'1).
            { assert (Hts : Ψib1 [<=] Ψ'1)
                by (eapply ad_partial_precise_tags_sub;
                      [ exact HwfΘ | exact Hpb1
                      | exact (a_tags_sort_d_tags Htags1) ]).
              clear - Hts; fsetdec. }
            assert (Hsubk2 : Ψib2 `union` (Ψ2 ∩ Ψ'2)
                               [<=] Ψ'2).
            { assert (Hts : Ψib2 [<=] Ψ'2)
                by (eapply ad_partial_precise_tags_sub;
                      [ exact HwfΘ | exact Hpb2
                      | exact (a_tags_sort_d_tags Htags2) ]).
              clear - Hts; fsetdec. }
            assert (Hapart1 : forall α, α `in` Δρ ->
                      α `notin` pskl_shielded_ftv (msubst_pskl κ Pi1)).
            { intros α0 HX0; pose proof (Hapart0 α0 HX0) as Hs0;
              simpl in Hs0; clear - Hs0; fsetdec. }
            assert (Hapart2 : forall α, α `in` Δρ ->
                      α `notin` pskl_shielded_ftv (msubst_pskl κ Pi2)).
            { intros α0 HX0; pose proof (Hapart0 α0 HX0) as Hs0;
              simpl in Hs0; clear - Hs0; fsetdec. }
            (* ⭐ THE TWO BRANCHES' κ-EXTENSIONS MERGE.  [SE-Arrow] THREADS —
               its second premise runs at [Ξ1 ++ Θ0] — but both branches come
               out of induction hypotheses stated at [Θ0], so the second
               branch's solve is PUSHED UNDER the first branch's block by
               [a_solve_eq_weaken_flex_block].  The avoid-sets are what makes
               that legal (the second block dodges the first, so the guess
               can be replayed at the enlarged context) and what keeps each
               branch's extension invisible to the other's output. *)
            destruct (IHHconsis1 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ1 Ψ'1 _ _
                        ψa1 Pi1 P01
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 Hmon Hnr HwfPi1 HwfP01 Hκ Hκw Hrho1 Htags1
                        Hsubk1 Hint1 Hfresh Hdelta Hapart1 Hdfresh Hpb1 Hbs1 Hba1 Hrb1
                        (Lav `union` ftvar_in_pskl Pi1
                           `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01
                           `union` ftvar_in_pskl P02)
                        ltac:(clear - HLav; solve_notin_auto))
              as (Ξ1 & Pa1 & κa & Hs1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hq1).
            destruct (IHHconsis2 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ2 Ψ'2 _ _
                        ψa2 Pi2 P02
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 Hmon Hnr HwfPi2 HwfP02 Hκ Hκw Hrho2 Htags2
                        Hsubk2 Hint2 Hfresh Hdelta Hapart2 Hdfresh Hpb2 Hbs2 Hba2 Hrb2
                        (Lav `union` ftvar_in_pskl Pi1
                           `union` ftvar_in_pskl Pi2
                           `union` ftvar_in_pskl P01
                           `union` ftvar_in_pskl P02
                           `union` dom Ξ1)
                        ltac:(clear - HLav; solve_notin_auto))
              as (Ξ2 & Pa2 & κb & Hs2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hq2).
            assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
            assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
            assert (HPa1 : ftvar_in_pskl Pa1
                     [<=] ftvar_in_pskl Pi1 `union` ftvar_in_pskl P01
                            `union` dom Ξ1)
              by (eapply a_solve_eq_ftv; exact Hs1).
            assert (HPa2 : ftvar_in_pskl Pa2
                     [<=] ftvar_in_pskl Pi2 `union` ftvar_in_pskl P02
                            `union` dom Ξ2)
              by (eapply a_solve_eq_ftv; exact Hs2).
            assert (HΞ12 : forall x, x `in` dom Ξ1 -> x `notin` dom Ξ2).
            { intros x Hx Hc. specialize (Hfr2 x Hc). clear - Hfr2 Hx; fsetdec. }
            assert (Hdisj : disjoint Ξ2 Ξ1).
            { unfold disjoint. intros x Hx.
              assert (Hin1 : x `in` dom Ξ1) by (clear - Hx; fsetdec).
              specialize (HΞ12 x Hin1). clear - Hx HΞ12; fsetdec. }
            assert (Hs2' : (Ξ1 ++ Θ0) ⊢ₑ Pi2 ∼ P02 ⤳ Ξ2 ⨾ Pa2).
            { eapply a_solve_eq_weaken_flex_block;
                [ exact Hs2 | exact Hfm1
                | intros x Hx; specialize (Hfr1 x Hx);
                  pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd;
                  clear - Hfr1 Hd HLav; fsetdec
                | intros x Hx; specialize (Hfr1 x Hx); clear - Hfr1; fsetdec
                | intros x Hx; pose proof (HΞ12 x Hx) as Hne;
                  specialize (Hfr1 x Hx); clear - Hfr1 Hne HPa2; fsetdec
                | exact HΞ12 ]. }
            assert (Heq1 : msubst_pskl (nil ++ κb ++ (κa ++ κ)) Pa1
                           = msubst_pskl (nil ++ (κa ++ κ)) Pa1).
            { apply msubst_pskl_mid_skip. intros x Hx.
              assert (Hin : x `in` dom Ξ2) by (clear - Hx Hdκb; fsetdec).
              specialize (Hfr2 x Hin). clear - Hfr2 HPa1; fsetdec. }
            cbn [app] in Heq1.
            assert (Heq2 : msubst_pskl (κb ++ κa ++ κ) Pa2
                           = msubst_pskl (κb ++ κ) Pa2).
            { apply msubst_pskl_mid_skip. intros x Hx.
              assert (Hin : x `in` dom Ξ1) by (clear - Hx Hdκa; fsetdec).
              pose proof (HΞ12 x Hin) as Hne.
              specialize (Hfr1 x Hin). clear - Hfr1 Hne HPa2; fsetdec. }
            exists (Ξ2 ++ Ξ1), (pskl_arrow Pa1 Pa2), (κb ++ κa).
            split; [ apply a_solve_eq__arrow; [ exact Hs1 | exact Hs2' ] | ].
            split; [ apply all_flex_mono_app; assumption | ].
            split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
            split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
            split; [ intros x Hx; rewrite dom_app in Hx;
                     destruct (union_1 Hx) as [Hin2 | Hin1];
                       [ specialize (Hfr2 x Hin2); clear - Hfr2; fsetdec
                       | specialize (Hfr1 x Hin1); clear - Hfr1; fsetdec ] | ].
            split; [ apply Forall_app; split; assumption | ].
            intros Δ' HS1 HS2 HS3.
            rewrite list_app_assoc. cbn [msubst_pskl].
            rewrite Heq1, Heq2.
            eapply ad_ppre__arrow;
              [ exact (Hq1 Δ' HS1 HS2 HS3) | exact (Hq2 Δ' HS1 HS2 HS3) | ].
            clear - HΨis HΨaeq; fsetdec.
          + (* P0 = all_syn: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = □: SE-VacuousR *)
            simpl in Hrefine1.
            assert (HΨae : Ψa [=] empty) by (apply VACR; exact Hrefine1).
            assert (HQB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr).
            { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine1).
              simpl in Ht. simpl. clear - Ht; fsetdec. }
            eapply solve_ext_nil with (Pa := (pskl_arrow Pi1 Pi2));
              [ apply a_solve_eq__hole_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨae; fsetdec ].
          + (* P0 = ∀◇.P0': GuardedGhost-right + same-node recursion *)
            assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            inversion Hrefine1; subst.
            match goal with
            | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _
              |- _ =>
              eapply p6cv_step;
                [ | exact (IHn (pskl_arrow Pi1 Pi2) P0' Ψi0
                             ltac:(simpl in Hn; simpl; lia)
                             HwfPi0 HwfP0' Hapart0
                             Hpre1 Hin) ]
            end.
            intros Ξ0 Pa0 Hs0. apply a_solve_eq__tophole_r_guarded;
              [ apply guarded_pskl__arrow;
                  [ eapply a_wf_pskl_lc; exact HwfPi1
                  | eapply a_wf_pskl_lc; exact HwfPi2 ]
              | exact Hs0 ].
        - (* Pi = all_syn: no precision into an arrow *)
          simpl in Hpre1. inversion Hpre1.
        - (* Pi = □ *)
          simpl in Hpre1.
          assert (HΨie : Ψi0 [=] empty) by (inversion Hpre1; assumption).
          assert (Hhd : Δ ∩
                    (ftvar_in_uskl (uskl_arrow ψa1 ψa2)) [=] empty)
            by (inversion Hpre1; assumption).
          simpl in Hhd.
          destruct P00 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          + (* P0 = unit: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = var_b *) inversion HwfP00.
          + (* P0 = var β: rigid absurd / flexible via SE-GhostL + FLEX *)
            inversion HwfP00; subst;
            match goal with Hor : _ \/ a_binds_tvar β _ |- _ =>
              destruct Hor as [Hemp | Habt] end;
              [ clear - Hemp; fsetdec | ].
            destruct Habt as [Hrig | Hflx].
            * exfalso.
              assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
                by (eapply msubst_pskl_tvar_id;
                    [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
              rewrite Hmid in Hrefine1. simpl in Hrefine1.
              eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hrefine1);
                [ intros x b Hb; eapply aenv_split_sub_r;
                    [ exact HspΘ | exact Hb ]
                | apply a_wf_aenv_uniq; exact HwfΘ
                | eapply a_inc_binds_tvar; eauto
                | intros β0 Hcc; discriminate Hcc ].
            * (* ⭐ the cleanliness [FLEX] wants is FREE here: the subject is
                 [◇], so [Hpre1] IS [ad_ppre__hole] and [Hhd] is its own side
                 condition — with [Δρ ⊆ Δ] that is exactly the premise.
                 ⚠️ NAMED, not [ltac:(… solve_notin_auto)]: a premise slot runs its
                 tactic against a goal whose set arguments are still evars. *)
              assert (Hclean0 : (ftvar_in_uskl (uskl_arrow ψa1 ψa2))
                                ∩ Δρ [=] empty)
                by (cbn [ftvar_in_uskl]; clear - Hhd Hdelta; fsetdec).
              destruct (FLEX β Hclean0 Hflx Hrefine1) as (HΨae & _ & Hqf).
              eapply solve_ext_nil with (Pa := (pskl_var_f β)); [ apply a_solve_eq__hole_l | ].
              intros Δ' HS1 HS2 HS3.
              eapply ad_partial_precise_psi_cong;
                [ exact (Hqf (Δ `union` Δ'))
                | clear - HΨie HΨae; fsetdec ].
          + (* P0 = arrow: □-precisions per branch + branch main IHs *)
            assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01)
              by (inversion HwfP00; assumption).
            assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02)
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            destruct (ad_refine_arrow_arrow_inv Hrefine1) as [Hrb1 Hrb2].
            assert (Hp01 : Θ ⨟ Δ ⊢ msubst_pskl κ pskl_hole
                             ⊑ᵖ[ empty ] ψa1).
            { simpl. apply ad_ppre__hole;
                [ clear; fsetdec | clear - Hhd; fsetdec ]. }
            assert (Hp02 : Θ ⨟ Δ ⊢ msubst_pskl κ pskl_hole
                             ⊑ᵖ[ empty ] ψa2).
            { simpl. apply ad_ppre__hole;
                [ clear; fsetdec | clear - Hhd; fsetdec ]. }
            assert (Hsubk01 : empty `union` (Ψ1 ∩ Ψ'1)
                                [<=] Ψ'1) by (clear; fsetdec).
            assert (Hsubk02 : empty `union` (Ψ2 ∩ Ψ'2)
                                [<=] Ψ'2) by (clear; fsetdec).
            (* ⚙️ NO merge here: both branches have a GHOST subject, and
               [a_solve_eq_hole_subject_inv] pins their blocks to [nil] —
               which is exactly what the [nonghost_pskl] side condition on
               SE-FlexR buys (docs/PAPER-GAPS.md finding 2).  Their aligned
               extensions are then [nil] too. *)
            destruct (IHHconsis1 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ1 Ψ'1 _ _
                        ψa1 pskl_hole P01
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 Hmon Hnr
                        ltac:(apply a_wf_pskl__hole) HwfP01
                        Hκ Hκw
                        Hrho1 Htags1 Hsubk01 Hint1 Hfresh Hdelta
                        ltac:(intros α0 HX0; simpl; auto)
                        Hdfresh Hp01 Hbs1 Hba1 Hrb1 Lav HLav)
              as (Ξ1 & Pa1 & κa & Hs1 & _ & _ & Hk1 & _ & _ & Hq1).
            destruct (IHHconsis2 NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr Ψρ2 Ψ'2 _ _
                        ψa2 pskl_hole P02
                        HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                        HwfΘ HwfΘ0 Hmon Hnr
                        ltac:(apply a_wf_pskl__hole) HwfP02
                        Hκ Hκw
                        Hrho2 Htags2 Hsubk02 Hint2 Hfresh Hdelta
                        ltac:(intros α0 HX0; simpl; auto)
                        Hdfresh Hp02 Hbs2 Hba2 Hrb2 Lav HLav)
              as (Ξ2 & Pa2 & κb & Hs2 & _ & _ & Hk2 & _ & _ & Hq2).
            destruct (a_solve_eq_hole_subject_inv Hs1) as [HΞ1e HPa1e].
            destruct (a_solve_eq_hole_subject_inv Hs2) as [HΞ2e HPa2e].
            subst Ξ1 Pa1 Ξ2 Pa2.
            destruct κa as [ | ? ? ];
              [ | unfold keys in Hk1; simpl in Hk1; discriminate ].
            destruct κb as [ | ? ? ];
              [ | unfold keys in Hk2; simpl in Hk2; discriminate ].
            eapply solve_ext_nil with (Pa := (pskl_arrow P01 P02));
              [ apply a_solve_eq__hole_l | ].
            intros Δ' HS1 HS2 HS3.
            cbn [app msubst_pskl]. eapply ad_ppre__arrow;
              [ exact (Hq1 Δ' HS1 HS2 HS3) | exact (Hq2 Δ' HS1 HS2 HS3) | ].
            clear - HΨie HΨaeq; fsetdec.
          + (* P0 = all_syn: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = □: SE-VacuousR *)
            simpl in Hrefine1.
            assert (HΨae : Ψa [=] empty) by (apply VACR; exact Hrefine1).
            assert (HQB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr).
            { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine1).
              simpl in Ht. simpl. clear - Ht; fsetdec. }
            eapply solve_ext_nil with (Pa := pskl_hole); [ apply a_solve_eq__hole_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨae; fsetdec ].
          + (* P0 = ∀◇.P0': SE-GhostL + same-node recursion at (□, P0') *)
            assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            inversion Hrefine1; subst.
            match goal with
            | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _
              |- _ =>
              destruct (IHn pskl_hole P0' Ψi0
                          ltac:(simpl in Hn; simpl; lia)
                          ltac:(apply a_wf_pskl__hole) HwfP0'
                          ltac:(intros α0 HX0; simpl; auto)
                          Hpre1 Hin)
                as (Ξ' & Pa' & κ' & Hs' & _ & _ & Hk' & _ & _ & Hq')
            end.
            destruct (a_solve_eq_hole_subject_inv Hs') as [HΞ'e HPa'e].
            subst Ξ' Pa'.
            destruct κ' as [ | ? ? ];
              [ | unfold keys in Hk'; simpl in Hk'; discriminate ].
            eapply solve_ext_nil with (Pa := (pskl_tophole P0'));
              [ apply a_solve_eq__hole_l | ].
            intros Δ' HS1 HS2 HS3.
            cbn [app msubst_pskl]. apply ad_ppre__tophole_remove.
            exact (Hq' Δ' HS1 HS2 HS3).
        - (* Pi = ∀◇.Pi' *)
          assert (HgPi' : guarded_pskl Pi')
            by (inversion HwfPi0; assumption).
          assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi')
            by (inversion HwfPi0; assumption).
          simpl in Hpre1.
          inversion Hpre1; subst.
          match goal with
          | Hp' : _ ⨟ _ ⊢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] uskl_arrow ψa1 ψa2
            |- _ => rename Hp' into Hpre'
          end.
          assert (Hapart' : forall α, α `in` Δρ ->
                    α `notin` pskl_shielded_ftv (msubst_pskl κ Pi')).
          { intros α0 HX0.
            pose proof (Hapart0 α0 HX0) as Hsh0. simpl in Hsh0.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi')).
            fsetdec. }
          destruct P00 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          + (* P0 = unit: GhostGuarded *)
            eapply p6cv_step;
              [ intros Ξ0 Pa0 Hs; apply a_solve_eq__tophole_l_guarded;
                  [ apply guarded_pskl__unit | exact Hs ]
              | exact (IHn Pi' pskl_unit Ψi0
                        ltac:(simpl in Hn; simpl; lia)
                        HwfPi' HwfP00 Hapart' Hpre' Hrefine1) ].
          + (* P0 = var_b *) inversion HwfP00.
          + (* P0 = var: GhostGuarded (a var is guarded) *)
            eapply p6cv_step;
              [ intros Ξ0 Pa0 Hs; apply a_solve_eq__tophole_l_guarded;
                  [ apply guarded_pskl__var | exact Hs ]
              | exact (IHn Pi' (pskl_var_f β) Ψi0
                        ltac:(simpl in Hn; simpl; lia)
                        HwfPi' HwfP00 Hapart' Hpre' Hrefine1) ].
          + (* P0 = arrow: GhostGuarded *)
            assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01)
              by (inversion HwfP00; assumption).
            assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02)
              by (inversion HwfP00; assumption).
            eapply p6cv_step;
              [ intros Ξ0 Pa0 Hs; apply a_solve_eq__tophole_l_guarded;
                  [ apply guarded_pskl__arrow;
                      [ eapply a_wf_pskl_lc; exact HwfP01
                      | eapply a_wf_pskl_lc; exact HwfP02 ]
                  | exact Hs ]
              | exact (IHn Pi' (pskl_arrow P01 P02) Ψi0
                        ltac:(simpl in Hn; simpl; lia)
                        HwfPi' HwfP00 Hapart' Hpre' Hrefine1) ].
          + (* P0 = all_syn: refinement absurd *)
            simpl in Hrefine1. inversion Hrefine1.
          + (* P0 = □: SE-VacuousR *)
            simpl in Hrefine1.
            assert (HΨae : Ψa [=] empty) by (apply VACR; exact Hrefine1).
            assert (HQB : ftvar_in_bskl (bskl_arrow Q1 Q2) [<=] dom Θr).
            { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine1).
              simpl in Ht. simpl. clear - Ht; fsetdec. }
            eapply solve_ext_nil with (Pa := (pskl_tophole Pi'));
              [ apply a_solve_eq__hole_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨae; fsetdec ].
          + (* P0 = ∀◇.P0': SE-UnivGhost *)
            assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
              by (inversion HwfP00; assumption).
            simpl in Hrefine1.
            inversion Hrefine1; subst.
            match goal with
            | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ _
              |- _ =>
              apply (p6cv_tophole_both
                       (IHn Pi' P0' Ψi0
                          ltac:(simpl in Hn; lia)
                          HwfPi' HwfP0' Hapart'
                          Hpre' Hin))
            end. }
      assert (Hsz : size_pskl Pi + size_pskl P0
                      <= size_pskl Pi + size_pskl P0) by lia.
      eapply CORE;
        [ exact Hsz | exact HwfPi | exact HwfP0 | exact Hapart
        | exact Hpre0 | exact Hrefine ]. }
    destruct (uskl_rho_arrow_l_inv Hrho)
      as [[Heqψa HΨρe]
         | [Hleaf | (ψa1 & ψa2 & Ψρ1 & Ψρ2 & Heqψa & Hrho1 & Hrho2 & HΨρs)]].
    + (* refl: recast as a congruence with refl branch-ρs *)
      subst ψa.
      assert (Htsk : is_tskl (uskl_arrow R1 R2))
        by (inversion Htags; assumption).
      assert (HlcR1 : lc_uskl R1)
        by (apply is_tskl_lc; inversion Htsk; assumption).
      assert (HlcR2 : lc_uskl R2)
        by (apply is_tskl_lc; inversion Htsk; assumption).
      apply (KEY R1 R2 empty empty);
        [ apply urho__refl; [ exact HlcR1 | clear; fsetdec ]
        | apply urho__refl; [ exact HlcR2 | clear; fsetdec ]
        | clear - HΨρe; fsetdec
        | exact Htags | exact Hpre ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
    + subst ψa.
      apply (KEY ψa1 ψa2 Ψρ1 Ψρ2);
        [ exact Hrho1 | exact Hrho2 | exact HΨρs
        | exact Htags | exact Hpre ].
  - (* forall_inh_tagged (case 1): rows A (Pi=∀) / B (Pi=□) / C (Pi=∀◇
       via the precision fill); everything else is absurd (guardedness /
       paint-shape / ε-tag contradictions).  DESIGN §6(o). *)
    assert (HwfΘr2 := HwfΘr).
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hκ).
    assert (Himav : forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ)
      by (intros p Hp; eapply a_inc_image_ftv_dom; [ exact Hκ | exact Hp ]).
    assert (KEYF : forall ψR Lr,
      (forall α, α `notin` Lr ->
         uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R (uskl_var_f α))
                             (open_uskl_wrt_uskl ψR (uskl_var_f α))) ->
      a_tags_sort NM Ψ' (uskl_all_etag ε ψR) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_all_etag ε ψR) ->
      p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa (uskl_all_etag ε ψR) Pi P0 Lav).
    { intros ψR Lr Hrhof Htags0 Hpre0.
      destruct (a_tags_sort_all_etag_inv Htags0)
        as (Lt & Ψ0' & Htagsf & Hεnin & HΨ'eq).
      (* ε is premise-solved: it is a Ψ'-tag, hence never ρ-introduced *)
      assert (Hεa : ε `in` Ψa)
        by (clear - H1 Hsubeq1 Hinter HΨ'eq; fsetdec).
      (* the body ftag flow, at one fresh variable *)
      assert (HbF : Ψ0 [<=] Ψρ `union` Ψ0').
      { pick fresh αf for (L `union` Lr `union` Lt).
        pose proof (ad_pat_consis_ftag_sub
                      (H αf ltac:(clear - Fr; solve_notin))) as Ha.
        pose proof (uskl_rho_ftag_sub
                      (Hrhof αf ltac:(clear - Fr; solve_notin))) as Hb.
        pose proof (d_tags_skl_ftag
                      (a_tags_sort_d_tags
                         (Htagsf αf ltac:(clear - Fr; solve_notin)))) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hsubeq1b : Ψ0 [<=] Ψρ `union` (remove ε Ψa))
        by (clear - H1 Hsubeq1 HbF Hεnin HΨ'eq Hinter; fsetdec).
      assert (Hsubeq2b : (remove ε Ψa) [<=] Ψ0)
        by (clear - H1 Hsubeq2; fsetdec).
      assert (Hintb : Ψρ ∩ Ψ0' [=] empty)
        by (clear - Hinter HΨ'eq; fsetdec).
      assert (Hdomsub : dom Θr [<=] dom Θ)
        by (eapply aenv_split_dom_r; exact HspΘ).
      (* P0-grid: only P0 = ∀.P0b survives the refinement *)
      destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
      - (* unit *) simpl in Hrefine. inversion Hrefine.
      - (* var_b *) inversion HwfP0.
      - (* var β: rigid / flexible both die against all_inh *)
        exfalso.
        assert (Hor : β `in` empty \/ a_binds_tvar β Θ0)
          by (inversion HwfP0; subst; assumption).
        destruct Hor as [Hemp | Habt]; [ clear - Hemp; fsetdec | ].
        destruct Habt as [Hrig | Hflx].
        + assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
            by (eapply msubst_pskl_tvar_id;
                [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
          rewrite Hmid in Hrefine. simpl in Hrefine.
          eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hrefine)
            with (Θfull := Θ);
            [ intros x b Hb; eapply aenv_split_sub_r;
                [ exact HspΘ | exact Hb ]
            | apply a_wf_aenv_uniq; exact HwfΘ
            | eapply a_inc_binds_tvar; eauto
            | intros β0 Hcc; discriminate Hcc ].
        + assert (Hml : mono_ptyp (msubst_lookup κ β))
            by (eapply a_inc_lookup_mono; eauto).
          simpl in Hrefine.
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          eapply ad_refine_mono_paint_allinh_rhs_absurd;
            [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
            | exact Hml ].
      - (* arrow *) simpl in Hrefine. inversion Hrefine.
      - (* P0 = ∀.P0b: the REAL column *)
        assert (HwfP0f : exists Lw0, forall α, α `notin` Lw0 ->
                  ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                  (open_pskl_wrt_pskl P0b (pskl_var_f α))).
        { assert (Hi : exists Lw0, forall α0, α0 `notin` Lw0 ->
                    Θ0 ⨟ (add α0 empty) ⊢ₚₛᵃ
                    (open_pskl_wrt_pskl P0b (pskl_var_f α0)))
            by (inversion HwfP0; subst; eexists; eassumption).
          destruct Hi as (Lw0 & Hi).
          exists Lw0; intros α0 Hα0.
          eapply a_wf_pskl_delta_to_tvar;
            [ apply Hi; exact Hα0 | clear; fsetdec ]. }
        destruct HwfP0f as (Lw0 & HwfP0f).
        assert (Hreff : exists Lq, forall α, α `notin` Lq ->
          Θr ⨟ (add α Δr) ⊢ᵣᵃ
            pskl_to_bskl_inh (msubst_pskl κ
              (open_pskl_wrt_pskl P0b (pskl_var_f α)))
            ⊳ open_bskl_wrt_bskl Q (bskl_var_f α)).
        { simpl in Hrefine.
          inversion Hrefine; subst.
          match goal with
          | Hf : forall α0, α0 `notin` ?L0 -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
            exists (L0 `union` dom κ); intros α0 Hα0;
            rewrite msubst_pskl_open_lc_local;
              [ | exact Hlcκ | clear - Hα0; fsetdec ];
            rewrite pskl_to_bskl_inh_open;
            apply Hf; clear - Hα0; fsetdec
          end. }
        destruct Hreff as (Lq & Hreff).
        (* the shared body-IH invocation *)
        assert (IHX : forall α Pi0 Ψi0 Δx,
          α `notin` (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b) ->
          Δρ [<=] Δx -> Δx [<=] add α Δ ->
          ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi0 ->
          (forall α0, α0 `in` Δρ ->
             α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi0)) ->
          ((α ~ abind_tvar) ++ Θ) ⨟ Δx ⊢ (msubst_pskl κ Pi0)
              ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψR (uskl_var_f α)) ->
          Ψi0 [<=] Ψ0' ->
          (* ⭐ THE PACKAGE, under the binder (2026-08-04).  [solve_ext]'s
             wf context is [Θw] — FIXED — so the body's block is already
             reported OUTSIDE the ∀ it was generated under; that is exactly
             what lets the row hand it back up unchanged (the solve's ∀ rows
             pass [Ξ] through). *)
          exists Ξ0 Pa0 κ0,
            ((α ~ abind_tvar) ++ Θ0) ⊢ₑ Pi0 ∼
               (open_pskl_wrt_pskl P0b (pskl_var_f α)) ⤳ Ξ0 ⨾ Pa0 /\
            all_flex_mono Ξ0 /\
            uniq Ξ0 /\
            keys κ0 = keys Ξ0 /\
            (* ⚙️ [add α Lav], not [Lav]: the ROW's own binder must also be
               dodged, because the block is emitted OUTSIDE the ∀ and the fold
               renames α.  It costs nothing — [H0]'s avoid-set premise is
               [ftvar_in_aenv ((α ~ tvar) ++ Θ0) [<=] L], which needs α ∈ L
               anyway. *)
            (forall α0, α0 `in` dom Ξ0 -> α0 `notin` (add α Lav)) /\
            Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 /\
            forall Δ', Δ' ∩ Δx [=] empty ->
              Δ' ∩ dom Θr [=] empty ->
              delta_def_fresh Δ' ((α ~ abind_tvar) ++ Θ) ->
              ((α ~ abind_tvar) ++ Θ) ⨟ (Δx `union` Δ')
                ⊢ (msubst_pskl (κ0 ++ κ) Pa0)
                  ⊑ᵖ[ Ψi0 `union` (remove ε Ψa) ]
                  (open_uskl_wrt_uskl ψR (uskl_var_f α))).
        { intros α Pi0 Ψi0 Δx HXf HΔρx HΔxs HwfPi0 Hapart0 Hpre0x HΨi0s.
          apply (H0 α ltac:(clear - HXf; solve_notin)
                   NM ((α ~ abind_tvar) ++ Θ0)
                   ((α ~ abind_tvar) ++ Θtv) Θr Θ0r κ
                   Δx Δρ (add α Δr) Ψρ Ψ0' Ψi0 (remove ε Ψa)
                   (open_uskl_wrt_uskl ψR (uskl_var_f α))
                   Pi0 (open_pskl_wrt_pskl P0b (pskl_var_f α))).
          - apply aenv_split_cons_tv; [ exact HspΘ | clear - HXf; solve_notin ].
          - apply aenv_split_cons_tv; [ exact HspΘ0 | clear - HXf; solve_notin ].
          - exact HwfΘr.
          - intros x b Hb.
            destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
              [ exact Heqb | exact (Htvs _ _ Hb') ].
          - simpl. clear - HΔrd; fsetdec.
          - simpl. clear - HΔρtv HXf; destruct_notin; fsetdec.
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ ].
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ0 ].
          - intros x b Hb. apply binds_cons_3. apply Hmon; exact Hb.
          - intros x b Hb.
            destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
              [ right; exact Heqb | exact (Hnr _ _ Hb') ].
          - exact HwfPi0.
          - apply HwfP0f. clear - HXf; solve_notin.
          - apply a_inc__tvar with (Ξ := (@nil (atom * abind)));
              [ exact Hκ | apply a_suffix__nil ].
          - (* the κ-image bound is INVARIANT: the row adds only a rigid *)
            intros α0 Hf. apply Hκw. eapply a_flex_tvar_strip_tvar; exact Hf.
          - eapply uskl_rho_weaken;
              [ apply Hrhof; clear - HXf; solve_notin
              | intros x b Hb; apply binds_cons_3; exact Hb ].
          - apply Htagsf. clear - HXf; solve_notin.
          - clear - HΨi0s Hsub HΨ'eq; fsetdec.
          - exact Hintb.
          - intros x Hx.
            destruct (Hfresh x Hx) as (Hb & Hav & Hdef).
            repeat split.
            + apply binds_cons_3; exact Hb.
            + exact Hav.
            + intros αd τ Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | exact (Hdef _ _ Hbd') ].
          - exact HΔρx.
          - exact Hapart0.
          - intros Yd αd τ HYd Hbd.
            destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
              [ discriminate Hc | ].
            assert (HYx : Yd `in` add α Δ) by (clear - HYd HΔxs; fsetdec).
            destruct (Yd == α) as [-> | Hne].
            + assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                by (eapply a_wf_aenv_def_ftv_dom;
                    [ exact HwfΘ | exact Hbd' ]).
              clear - Hd HXf; destruct_notin; fsetdec.
            + eapply Hdfresh; [ | exact Hbd' ].
              clear - HYx Hne; fsetdec.
          - exact Hpre0x.
          - exact Hsubeq1b.
          - exact Hsubeq2b.
          - apply Hreff. clear - HXf; solve_notin.
          - rewrite ftvar_in_aenv_cons_tvar. clear - HLav; fsetdec. }
        (* the shared per-instance fold: strengthen + rename + rewrites.
           ⭐ It now runs under [κ0 ++ κ], the body's extension prefixed to the
           incoming metasubstitution.  The two facts it needs of the prefix —
           local closure and [dom Θ]-scoping of the images — are read off the
           package's [Forall] component. *)
        assert (FOLD : forall κ0 α PaR Ψc Δ',
          Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 ->
          α `notin` (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` dom κ0
               `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b) ->
          Δ' ∩ Δ [=] empty ->
          Δ' ∩ dom Θr [=] empty ->
          delta_def_fresh Δ' Θ ->
          ((α ~ abind_tvar) ++ Θ)
            ⨟ (add α (Δ `union` (remove α Δ')))
            ⊢ (msubst_pskl (κ0 ++ κ) PaR) ⊑ᵖ[ Ψc ]
              (open_uskl_wrt_uskl ψR (uskl_var_f α)) ->
          forall α', α' `notin` (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` dom κ0
               `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b `union` Δ' `union` singleton α
              `union` ftvar_in_pskl (msubst_pskl (κ0 ++ κ) PaR)) ->
          Θ ⨟ (add α' (Δ `union` Δ')) ⊢
            (msubst_pskl (κ0 ++ κ) (open_pskl_wrt_pskl
               (close_pskl_wrt_pskl α PaR) (pskl_var_f α')))
            ⊑ᵖ[ Ψc ] (open_uskl_wrt_uskl ψR (uskl_var_f α'))).
        { intros κ0 α PaR Ψc Δ' HF0 HXf HS1 HS2 HS3 Hrun α' HX'f.
          assert (HimavX : forall p, In p (κ0 ++ κ) ->
                    ftvar_in_ptyp (snd p) [<=] dom Θ).
          { intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp | Hp];
              [ | exact (Himav p Hp) ].
            assert (Hd := forall_wf_mono_images_dom HF0 p Hp).
            assert (Hdw : dom Θw [<=] dom Θ) by (apply aenv_binds_dom_sub; exact Hmon).
            clear - Hd Hdw; fsetdec. }
          assert (Hdκ0 : dom (κ0 ++ κ) [=] dom κ0 `union` dom κ)
            by (rewrite dom_app; clear; fsetdec).
          assert (Hst : Θ ⨟ (add α (Δ `union` (remove α Δ')))
                   ⊢ (msubst_pskl (κ0 ++ κ) PaR) ⊑ᵖ[ Ψc ]
                   (open_uskl_wrt_uskl ψR (uskl_var_f α)))
            by (eapply ad_partial_precise_strengthen_tvar;
                [ exact Hrun | clear; fsetdec ]).
          assert (Hrn : Θ ⨟ (add α' (remove α (add α (Δ `union` (remove α Δ')))))
                   ⊢ (subst_pskl_in_pskl (pskl_var_f α') α
                        (msubst_pskl (κ0 ++ κ) PaR))
                   ⊑ᵖ[ Ψc ]
                   (subst_bskl_in_uskl (uskl_var_f α') α
                        (open_uskl_wrt_uskl ψR (uskl_var_f α)))).
          { eapply ad_partial_precise_rename;
              [ exact Hst
              | clear; fsetdec
              | clear - HXf; solve_notin
              | clear - HX'f; solve_notin
              | clear - HX'f; solve_notin
              | clear - HX'f; solve_notin
              | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                              (uskl_var_f α)) as Hup;
                simpl in Hup; clear - HX'f Hup; destruct_notin; fsetdec
              | intros αd τ Hbd;
                assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                  by (eapply a_wf_aenv_def_ftv_dom;
                      [ exact HwfΘ | exact Hbd ]);
                split; [ clear - Hd HXf; destruct_notin; fsetdec
                       | clear - Hd HX'f; destruct_notin; fsetdec ] ]. }
          rewrite <- (subst_bskl_in_uskl_intro α ψR (uskl_var_f α')
                        ltac:(clear - HXf; solve_notin)) in Hrn.
          rewrite (@msubst_pskl_subst_var_paired (κ0 ++ κ) PaR α α'
                     ltac:(clear - HXf Hdκ0; destruct_notin; solve_notin_auto)
                     ltac:(clear - HX'f Hdκ0; destruct_notin; solve_notin_auto)
                     ltac:(intros p Hp;
                           pose proof (HimavX p Hp) as Hd;
                           clear - Hd HXf; destruct_notin; solve_notin_auto)) in Hrn.
          rewrite (subst_pskl_in_pskl_spec PaR (pskl_var_f α') α) in Hrn.
          eapply ad_partial_precise_delta_cong;
            [ eapply ad_partial_precise_delta_weaken_fresh
                with (Δ' := Δ' ∩ singleton α);
                [ exact Hrn
                | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                (uskl_var_f α')) as Hup;
                  simpl in Hup;
                  apply atoms_inter_empty_pointwise;
                  intros y Hy;
                  assert (Heqy : y = α) by (clear - Hy; fsetdec);
                  subst y;
                  clear - HXf HX'f Hup; destruct_notin; fsetdec
                | intros Yd αd τ HYd Hbd;
                  assert (Heqy : Yd = α) by (clear - HYd; fsetdec);
                  subst Yd;
                  assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                    by (eapply a_wf_aenv_def_ftv_dom;
                        [ exact HwfΘ | exact Hbd ]);
                  clear - Hd HXf; destruct_notin; fsetdec ]
            | clear - HXf HX'f; destruct_notin; fsetdec ]. }
        (* ---- the Pi grid ---- *)
        destruct Pi as [ | nb | β | Pi1 Pi2 | Pib | | Pi' ].
        + (* unit *) simpl in Hpre0. inversion Hpre0.
        + (* var_b *) inversion HwfPi.
        + (* var: a mono-paint subject vs the ε-tagged target *)
          exfalso.
          assert (HΨ'e : Ψ' [=] empty).
          { eapply ad_ppre_mono_subject_target_tags_empty
              with (τ := msubst_lookup κ β);
              [ exact HwfΘ | exact Hpre0 | reflexivity
              | eapply a_inc_lookup_mono; eauto
              | exact (a_tags_sort_d_tags Htags0) ]. }
          assert (Hcon : ε `in` empty).
          { apply (proj1 (HΨ'e ε)). apply (proj2 (HΨ'eq ε)).
            clear; fsetdec. }
          clear - Hcon; fsetdec.
        + (* arrow *) simpl in Hpre0. inversion Hpre0.
        + (* Pi = ∀.Pib — ROW A: SE-Forall from a single fresh-α run;
             the family folds via FOLD (family{α} → strengthen → rename) *)
          assert (HwfPif : exists Lwi, forall α, α `notin` Lwi ->
                    ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                    (open_pskl_wrt_pskl Pib (pskl_var_f α))).
          { assert (Hi : exists Lwi, forall α0, α0 `notin` Lwi ->
                      Θ0 ⨟ (add α0 empty) ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl Pib (pskl_var_f α0)))
              by (inversion HwfPi; subst; eexists; eassumption).
            destruct Hi as (Lwi & Hi).
            exists Lwi; intros α0 Hα0.
            eapply a_wf_pskl_delta_to_tvar;
              [ apply Hi; exact Hα0 | clear; fsetdec ]. }
          destruct HwfPif as (Lwi & HwfPif).
          assert (HpreF : exists Lp Ψi',
            (forall α, α `notin` Lp ->
               Θ ⨟ (add α Δ) ⊢
                 (msubst_pskl κ (open_pskl_wrt_pskl Pib (pskl_var_f α)))
                 ⊑ᵖ[ Ψi' ] (open_uskl_wrt_uskl ψR (uskl_var_f α))) /\
            Ψi [=] add ε Ψi').
          { simpl in Hpre0.
            inversion Hpre0; subst.
            match goal with
            | Hf : forall α0, α0 `notin` ?L0 ->
                _ ⨟ _ ⊢ _ ⊑ᵖ[ ?PS ] _ |- _ =>
              exists (L0 `union` dom κ), PS; split;
                [ intros α0 Hα0;
                  rewrite msubst_pskl_open_lc_local;
                    [ apply Hf; clear - Hα0; fsetdec
                    | exact Hlcκ | clear - Hα0; fsetdec ]
                | assumption ]
            end. }
          destruct HpreF as (Lp & Ψi' & HpreF & HΨis).
          assert (HΨi's : Ψi' [<=] Ψ0').
          { pick fresh αp for (Lp `union` Lt).
            eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ
              | apply HpreF; clear - Fr; solve_notin
              | exact (a_tags_sort_d_tags
                        (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
               `union` Lwi `union` Lp `union` ftvar_in_pskl Pib).
          destruct (IHX α (open_pskl_wrt_pskl Pib (pskl_var_f α)) Ψi'
                      (add α Δ)
                      ltac:(clear - Fr; solve_notin)
                      ltac:(clear - Hdelta; solve_notin_auto)
                      ltac:(clear; solve_notin_auto)
                      (HwfPif α ltac:(clear - Fr; solve_notin))
                      ltac:(intros α0 HX0;
                            pose proof (Hapart α0 HX0) as Hs0;
                            simpl in Hs0;
                            rewrite msubst_pskl_open_lc_local;
                              [ | exact Hlcκ | clear - Fr; solve_notin ];
                            pose proof (pskl_shielded_ftv_open_upper
                              (msubst_pskl κ Pib) (pskl_var_f α)) as Hup;
                            simpl in Hup;
                            assert (HneX0 : α0 <> α)
                              by (clear - HX0 Fr; destruct_notin; fsetdec);
                            clear - Hs0 Hup HneX0; fsetdec)
                      ltac:(eapply ad_partial_precise_weaken;
                              [ apply HpreF; clear - Fr; solve_notin
                              | intros x b Hb; apply binds_cons_3;
                                exact Hb ])
                      HΨi's)
            as (ΞX & PaX & κX & HsX & HfmX & HuX & HkX & HfrX & HFX & HqX).
          (* ⚙️ NO [a_solve_eq_strengthen_tvar] any more: SE-Forall's premise
             now RUNS AT [(β ~ tvar) ++ Θ] (the repair's decision §2(1) — the
             solve generates names, and a generated β must dodge the closing
             binder), so [HsX] is already the premise. *)
          (* ⭐ the block RIDES OUT of the ∀ unchanged — [SE-Forall] passes [Ξ]
             through — and it is apart from the row's own binder, which is what
             the [add α Lav] avoid-set bought. *)
          assert (HαΞ : α `notin` dom ΞX)
            by (intros Hin; exact (HfrX α Hin ltac:(clear; solve_notin_auto))).
          assert (HdκX : dom κX [=] dom ΞX) by (apply keys_eq_dom; exact HkX).
          assert (HlcκX : msubst_lc (κX ++ κ))
            by (eapply msubst_lc_app_wf; [ exact HFX | exact Hlcκ ]).
          exists ΞX, (pskl_all_syn (close_pskl_wrt_pskl α PaX)), κX.
          split.
          { (* SE-Forall is EXISTS-FRESH + CLOSE now (DESIGN §4.3): the
               single fresh-α run IS the premise, and the rule closes the
               output itself — no cofinite family to fold, and the old
               rename-per-member step disappears. *)
            apply a_solve_eq__forall with (β := α);
              [ clear - Fr; solve_notin | exact HsX ]. }
          split; [ exact HfmX | ].
          split; [ exact HuX | ].
          split; [ exact HkX | ].
          split; [ intros α0 Hα0; pose proof (HfrX α0 Hα0) as Hn;
                   clear - Hn; fsetdec | ].
          split; [ exact HFX | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          apply ad_ppre__forall with
            (L := L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` dom κX
               `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
               `union` Δ' `union` singleton α
               `union` ftvar_in_pskl (msubst_pskl (κX ++ κ) PaX))
            (Ψ0 := Ψi' `union` (remove ε Ψa));
            [ | clear - HΨis Hεa; fsetdec ].
          intros α' HX'.
          rewrite <- msubst_pskl_open_lc_local;
            [ | exact HlcκX
            | rewrite dom_app; clear - HX'; solve_notin ].
          assert (Hrun : ((α ~ abind_tvar) ++ Θ) ⨟
                    (add α (Δ `union` (remove α Δ'))) ⊢
                    (msubst_pskl (κX ++ κ) PaX)
                    ⊑ᵖ[ Ψi' `union` (remove ε Ψa) ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α))).
          { eapply ad_partial_precise_delta_cong;
              [ apply (HqX (remove α Δ'));
                [ clear - HS1; destruct_notin; fsetdec
                | simpl; clear - HS2; fsetdec
                | intros Yd αd τ HYd Hbd;
                  destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                    as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                  eapply HS3; [ clear - HYd; fsetdec | exact Hbd' ] ]
              | clear; fsetdec ]. }
          apply (FOLD κX α PaX (Ψi' `union` (remove ε Ψa)) Δ' HFX
                   ltac:(clear - Fr HαΞ HdκX; destruct_notin; solve_notin_auto)
                   HS1 HS2 HS3 Hrun
                   α' ltac:(clear - HX'; solve_notin)).
        + (* Pi = □ — ROW B: SE-GhostL; ONE fresh-α body-IH run at the row
             top (not per-instance — the giant IH must not be re-elaborated
             under the ∀-fold binder), then FOLD-rename.  The solve is a
             single a_solve_eq__hole_l (Pa := ∀.P0b). *)
          assert (HΨie : Ψi [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          assert (Hhd : Δ ∩
                    (ftvar_in_uskl (uskl_all_etag ε ψR)) [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          simpl in Hhd.
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b).
          assert (Hp0X : ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢
                    (msubst_pskl κ pskl_hole) ⊑ᵖ[ empty ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α))).
          { simpl. apply ad_ppre__hole; [ clear; fsetdec | ].
            pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                          (uskl_var_f α)) as Hup.
            simpl in Hup. clear - Hhd Hup Fr; destruct_notin; fsetdec. }
          eapply solve_ext_nil with (Pa := (pskl_all_syn P0b));
            [ apply a_solve_eq__hole_l | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          apply ad_ppre__forall with
            (L := L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b `union` Δ')
            (Ψ0 := empty `union` (remove ε Ψa));
            [ | clear - HΨie Hεa; fsetdec ].
          intros α' HX'.
          rewrite <- msubst_pskl_open_lc_local;
            [ | exact Hlcκ | clear - HX'; solve_notin ].
          assert (Hp0X' : ((α' ~ abind_tvar) ++ Θ) ⨟ Δ ⊢
                    (msubst_pskl κ pskl_hole) ⊑ᵖ[ empty ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α'))).
          { simpl. apply ad_ppre__hole; [ clear; fsetdec | ].
            pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                          (uskl_var_f α')) as Hup.
            simpl in Hup. clear - Hhd Hup HX'; destruct_notin; fsetdec. }
          clear FOLD.
          destruct (IHX α' pskl_hole empty Δ
                      ltac:(clear - HX'; solve_notin)
                      Hdelta
                      ltac:(clear; solve_notin_auto)
                      ltac:(apply a_wf_pskl__hole)
                      ltac:(intros α0 HX0; simpl; auto)
                      Hp0X'
                      ltac:(clear; solve_notin_auto))
            as (Ξ0 & Pa0 & κ0 & Hs0 & _ & _ & Hk0 & _ & _ & Hq0).
          (* ⭐ a GHOST subject pins the block to [nil] — [nonghost_pskl] on
             SE-FlexR is what keeps [a_solve_eq_hole_subject_inv] true — and
             the aligned extension with it. *)
          destruct (a_solve_eq_hole_subject_inv Hs0) as [HΞ0e HPa0]; subst.
          destruct κ0 as [ | ? ? ];
            [ | unfold keys in Hk0; simpl in Hk0; discriminate ].
          cbn [app] in Hq0.
          assert (HqS : ((α' ~ abind_tvar) ++ Θ) ⨟
                    (Δ `union` (add α' Δ')) ⊢
                    (msubst_pskl κ (open_pskl_wrt_pskl P0b (pskl_var_f α')))
                    ⊑ᵖ[ empty `union` (remove ε Ψa) ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α'))).
          { apply (Hq0 (add α' Δ')).
            - clear - HS1 HX'; destruct_notin; fsetdec.
            - clear - HS2 HX' Hdomsub; destruct_notin; fsetdec.
            - intros Yd αd τ HYd Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | ].
              destruct (Yd == α') as [-> | Hne].
              + assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                  by (eapply a_wf_aenv_def_ftv_dom;
                      [ exact HwfΘ | exact Hbd' ]).
                clear - Hd HX'; destruct_notin; fsetdec.
              + eapply HS3; [ clear - HYd Hne; fsetdec | exact Hbd' ]. }
          eapply ad_partial_precise_delta_cong;
            [ eapply ad_partial_precise_strengthen_tvar;
                [ exact HqS | clear; fsetdec ]
            | clear; fsetdec ].
        + (* Pi = ∀◇.Pi' — the remove-branch dies (guarded body);
             the fill branch is ROW C (SE-GhostForall) *)
          assert (Hg : guarded_pskl Pi' /\ (Θ0 ⨟ empty ⊢ₚₛᵃ Pi'))
            by (inversion HwfPi; subst; split; assumption).
          destruct Hg as [HgPi' HwfPi'].
          assert (Hdisj :
            (Θ ⨟ Δ ⊢ (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ]
               (uskl_all_etag ε ψR)) \/
            (exists Lf, forall α, α `notin` Lf ->
               ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢
                 pskl_tophole (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ]
                 (open_uskl_wrt_uskl ψR (uskl_var_f α)))).
          { simpl in Hpre0. inversion Hpre0; subst;
              [ left; assumption | right; eexists; eassumption ]. }
          destruct Hdisj as [Hrem | (Lf & HF)].
          * (* remove: the guarded body dies against the ε-tagged target *)
            exfalso.
            inversion HgPi'; subst.
            -- simpl in Hrem. inversion Hrem.
            -- assert (HΨ'e : Ψ' [=] empty).
               { eapply ad_ppre_mono_subject_target_tags_empty
                   with (τ := msubst_lookup κ α);
                   [ exact HwfΘ | exact Hrem | reflexivity
                   | eapply a_inc_lookup_mono; eauto
                   | exact (a_tags_sort_d_tags Htags0) ]. }
               assert (Hcon : ε `in` empty).
          { apply (proj1 (HΨ'e ε)). apply (proj2 (HΨ'eq ε)).
            clear; fsetdec. }
          clear - Hcon; fsetdec.
            -- simpl in Hrem. inversion Hrem.
          * (* fill — ROW C *)
            assert (HΨiS : Ψi [<=] Ψ0').
            { pick fresh αp for (Lf `union` Lt `union` dom Θ).
              assert (HwfΘx : a_wf_aenv ((αp ~ abind_tvar) ++ Θ))
                by (apply a_wf_aenv__tvar;
                    [ clear - Fr; solve_notin | exact HwfΘ ]).
              eapply ad_partial_precise_tags_sub;
                [ exact HwfΘx
                | apply HF; clear - Fr; solve_notin
                | exact (a_tags_sort_d_tags
                          (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
            pick fresh α for
              (L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
                 `union` Lf `union` ftvar_in_pskl Pi').
            destruct (IHX α (pskl_tophole Pi') Ψi Δ
                        ltac:(clear - Fr; solve_notin)
                        Hdelta
                        ltac:(clear; solve_notin_auto)
                        ltac:(eapply a_wf_pskl_weaken;
                              [ intros x b Hb; apply binds_cons_3;
                                exact Hb
                              | exact HwfPi ])
                        Hapart
                        (HF α ltac:(clear - Fr; solve_notin))
                        HΨiS)
              as (ΞX & PaX & κX & HsX & HfmX & HuX & HkX & HfrX & HFX & HqX).
            assert (HαΞ : α `notin` dom ΞX)
              by (intros Hin; exact (HfrX α Hin ltac:(clear; solve_notin_auto))).
            assert (HdκX : dom κX [=] dom ΞX) by (apply keys_eq_dom; exact HkX).
            assert (HlcκX : msubst_lc (κX ++ κ))
              by (eapply msubst_lc_app_wf; [ exact HFX | exact Hlcκ ]).
            exists ΞX, (pskl_all_syn (close_pskl_wrt_pskl α PaX)), κX.
            split.
            { (* SE-GhostForall, exists-fresh + CLOSE (DESIGN §4.3); its
                 premise runs at [(β ~ tvar) ++ Θ] now, so [HsX] IS it. *)
              apply a_solve_eq__tophole_l_all with (β := α);
                [ clear - Fr; solve_notin | exact HsX ]. }
            split; [ exact HfmX | ].
            split; [ exact HuX | ].
            split; [ exact HkX | ].
            split; [ intros α0 Hα0; pose proof (HfrX α0 Hα0) as Hn;
                     clear - Hn; fsetdec | ].
            split; [ exact HFX | ].
            intros Δ' HS1 HS2 HS3.
            simpl.
            apply ad_ppre__forall with
              (L := L `union` Lr `union` Lt `union` Lw0 `union` Lq
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` dom κX
               `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0b
                 `union` Lf `union` Δ' `union` singleton α
                 `union` ftvar_in_pskl (msubst_pskl (κX ++ κ) PaX))
              (Ψ0 := Ψi `union` (remove ε Ψa));
              [ | clear - Hεa; fsetdec ].
            intros α' HX'.
            rewrite <- msubst_pskl_open_lc_local;
              [ | exact HlcκX
              | rewrite dom_app; clear - HX'; solve_notin ].
            assert (Hrun : ((α ~ abind_tvar) ++ Θ) ⨟
                      (add α (Δ `union` (remove α Δ'))) ⊢
                      (msubst_pskl (κX ++ κ) PaX)
                      ⊑ᵖ[ Ψi `union` (remove ε Ψa) ]
                      (open_uskl_wrt_uskl ψR (uskl_var_f α))).
            { eapply ad_partial_precise_delta_cong;
                [ apply (HqX (add α Δ'));
                  [ clear - HS1 Fr; destruct_notin; fsetdec
                  | clear - HS2 Fr Hdomsub; destruct_notin; fsetdec
                  | intros Yd αd τ HYd Hbd;
                    destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                      as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                    destruct (Yd == α) as [-> | Hne];
                    [ assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                        by (eapply a_wf_aenv_def_ftv_dom;
                            [ exact HwfΘ | exact Hbd' ]);
                      clear - Hd Fr; destruct_notin; fsetdec
                    | eapply HS3;
                      [ clear - HYd Hne; fsetdec | exact Hbd' ] ] ]
                | clear; fsetdec ]. }
            apply (FOLD κX α PaX (Ψi `union` (remove ε Ψa)) Δ' HFX
                     ltac:(clear - Fr HαΞ HdκX; destruct_notin; solve_notin_auto)
                     HS1 HS2 HS3 Hrun
                     α' ltac:(clear - HX'; solve_notin)).
      - (* P0 = □: the fill would be an all_inh — not a syn paint *)
        exfalso.
        simpl in Hrefine.
        inversion Hrefine; subst.
        match goal with
        | Heq : pskl_to_bskl_syn ?P = bskl_all_inh _ |- _ =>
          destruct P; simpl in Heq; discriminate Heq
        | Heq : bskl_all_inh _ = pskl_to_bskl_syn ?P |- _ =>
          destruct P; simpl in Heq; discriminate Heq
        end.
      - (* P0 = ∀◇.P0': the guarded body dies against all_inh *)
        exfalso.
        assert (Hg : guarded_pskl P0' /\ (Θ0 ⨟ empty ⊢ₚₛᵃ P0')).
        { inversion HwfP0; subst; split; assumption. }
        destruct Hg as [HgP0' HwfP0'].
        simpl in Hrefine.
        inversion Hrefine; subst.
        inversion HgP0'; subst.
        + match goal with
          | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _
            |- _ => simpl in Hin; inversion Hin
          end.
        + (* var: rigid / flexible both die *)
          match goal with
          | Hwv : _ ⨟ _ ⊢ₚₛᵃ pskl_var_f ?v,
            Hin : _ ⨟ _ ⊢ᵣᵃ
              pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _ |- _ =>
            assert (Hor : v `in` empty \/ a_binds_tvar v Θ0)
              by (inversion Hwv; subst; assumption);
            destruct Hor as [Hemp | Habt]; [ clear - Hemp; fsetdec | ];
            destruct Habt as [Hrig | Hflx];
            [ let Hmid := fresh in
              assert (Hmid : msubst_pskl κ (pskl_var_f v) = pskl_var_f v)
                by (eapply msubst_pskl_tvar_id;
                    [ exact HwfΘ0 | exact Hκ | exact Hrig ]);
              rewrite Hmid in Hin; simpl in Hin;
              eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hin);
                [ intros x b Hb; eapply aenv_split_sub_r;
                    [ exact HspΘ | exact Hb ]
                | apply a_wf_aenv_uniq; exact HwfΘ
                | eapply a_inc_binds_tvar; eauto
                | intros β0 Hcc; discriminate Hcc ]
            | let Hml := fresh in
              assert (Hml : mono_ptyp (msubst_lookup κ v))
                by (eapply a_inc_lookup_mono; eauto);
              simpl in Hin;
              rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
              eapply ad_refine_mono_paint_allinh_rhs_absurd;
                [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                | exact Hml ] ]
          end.
        + match goal with
          | Hin : _ ⨟ _ ⊢ᵣᵃ
              pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _
            |- _ => simpl in Hin; inversion Hin
          end. }
    destruct (uskl_rho_all_etag_l_inv Hrho)
      as [[Heqψa HΨρe] | [Hleaf | (Lr & ψR & Heqψa & Hrhof)]].
    + (* refl: recast as a congruence with refl bodies *)
      subst ψa.
      assert (Htskf : exists Li, forall α, α `notin` Li ->
                is_tskl (open_uskl_wrt_uskl R (uskl_var_f α))).
      { destruct (a_tags_sort_all_etag_inv Htags)
          as (Lt0 & Ψt0 & Hf & _ & _).
        exists Lt0; intros α0 Hα0.
        destruct (Hf α0 Hα0); assumption. }
      destruct Htskf as (Li & Htskf).
      apply (KEYF R Li);
        [ intros α0 Hα0; apply urho__refl;
            [ apply is_tskl_lc; apply Htskf; exact Hα0 | exact HΨρe ]
        | exact Htags | exact Hpre ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
    + subst ψa.
      apply (KEYF ψR Lr);
        [ exact Hrhof | exact Htags | exact Hpre ].
  - (* forall_inh_untagged: tag-sort absurd *)
    destruct (uskl_rho_all_syn_l_inv Hrho)
      as [[-> _] | [Hleaf | (L' & R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* forall_syn_tagged: subject ∀^ε.R ∼ bskl_all_syn Q.  ε is a Ψ'-only
       tag (the rule keeps Ψ, does NOT add ε), so NO ε-split.  P0 grid:
       □ (VacuousR) and ∀◇.P0' (the main tophole_fill column) are real;
       the rest are refinement-absurd.  Split-A (DESIGN §6(t)):
       Θtv_ih:=(α~tvar)++Θtv, Θr_ih:=Θr — valid split (α at front), tight
       family dom Θr; matches the CLOSED forall_inh_tagged IHX exactly. *)
    assert (HwfΘr2 := HwfΘr).
    assert (Hlcκ : msubst_lc κ) by (eapply a_inc_msubst_lc; exact Hκ).
    assert (Himav : forall p, In p κ -> ftvar_in_ptyp (snd p) [<=] dom Θ)
      by (intros p Hp; eapply a_inc_image_ftv_dom; [ exact Hκ | exact Hp ]).
    assert (KEYF : forall ψR Lr,
      (forall α, α `notin` Lr ->
         uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R (uskl_var_f α))
                             (open_uskl_wrt_uskl ψR (uskl_var_f α))) ->
      a_tags_sort NM Ψ' (uskl_all_etag ε ψR) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_all_etag ε ψR) ->
      p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa (uskl_all_etag ε ψR) Pi P0 Lav).
    { intros ψR Lr Hrhof Htags0 Hpre0.
      destruct (a_tags_sort_all_etag_inv Htags0)
        as (Lt & Ψ0' & Htagsf & Hεnin & HΨ'eq).
      assert (Hdomsub : dom Θr [<=] dom Θ)
        by (eapply aenv_split_dom_r; exact HspΘ).
      (* body ftag flow at one fresh var: Ψ ⊆ Ψρ ∪ Ψ0' *)
      assert (HbF : Ψ [<=] Ψρ `union` Ψ0').
      { pick fresh αf for (L `union` Lr `union` Lt).
        pose proof (ad_pat_consis_ftag_sub
                      (H αf ltac:(clear - Fr; solve_notin))) as Ha.
        pose proof (uskl_rho_ftag_sub
                      (Hrhof αf ltac:(clear - Fr; solve_notin))) as Hb.
        pose proof (d_tags_skl_ftag
                      (a_tags_sort_d_tags
                         (Htagsf αf ltac:(clear - Fr; solve_notin)))) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      (* Ψa ⊆ Ψ0' (Ψa ⊆ Ψ ⊆ Ψρ∪Ψ0', and Ψa ⊆ Ψ' disjoint Ψρ) *)
      assert (HΨaΨ0' : Ψa [<=] Ψ0')
        by (clear - Hsubeq2 HbF Hinter HΨ'eq Hsub; fsetdec).
      assert (Hintb : Ψρ ∩ Ψ0' [=] empty)
        by (clear - Hinter HΨ'eq; fsetdec).
      (* target ftv bound: reconstruct the whole ρ and bound ftv ψR *)
      assert (Hrhow : uskl_rho NM Θ Δρ Ψρ (uskl_all_etag ε R)
                        (uskl_all_etag ε ψR))
        by (eapply urho__all_etag with (L := Lr); exact Hrhof).
      assert (HψaB : ftvar_in_bskl Q [<=] dom Θr ->
                ftvar_in_uskl (uskl_all_etag ε ψR) [<=] dom Θr `union` Δρ).
      { intros HQB.
        assert (HftR : ftvar_in_uskl (uskl_all_etag ε R) [<=]
                  ftvar_in_bskl (bskl_all_syn Q) `union` dom Θr)
          by (eapply consis_subject_ftv_bag_bound;
                [ eapply ad_pat_consis__forall_syn_tagged; exact H
                | exact HspΘ | exact Htvs | exact HwfΘr ]).
        pose proof (uskl_rho_ftv_target_bound Hrhow) as HftA.
        simpl in *. clear - HQB HftR HftA; fsetdec. }
      (* P0-grid *)
      destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
      - (* unit *) simpl in Hrefine. inversion Hrefine.
      - (* var_b *) inversion HwfP0.
      - (* var β: rigid absurd / flex → mono paint vs all_syn absurd *)
        exfalso.
        assert (Hor : β `in` empty \/ a_binds_tvar β Θ0)
          by (inversion HwfP0; subst; assumption).
        destruct Hor as [Hemp | Habt]; [ clear - Hemp; fsetdec | ].
        destruct Habt as [Hrig | Hflx].
        + assert (Hmid : msubst_pskl κ (pskl_var_f β) = pskl_var_f β)
            by (eapply msubst_pskl_tvar_id;
                [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
          rewrite Hmid in Hrefine. simpl in Hrefine.
          eapply (ad_refine_syn_rigid_var_nonvar_absurd_sub Hrefine)
            with (Θfull := Θ);
            [ intros x b Hb; eapply aenv_split_sub_r;
                [ exact HspΘ | exact Hb ]
            | apply a_wf_aenv_uniq; exact HwfΘ
            | eapply a_inc_binds_tvar; eauto
            | intros β0 Hcc; discriminate Hcc ].
        + assert (Hml : mono_ptyp (msubst_lookup κ β))
            by (eapply a_inc_lookup_mono; eauto).
          simpl in Hrefine.
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          eapply ad_refine_mono_paint_allsyn_rhs_absurd;
            [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
            | exact Hml ].
      - (* arrow *) simpl in Hrefine. inversion Hrefine.
      - (* all_syn P0b: inh-paint = bskl_all_inh, refines to all_syn absurd *)
        exfalso. simpl in Hrefine. inversion Hrefine.
      - (* P0 = □: VacuousR.  Q = all_syn synthesised ⇒ Ψ = ∅ ⇒ Ψa = ∅ *)
        simpl in Hrefine.
        pose proof (ad_refine_syn_hole_sskl Hrefine eq_refl) as Hss.
        assert (HΨe : Ψ [=] empty).
        { eapply ad_pat_consis_sskl_tags;
            [ eapply ad_pat_consis__forall_syn_tagged; exact H
            | exact HwfΘ | exact Hss ]. }
        assert (HΨae : Ψa [=] empty) by (clear - Hsubeq2 HΨe; fsetdec).
        assert (HQB : ftvar_in_bskl Q [<=] dom Θr).
        { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine).
          simpl in Ht. clear - Ht; fsetdec. }
        eapply solve_ext_nil with (Pa := Pi); [ apply a_solve_eq__hole_r | ].
        intros Δ' HS1 HS2 HS3.
        eapply ad_partial_precise_psi_cong;
          [ eapply ad_partial_precise_delta_weaken_fresh;
              [ exact Hpre0
              | pose proof (HψaB HQB) as Hbb;
                clear - Hbb HS1 HS2 Hdelta; fsetdec
              | exact HS3 ]
          | clear - HΨae; fsetdec ].
      - (* P0 = ∀◇.P0': the MAIN tophole_fill column.  IHX runs the body
           IH with the binder joining Θr (bag split: Θr_ih:=(α~tvar)++Θr);
           Hrefb = the inverted tophole_fill body at (α~tvar)++Θr ⨟ Δr,
           which is the IH's refinement premise VERBATIM. *)
        assert (HgP0' : guarded_pskl P0') by (inversion HwfP0; assumption).
        assert (HwfP0'0 : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
          by (inversion HwfP0; assumption).
        (* invert the tophole_fill refinement: the fill body sits at
           (α~tvar)++Θr ⨟ Δr — exactly the IH's refinement premise *)
        simpl in Hrefine.
        assert (Hrefb : exists Lq, forall α, α `notin` Lq ->
          ((α ~ abind_tvar) ++ Θr) ⨟ Δr ⊢ᵣᵃ
            (bskl_tophole (pskl_to_bskl_inh (msubst_pskl κ P0')))
            ⊳ open_bskl_wrt_bskl Q (bskl_var_f α)).
        { inversion Hrefine; subst.
          - (* tophole_remove: the guarded body can't refine to all_syn *)
            exfalso. inversion HgP0'; subst.
            + match goal with
              | Hin : _ ⨟ _ ⊢ᵣᵃ
                  pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ |- _ =>
                simpl in Hin; inversion Hin
              end.
            + match goal with
              | Hin : _ ⨟ _ ⊢ᵣᵃ
                  pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _ |- _ =>
                let Hml := fresh in
                assert (Hml : mono_ptyp (msubst_lookup κ v))
                  by (eapply a_inc_lookup_mono; eauto);
                simpl in Hin;
                rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
                eapply ad_refine_mono_paint_allsyn_rhs_absurd;
                  [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                  | exact Hml ]
              end.
            + match goal with
              | Hin : _ ⨟ _ ⊢ᵣᵃ
                  pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _ |- _ =>
                simpl in Hin; inversion Hin
              end.
          - (* tophole_fill: the cofinite premise IS the fill body *)
            rename H5 into Hfill; rename L0 into Lfill.
            exists Lfill; exact Hfill. }
        destruct Hrefb as (Lrb & Hrefb).
        (* the body-IH wrapper (bag split: Θtv_ih:=Θtv, Θr_ih:=(α0~tvar)++Θr,
           Δr_ih:=Δr) — the family premise grows to dom((α0~tvar)++Θr), so
           rows whose α0 predates Δ' instantiate at Δ'∖{α0} and weaken the
           missing Δ'∩{α0} back; refinement per row = Hrefb verbatim.  Δx is
           the IH's Δ (Δ for ∀◇/□, add α0 Δ for the ∀ row). *)
        assert (IHX : forall α0 Pi0 Ψi0 P0i Δx,
          α0 `notin` (L `union` Lr `union` Lt `union` Lrb
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0') ->
          Δρ [<=] Δx -> Δx [<=] add α0 Δ ->
          ((α0 ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi0 ->
          ((α0 ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0i ->
          (forall α00, α00 `in` Δρ ->
             α00 `notin` pskl_shielded_ftv (msubst_pskl κ Pi0)) ->
          ((α0 ~ abind_tvar) ++ Θ) ⨟ Δx ⊢ (msubst_pskl κ Pi0)
              ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψR (uskl_var_f α0)) ->
          Ψi0 [<=] Ψ0' ->
          ((α0 ~ abind_tvar) ++ Θr) ⨟ Δr ⊢ᵣᵃ
             (pskl_to_bskl_inh (msubst_pskl κ P0i))
             ⊳ open_bskl_wrt_bskl Q (bskl_var_f α0) ->
          (* ⭐ THE PACKAGE, under the binder — see the [forall_inh_tagged]
             row's [IHX] for why the block rides out of the ∀ and why the
             avoid-set is [add α0 Lav]. *)
          exists Ξ0 Pa0 κ0,
            ((α0 ~ abind_tvar) ++ Θ0) ⊢ₑ Pi0 ∼ P0i ⤳ Ξ0 ⨾ Pa0 /\
            all_flex_mono Ξ0 /\
            uniq Ξ0 /\
            keys κ0 = keys Ξ0 /\
            (forall α00, α00 `in` dom Ξ0 -> α00 `notin` (add α0 Lav)) /\
            Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 /\
            forall Δ', Δ' ∩ Δx [=] empty ->
              Δ' ∩ (dom ((α0 ~ abind_tvar) ++ Θr)) [=] empty ->
              delta_def_fresh Δ' ((α0 ~ abind_tvar) ++ Θ) ->
              ((α0 ~ abind_tvar) ++ Θ) ⨟ (Δx `union` Δ')
                ⊢ (msubst_pskl (κ0 ++ κ) Pa0)
                  ⊑ᵖ[ Ψi0 `union` Ψa ]
                  (open_uskl_wrt_uskl ψR (uskl_var_f α0))).
        { intros α0 Pi0 Ψi0 P0i Δx HXf HΔρx HΔxs HwfPi0 HwfP0i Hapart0
                 Hpre0x HΨi0s Hrefi.
          apply (H0 α0 ltac:(clear - HXf; solve_notin)
                   NM ((α0 ~ abind_tvar) ++ Θ0)
                   Θtv ((α0 ~ abind_tvar) ++ Θr)
                   ((α0 ~ abind_tvar) ++ Θ0r) κ
                   Δx Δρ Δr Ψρ Ψ0' Ψi0 Ψa
                   (open_uskl_wrt_uskl ψR (uskl_var_f α0))
                   Pi0 P0i).
          - apply aenv_split_cons_r;
              [ exact HspΘ | clear - HXf; solve_notin ].
          - apply aenv_split_cons_r;
              [ exact HspΘ0 | clear - HXf; solve_notin ].
          - apply a_wf_aenv__tvar;
              [ clear - HXf Hdomsub; destruct_notin; fsetdec
              | exact HwfΘr ].
          - exact Htvs.
          - exact HΔrd.
          - exact HΔρtv.
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ ].
          - apply a_wf_aenv__tvar; [ clear - HXf; solve_notin | exact HwfΘ0 ].
          - intros x b Hb. apply binds_cons_3. apply Hmon; exact Hb.
          - intros x b Hb.
            destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heqb] | Hb'];
              [ right; exact Heqb | exact (Hnr _ _ Hb') ].
          - exact HwfPi0.
          - exact HwfP0i.
          - apply a_inc__tvar with (Ξ := (@nil (atom * abind)));
              [ exact Hκ | apply a_suffix__nil ].
          - intros α00 Hf. apply Hκw. eapply a_flex_tvar_strip_tvar; exact Hf.
          - eapply uskl_rho_weaken;
              [ apply Hrhof; clear - HXf; solve_notin
              | intros x b Hb; apply binds_cons_3; exact Hb ].
          - apply Htagsf. clear - HXf; solve_notin.
          - clear - HΨi0s HΨaΨ0'; fsetdec.
          - exact Hintb.
          - intros x Hx.
            destruct (Hfresh x Hx) as (Hb & Hav & Hdef).
            repeat split.
            + apply binds_cons_3; exact Hb.
            + exact Hav.
            + intros αd τ Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | exact (Hdef _ _ Hbd') ].
          - exact HΔρx.
          - exact Hapart0.
          - intros Yd αd τ HYd Hbd.
            destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
              [ discriminate Hc | ].
            assert (HYx : Yd `in` add α0 Δ) by (clear - HYd HΔxs; fsetdec).
            destruct (Yd == α0) as [-> | Hne].
            + assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                by (eapply a_wf_aenv_def_ftv_dom;
                    [ exact HwfΘ | exact Hbd' ]).
              clear - Hd HXf; destruct_notin; fsetdec.
            + eapply Hdfresh; [ | exact Hbd' ].
              clear - HYx Hne; fsetdec.
          - exact Hpre0x.
          - exact Hsubeq1.
          - exact Hsubeq2.
          - exact Hrefi.
          - rewrite ftvar_in_aenv_cons_tvar. clear - HLav; fsetdec. }
        (* per-instance fold (strengthen α out of the aenv [α∈Δ] + rename
           α↦α' in Δ), for the ∀-row precision via ad_ppre__forall *)
        assert (FOLD : forall κ0 α PaR Ψc Δ',
          Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 ->
          α `notin` (L `union` Lr `union` Lt `union` Lrb
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` dom κ0
               `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0') ->
          Δ' ∩ Δ [=] empty ->
          Δ' ∩ dom Θr [=] empty ->
          delta_def_fresh Δ' Θ ->
          ((α ~ abind_tvar) ++ Θ)
            ⨟ (add α (Δ `union` (remove α Δ')))
            ⊢ (msubst_pskl (κ0 ++ κ) PaR) ⊑ᵖ[ Ψc ]
              (open_uskl_wrt_uskl ψR (uskl_var_f α)) ->
          forall α', α' `notin` (L `union` Lr `union` Lt `union` Lrb
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0
               `union` ftvar_in_aenv Θ0
               `union` dom Θr `union` dom κ `union` dom κ0 `union` singleton ε
               `union` ftvar_in_uskl ψR `union` ftvar_in_pskl P0'
               `union` Δ' `union` singleton α
               `union` ftvar_in_pskl (msubst_pskl (κ0 ++ κ) PaR)) ->
          Θ ⨟ (add α' (Δ `union` Δ')) ⊢
            (msubst_pskl (κ0 ++ κ) (open_pskl_wrt_pskl
               (close_pskl_wrt_pskl α PaR) (pskl_var_f α')))
            ⊑ᵖ[ Ψc ] (open_uskl_wrt_uskl ψR (uskl_var_f α'))).
        { intros κ0 α PaR Ψc Δ' HF0 HXf HS1 HS2 HS3 Hrun α' HX'f.
          assert (HimavX : forall p, In p (κ0 ++ κ) ->
                    ftvar_in_ptyp (snd p) [<=] dom Θ).
          { intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp | Hp];
              [ | exact (Himav p Hp) ].
            assert (Hd := forall_wf_mono_images_dom HF0 p Hp).
            assert (Hdw : dom Θw [<=] dom Θ)
              by (apply aenv_binds_dom_sub; exact Hmon).
            clear - Hd Hdw; fsetdec. }
          assert (Hdκ0 : dom (κ0 ++ κ) [=] dom κ0 `union` dom κ)
            by (rewrite dom_app; clear; fsetdec).
          assert (Hst : Θ ⨟ (add α (Δ `union` (remove α Δ')))
                   ⊢ (msubst_pskl (κ0 ++ κ) PaR) ⊑ᵖ[ Ψc ]
                   (open_uskl_wrt_uskl ψR (uskl_var_f α)))
            by (eapply ad_partial_precise_strengthen_tvar;
                [ exact Hrun | clear; fsetdec ]).
          assert (Hrn : Θ ⨟ (add α' (remove α (add α (Δ `union`
                    (remove α Δ')))))
                   ⊢ (subst_pskl_in_pskl (pskl_var_f α') α
                        (msubst_pskl (κ0 ++ κ) PaR))
                   ⊑ᵖ[ Ψc ]
                   (subst_bskl_in_uskl (uskl_var_f α') α
                        (open_uskl_wrt_uskl ψR (uskl_var_f α)))).
          { eapply ad_partial_precise_rename;
              [ exact Hst
              | clear; fsetdec
              | clear - HXf; solve_notin
              | clear - HX'f; solve_notin
              | clear - HX'f; solve_notin
              | clear - HX'f; solve_notin
              | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                              (uskl_var_f α)) as Hup;
                simpl in Hup; clear - HX'f Hup; destruct_notin; fsetdec
              | intros αd τ Hbd;
                assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                  by (eapply a_wf_aenv_def_ftv_dom;
                      [ exact HwfΘ | exact Hbd ]);
                split; [ clear - Hd HXf; destruct_notin; fsetdec
                       | clear - Hd HX'f; destruct_notin; fsetdec ] ]. }
          rewrite <- (subst_bskl_in_uskl_intro α ψR (uskl_var_f α')
                        ltac:(clear - HXf; solve_notin)) in Hrn.
          rewrite (@msubst_pskl_subst_var_paired (κ0 ++ κ) PaR α α'
                     ltac:(clear - HXf Hdκ0; destruct_notin; solve_notin_auto)
                     ltac:(clear - HX'f Hdκ0; destruct_notin; solve_notin_auto)
                     ltac:(intros p Hp;
                           pose proof (HimavX p Hp) as Hd;
                           clear - Hd HXf; destruct_notin; solve_notin_auto)) in Hrn.
          rewrite (subst_pskl_in_pskl_spec PaR (pskl_var_f α') α) in Hrn.
          eapply ad_partial_precise_delta_cong;
            [ eapply ad_partial_precise_delta_weaken_fresh
                with (Δ' := Δ' ∩ singleton α);
                [ exact Hrn
                | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                (uskl_var_f α')) as Hup;
                  simpl in Hup;
                  apply atoms_inter_empty_pointwise;
                  intros y Hy;
                  assert (Heqy : y = α) by (clear - Hy; fsetdec);
                  subst y;
                  clear - HXf HX'f Hup; destruct_notin; fsetdec
                | intros Yd αd τ HYd Hbd;
                  assert (Heqy : Yd = α) by (clear - HYd; fsetdec);
                  subst Yd;
                  assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                    by (eapply a_wf_aenv_def_ftv_dom;
                        [ exact HwfΘ | exact Hbd ]);
                  clear - Hd HXf; destruct_notin; fsetdec ]
            | clear - HXf HX'f; destruct_notin; fsetdec ]. }
        (* the Pi grid *)
        destruct Pi as [ | nb | β | Pi1 Pi2 | Pib | | Pi' ].
        + (* unit: no precision into all_etag *)
          simpl in Hpre0. inversion Hpre0.
        + (* var_b *) inversion HwfPi.
        + (* var β: mono-paint subject vs ε-tagged target — Ψ' = ∅ absurd *)
          exfalso.
          assert (HΨ'e : Ψ' [=] empty).
          { eapply ad_ppre_mono_subject_target_tags_empty
              with (τ := msubst_lookup κ β);
              [ exact HwfΘ | exact Hpre0 | reflexivity
              | eapply a_inc_lookup_mono; eauto
              | exact (a_tags_sort_d_tags Htags0) ]. }
          clear - HΨ'e HΨ'eq Hεnin; fsetdec.
        + (* arrow *) simpl in Hpre0. inversion Hpre0.
        + (* Pi = ∀.Pib — ForallGhost row: solve = a_solve_eq__all_l_tophole
             (P0i:=∀◇.P0' KEPT, α-free); IHX at Δx:=add α Δ (α∈Δ ⇒ FOLD);
             precision conclusion = ad_ppre__forall (Pa = ∀.close). *)
          assert (HwfPif : exists Lwi, forall α, α `notin` Lwi ->
                    ((α ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ
                    (open_pskl_wrt_pskl Pib (pskl_var_f α))).
          { assert (Hi : exists Lwi, forall α0, α0 `notin` Lwi ->
                      Θ0 ⨟ (add α0 empty) ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl Pib (pskl_var_f α0)))
              by (inversion HwfPi; subst; eexists; eassumption).
            destruct Hi as (Lwi & Hi).
            exists Lwi; intros α0 Hα0.
            eapply a_wf_pskl_delta_to_tvar;
              [ apply Hi; exact Hα0 | clear; fsetdec ]. }
          destruct HwfPif as (Lwi & HwfPif).
          assert (HpreF : exists Lp Ψi',
            (forall α, α `notin` Lp ->
               Θ ⨟ (add α Δ) ⊢
                 (msubst_pskl κ (open_pskl_wrt_pskl Pib (pskl_var_f α)))
                 ⊑ᵖ[ Ψi' ] (open_uskl_wrt_uskl ψR (uskl_var_f α))) /\
            Ψi [=] add ε Ψi').
          { simpl in Hpre0.
            inversion Hpre0; subst.
            match goal with
            | Hf : forall α0, α0 `notin` ?L0 ->
                _ ⨟ _ ⊢ _ ⊑ᵖ[ ?PS ] _ |- _ =>
              exists (L0 `union` dom κ), PS; split;
                [ intros α0 Hα0;
                  rewrite msubst_pskl_open_lc_local;
                    [ apply Hf; clear - Hα0; fsetdec
                    | exact Hlcκ | clear - Hα0; fsetdec ]
                | assumption ]
            end. }
          destruct HpreF as (Lp & Ψi' & HpreF & HΨis).
          assert (HΨi's : Ψi' [<=] Ψ0').
          { pick fresh αp for (Lp `union` Lt).
            eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ
              | apply HpreF; clear - Fr; solve_notin
              | exact (a_tags_sort_d_tags
                        (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lrb
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0'
               `union` Lwi `union` Lp `union` ftvar_in_pskl Pib).
          destruct (IHX α (open_pskl_wrt_pskl Pib (pskl_var_f α)) Ψi'
                      (pskl_tophole P0') (add α Δ)
                      ltac:(clear - Fr; solve_notin)
                      ltac:(clear - Hdelta; solve_notin_auto)
                      ltac:(clear; solve_notin_auto)
                      (HwfPif α ltac:(clear - Fr; solve_notin))
                      ltac:(eapply a_wf_pskl_weaken;
                            [ intros x b Hb; apply binds_cons_3; exact Hb
                            | exact HwfP0 ])
                      ltac:(intros α0 HX0;
                            pose proof (Hapart α0 HX0) as Hs0;
                            simpl in Hs0;
                            rewrite msubst_pskl_open_lc_local;
                              [ | exact Hlcκ | clear - Fr; solve_notin ];
                            pose proof (pskl_shielded_ftv_open_upper
                              (msubst_pskl κ Pib) (pskl_var_f α)) as Hup;
                            simpl in Hup;
                            assert (HneX0 : α0 <> α)
                              by (clear - HX0 Fr; destruct_notin; fsetdec);
                            clear - Hs0 Hup HneX0; fsetdec)
                      ltac:(eapply ad_partial_precise_weaken;
                              [ apply HpreF; clear - Fr; solve_notin
                              | intros x b Hb; apply binds_cons_3;
                                exact Hb ])
                      HΨi's
                      ltac:(apply Hrefb; clear - Fr; solve_notin))
            as (ΞX & PaX & κX & HsX & HfmX & HuX & HkX & HfrX & HFX & HqX).
          assert (HαΞ : α `notin` dom ΞX)
            by (intros Hin; exact (HfrX α Hin ltac:(clear; solve_notin_auto))).
          assert (HdκX : dom κX [=] dom ΞX) by (apply keys_eq_dom; exact HkX).
          assert (HlcκX : msubst_lc (κX ++ κ))
            by (eapply msubst_lc_app_wf; [ exact HFX | exact Hlcκ ]).
          exists ΞX, (pskl_all_syn (close_pskl_wrt_pskl α PaX)), κX.
          split.
          { (* SE-ForallGhost, exists-fresh + CLOSE (DESIGN §4.3); the premise
               runs at [(β ~ tvar) ++ Θ], so [HsX] IS it. *)
            apply a_solve_eq__all_l_tophole with (β := α);
              [ clear - Fr; solve_notin | exact HsX ]. }
          split; [ exact HfmX | ].
          split; [ exact HuX | ].
          split; [ exact HkX | ].
          split; [ intros α0 Hα0; pose proof (HfrX α0 Hα0) as Hn;
                   clear - Hn; fsetdec | ].
          split; [ exact HFX | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          apply ad_ppre__forall with (ε := ε)
            (L := L `union` Lr `union` Lt `union` Lrb
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` dom κX
               `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0'
               `union` Δ' `union` singleton α
               `union` ftvar_in_pskl (msubst_pskl (κX ++ κ) PaX))
            (Ψ0 := Ψi' `union` Ψa);
            [ | clear - HΨis; fsetdec ].
          intros α' HX'.
          rewrite <- msubst_pskl_open_lc_local;
            [ | exact HlcκX
            | rewrite dom_app; clear - HX'; solve_notin ].
          assert (Hrun : ((α ~ abind_tvar) ++ Θ) ⨟
                    (add α (Δ `union` (remove α Δ'))) ⊢
                    (msubst_pskl (κX ++ κ) PaX) ⊑ᵖ[ Ψi' `union` Ψa ]
                    (open_uskl_wrt_uskl ψR (uskl_var_f α))).
          { eapply ad_partial_precise_delta_cong;
              [ apply (HqX (remove α Δ'));
                [ clear - HS1; destruct_notin; fsetdec
                | simpl; clear - HS2; fsetdec
                | intros Yd αd τ HYd Hbd;
                  destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                    as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                  eapply HS3; [ clear - HYd; fsetdec | exact Hbd' ] ]
              | clear; fsetdec ]. }
          apply (FOLD κX α PaX (Ψi' `union` Ψa) Δ' HFX
                   ltac:(clear - Fr HαΞ HdκX; destruct_notin; solve_notin_auto)
                   HS1 HS2 HS3 Hrun
                   α' ltac:(clear - HX'; solve_notin)).
        + (* Pi = □ — GhostL row.  solve = a_solve_eq__hole_l (Pa:=∀◇.P0');
             precision = ad_ppre__tophole_fill, family via rename_tvar.
             Pi0:=□ (Hpre0x = ad_ppre__hole); refinement + closure as ∀◇. *)
          assert (HΨie : Ψi [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          assert (Hhd : Δ ∩
                    (ftvar_in_uskl (uskl_all_etag ε ψR)) [=] empty)
            by (simpl in Hpre0; inversion Hpre0; assumption).
          simpl in Hhd.
          eapply solve_ext_nil with (Pa := (pskl_tophole P0')); [ apply a_solve_eq__hole_l | ].
          intros Δ' HS1 HS2 HS3.
          simpl.
          pick fresh α for
            (L `union` Lr `union` Lt `union` Lrb
             `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` ftvar_in_aenv Θ0
             `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
             `union` ftvar_in_pskl P0' `union` Δ').
          destruct (IHX α pskl_hole Ψi (pskl_tophole P0') Δ
                      ltac:(clear - Fr; solve_notin)
                      Hdelta
                      ltac:(clear; solve_notin_auto)
                      ltac:(apply a_wf_pskl__hole)
                      ltac:(eapply a_wf_pskl_weaken;
                            [ intros x b Hb; apply binds_cons_3; exact Hb
                            | exact HwfP0 ])
                      ltac:(intros α0 HX0; simpl; auto)
                      ltac:(simpl; apply ad_ppre__hole;
                            [ exact HΨie
                            | pose proof
                                (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                   (uskl_var_f α)) as Hup;
                              simpl in Hup; clear - Hhd Hup Fr;
                              destruct_notin; fsetdec ])
                      ltac:(clear - HΨie; solve_notin_auto)
                      ltac:(apply Hrefb; clear - Fr; solve_notin))
            as (ΞX & PaX & κX & HsX & _ & _ & HkX & _ & _ & HqX).
          (* ⭐ ghost subject ⇒ block and extension are [nil] *)
          destruct (a_solve_eq_hole_subject_inv HsX) as [HΞXe HPaXe]; subst.
          destruct κX as [ | ? ? ];
            [ | unfold keys in HkX; simpl in HkX; discriminate ].
          cbn [app] in HqX.
          (* α ∉ ftv(msubst κ (∀◇.P0')) *)
          assert (HXPaX : α `notin` ftvar_in_pskl
                    (msubst_pskl κ (pskl_tophole P0'))).
          { apply msubst_pskl_ftv_avoid.
            - intros p Hp; pose proof (Himav p Hp) as Hb;
                clear - Hb Fr; destruct_notin; fsetdec.
            - simpl;
              assert (HXP0' : α `notin` ftvar_in_pskl P0')
                by (pose proof (a_wf_pskl_ftv_dom HwfP0'0) as Hd;
                    clear - Hd Fr; destruct_notin; fsetdec);
              exact HXP0'. }
          apply ad_ppre__tophole_fill with (ε := ε)
            (L := Δ `union` Δ' `union` dom Θ `union` dom Θ0 `union` dom κ
               `union` singleton ε `union` singleton α `union` Δρ
               `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl (msubst_pskl κ P0')).
          intros α' HX'.
          assert (HS3' : delta_def_fresh Δ' ((α ~ abind_tvar) ++ Θ)).
          { intros Yd αd τ HYd Hbd.
            destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
              [ discriminate Hc | exact (HS3 Yd αd τ HYd Hbd') ]. }
          pose proof (HqX Δ' HS1
                        ltac:(simpl; clear - HS2 Fr; destruct_notin; solve_notin_auto)
                        HS3') as Hq1.
          pose proof (@ad_partial_precise_rename_tvar
                        _ _ _ _ _ Hq1 α α' (@nil (atom * abind)) Θ
                        ltac:(apply a_wf_aenv_uniq; apply a_wf_aenv__tvar;
                              [ clear - Fr; solve_notin | exact HwfΘ ])
                        eq_refl
                        ltac:(simpl; clear - Fr HX'; solve_notin)
                        ltac:(clear - HX'; solve_notin)
                        ltac:(simpl; clear - HX' HXPaX; simpl in HXPaX;
                              solve_notin)
                        ltac:(pose proof
                                (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                   (uskl_var_f α)) as Hup;
                              simpl in Hup; clear - HX' Hup;
                              destruct_notin; fsetdec)
                        ltac:(intros αd τ Hb;
                              destruct (binds_cons_1 _ _ _ _ _ _ Hb)
                                as [[_ Hc] | Hb'];
                                [ discriminate Hc | ];
                              assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                                by (eapply a_wf_aenv_def_ftv_dom;
                                    [ exact HwfΘ | exact Hb' ]);
                              split; [ clear - Hd Fr | clear - Hd HX' ];
                              destruct_notin; solve_notin_auto))
            as Hren.
          simpl in Hren.
          rewrite (subst_pskl_in_pskl_fresh_eq _ (pskl_var_f α') α)
            in Hren;
            [ | simpl in HXPaX; exact HXPaX ].
          rewrite <- (subst_bskl_in_uskl_intro α ψR (uskl_var_f α')
                        ltac:(clear - Fr; solve_notin)) in Hren.
          exact Hren.
        + (* Pi = ∀◇.Pi' — UnivGhost row.  WRAPPED IHX (Pi0:=∀◇.Pi',
             P0i:=∀◇.P0'); refinement = Hrefb verbatim; solve = IHX output
             (tophole_both, strengthen_tvar); precision =
             ad_ppre__tophole_fill (subject ∀◇.P', keeps Ψ, no ε), family
             built by ad_partial_precise_rename_tvar (aenv-tvar rename). *)
          assert (HgPi'w : guarded_pskl Pi' /\ (Θ0 ⨟ empty ⊢ₚₛᵃ Pi'))
            by (inversion HwfPi; subst; split; assumption).
          destruct HgPi'w as [HgPi' HwfPi'].
          assert (Hdisj :
            (Θ ⨟ Δ ⊢ (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ] (uskl_all_etag ε ψR)) \/
            (exists Lf, forall α, α `notin` Lf ->
               ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢
                 pskl_tophole (msubst_pskl κ Pi') ⊑ᵖ[ Ψi ]
                 (open_uskl_wrt_uskl ψR (uskl_var_f α)))).
          { simpl in Hpre0. inversion Hpre0; subst;
              [ left; assumption | right; eexists; eassumption ]. }
          destruct Hdisj as [Hrem | (Lf & HF)].
          * (* remove: the guarded body dies against the ε-tagged target *)
            exfalso. inversion HgPi'; subst.
            -- simpl in Hrem. inversion Hrem.
            -- assert (HΨ'e : Ψ' [=] empty).
               { eapply ad_ppre_mono_subject_target_tags_empty
                   with (τ := msubst_lookup κ α);
                   [ exact HwfΘ | exact Hrem | reflexivity
                   | eapply a_inc_lookup_mono; eauto
                   | exact (a_tags_sort_d_tags Htags0) ]. }
               clear - HΨ'e HΨ'eq Hεnin; fsetdec.
            -- simpl in Hrem. inversion Hrem.
          * (* fill *)
            assert (HΨiS : Ψi [<=] Ψ0').
            { pick fresh αp for (Lf `union` Lt `union` dom Θ).
              assert (HwfΘx : a_wf_aenv ((αp ~ abind_tvar) ++ Θ))
                by (apply a_wf_aenv__tvar;
                    [ clear - Fr; solve_notin | exact HwfΘ ]).
              eapply ad_partial_precise_tags_sub;
                [ exact HwfΘx
                | apply HF; clear - Fr; solve_notin
                | exact (a_tags_sort_d_tags
                          (Htagsf αp ltac:(clear - Fr; solve_notin))) ]. }
            pick fresh α for
              (L `union` Lr `union` Lt `union` Lrb
               `union` Δ `union` Δρ `union` dom Θ `union` dom Θ0 `union` dom Θr
               `union` ftvar_in_aenv Θ0
               `union` dom κ `union` singleton ε `union` ftvar_in_uskl ψR
               `union` ftvar_in_pskl P0' `union` Lf `union` ftvar_in_pskl Pi').
            destruct (IHX α (pskl_tophole Pi') Ψi (pskl_tophole P0') Δ
                        ltac:(clear - Fr; solve_notin)
                        Hdelta
                        ltac:(clear; solve_notin_auto)
                        ltac:(eapply a_wf_pskl_weaken;
                              [ intros x b Hb; apply binds_cons_3; exact Hb
                              | exact HwfPi ])
                        ltac:(eapply a_wf_pskl_weaken;
                              [ intros x b Hb; apply binds_cons_3; exact Hb
                              | exact HwfP0 ])
                        Hapart
                        (HF α ltac:(clear - Fr; solve_notin))
                        HΨiS
                        ltac:(apply Hrefb; clear - Fr; solve_notin))
              as (ΞX & PaX & κX & HsX & HfmX & HuX & HkX & HfrX & HFX & HqX).
            (* ⚙️ SE-UnivGhost has NO binder of its own, so the strengthening
               IS still needed here (unlike the three ∀ rows). *)
            assert (HsX0 : Θ0 ⊢ₑ (pskl_tophole Pi') ∼ (pskl_tophole P0')
                      ⤳ ΞX ⨾ PaX)
              by (eapply a_solve_eq_strengthen_tvar; exact HsX).
            assert (HαΞ : α `notin` dom ΞX)
              by (intros Hin; exact (HfrX α Hin ltac:(clear; solve_notin_auto))).
            assert (HdκX : dom κX [=] dom ΞX) by (apply keys_eq_dom; exact HkX).
            assert (HimX : forall p, In p (κX ++ κ) ->
                      α `notin` ftvar_in_ptyp (snd p)).
            { intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp | Hp].
              - assert (Hd := forall_wf_mono_images_dom HFX p Hp).
                assert (Hdw : dom Θw [<=] dom Θ)
                  by (apply aenv_binds_dom_sub; exact Hmon).
                clear - Hd Hdw Fr; destruct_notin; fsetdec.
              - pose proof (Himav p Hp) as Hb;
                  clear - Hb Fr; destruct_notin; fsetdec. }
            (* α ∉ ftv(msubst (κX++κ) PaX): ftv PaX ⊆ ftv Pi' ∪ ftv P0' ∪ dom ΞX,
               all three α-free *)
            assert (HXPaX : α `notin`
                      ftvar_in_pskl (msubst_pskl (κX ++ κ) PaX)).
            { apply msubst_pskl_ftv_avoid; [ exact HimX | ].
              pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ _ HsX) as Hfsub;
                simpl in Hfsub.
              assert (HXPi' : α `notin` ftvar_in_pskl Pi')
                by (pose proof (a_wf_pskl_ftv_dom HwfPi') as Hd;
                    clear - Hd Fr; simpl in Hd; destruct_notin; fsetdec).
              assert (HXP0' : α `notin` ftvar_in_pskl P0')
                by (pose proof (a_wf_pskl_ftv_dom HwfP0'0) as Hd;
                    clear - Hd Fr; destruct_notin; fsetdec).
              clear - Hfsub HXPi' HXP0' HαΞ; fsetdec. }
            (* tophole_both ⇒ PaX = ∀◇.Pbody (avoid global subst: HeqΘ would
               clear Θ) *)
            assert (Hpaform : exists Pbody, PaX = pskl_tophole Pbody).
            { inversion HsX;
                solve [ eexists; reflexivity
                      | match goal with
                        | Hg : guarded_pskl (pskl_tophole _) |- _ =>
                          inversion Hg
                        end ]. }
            destruct Hpaform as [Pbody Hpeq]; subst PaX.
            exists ΞX, (pskl_tophole Pbody), κX.
            split; [ exact HsX0 | ].
            split; [ exact HfmX | ].
            split; [ exact HuX | ].
            split; [ exact HkX | ].
            split; [ intros α0 Hα0; pose proof (HfrX α0 Hα0) as Hn;
                     clear - Hn; fsetdec | ].
            split; [ exact HFX | ].
            intros Δ' HS1 HS2 HS3.
            simpl.
            apply ad_ppre__tophole_fill with (ε := ε)
              (L := Δ `union` Δ' `union` dom Θ `union` dom Θ0 `union` dom κ
                 `union` dom κX
                 `union` singleton ε `union` singleton α `union` Δρ
                 `union` ftvar_in_uskl ψR
                 `union` ftvar_in_pskl (msubst_pskl (κX ++ κ) Pbody)).
            intros α' HX'.
            (* rename α↦α' in the single IHX precision instance *)
            assert (HS3' : delta_def_fresh Δ' ((α ~ abind_tvar) ++ Θ)).
            { intros Yd αd τ HYd Hbd.
              destruct (binds_cons_1 _ _ _ _ _ _ Hbd) as [[_ Hc] | Hbd'];
                [ discriminate Hc | exact (HS3 Yd αd τ HYd Hbd') ]. }
            (* α was picked BEFORE Δ' (it flows into the solve output), so
               instantiate the family at Δ'∖{α} and weaken the missing
               Δ'∩{α} back at the end (α is fresh for the renamed target). *)
            pose proof (HqX (remove α Δ')
                          ltac:(clear - HS1; solve_notin_auto)
                          ltac:(simpl; clear - HS2; solve_notin_auto)
                          ltac:(intros Yd αd τ HYd Hbd;
                                eapply HS3';
                                  [ clear - HYd; solve_notin_auto | exact Hbd ]))
              as Hq1.
            pose proof (@ad_partial_precise_rename_tvar
                          _ _ _ _ _ Hq1 α α' (@nil (atom * abind)) Θ
                          ltac:(apply a_wf_aenv_uniq; apply a_wf_aenv__tvar;
                                [ clear - Fr; solve_notin | exact HwfΘ ])
                          eq_refl
                          ltac:(simpl; clear - Fr HX'; solve_notin)
                          ltac:(clear - HX'; solve_notin)
                          ltac:(simpl; clear - HX' HXPaX; simpl in HXPaX;
                                solve_notin)
                          ltac:(pose proof
                                  (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                     (uskl_var_f α)) as Hup;
                                simpl in Hup; clear - HX' Hup;
                                destruct_notin; fsetdec)
                          ltac:(intros αd τ Hb;
                                destruct (binds_cons_1 _ _ _ _ _ _ Hb)
                                  as [[_ Hc] | Hb'];
                                  [ discriminate Hc | ];
                                assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                                  by (eapply a_wf_aenv_def_ftv_dom;
                                      [ exact HwfΘ | exact Hb' ]);
                                split; [ clear - Hd Fr | clear - Hd HX' ];
                                destruct_notin; solve_notin_auto))
              as Hren.
            simpl in Hren.
            rewrite (subst_pskl_in_pskl_fresh_eq _ (pskl_var_f α') α)
              in Hren;
              [ | simpl in HXPaX; exact HXPaX ].
            rewrite <- (subst_bskl_in_uskl_intro α ψR (uskl_var_f α')
                          ltac:(clear - Fr; solve_notin)) in Hren.
            eapply ad_partial_precise_delta_cong;
              [ eapply ad_partial_precise_delta_weaken_fresh
                  with (Δ' := Δ' ∩ singleton α);
                  [ exact Hren
                  | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψR
                                  (uskl_var_f α')) as Hup;
                    simpl in Hup;
                    apply atoms_inter_empty_pointwise;
                    intros y Hy;
                    assert (Heqy : y = α) by (clear - Hy; fsetdec);
                    subst y;
                    clear - Fr HX' Hup; destruct_notin; fsetdec
                  | intros Yd αd τ HYd Hbd;
                    assert (Heqy : Yd = α) by (clear - HYd; fsetdec);
                    subst Yd;
                    destruct (binds_cons_1 _ _ _ _ _ _ Hbd)
                      as [[_ Hc] | Hbd']; [ discriminate Hc | ];
                    assert (Hd : ftvar_in_ptyp τ [<=] dom Θ)
                      by (eapply a_wf_aenv_def_ftv_dom;
                          [ exact HwfΘ | exact Hbd' ]);
                    clear - Hd Fr; destruct_notin; fsetdec ]
              | clear; fsetdec ]. }
    (* the tophole_fill family leaves the rule's ε-witness unconstrained
       (any ε inhabits the same family); discharge it with the case's ε. *)
    Unshelve. all: match goal with |- εvar => exact ε | |- _ => idtac end.
    destruct (uskl_rho_all_etag_l_inv Hrho)
      as [[Heqψa HΨρe] | [Hleaf | (Lr & ψR & Heqψa & Hrhof)]].
    + (* refl *)
      subst ψa.
      assert (Htskf : exists Li, forall α, α `notin` Li ->
                is_tskl (open_uskl_wrt_uskl R (uskl_var_f α))).
      { destruct (a_tags_sort_all_etag_inv Htags)
          as (Lt0 & Ψt0 & Hf & _ & _).
        exists Lt0; intros α0 Hα0. destruct (Hf α0 Hα0); assumption. }
      destruct Htskf as (Li & Htskf).
      apply (KEYF R Li);
        [ intros α0 Hα0; apply urho__refl;
            [ apply is_tskl_lc; apply Htskf; exact Hα0 | exact HΨρe ]
        | exact Htags | exact Hpre ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
    + subst ψa.
      apply (KEYF ψR Lr);
        [ exact Hrhof | exact Htags | exact Hpre ].
  - (* forall_syn: tag-sort absurd *)
    destruct (uskl_rho_all_syn_l_inv Hrho)
      as [[-> _] | [Hleaf | (L' & R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* ghostg *)
    assert (Hrefine' : Θ ⨟ empty ⊢ᵣᵃ
              (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ bskl_hole)
      by (eapply refine_primary_to_plain_split; eassumption).
    destruct (uskl_rho_holeg_l_inv Hrho) as [[-> HΨρ] | Hleaf].
    + assert (HΨ'e : Ψ' [=] empty)
        by (exact (d_tags_skl_holeg_inv (a_tags_sort_d_tags Htags))).
      assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
      destruct (a_solve_eq_cv_ghostg HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hpre Hrefine')
        as (Pa & Hsolve & Hprec).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hsolve | ].
      intros Δ' HS1 HS2 HS3.
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_partial_precise_delta_weaken_fresh;
            [ exact Hprec | simpl; clear; fsetdec | exact HS3 ]
        | clear - HΨae; fsetdec ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
  - (* topholeg: the ∀◈ congruence — recurse through the main IH.  Both
       the refl and congruence branches of the ρ-inversion land in KEY. *)
    assert (HwfΘr2 := HwfΘr).
    assert (KEY : forall ψa0,
      uskl_rho NM Θ Δρ Ψρ R ψa0 ->
      a_tags_sort NM Ψ' (uskl_topholeg ψa0) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_topholeg ψa0) ->
      p6cv_concl Θ0 Θ Θw Θr κ Δ Ψi Ψa (uskl_topholeg ψa0) Pi P0 Lav).
    { intros ψa0 Hrho0 Htags0 Hpre0.
      assert (Htags1 : a_tags_sort NM Ψ' ψa0)
        by (apply a_tags_sort_topholeg_inv; exact Htags0).
      (* the P0=□ rows' target bound: ψa0's variables are Θr- or
         Δρ-scoped once the counterpart is a synthesised fill *)
      assert (HψaB : ftvar_in_bskl Q [<=] dom Θr ->
                ftvar_in_uskl ψa0 [<=] dom Θr `union` Δρ).
      { intros HQB.
        assert (HftR : ftvar_in_uskl R [<=]
                  ftvar_in_bskl Q `union` dom Θr)
          by (eapply consis_subject_ftv_bag_bound;
                [ exact Hconsis | exact HspΘ | exact Htvs | exact HwfΘr ]).
        pose proof (uskl_rho_ftv_target_bound Hrho0) as HftA.
        clear - HQB HftR HftA; fsetdec. }
      destruct Pi as [ | nb | α | Pi1 Pi2 | Pib | | Pi' ].
      - (* Pi = unit: no precision into ∀◈ *)
        simpl in Hpre0. inversion Hpre0.
      - (* Pi = var_b *) inversion HwfPi.
      - (* Pi = var: mono paint, absurd *)
        exfalso. simpl in Hpre0.
        eapply ad_ppre_mono_paint_topholeg_absurd;
          [ exact HwfΘ | exact Hpre0 | reflexivity | reflexivity
          | eapply a_inc_lookup_mono; eauto ].
      - (* Pi = arrow *) simpl in Hpre0. inversion Hpre0.
      - (* Pi = all_syn *) simpl in Hpre0. inversion Hpre0.
      - (* Pi = □: SE-GhostL / VacuousR column *)
        destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
        + (* P0 = unit *) simpl in Hrefine. inversion Hrefine.
        + (* P0 = var_b *) inversion HwfP0.
        + (* P0 = var: mono paint vs ∀◇ RHS, absurd *)
          exfalso. simpl in Hrefine.
          assert (Hml : mono_ptyp (msubst_lookup κ β))
            by (eapply a_inc_lookup_mono; eauto).
          rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
          eapply ad_refine_mono_paint_tophole_rhs_absurd;
            [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
            | exact Hml ].
        + (* P0 = arrow *) simpl in Hrefine. inversion Hrefine.
        + (* P0 = all_syn *) simpl in Hrefine. inversion Hrefine.
        + (* P0 = □: SE-VacuousR; Q synthesized ⇒ Ψa = ∅ *)
          simpl in Hrefine.
          pose proof (ad_refine_syn_hole_sskl Hrefine eq_refl) as Hss.
          assert (HskQ : is_sskl Q) by (inversion Hss; subst; assumption).
          pose proof (ad_pat_consis_sskl_tags Hconsis HwfΘ HskQ) as HΨe.
          assert (HQB : ftvar_in_bskl Q [<=] dom Θr).
          { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine).
            simpl in Ht. clear - Ht; fsetdec. }
          eapply solve_ext_nil with (Pa := pskl_hole); [ apply a_solve_eq__hole_r | ].
          intros Δ' HS1 HS2 HS3.
          eapply ad_partial_precise_psi_cong;
            [ eapply ad_partial_precise_delta_weaken_fresh;
                [ exact Hpre0
                | simpl;
                  pose proof (HψaB HQB) as Hbb;
                  clear - Hbb HS1 HS2 Hdelta; fsetdec
                | exact HS3 ]
            | clear - HΨe Hsubeq2; fsetdec ].
        + (* P0 = ∀◇.P0': Pa := P0; body precision via the main IH at □ *)
          assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
            by (inversion HwfP0; assumption).
          assert (HgP0' : guarded_pskl P0')
            by (inversion HwfP0; assumption).
          simpl in Hrefine.
          inversion Hrefine; subst.
          * (* tophole_remove: the guarded body dies against a ∀◇ RHS *)
            exfalso. inversion HgP0'; subst.
            -- match goal with
               | Hin : _ ⨟ _ ⊢ᵣᵃ
                   pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ |- _ =>
                 simpl in Hin; inversion Hin
               end.
            -- match goal with
               | Hin : _ ⨟ _ ⊢ᵣᵃ
                   pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _
                 |- _ =>
                 let Hml := fresh in
                 assert (Hml : mono_ptyp (msubst_lookup κ v))
                   by (eapply a_inc_lookup_mono; eauto);
                 simpl in Hin;
                 rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
                 eapply ad_refine_mono_paint_tophole_rhs_absurd;
                   [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                   | exact Hml ]
               end.
            -- match goal with
               | Hin : _ ⨟ _ ⊢ᵣᵃ
                   pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _
                 |- _ =>
                 simpl in Hin; inversion Hin
               end.
          * (* tophole_keep: recurse with Pi := □ *)
            assert (Hhp0 : Θ ⨟ Δ ⊢
                      msubst_pskl κ pskl_hole ⊑ᵖ[ Ψi ] ψa0).
            { simpl. simpl in Hpre0. inversion Hpre0; subst.
              match goal with
              | HΨE : Ψi [=] empty,
                Hint : _ ∩ _ [=] empty |- _ =>
                apply ad_ppre__hole; [ exact HΨE | ];
                simpl in Hint; exact Hint
              end. }
            match goal with
            | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ Q
              |- _ =>
              destruct (IHHconsis NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr
                          Ψρ Ψ' Ψi Ψa ψa0 pskl_hole P0'
                          HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                          HwfΘ HwfΘ0 Hmon Hnr
                          ltac:(apply a_wf_pskl__hole) HwfP0'
                          Hκ Hκw
                          Hrho0 Htags1 Hsub Hinter Hfresh Hdelta
                          ltac:(intros α0 HX0; simpl; auto)
                          Hdfresh
                          Hhp0 Hsubeq1 Hsubeq2 Hin Lav HLav)
                as (Ξ' & Pa' & κ' & Hs' & _ & _ & Hk' & _ & _ & Hq')
            end.
            (* ghost subject ⇒ block and extension are [nil] *)
            destruct (a_solve_eq_hole_subject_inv Hs') as [HΞ'e HPa']; subst.
            destruct κ' as [ | ? ? ];
              [ | unfold keys in Hk'; simpl in Hk'; discriminate ].
            eapply solve_ext_nil with (Pa := (pskl_tophole P0'));
              [ apply a_solve_eq__hole_l | ].
            intros Δ' HS1 HS2 HS3.
            cbn [app]. simpl. apply ad_ppre__tophole_keep.
            exact (Hq' Δ' HS1 HS2 HS3).
      - (* Pi = ∀◇.Pi' *)
        assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
        assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi') by (inversion HwfPi; assumption).
        simpl in Hpre0. inversion Hpre0; subst.
        + (* tophole_remove: the guarded body dies against ∀◈ *)
          exfalso. inversion HgPi'; subst.
          * match goal with
            | Hp' : _ ⨟ _ ⊢ msubst_pskl κ pskl_unit ⊑ᵖ[ _ ] _ |- _ =>
                simpl in Hp'; inversion Hp'
            end.
          * match goal with
            | Hp' : _ ⨟ _ ⊢ msubst_pskl κ (pskl_var_f ?v) ⊑ᵖ[ _ ] _ |- _ =>
                simpl in Hp';
                eapply ad_ppre_mono_paint_topholeg_absurd;
                  [ exact HwfΘ | exact Hp' | reflexivity | reflexivity
                  | eapply a_inc_lookup_mono; eauto ]
            end.
          * match goal with
            | Hp' : _ ⨟ _ ⊢ msubst_pskl κ (pskl_arrow _ _) ⊑ᵖ[ _ ] _ |- _ =>
                simpl in Hp'; inversion Hp'
            end.
        + (* tophole_keep: the live congruence *)
          match goal with
          | Hp' : _ ⨟ _ ⊢ msubst_pskl κ Pi' ⊑ᵖ[ _ ] ψa0 |- _ =>
            rename Hp' into Hpre1
          end.
          assert (Hapart' : forall α, α `in` Δρ ->
                    α `notin` pskl_shielded_ftv (msubst_pskl κ Pi')).
          { intros α0 HX0.
            pose proof (Hapart α0 HX0) as Hsh. simpl in Hsh.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi')).
            fsetdec. }
          destruct P0 as [ | nb0 | β | P01 P02 | P0b | | P0' ].
          * (* P0 = unit *) simpl in Hrefine. inversion Hrefine.
          * (* P0 = var_b *) inversion HwfP0.
          * (* P0 = var: mono paint vs ∀◇ RHS *)
            exfalso. simpl in Hrefine.
            assert (Hml : mono_ptyp (msubst_lookup κ β))
              by (eapply a_inc_lookup_mono; eauto).
            rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hrefine.
            eapply ad_refine_mono_paint_tophole_rhs_absurd;
              [ exact HwfΘr | exact Hrefine | reflexivity | reflexivity
              | exact Hml ].
          * (* P0 = arrow *) simpl in Hrefine. inversion Hrefine.
          * (* P0 = all_syn *) simpl in Hrefine. inversion Hrefine.
          * (* P0 = □: SE-VacuousR *)
            simpl in Hrefine.
            pose proof (ad_refine_syn_hole_sskl Hrefine eq_refl) as Hss.
            assert (HskQ : is_sskl Q) by (inversion Hss; subst; assumption).
            pose proof (ad_pat_consis_sskl_tags Hconsis HwfΘ HskQ) as HΨe.
            assert (HQB : ftvar_in_bskl Q [<=] dom Θr).
            { assert (Ht := ad_refine_syn_ftv_rhs_bound HwfΘr Hrefine).
              simpl in Ht. clear - Ht; fsetdec. }
            eapply solve_ext_nil with (Pa := (pskl_tophole Pi'));
              [ apply a_solve_eq__hole_r | ].
            intros Δ' HS1 HS2 HS3.
            eapply ad_partial_precise_psi_cong;
              [ simpl; apply ad_ppre__tophole_keep;
                eapply ad_partial_precise_delta_weaken_fresh;
                  [ exact Hpre1
                  | pose proof (HψaB HQB) as Hbb;
                    clear - Hbb HS1 HS2 Hdelta; fsetdec
                  | exact HS3 ]
              | clear - HΨe Hsubeq2; fsetdec ].
          * (* P0 = ∀◇.P0': SE-UnivGhost via the main IH *)
            assert (HwfP0' : Θ0 ⨟ empty ⊢ₚₛᵃ P0')
              by (inversion HwfP0; assumption).
            assert (HgP0' : guarded_pskl P0')
              by (inversion HwfP0; assumption).
            simpl in Hrefine.
            inversion Hrefine; subst.
            -- (* tophole_remove: guarded body dies *)
               exfalso. inversion HgP0'; subst.
               ++ match goal with
                  | Hin : _ ⨟ _ ⊢ᵣᵃ
                      pskl_to_bskl_inh (msubst_pskl κ pskl_unit) ⊳ _ |- _ =>
                    simpl in Hin; inversion Hin
                  end.
               ++ match goal with
                  | Hin : _ ⨟ _ ⊢ᵣᵃ
                      pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f ?v)) ⊳ _
                    |- _ =>
                    let Hml := fresh in
                    assert (Hml : mono_ptyp (msubst_lookup κ v))
                      by (eapply a_inc_lookup_mono; eauto);
                    simpl in Hin;
                    rewrite (ptyp_to_bskl_inh_syn_eq Hml) in Hin;
                    eapply ad_refine_mono_paint_tophole_rhs_absurd;
                      [ exact HwfΘr | exact Hin | reflexivity | reflexivity
                      | exact Hml ]
                  end.
               ++ match goal with
                  | Hin : _ ⨟ _ ⊢ᵣᵃ
                      pskl_to_bskl_inh (msubst_pskl κ (pskl_arrow _ _)) ⊳ _
                    |- _ =>
                    simpl in Hin; inversion Hin
                  end.
            -- (* tophole_keep: recurse *)
               match goal with
               | Hin : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0') ⊳ Q
                 |- _ =>
                 destruct (IHHconsis NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr
                             Ψρ Ψ' Ψi Ψa ψa0 Pi' P0'
                             HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                             HwfΘ HwfΘ0 Hmon Hnr HwfPi' HwfP0' Hκ Hκw
                             Hrho0 Htags1 Hsub Hinter Hfresh Hdelta
                             Hapart' Hdfresh
                             Hpre1 Hsubeq1 Hsubeq2 Hin Lav HLav)
                   as (Ξ' & Pa' & κ' & Hs' & Hfm' & Hu' & Hk' & Hfr' & HF' & Hq')
               end.
               (* SE-UnivGhost is a PASS-THROUGH: the whole package rides *)
               exists Ξ', (pskl_tophole Pa'), κ'.
               split; [ apply a_solve_eq__tophole_both; exact Hs' | ].
               split; [ exact Hfm' | ].
               split; [ exact Hu' | ].
               split; [ exact Hk' | ].
               split; [ exact Hfr' | ].
               split; [ exact HF' | ].
               intros Δ' HS1 HS2 HS3.
               simpl. apply ad_ppre__tophole_keep.
               exact (Hq' Δ' HS1 HS2 HS3). }
    destruct (uskl_rho_topholeg_l_inv Hrho)
      as [[Heqψa HΨρ] | [Hleaf | (ψa0 & Heqψa & Hrho0)]].
    + (* refl: recast as a congruence with a refl body-ρ *)
      subst ψa.
      assert (HlcR : lc_uskl R).
      { apply is_tskl_lc.
        match goal with Ht : a_tags_sort _ _ (uskl_topholeg R) |- _ =>
          inversion Ht; subst;
          match goal with Hti : is_tskl (uskl_topholeg _) |- _ =>
            inversion Hti; subst; assumption end end. }
      apply KEY;
        [ apply urho__refl; [ exact HlcR | exact HΨρ ]
        | exact Htags | exact Hpre ].
    + destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                  HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
        as (Pa & Hs & Hq).
      eapply solve_ext_nil with (Pa := Pa); [ exact Hs | ].
      intros Δ' HS1 HS2 HS3. apply Hq. clear; fsetdec.
    + subst ψa.
      apply KEY; [ exact Hrho0 | exact Htags | exact Hpre ].
  - (* hole: ψa is tag-sorted, hence never a PLAIN ghost *)
    destruct (uskl_rho_hole_l_inv Hrho) as [[-> _] | Hleaf].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
  - (* tophole *)
    destruct (uskl_rho_tophole_l_inv Hrho)
      as [[-> _] | [Hleaf | (R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* tophole_inh *)
    destruct (uskl_rho_tophole_l_inv Hrho)
      as [[-> _] | [Hleaf | (R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* tophole_drop *)
    destruct (uskl_rho_tophole_l_inv Hrho)
      as [[-> _] | [Hleaf | (R' & -> & _)]].
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
    + destruct Hleaf as (α & Ψ'' & _ & _ & Htagsub & _ & _).
      pose proof (a_tags_sort_d_tags Htagsub) as Hd; inversion Hd.
    + pose proof (a_tags_sort_d_tags Htags) as Hd; inversion Hd.
  - (* flex_l: switch the whole problem to the definition's mono paint *)
    destruct (uskl_rho_var_l_inv Hrho) as [[-> HΨρ] | Hleaf];
      [ | destruct (@p6cv_close_leaf_mono _ Θ0 _ _ _ _ _ _ _ _ _ _ _ P0
                      HwfΘ Htags Hsub Hfresh Hdelta Hapart Hpre Hleaf)
            as (Pa & Hs & Hq);
          eapply solve_ext_nil with (Pa := Pa);
            [ exact Hs
            | intros Δ' HS1 HS2 HS3; apply Hq; clear; fsetdec ] ].
    assert (HΨ'e : Ψ' [=] empty)
      by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
    assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact H ]).
    assert (HΨie : Ψi [=] empty)
      by (eapply ad_ppre_mono_tags_empty with (τ := ptyp_var_f α);
            [ exact HwfΘ | exact Hpre | reflexivity | apply mono_ptyp__var ]).
    destruct (IHHconsis NM Θ0 Θtv Θr Θ0r κ Δ Δρ Δr empty empty Ψi empty
                (ptyp_to_uskl_syn τ) Pi P0
                HspΘ HspΘ0 HwfΘr Htvs HΔrd HΔρtv
                HwfΘ HwfΘ0 Hmon Hnr HwfPi HwfP0 Hκ Hκw
                ltac:(apply urho__refl;
                        [ apply mono_ptyp_to_uskl_syn_lc; exact Hmd
                        | solve_notin_auto ])
                ltac:(apply a_tags_sort_mono_paint; exact Hmd)
                ltac:(clear - HΨie; solve_notin_auto)
                ltac:(clear; solve_notin_auto)
                Hfresh Hdelta Hapart Hdfresh
                ltac:(eapply ad_ppre_flexdef_target_unfold;
                        [ exact HwfΘ | exact Hdfresh | exact Hpre
                        | reflexivity | eassumption ])
                ltac:(clear - Hsubeq1 HΨρ HΨae; solve_notin_auto)
                ltac:(clear; solve_notin_auto)
                Hrefine Lav HLav)
      as (Ξ0 & Pa & κ0 & Hsolve & Hfm0 & Hu0 & Hk0 & Hfr0 & HF0 & Hprec).
    exists Ξ0, Pa, κ0.
    split; [ exact Hsolve | ].
    split; [ exact Hfm0 | ].
    split; [ exact Hu0 | ].
    split; [ exact Hk0 | ].
    split; [ exact Hfr0 | ].
    split; [ exact HF0 | ].
    intros Δ' HS1 HS2 HS3.
    eapply ad_partial_precise_psi_cong;
      [ eapply ad_ppre__flex_r;
          [ eassumption | exact (Hprec Δ' HS1 HS2 HS3) ]
      | clear - HΨae; fsetdec ].
  - (* flex_r: unfold the counterpart-side definition in the PRIMARY
       refinement (the defined flexible lives in Θr) *)
    assert (HwfΘr2 := HwfΘr).
    assert (Hbdef : binds α (abind_flex_mono_def τ) Θr).
    { eapply aenv_split_binds_def_r;
        [ exact HspΘ | exact Htvs | eassumption ]. }
    eapply IHHconsis; try eassumption.
    eapply ad_refine_flexdef_target_unfold;
      [ exact HwfΘr | exact Hrefine | reflexivity | exact Hbdef ].
Qed.

(* ===================================================================== *)
(*  THE PAPER STATEMENT — P6-Cv,                                          *)
(*  [lemma:complete-consistency-constraint-collection-solving-var]        *)
(*  (consistency-proofs.tex:1180), via _gen at Θtv := [] / Δr := ∅ /      *)
(*  R := ∅.  Premises are annotated inline; the MECH-ONLY ones, and what  *)
(*  callers (P6-Cs consistency-proofs.tex:993; P6-Rv subtyping-proofs     *)
(*  .tex:1778/1965/2035) owe for them:                                    *)
(*   1. (REMOVED 2026-07-27) an earlier closure carried a MECH-ONLY       *)
(*      [pskl_no_hole P0] premise: with the LIST split Θ = Θtv ++ Θr the  *)
(*      ForallSyn binder was forced into Θtv, so the tophole_fill body    *)
(*      had to be transported aenv→Δr — false for □-sources whose fill    *)
(*      mentions the binder (inh(□→1) ⊳ β→1, fill β).  The BAG split     *)
(*      [aenv_split] lets that binder join Θr instead, the body is the   *)
(*      IH's refinement premise verbatim, and holey P0 flows through the  *)
(*      recursion to the per-row SolE-VacuousR columns — exactly the      *)
(*      paper's per-node "P0 = Hole" dispatch.  The statement is now      *)
(*      PREMISE-FAITHFUL to the paper on this point.                      *)
(*   2. delta_def_fresh Δ Θ — the paper's implicit wf of the Δ-extended   *)
(*      context; machine-checked necessary; free at call sites            *)
(*      (WF-SIDE-CONDITIONS §7: binders postdate definitions).            *)
(*   3. flex_apart Θ0 Δρ P0 ψa — the LE-FlexR freshening invariant (a     *)
(*      raw Θ0-flex of P0 never faces a ρ-replaced part of ψa); NOT       *)
(*      derivable from the other premises (cex_p6_flex_freshened.v);      *)
(*      ⭕ and, since 2026-08-05, NOT CONSUMED BY THIS PROOF EITHER —     *)
(*      see the annotation on the premise itself.  The witness that       *)
(*      motivated it (cex_p6_flex_counterpart.v) is RETRACTED, killed by  *)
(*      the repaired SolE-FlexR (cex/probe_flexr_neutralises_p6.v).       *)
(*      vacuous (fa_clean) at every ρ = id call site, e.g. P6-Cs's,       *)
(*      since Δρ = ∅ — only the P6-Rv ForallL descent maintains it.       *)
(*   4. the rho_fresh / Δρ ⊆ Δ / shielded pack — replaces the paper's     *)
(*      positional "Pi has the same rigid variable at every ρ-position"   *)
(*      side condition ([paper-gap], see the sub/look/prop_rho_relation.v         *)
(*      header); established at the one leaf-creating call site, P6-Rv    *)
(*      ForallL.                                                          *)
(*  CONCLUSION vs paper: κa is instantiated to κ itself (a strengthening  *)
(*  — the paper's κa-inc and κ ≡ κa conjuncts become trivial); Θ0 ⊢ Pa    *)
(*  is omitted (recover by solve-output wf preservation when P6-Cs        *)
(*  needs it).                                                            *)
(*  PROOF/CASE MAP (the _gen induction is on the ad_pat_consis            *)
(*  derivation of the subject ψsub = ρ(ψa), as the paper prescribes):     *)
(*  unit/var/ghostg ↔ Case Unit/Var/GhostG; arrow ↔ Case Arrow (+ the     *)
(*  flexible-P0 subcase repair, DESIGN §6(g)); forall_inh_tagged ↔        *)
(*  ForallInh; forall_syn_tagged ↔ ForallSyn; topholeg ↔ UnivGhostG;      *)
(*  hole ↔ Ghost (impossible); tophole ↔ UnivGhost; tophole_inh ↔         *)
(*  UnivGhost1; tophole_drop ↔ UnivGhost2; forall_inh_untagged/           *)
(*  forall_syn ↔ the β1 = · instances of C-ForallInh/C-ForallSyn (the      *)
(*  paper's ∀^β1 subject carries a POTENTIAL tag β1 ::= · | ε,              *)
(*  declarative.tex:884 — one paper rule per target = two mech            *)
(*  constructors), absurd here since the tags-sorted target forces        *)
(*  β1 = ε; flex_l/flex_r ↔ paper C-FlexL/C-FlexR                          *)
(*  (full-algo-spec.tex:183/190) — real paper rules, merely OMITTED from  *)
(*  the paper proof's case list (routine definition-unfolding).  The      *)
(*  paper's upfront special case "ψa is a ρ-replaced rigid variable" is   *)
(*  handled per-case via the uskl_rho_*_l_inv leaf disjunct +             *)
(*  p6cv_close_leaf_mono; its "P0 = Hole" special case is the per-case    *)
(*  SolE-VacuousR columns (P0-grids of the arrow/∀/∀◇ cases and the       *)
(*  leaf-closer lemmas), re-dispatched inside every IH exactly as the     *)
(*  paper's proof does.                                                   *)
(* ===================================================================== *)
Theorem a_solve_eq_complete_var :
  forall NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->      (* paper: prose "all inputs wf" *)
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->   (* Θ0 ⊢ Pi, Θ0 ⊢ P0 *)
  κ ∷ Θ0 ⊑ Θ ->                       (* κ : Θ0 ⊑ Θ *)
  uskl_rho NM Θ Δρ Ψρ ψsub ψa ->      (* ρ: ψsub = ρ(ψa), Ψρ = its Ψ *)
  a_tags_sort NM Ψ' ψa ->             (* Θ ⊢^N Ψ'{syn ψa} *)
  Ψi `union` Ψa [<=] Ψ' ->            (* Ψi, Ψa ⊆ Ψ' *)
  Ψρ ∩ Ψ' [=] empty ->   (* the fresh{Ψ'} instance used *)
  rho_fresh Δρ Θ κ -> Δρ [<=] Δ ->    (* MECH-ONLY (4): the ρ-freshness *)
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->              (* MECH-ONLY (2) *)
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->   (* Δ|Θ ⊢ κPi ⊑ᵖ[Ψi] ψa *)
  Ψsub [<=] Ψρ `union` Ψa ->          (* the consistency index is the *)
  Ψa [<=] Ψsub ->                     (*   paper's "Ψ,Ψa", as bounds *)
  Ψsub ⨟ Θ ⊢ₛᵃ ψsub ∼ Q ->            (* Θ ⊨[Ψ,Ψa] syn(ρψa) ∼ Q *)
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
                                      (* Θ ⊢ inh(κP0) ⊳ Q *)
  (* ⭐ THE CONCLUSION CARRIES THE κ-EXTENSION (the SolE-FlexR repair,
     2026-08-04).  [L] is an avoid-set PARAMETER: the generated block must be
     fixed apart from whatever the caller already has in play, and at a binder
     row that has to be decided BEFORE the block is picked. *)
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists Ξ Pa κ',
    Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa /\        (* solveeq{Pi}{P0}{Ξ ⨾ Pa} *)
    all_flex_mono Ξ /\ uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
                              (* Δ|Θ ⊢ (κ',κ)Pa ⊑ᵖ[Ψi,Ψa] ψa, κa := κ',κ *)
Proof.
  intros NM Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HwfΘ HwfΘ0 HwfPi HwfP0 Hκ Hrho Htags Hsub Hinter Hfresh Hdelta
         Hapart Hdfresh Hpre Hsubeq1 Hsubeq2 Hconsis Hrefine L HL.
  destruct (@a_solve_eq_complete_var_gen NM Θ Θ0 Θ nil Θ Θ0 κ Δ Δρ empty
              Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0
              (aenv_split_nil Θ) (aenv_split_nil Θ0) HwfΘ
              ltac:(intros x b Hb; destruct Hb)
              ltac:(simpl; clear; solve_notin_auto)
              ltac:(clear; solve_notin_auto)
              HwfΘ HwfΘ0 HwfΘ
              ltac:(intros x b Hb; exact Hb)
              ltac:(intros x b Hb; left; exact Hb)
              HwfPi HwfP0 Hκ
              (* ⭐ at the TOP-LEVEL call [Θw] IS [Θ], so the κ-image bound is
                 just [a_inc_lookup_wf] — the premise costs the paper
                 statement nothing. *)
              ltac:(intros α Hf;
                    eapply a_inc_lookup_flex_ftv_dom; [ exact Hκ | exact Hf ])
              Hrho Htags Hsub Hinter Hfresh
              Hdelta Hapart Hdfresh Hpre Hsubeq1 Hsubeq2 Hconsis
              Hrefine L HL)
    as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hfam).
  exists Ξ, Pa, κ'.
  split; [ exact Hs | ].
  split; [ exact Hfm | ].
  split; [ exact Hu | ].
  split; [ exact Hk | ].
  split; [ exact Hfr | ].
  split; [ exact HF | ].
  eapply ad_partial_precise_delta_cong;
    [ apply (Hfam empty);
      [ clear; fsetdec | clear; fsetdec
      | intros β α τ Hβ Hb; exfalso; clear - Hβ; fsetdec ]
    | clear; fsetdec ].
Qed.

Print Assumptions a_solve_eq_complete_var.

(* ⭐ THE Θw-CARRYING INTERFACE (2026-08-04).  [a_solve_eq_complete_var] above
   is the PAPER statement and fixes [Θw := Θ]; P6-Cs cannot use it, because its
   ∀ rows call the IH at [(β ~ tvar) ++ Θ] and must then STRIP β out of the
   [a_inc] conclusion ([a_inc_strip_tvar_mid]) — which needs the extension's
   payloads to be wf in a context that does NOT have β.  So the caller passes
   its own fixed [Θw] down, exactly as [_gen] already threads it.  Same proof,
   one line: [_gen] at [Θtv := nil]. *)
Theorem a_solve_eq_complete_var_at :
  forall NM Θ0 Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  a_wf_aenv Θw ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α, a_flex_tvar Θ0 α ->
     ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θw) ->
  uskl_rho NM Θ Δρ Ψρ ψsub ψa ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  Ψρ ∩ Ψ' [=] empty ->
  rho_fresh Δρ Θ κ -> Δρ [<=] Δ ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  Ψsub ⨟ Θ ⊢ₛᵃ ψsub ∼ Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists Ξ Pa κ',
    Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa /\
    all_flex_mono Ξ /\ uniq Ξ /\
    keys κ' = keys Ξ /\
    (forall α, α `in` dom Ξ -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ' /\
    Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  intros NM Θ0 Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfPi HwfP0 Hκ Hκw
         Hrho Htags Hsub Hinter Hfresh Hdelta
         Hapart Hdfresh Hpre Hsubeq1 Hsubeq2 Hconsis Hrefine L HL.
  destruct (@a_solve_eq_complete_var_gen NM Θ Θ0 Θw nil Θ Θ0 κ Δ Δρ empty
              Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0
              (aenv_split_nil Θ) (aenv_split_nil Θ0) HwfΘ
              ltac:(intros x b Hb; destruct Hb)
              ltac:(simpl; clear; solve_notin_auto)
              ltac:(clear; solve_notin_auto)
              HwfΘ HwfΘ0 HwfΘw Hmon Hnr
              HwfPi HwfP0 Hκ Hκw
              Hrho Htags Hsub Hinter Hfresh
              Hdelta Hapart Hdfresh Hpre Hsubeq1 Hsubeq2 Hconsis
              Hrefine L HL)
    as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hfam).
  exists Ξ, Pa, κ'.
  repeat (split; [ solve [ exact Hs | exact Hfm | exact Hu | exact Hk
                         | exact Hfr | exact HF ] | ]).
  eapply ad_partial_precise_delta_cong;
    [ apply (Hfam empty);
      [ clear; fsetdec | clear; fsetdec
      | intros β α τ Hβ Hb; exfalso; clear - Hβ; fsetdec ]
    | clear; fsetdec ].
Qed.
