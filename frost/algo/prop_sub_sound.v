(** SOUNDNESS OF DECORATED SUBTYPING (lemma:sound-decorated-subtyping,
    subtyping-proofs.tex:43-58, mutual with
    lemma:sound-decorated-flex-subtyping :1094) — the L-B half of
    thm:sound-subtyping (docs/DESIGN-subtyping.md §2.1).

    A decorated run is an identity information increase whose output (read
    back as a [bskl] Qt) is a declarative subtype of the subject over the
    OUTPUT context, and a valid fill of the input [P0].  Every consistency
    premise is discharged by [a_consistag_sound_aux] (Qed); the flexible
    walk recurses on the decorated walk [a_subtag_flex].

    WIP FLAGSHIP — honest admits on unfinished (true) cases, each marked
    with what remains.  The bundle compiles; the easy half is Qed. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_pat_sub.

Set Implicit Arguments.

Scheme a_subtag_mutind := Induction for a_subtag Sort Prop
  with a_subtag_flex_mutind := Induction for a_subtag_flex Sort Prop.

Combined Scheme a_subtag_subtag_flex_mutind
  from a_subtag_mutind, a_subtag_flex_mutind.

(* ===================================================================== *)
(*  §1  Small erasure/painting transports                                 *)
(* ===================================================================== *)

(** The syn painting of an lc skeleton is synthesised. *)
Lemma is_sskl_pskl_to_bskl_syn : forall P,
  lc_pskl P ->
  is_sskl (pskl_to_bskl_syn P).
Proof.
  intros P Hlc; induction Hlc; simpl; try (constructor; auto; fail).
  apply is_sskl__all with (L := {}).
  intros X _. rewrite <- pskl_to_bskl_syn_open. auto.
Qed.

(** Erasure preserves local closure. *)
Lemma lc_uskl_to_pskl : forall S,
  lc_uskl S ->
  lc_pskl ⌊ S ⌋ˢ.
Proof.
  intros S H; induction H; simpl;
    try (constructor; auto; fail);
    constructor; intros X; rewrite <- uskl_to_pskl_open; auto.
Qed.

(** Erasure preserves guardedness (guarded shapes have no decorations). *)
Lemma guarded_uskl_to_pskl : forall S,
  guarded_uskl S ->
  guarded_pskl ⌊ S ⌋ˢ.
Proof.
  intros S H; inversion H; simpl; constructor;
    auto using lc_uskl_to_pskl.
Qed.

(** The syn painting preserves guardedness. *)
Lemma guarded_pskl_to_bskl_syn : forall P,
  guarded_pskl P ->
  guarded_bskl (pskl_to_bskl_syn P).
Proof.
  intros P H; inversion H; simpl; constructor;
    auto using lc_pskl_to_bskl_syn.
Qed.

(** A declaration-only prefix preserves context well-formedness (decls
    carry no payload; freshness comes from the uniq hypothesis). *)
Lemma a_wf_aenv_prepend_decls : forall Ξ Θ,
  a_decls Ξ ->
  uniq Ξ ->
  (forall γ, γ `in` dom Ξ -> γ `notin` dom Θ) ->
  a_wf_aenv Θ ->
  a_wf_aenv (Ξ ++ Θ).
Proof.
  induction Ξ as [ | [γ b] Ξ' IH ]; intros Θ Hdecl Huq Hfr Hwf;
    [ exact Hwf | ].
  inversion Hdecl; subst.
  simpl_env. apply a_wf_aenv__flex.
  - simpl_env. 
    assert (HγΘ : γ `notin` dom Θ)
      by (apply Hfr; simpl; fsetdec).
    clear - Huq HγΘ. simpl_env in *. solve_uniq.
  - apply IH; auto.
    + clear - Huq. solve_uniq.
    + intros γ0 Hγ0. apply Hfr. simpl. fsetdec.
Qed.

(* ===================================================================== *)
(*  §2  The mutual soundness statement                                    *)
(* ===================================================================== *)

(** The subtyping conclusion (paper: ⊴, the fill of [P0], and the
    declarative subtyping of the subject, at the OUTPUT context). *)
Definition subtag_sound_concl
    (NM : a_sub_mode) (M : mode) (P0 : pskl) (Ψ : atoms)
    (Θ0 : aenv) (S : uskl) (Q : pskl) (Θ1 : aenv) : Prop :=
  a_wf_aenv Θ0 ->
  lc_uskl S ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ S ⌋ˢ ->
  mod_comp_sk (pskl_to_bskl_inh P0) M ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  (exists Qt, bskl_to_pskl Qt = Q /\
     Ψ ⨟ Θ1 ⊢ₛᵃ[ NM | M ] S ⊑ Qt /\
     ad_refine_syn_f empty Θ1 empty (pskl_to_bskl_inh P0) Qt).

(** The flexible-walk conclusion (paper lemma:sound-decorated-flex-subtyping:
    the walked context [Θ0 ∣ Ξ] re-merges on the left). *)
Definition subtag_flex_sound_concl
    (NM : a_sub_mode) (M : mode) (P0 : pskl)
    (Θ0 Ξ : aenv) (α : atom) (A : pskl) (Θ1 : aenv) : Prop :=
  a_wf_aenv (Ξ ++ Θ0) ->
  a_decls Ξ ->
  (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  mod_comp_sk (pskl_to_bskl_inh P0) (mode_fn M) ->
  (Ξ ++ Θ0) ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  (exists Qt, bskl_to_pskl Qt = A /\
     empty ⨟ Θ1 ⊢ₛᵃ[ NM | mode_fn M ] (uskl_var_f α) ⊑ Qt /\
     ad_refine_syn_f empty Θ1 empty (pskl_to_bskl_inh P0) Qt).

Theorem a_subtag_sound_bundle :
  (forall NM M P0 Ψ Θ0 S Q Θ1,
     Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] S ⊑ Q ⊣ Θ1 ->
     subtag_sound_concl NM M P0 Ψ Θ0 S Q Θ1) /\
  (forall NM M P0 Θ0 Ξ α A Θ1,
     a_subtag_flex NM M P0 Θ0 Ξ α A Θ1 ->
     subtag_flex_sound_concl NM M P0 Θ0 Ξ α A Θ1).
Proof.
  apply (a_subtag_subtag_flex_mutind
           (fun NM M P0 Ψ Θ0 S Q Θ1 _ =>
              subtag_sound_concl NM M P0 Ψ Θ0 S Q Θ1)
           (fun NM M P0 Θ0 Ξ α A Θ1 _ =>
              subtag_flex_sound_concl NM M P0 Θ0 Ξ α A Θ1));
    unfold subtag_sound_concl, subtag_flex_sound_concl.

  - (* Infer : output ⌊S⌋, context unchanged *)
    intros NM Ψ Θ0 S HΨ Hwf HlcS HwfP0 HwfS Hmod.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ].
    exists (pskl_to_bskl_syn ⌊ S ⌋ˢ).
    split; [ apply bskl_to_pskl_pskl_to_bskl_syn | ].
    assert (Hvis : forall X, X `in` ftvar_in_uskl S -> a_binds_tvar X Θ0).
    { intros X HX.
      rewrite <- ftvar_in_pskl_uskl_to_pskl in HX.
      destruct (ad_wf_pskl_ftv_tvarish HwfS HX) as [HΔ | Ht];
        [ exfalso; clear - HΔ; fsetdec | exact Ht ]. }
    split.
    + apply ad_pat_sub__infer;
        [ exact HΨ
        | apply ad_pat_consis_refl_erase; assumption
        | apply is_sskl_pskl_to_bskl_syn; eauto using ad_wf_pskl_lc ].
    + (* P0 = ◇ : the fill is the hole rule *)
      simpl. apply ad_refine_syn_f__hole;
        [ clear; fsetdec | exact HwfS ].

  - (* Check (TY) : the consistency run must land on B itself.
       ADMIT [true]: needs the re-inherit transport of the run's output
       join onto the inh painting of B ([refine_join_reinherit]) plus the
       output-equals-input argument for a concrete B (both sides of the
       decorated run are guarded types).  See DESIGN-subtyping.md §2.1. *)
    intros Ψ Θ0 Θ1 T B HgT HgB Hc Hwf HlcT HwfB HwfT Hmod.
    admit.

  - (* ForallR (TY) : re-attach the rigid head.
       ADMIT [true]: the L8-style head re-attachment (crib the ForallInh
       case of [a_consistag_sound_aux]): strip the ⊴ across the
       (α~tvar)-cons, rebuild the fill and the subtyping with
       [ad_pat_sub__forall_r], discharging the binder by renaming. *)
    intros L Ψ Θ0 Θ1 Ξ S B Hsuf Hprem IH Hwf HlcS HwfP0 HwfS Hmod.
    admit.

  - (* UnivGhostR (SK) : axis — output ⊤◇⌊S⌋, context unchanged *)
    intros Ψ Θ0 S HgS HΨ Hwf HlcS HwfP0 HwfS Hmod.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ].
    exists (bskl_tophole (pskl_to_bskl_syn ⌊ S ⌋ˢ)).
    split; [ simpl; f_equal; apply bskl_to_pskl_pskl_to_bskl_syn | ].
    assert (Hvis : forall X, X `in` ftvar_in_uskl S -> a_binds_tvar X Θ0).
    { intros X HX.
      rewrite <- ftvar_in_pskl_uskl_to_pskl in HX.
      destruct (ad_wf_pskl_ftv_tvarish HwfS HX) as [HΔ | Ht];
        [ exfalso; clear - HΔ; fsetdec | exact Ht ]. }
    assert (Hg : guarded_pskl ⌊ S ⌋ˢ) by (apply guarded_uskl_to_pskl; auto).
    split.
    + apply ad_pat_sub__univ_ghost_r;
        [ exact HΨ | exact HgS
        | apply guarded_pskl_to_bskl_syn; exact Hg
        | apply is_sskl_pskl_to_bskl_syn; eauto using ad_wf_pskl_lc
        | apply ad_pat_consis_refl_erase; assumption ].
    + (* P0 = ◇ : hole rule against the syn painting of ⊤◇⌊S⌋ *)
      simpl.
      change (bskl_tophole (pskl_to_bskl_syn ⌊ S ⌋ˢ))
        with (pskl_to_bskl_syn (pskl_tophole ⌊ S ⌋ˢ)).
      apply ad_refine_syn_f__hole; [ clear; fsetdec | ].
      apply ad_wf_pskl__tophole; [ exact Hg | exact HwfS ].

  - (* Arrow : a_consistag_sound_aux on the consistency premise (Δs = ∅),
       ⊴-transport its conclusions to Θ2, IH on the sub-premise. *)
    intros NM M Ψ Ψ1 Ψ2 Θ0 Θ1 Θ2 P0a P0b S1 S2 Q1 Q2
      Hc Hsub IH HΨ Hwf Hlc HwfP0 HwfS Hmod.
    inversion Hlc; subst.
    match goal with H : lc_uskl S1 |- _ => rename H into HlcS1 end.
    match goal with H : lc_uskl S2 |- _ => rename H into HlcS2 end.
    inversion HwfP0; subst.
    match goal with H : Θ0 ⨟ empty ⊢ₚₛᵃ P0a |- _ => rename H into HwfP0a end.
    match goal with H : Θ0 ⨟ empty ⊢ₚₛᵃ P0b |- _ => rename H into HwfP0b end.
    simpl in HwfS. inversion HwfS; subst.
    match goal with H : Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ S1 ⌋ˢ |- _ => rename H into HwfS1 end.
    match goal with H : Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ S2 ⌋ˢ |- _ => rename H into HwfS2 end.
    simpl in Hmod. inversion Hmod; subst.
    match goal with
    | H : mod_comp_sk (pskl_to_bskl_inh P0b) M |- _ => rename H into HmodB
    end.
    destruct (a_consistag_sound_aux Hc Hwf HlcS1 HwfP0a HwfS1
                ltac:(intros X HX; clear - HX; fsetdec)
                ltac:(intros β τ Hb; apply inter_empty_pointwise;
                      intros X HX; clear - HX; fsetdec)
                ltac:(intros Θa β b Θb Heq Hne;
                      apply inter_empty_pointwise;
                      intros X HX; clear - HX; fsetdec))
      as [Hle1 [Hwf1 [_ [_ [[Qt1 [HeQt1 [Hcons1 Hfill1]]] _]]]]].
    assert (HwfP0b1 : Θ1 ⨟ empty ⊢ₚₛᵃ P0b)
      by (eapply ad_wf_pskl_isub; eauto).
    assert (HwfS21 : Θ1 ⨟ empty ⊢ₚₛᵃ ⌊ S2 ⌋ˢ)
      by (eapply ad_wf_pskl_isub; eauto).
    destruct (IH Hwf1 HlcS2 HwfP0b1 HwfS21 HmodB)
      as [Hle2 [Hwf2 [Qt2 [HeQt2 [Hsub2 Hfill2]]]]].
    split; [ eapply a_isub_trans; eauto | ].
    split; [ exact Hwf2 | ].
    exists (bskl_arrow Qt1 Qt2).
    split; [ simpl; f_equal; assumption | ].
    split.
    + eapply ad_pat_sub__arrow;
        [ eapply ad_pat_consis_isub; eauto | exact Hsub2 | exact HΨ ].
    + simpl. apply ad_refine_syn_f__arrow;
        [ eapply ad_refine_syn_f_isub; eauto | exact Hfill2 ].

  - (* ForallL (tagged) : instantiate with the decorated candidate.
       ADMIT [true]: IH at (Ξ ++ Θ0) (wf from the new uniq premise +
       a_decls of the extract), strip the ⊴ over the decls prefix
       (a_isub_strengthen_decls_src), conclude with
       ad_pat_sub__forall_l_tagged (scope premise via
       a_wf_pskl → ad_wf_pskl conversion + ⊴-transport). *)
    intros L NM M P0 Ψ Ψg Θ0 Θ1 ε S Q Ξ P1 ψg
      Hneq Hgor Hex Huq HwfP1 Hint Hsort Herase Hprem IH
      Hwf Hlc HwfP0 HwfS Hmod.
    admit.

  - (* ForallL (untagged) : same as tagged. ADMIT [true]. *)
    intros L NM M P0 Ψ Ψg Θ0 Θ1 S Q Ξ P1 ψg
      Hneq Hgor Hex Huq HwfP1 Hint Hsort Herase Hprem IH
      Hwf Hlc HwfP0 HwfS Hmod.
    admit.

  - (* Ghost (SK) : ◇ below the input P0 *)
    intros M Ψ Θ0 P0 HΨ Hwf HlcS HwfP0 HwfS Hmod.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ].
    exists (pskl_to_bskl_inh P0).
    split; [ apply bskl_to_pskl_pskl_to_bskl_inh | ].
    split.
    + apply ad_pat_sub__ghost; [ exact HΨ | exact HwfP0 | exact Hmod ].
    + apply ad_refine_syn_f_refl_inh; exact HwfP0.

  - (* GhostG (SK) : dotted ghost below ◇ *)
    intros M Ψ Θ0 HΨ Hwf HlcS HwfP0 HwfS Hmod.
    split; [ apply a_isub_refl; exact Hwf | ].
    split; [ exact Hwf | ].
    exists bskl_hole.
    split; [ reflexivity | ].
    split.
    + apply ad_pat_sub__ghostg; [ exact HΨ | ].
      simpl in Hmod. exact Hmod.
    + simpl. change bskl_hole with (pskl_to_bskl_syn pskl_hole).
      apply ad_refine_syn_f__hole;
        [ clear; fsetdec | apply ad_wf_pskl__hole ].

  - (* UnivGhostL (SK) : drop the subject's ⊤◇ *)
    intros M Ψ Θ0 Θ1 P0 S Q Hne Hprem IH Hwf HlcS HwfP0 HwfS Hmod.
    inversion HlcS; subst.
    simpl in HwfS.
    inversion HwfS; subst.
    destruct (IH Hwf ltac:(assumption) HwfP0 ltac:(assumption) Hmod)
      as [Hle [Hwf1 [Qt [HeqQt [Hsub Hfill]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeqQt | ].
    split; [ apply ad_pat_sub__univ_ghost_l; assumption | exact Hfill ].

  - (* UnivGhostLG (SK) : drop the subject's dotted ⊤◇ *)
    intros M Ψ Θ0 Θ1 P0 S Q Hne Hprem IH Hwf HlcS HwfP0 HwfS Hmod.
    inversion HlcS; subst.
    simpl in HwfS.
    inversion HwfS; subst.
    destruct (IH Hwf ltac:(assumption) HwfP0 ltac:(assumption) Hmod)
      as [Hle [Hwf1 [Qt [HeqQt [Hsub Hfill]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeqQt | ].
    split; [ apply ad_pat_sub__univ_ghost_lg; assumption | exact Hfill ].

  - (* FlexMono : hand off to the decorated walk (Ξ = nil) *)
    intros NM M P0 Ψ Θ0 Θ1 α A Hflex IH HΨ Hwf HlcS HwfP0 HwfS Hmod.
    destruct (IH Hwf a_decls__nil HwfP0 Hmod)
      as [Hle [Hwf1 [Qt [HeqQt [Hsub Hfill]]]]].
    split; [ exact Hle | ]. split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeqQt | ].
    split; [ | exact Hfill ].
    eapply ad_pat_sub_psi_cong; [ exact Hsub | clear - HΨ; fsetdec ].

  - (* Flex-Solve : deposit α̂0 := α̂→β̂ and recurse on the arrow.  The
       source lifts into the deposited context by a ⊴ (suffix-weaken the
       core, then re-prepend α̂0 and Ξ as declarations), so every
       hypothesis transports by ⊴-stability and the conclusion is
       FlexMono off the IH's arrow subtyping. *)
    intros NM M P0 Θ0 Θ1 Ξ α0 α β A Hne Hαf Hβf Hprem IH Hwf Hdecl HwfP0 Hmod.
    set (τab := ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
    set (Θmid := (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0).
    set (Θ' := Ξ ++ (α0 ~ abind_flex_mono_def τab) ++ Θmid).
    assert (Huq : uniq (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact Hwf).
    assert (Hwf0 : a_wf_aenv Θ0).
    { eapply a_wf_aenv_app_r with (Θp := Ξ ++ (α0 ~ abind_flex_mono)).
      simpl_env. exact Hwf. }
    assert (Hbα : binds α abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; right; left; reflexivity).
    assert (Hbβ : binds β abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; left; reflexivity).
    assert (Hwfmid : a_wf_aenv Θmid).
    { unfold Θmid. apply a_wf_aenv__flex.
      { simpl. clear - Hβf Hne. simpl_env in *. fsetdec. }
      apply a_wf_aenv__flex;
        [ clear - Hαf; simpl_env in *; fsetdec | exact Hwf0 ]. }
    assert (Hwfdef : a_wf_aenv ((α0 ~ abind_flex_mono_def τab) ++ Θmid)).
    { apply a_wf_aenv__flex_def.
      - unfold Θmid. simpl. clear - Hαf Hβf Huq. simpl_env in *. solve_uniq.
      - apply a_wf_ptyp__arrow; apply a_wf_ptyp__var;
          [ right; left; exact Hbα | right; left; exact Hbβ ].
      - repeat constructor.
      - exact Hwfmid. }
    assert (HwfΘ' : a_wf_aenv Θ').
    { unfold Θ'. apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros γ Hγ. unfold Θmid. simpl_env.
        clear - Huq Hαf Hβf Hγ. destruct_uniq.
        unfold disjoint in *. simpl_env in *. fsetdec. }
    (* the source lifts into Θ' *)
    assert (Hbase : Θ0 ⊴ Θ').
    { unfold Θ', Θmid.
      replace (Ξ ++ (α0 ~ abind_flex_mono_def τab)
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
        with ((Ξ ++ (α0 ~ abind_flex_mono_def τab)
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono)) ++ Θ0)
        by (simpl_env; reflexivity).
      apply a_isub_weaken_suffix;
        [ apply a_wf_aenv_lc_aenv; exact Hwf0 | ].
      apply a_suffix_app; [ auto using a_decls_suffix | ].
      apply (a_suffix__cons α0);
        [ apply (a_suffix__cons β);
            [ apply (a_suffix__cons α);
                [ apply a_suffix__nil | constructor ]
            | constructor ]
        | constructor ]. }
    assert (Hbα0' : binds α0 (abind_flex_mono_def τab) Θ').
    { unfold Θ'. unfold binds. apply in_or_app. right. left. reflexivity. }
    assert (Hlift : (Ξ ++ (α0 ~ abind_flex_mono) ++ Θ0) ⊴ Θ').
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb. right; left.
        unfold Θ'. unfold binds. apply in_or_app. left. exact Hb. }
      apply a_isub_prepend_decls_src;
        [ apply (a_decls__cons α0); apply a_decls__nil | | exact Hbase ].
      intros γ Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> _] | Hb'];
        [ right; right; exists τab; exact Hbα0' | inversion Hb' ]. }
    (* transported hypotheses for the IH *)
    assert (HwfP0' : Θ' ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply ad_wf_pskl_isub; eauto).
    assert (Hwfarr : Θ' ⨟ empty ⊢ₚₛᵃ ⌊ uskl_arrow (uskl_var_f α)
                                        (uskl_var_f β) ⌋ˢ).
    { simpl. apply ad_wf_pskl__arrow; apply ad_wf_pskl__var;
        right; right; left;
        (unfold Θ'; unfold binds; apply in_or_app; right; simpl;
         right; auto). }
    destruct (IH HwfΘ' ltac:(repeat constructor) HwfP0' Hwfarr Hmod)
      as [Hle' [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split. { eapply a_isub_trans; [ exact Hlift | exact Hle' ]. }
    split; [ exact Hwf1 | ].
    exists Qt. split; [ exact HeQt | ].
    split; [ | exact Hfill ].
    eapply ad_pat_sub__flex_mono with (τ := τab).
    + destruct Hle' as [_ Hdefs]. apply Hdefs. exact Hbα0'.
    + exact Hsub.

  - (* Flex-Assign : substitute the walked definition into P0.
       ADMIT [true]: needs the fold-def transports on the fill and the
       subtyping conclusions (the [τ/β̂]-fold family;
       ad_refine_syn_f_unfold_def_source is the unfold direction) plus
       mod_comp stability under the monotype substitution. *)
    intros NM M P0 Θ0 Θ1 Ξ α β τ A Hβ1 Hprem IH Hwf Hdecl HwfP0 Hmod.
    admit.

  - (* Flex-Depend : β̂ joins the suffix at the Θ0-adjacent end, so the
       premise context is the conclusion's up to associativity. *)
    intros NM M P0 Θ0 Θ1 Ξ α β A Hne Hin Hprem IH Hwf Hdecl HwfP0 Hmod.
    assert (Hdecl' : a_decls (Ξ ++ (β ~ abind_flex_mono)))
      by (apply a_decls_app;
          [ exact Hdecl | apply (a_decls__cons β); apply a_decls__nil ]).
    destruct (IH ltac:(simpl_env; simpl_env in Hwf; exact Hwf) Hdecl'
                ltac:(simpl_env; simpl_env in HwfP0; exact HwfP0) Hmod)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split; [ simpl_env in Hle; simpl_env; exact Hle | ].
    split; [ exact Hwf1 | ].
    exists Qt. auto.

  - (* Flex-Skip : strip the mid entry, IH, re-cons + lift the outputs. *)
    intros NM M P0 Θ0 Θ1 Ξ α β A Hne Hni Hβ1 Hprem IH Hwf Hdecl HwfP0 Hmod.
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply ad_wf_pskl_strip_mid; eauto).
    destruct (IH Hwf' Hdecl HwfP0' Hmod)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    assert (Hlift : Θ1 ⊴ ((β ~ abind_flex_mono) ++ Θ1)).
    { apply a_isub_weaken_suffix;
        [ apply a_wf_aenv_lc_aenv; exact Hwf1 | ].
      apply (a_suffix__cons β); [ constructor | constructor ]. }
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_flex.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__flex; auto | ].
    exists Qt. split; [ exact HeQt | ].
    split; [ eapply ad_pat_sub_isub; eauto
           | eapply ad_refine_syn_f_isub; eauto ].

  - (* Flex-SkipRigid : as Flex-Skip with a rigid head. *)
    intros NM M P0 Θ0 Θ1 Ξ α β A Hni Hβ1 Hprem IH Hwf Hdecl HwfP0 Hmod.
    assert (Hwf' : a_wf_aenv (Ξ ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply ad_wf_pskl_strip_mid; eauto).
    destruct (IH Hwf' Hdecl HwfP0' Hmod)
      as [Hle [Hwf1 [Qt [HeQt [Hsub Hfill]]]]].
    split.
    { apply a_isub_prepend_decls_src; auto.
      { intros γ Hb.
        apply a_binds_tvar_weaken_cons.
        eapply a_isub_binds_flex; [ exact Hle | ].
        unfold binds; apply in_or_app; left; exact Hb. }
      apply a_isub_cons_tvar.
      eapply a_isub_strengthen_decls_src; eauto. }
    split; [ apply a_wf_aenv__tvar; auto | ].
    exists Qt. split; [ exact HeQt | ].
    split.
    + eapply ad_pat_sub_weaken; [ exact Hsub | ].
      intros x b0 Hb; unfold binds; right; exact Hb.
    + eapply ad_refine_syn_f_weaken_ctx; [ exact Hfill | ].
      intros x b0 Hb; unfold binds; right; exact Hb.
Admitted.
