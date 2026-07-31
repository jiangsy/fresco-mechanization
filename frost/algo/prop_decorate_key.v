(** KEY subtyping decoration + decorate-constraint-solving + MAIN + the
    assembled thm:sound-subtyping.  Split from prop_decorate_sub.v so the
    heavy earlier sections are not re-checked on every iteration. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_sub_sound.
Require Import src.frost.algo.prop_decorate_sub.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §14  Subtyping decoration (lemma:subtyping-decoration, KEY,           *)
(*  subtyping-proofs.tex:541-959): a decorated subtyping run on           *)
(*  R[⌊ψa⌋/α] replays on R[ψa/α], additionally solving ψa's tags Ψa as    *)
(*  computed by the solvetag run on the constraints collected at α's      *)
(*  occurrences.  Induction on the decorated subtyping premise            *)
(*  (generalizing the look run): the paper's WLOG reorderings become      *)
(*  a_looksub_open_target (ForallR) and per-case inversions; the looked   *)
(*  variable is renamed on the fly (a_looksub_rename_var) to keep it      *)
(*  clear of guessed flexible names (Barendregt prose-completion).        *)
(* ===================================================================== *)

Lemma subst_bskl_in_uskl_decompose : forall ψ α α' R,
  α `notin` ftvar_in_uskl ψ ->
  α' `notin` ftvar_in_uskl R ->
  α' <> α ->
  subst_bskl_in_uskl ψ α' (subst_bskl_in_uskl (uskl_var_f α') α R)
  = subst_bskl_in_uskl ψ α R.
Proof.
  intros ψ α α' R Hαψ Hα'S Hne.
  rewrite subst_bskl_in_uskl_subst_bskl_in_uskl;
    [ | assumption | auto ].
  simpl.
  destruct_if as [_ | Hc];
      [ | exfalso; congruence ].
  rewrite (subst_bskl_in_uskl_fresh_eq R); [ reflexivity | assumption ].
Qed.

Lemma pskl_to_uskl_not_etag : forall P ε ψ,
  pskl_to_uskl P <> uskl_all_etag ε ψ.
Proof. destruct P; simpl; discriminate. Qed.

Lemma pskl_to_uskl_not_holeg : forall P,
  pskl_to_uskl P <> uskl_holeg.
Proof. destruct P; simpl; discriminate. Qed.

Lemma pskl_to_uskl_not_topholeg : forall P ψ,
  pskl_to_uskl P <> uskl_topholeg ψ.
Proof. destruct P; simpl; discriminate. Qed.

(** Rename-composition for the decorated substitution: substituting at a
    RE-FRESHENED variable composes back — [αv' ∉ ftv R0] and the value's
    [αv]-freshness make the detour invisible.  (The exists-fresh ForallR
    case below re-freshens its substitution variable away from the rule's
    Barendregt binder.) *)
Lemma subst_bskl_in_uskl_rename_compose : forall ψ αv αv' R0,
  αv `notin` ftvar_in_uskl ψ ->
  αv' `notin` ftvar_in_uskl R0 ->
  αv <> αv' ->
  subst_bskl_in_uskl ψ αv' (subst_bskl_in_uskl (uskl_var_f αv') αv R0)
  = subst_bskl_in_uskl ψ αv R0.
Proof.
  intros ψ αv αv' R0 Hψ HR Hne.
  rewrite subst_bskl_in_uskl_subst_bskl_in_uskl;
    [ | exact Hψ | exact Hne ].
  simpl. destruct_if; [ | congruence ].
  rewrite (subst_bskl_in_uskl_fresh_eq R0); [ reflexivity | exact HR ].
Qed.

Lemma a_subtag_decoration : forall NM M P0 Ψ Θ0 R' P Θ1,
  Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] R' ⩽˙ P ⊣ Θ1 ->
  forall R0 ψa Ψa αv Ξc 𝒞,
    R' = subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ->
    ⌊ R0 ⌋ˢ ≼[ αv , M ] P0 ⤳ Ξc ⨾ 𝒞 ->
    𝒞 ⊩ᵗ ψa ⤳ Ψa ->
    αv `notin` ftvar_in_uskl ψa ->
    αv `notin` ftvar_in_pskl P0 ->
    lc_uskl ψa ->
    lc_uskl R0 ->
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ R' ⌋ˢ ->
    (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
    Θ0 ⊢ᵗ[ NM | M | P0 | (Ψ `union` Ψa) ]
      (subst_bskl_in_uskl ψa αv R0) ⩽˙ P ⊣ Θ1.
Proof.
  intros NM M P0 Ψ Θ0 R' P Θ1 Hsub.
  induction Hsub;
    intros R0 ψa Ψa αv Ξc C HeqT HD Hst Hαψ HαP0 Hlcψ HlcS0 Hwf
      HwfP0 HwfT Hmod.
  - (* Infer : P0 = ◇ solves nothing; the run is erasure-determined *)
    assert (Hemp : Ψa [=] empty)
      by (eapply a_looksub_hole_solvetag_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite <- erase_swap_subst.
    apply a_subtag__infer; assumption.
  - (* Check : dispatch on the look run *)
    inversion HD; subst.
    + (* LS-Var : R0 = αv; the decoration-var lemma at ρ = nil *)
      match goal with
      | He : pskl_var_f αv = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; inversion He; subst;
          try solve [ inversion HlcS0 ]
      end.
      simpl in *.
      revert HwfT Hmod.
      destruct_if as [_ | Hc];
          [ | exfalso; congruence ].
      intros HwfT Hmod.
      inversion Hst; subst.
      change ψa with (msubst_uskl nil ψa).
      eapply a_subtag_decoration_var;
        [ eapply a_subtag__check; eassumption
        | reflexivity
        | eassumption
        | intros α1 g Hb; inversion Hb
        | exact Hlcψ
        | exact Hwf
        | apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ
        | exact HwfP0
        | exact HwfT
        | exact Hmod ].
    + (* LS-Absent : both substitutions are the identity *)
      assert (HαR : αv `notin` ftvar_in_uskl R0).
      { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). assumption. }
      rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαR ].
      match goal with
      | Hg1 : guarded_uskl _, Hc : _ ⊢ᵗ[ _ | _ | _ | _ ] _ ∼˙ _ ⊣ _ |- _ =>
          rewrite subst_bskl_in_uskl_fresh_eq in Hg1, Hc; try exact HαR
      end.
      inversion Hst; subst.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ eapply a_subtag__check; eassumption
        | fsetdec_empty ].
    + (* LS-Vacuous : the Check target is guarded, not ◇ *)
      inv_guarded_hole.
    + (* LS-Check : decorate the consistency premise *)
      eapply a_subtag__check.
      * apply guarded_subst_decorate; assumption.
      * assumption.
      * eapply a_consistag_decoration;
          [ eassumption | exact Hst | reflexivity | exact Hαψ
          | exact Hlcψ | exact HlcS0 | eassumption | exact Hwf
          | exact HwfP0 | exact HwfT
          | apply rig_empty | apply no_flex_dep_empty | apply faf_empty ].
    + (* LS-ForallR : a guarded ∀ target is absurd *)
      match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
        inversion Hg end.
    + (* LS-ForallL : the source is ∀-headed, not guarded *)
      match goal with
      | He : pskl_all_syn _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      match goal with
      | Hg : guarded_uskl _ |- _ => simpl in Hg; inversion Hg
      end.
    + (* LS-UnivGhostL : the source is ∀◇-headed, not guarded *)
      match goal with
      | He : pskl_tophole _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      match goal with
      | Hg : guarded_uskl _ |- _ => simpl in Hg; inversion Hg
      end.
  - (* ForallR : transport the look run under the opened target.
       EXISTS-FRESH (2026-07-31): the substitution variable αv is first
       RE-FRESHENED to αv' away from the rule's Barendregt binder α (which
       is in scope here — this is exactly what the single-binder encoding
       requires of consumers): [a_looksub_rename_var] moves the look run to
       αv', [a_looksub_open_target_at] opens its ∀-target AT α, and the
       rename-composition collapses the detour in the conclusion. *)
    match goal with
    | Hn : ?a `notin` union (dom (_ ++ _)) _ |- _ => rename Hn into Hfr
    end.
    match goal with
    | Hn : a_suffix _ |- _ => rename Hn into Hsuf
    end.
    match goal with
    | Hn : uniq _ |- _ => rename Hn into Huq
    end.
    match goal with
    | Hn : forall _ : uskl, _ |- _ => rename Hn into IHprem
    end.
    rewrite dom_app in Hfr.
    (* the subject's ftv, read through the erasure *)
    assert (HeqE : ⌊ R ⌋ˢ = subst_pskl_in_pskl ⌊ ψa ⌋ˢ αv ⌊ R0 ⌋ˢ)
      by (rewrite HeqT; rewrite uskl_to_pskl_subst;
          rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
    assert (HαR0 : forall γ, γ `notin` ftvar_in_uskl R -> γ <> αv ->
              γ `notin` ftvar_in_uskl R0).
    { intros γ Hγ Hγv Hc.
      apply Hγ. rewrite HeqT.
      pose proof (ftvar_in_uskl_subst_bskl_in_uskl_lower
                    R0 (pskl_to_uskl (uskl_to_pskl ψa)) αv) as Hlo.
      clear - Hlo Hγv Hc. fsetdec. }
    (* the re-freshened substitution variable *)
    destruct (atom_fresh (singleton α `union` singleton αv
                `union` ftvar_in_uskl R0 `union` ftvar_in_uskl ψa
                `union` ftvar_in_pskl B)) as [αv' Hαv'].
    assert (HeqT' : R = subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                          αv' (subst_bskl_in_uskl (uskl_var_f αv') αv R0)).
    { rewrite subst_bskl_in_uskl_rename_compose;
        [ exact HeqT
        | pose proof Hαψ as Hαψ0;
          rewrite <- (ftvar_in_pskl_uskl_to_pskl ψa) in Hαψ0;
          rewrite <- (ftvar_in_pskl_uskl_to_pskl (pskl_to_uskl ⌊ ψa ⌋ˢ));
          rewrite uskl_to_pskl_pskl_to_uskl;
          exact Hαψ0
        | clear - Hαv'; fsetdec
        | intros ->; clear - Hαv'; fsetdec ]. }
    (* the look run, moved to αv' *)
    assert (HD1 : ⌊ subst_bskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                    ≼[ αv' , mode_tc ] (pskl_all_syn B) ⤳ Ξc ⨾ C).
    { rewrite uskl_to_pskl_subst. simpl.
      apply a_looksub_rename_var;
        [ exact HD
        | rewrite ftvar_in_pskl_uskl_to_pskl; clear - Hαv'; fsetdec ]. }
    (* …and opened at the rule's binder α *)
    assert (HαR0' : α `notin`
              ftvar_in_uskl (subst_bskl_in_uskl (uskl_var_f αv') αv R0)).
    { pose proof (ftvar_in_uskl_subst_bskl_in_uskl_upper
                    R0 (uskl_var_f αv') αv) as Hup.
      simpl in Hup.
      assert (HαRR : α `notin` ftvar_in_uskl R)
        by (clear - Hfr; fsetdec).
      assert (Hααv' : α <> αv') by (intros ->; clear - Hαv'; fsetdec).
      destruct (α == αv) as [-> | Hααv].
      - clear - Hup Hααv'. fsetdec.
      - intro Hc.
        assert (HinR0 : α `in` ftvar_in_uskl R0)
          by (clear - Hup Hc Hααv'; fsetdec).
        exact (HαR0 α HαRR Hααv HinR0). }
    destruct (a_looksub_open_target_at HD1 Hst (β := α)
                ltac:(intros ->; clear - Hαv'; fsetdec)
                ltac:(pose proof (ftvar_in_pskl_uskl_to_pskl
                        (subst_bskl_in_uskl (uskl_var_f αv') αv R0)) as Hepq;
                      clear - HαR0' Hfr Hepq; fsetdec))
      as [C' [HD2 Hst2]].
    (* the transported premise, via the IH at the re-freshened variable *)
    assert (Htrans :
        ((α ~ abind_tvar) ++ Θ0)
          ⊢ᵗ[ a_sub_mode_ty | mode_tc
            | (open_pskl_wrt_pskl B (pskl_var_f α)) | (Ψ `union` Ψa) ]
          (subst_bskl_in_uskl ψa αv'
             (subst_bskl_in_uskl (uskl_var_f αv') αv R0))
          ⩽˙ (open_pskl_wrt_pskl B (pskl_var_f α))
          ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1)).
    { eapply IHprem.
      { exact HeqT'. }
      { exact HD2. }
      { exact Hst2. }
      { clear - Hαv'; fsetdec. }
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                      B (pskl_var_f α)) as Hup.
        simpl in Hup. clear - Hαv' Hup. fsetdec. }
      { exact Hlcψ. }
      { apply subst_bskl_in_uskl_lc_uskl;
          [ exact HlcS0 | constructor ]. }
      { apply a_wf_aenv__tvar; [ clear - Hfr; fsetdec | exact Hwf ]. }
      { eapply a_wf_pskl_all_syn_open_tvar;
          [ exact HwfP0 | clear - Hfr; fsetdec ]. }
      { eapply a_wf_pskl_weaken;
          [ intros x b Hb; unfold binds; simpl; right; exact Hb
          | exact HwfT ]. }
      { intros Hsk; discriminate Hsk. } }
    (* collapse the detour in the transported subject *)
    assert (Hcollapse : subst_bskl_in_uskl ψa αv'
                          (subst_bskl_in_uskl (uskl_var_f αv') αv R0)
                        = subst_bskl_in_uskl ψa αv R0).
    { apply subst_bskl_in_uskl_rename_compose;
        [ exact Hαψ
        | clear - Hαv'; fsetdec
        | intros ->; clear - Hαv'; fsetdec ]. }
    rewrite Hcollapse in Htrans.
    (* assemble the exists-fresh node at the same binder *)
    eapply a_subtag__forall_r with (α := α) (Ξ := Ξ);
      [ exact Hsuf | exact Huq | | exact Htrans ].
    rewrite dom_app.
    assert (Hfteq : ftvar_in_uskl (subst_bskl_in_uskl ψa αv R0)
                    [=] ftvar_in_uskl R).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl
                    (subst_bskl_in_uskl ψa αv R0)).
      rewrite <- (ftvar_in_pskl_uskl_to_pskl R).
      rewrite uskl_to_pskl_subst. rewrite HeqE. reflexivity. }
    clear - Hfr Hfteq. fsetdec.
  - (* UnivGhostR : P0 = ◇ solves nothing *)
    assert (Hemp : Ψa [=] empty)
      by (eapply a_looksub_hole_solvetag_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite <- erase_swap_subst.
    apply a_subtag__univ_ghost_r;
      [ | assumption ].
    apply guarded_subst_decorate; try assumption.
    rewrite <- HeqT. assumption.
  - (* Arrow : split the constraints; decorate left via consistency,
       right via the IH threaded across the mid context *)
    inversion HD; subst.
    + (* LS-Var : R0 = αv *)
      match goal with
      | He : pskl_var_f αv = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; inversion He; subst;
          try solve [ inversion HlcS0 ]
      end.
      simpl in HeqT |- *.
      revert HeqT HwfT.
      destruct_if as [_ | Hc];
          [ | exfalso; congruence ].
      intros HeqT HwfT.
      inversion Hst; subst.
      change ψa with (msubst_uskl nil ψa).
      eapply a_subtag_decoration_var;
        [ eapply a_subtag__arrow; eassumption
        | simpl; exact HeqT
        | eassumption
        | intros α1 g Hb; inversion Hb
        | exact Hlcψ
        | exact Hwf
        | rewrite HeqT;
          apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ
        | exact HwfP0
        | exact HwfT
        | exact Hmod ].
    + (* LS-Absent *)
      assert (HαR : αv `notin` ftvar_in_uskl R0).
      { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). assumption. }
      rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαR ].
      rewrite subst_bskl_in_uskl_fresh_eq in HeqT; [ | exact HαR ].
      inversion Hst; subst.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ first [ rewrite HeqT | idtac ]; eapply a_subtag__arrow; eassumption
        | fsetdec_empty ].
    + (* LS-Arrow : the structural pair *)
      match goal with
      | He : pskl_arrow _ _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; inversion He; subst;
          try solve [ inversion HlcS0 ]
      end.
      simpl in HeqT.
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HαP0.
      simpl in HwfT.
      apply a_wf_pskl_arrow_inv in HwfT as [HwfT1 HwfT2].
      apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP0a HwfP0b].
      destruct (a_solvetag_split _ _ Hst) as [Ψa1 [Ψa2 [Hst1 [Hst2 HΨs]]]].
      simpl.
      match goal with
      | Hc1 : _ ⊢ᵗ[ _ | _ | ?P0a | ?Ψ1 ] _ ∼˙ ?Q1 ⊣ ?Θm,
        Hs2 : ?Θm ⊢ᵗ[ _ | _ | ?P0b | ?Ψ2 ] _ ⩽˙ ?Q2 ⊣ _,
        HΨc : _ [=] union ?Ψ1 ?Ψ2 |- _ =>
          destruct (a_consistag_sound_aux Hc1 Hwf
                      ltac:(apply subst_bskl_in_uskl_lc_uskl;
                            [ assumption
                            | apply pskl_to_uskl_lc;
                              apply lc_uskl_to_pskl_local; assumption ])
                      HwfP0a HwfT1
                      (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
            as [Hle [HwfΘm _]];
          eapply a_subtag__arrow
            with (Ψ1 := Ψ1 `union` Ψa1) (Ψ2 := Ψ2 `union` Ψa2) (Θ1 := Θm);
          [ eapply a_consistag_decoration;
            [ eassumption | exact Hst1 | reflexivity | exact Hαψ
            | exact Hlcψ | assumption | exact Hc1 | exact Hwf
            | exact HwfP0a | exact HwfT1
            | apply rig_empty | apply no_flex_dep_empty | apply faf_empty ]
          | match goal with
            | IH : forall R1 : uskl, _ |- _ =>
                eapply IH;
                  [ reflexivity | eassumption | exact Hst2 | exact Hαψ
                  | clear - HαP0; fsetdec
                  | exact Hlcψ | assumption
                  | exact HwfΘm
                  | eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle ]
                  | eapply a_wf_pskl_isub; [ exact HwfT2 | exact Hle ]
                  | intros Hsk; specialize (Hmod Hsk); simpl in Hmod;
                    inversion Hmod; subst; assumption ]
            end
          | clear - HΨc HΨs; fsetdec ]
      end.
    + (* LS-ForallL : shape clash with the arrow subject *)
      match goal with
      | He : pskl_all_syn _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      simpl in HeqT; discriminate HeqT.
    + (* LS-UnivGhostL : shape clash *)
      match goal with
      | He : pskl_tophole _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      simpl in HeqT; discriminate HeqT.
  - (* ForallL (tagged) : the source is a tagged ∀; the looked variable is
       renamed away from the guessed names before the family rebuild *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var : the strip is never a tagged ∀ *)
      revert HeqT.
      destruct_if as [_ | Hc]; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_etag; symmetry; exact HeqT
      | discriminate HeqT ].
    + (* R0 = all_etag ε0 R0 *)
      match goal with
      | He : uskl_all_etag _ _ = uskl_all_etag ?e (subst_bskl_in_uskl _ _ ?Rb)
        |- _ => idtac
      end.
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_all_etag ε0 R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_all_etag ε0 R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ]
                          (uskl_all_etag ε0
                             (subst_bskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                          ⩽˙ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_tagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        rewrite subst_bskl_in_uskl_fresh_eq in Hnode; [ | exact HαR' ].
        simpl. rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαR' ].
        inversion Hst; subst.
        eapply a_subtag_psi_cong;
          [ exact Hnode
          | fsetdec_empty ].
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | pskl_hole | Ψ ]
                          (uskl_all_etag ε0
                             (subst_bskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                          ⩽˙ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_tagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply subst_bskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ∀-headed source is not guarded *)
        match goal with
        | Hg : guarded_pskl ⌊ _ ⌋ˢ |- _ => simpl in Hg; inversion Hg
        end.
      * (* LS-ForallR : a ∀ input contradicts guarded-or-hole *)
        match goal with
        | Hg : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Hg as [Hg | Hg]; [ inversion Hg | discriminate Hg ]
        end.
      * (* LS-ForallL : the structural crux *)
      match goal with
      | HDf : forall b : atom, b `notin` ?L1 -> _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ |- _ =>
          rename HDf into HDbody; rename L1 into LD
      end.
      assert (Hlcstrip : lc_uskl (pskl_to_uskl (uskl_to_pskl ψa)))
        by (apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ).
      assert (HlcP1 : lc_pskl P1)
        by (eapply a_wf_pskl_lc; eauto).
      destruct (atom_fresh (singleton αv `union` ftvar_in_uskl ψa
                  `union` ftvar_in_uskl R0
                  `union` ftvar_in_pskl ⌊ R0 ⌋ˢ
                  `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P1 `union` LD)) as [αt Hαt].
      destruct (atom_fresh (LD `union` singleton αv `union` singleton αt
                  `union` ftvar_in_pskl ⌊ R0 ⌋ˢ
                  `union` ftvar_in_pskl P1)) as [β0 Hβ0].
      pose proof (HDbody β0 ltac:(clear - Hβ0; fsetdec)) as Dβ0.
      apply a_looksub_rename_var with (α' := αt) in Dβ0;
        [ | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          ⌊ R0 ⌋ˢ (pskl_var_f β0)) as Hup;
            simpl in Hup; clear - Hαt Hβ0 Hup; fsetdec ].
      rewrite <- subst_pskl_in_pskl_open_pskl_wrt_pskl_var in Dβ0;
        [ | clear - Hβ0; fsetdec | constructor ].
      apply a_looksub_subst_stable with (β := β0) (P0 := P1) in Dβ0;
        [ | clear - Hβ0; fsetdec
          | clear - Hαt; fsetdec
          | exact HlcP1 ].
      rewrite <- subst_pskl_in_pskl_intro in Dβ0;
        [ | pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          ⌊ R0 ⌋ˢ (pskl_var_f αt) αv) as Hup2;
            simpl in Hup2; clear - Hβ0 Hup2; fsetdec ].
      (* freshness facts for the rebuilt family *)
      assert (Hαtψa : αt `notin` ftvar_in_uskl ψa)
        by (clear - Hαt; fsetdec).
      assert (HαvStrip : αv `notin` ftvar_in_uskl
                           (pskl_to_uskl (uskl_to_pskl ψa))).
      { intro Hin.
        pose proof (ftvar_in_pskl_uskl_to_pskl
                      (pskl_to_uskl (uskl_to_pskl ψa))) as Hf1.
        rewrite uskl_to_pskl_pskl_to_uskl in Hf1.
        pose proof (ftvar_in_pskl_uskl_to_pskl ψa) as Hf2.
        clear - Hin Hf1 Hf2 Hαψ. fsetdec. }
      destruct (atom_fresh L) as [α0 Hα0].
      assert (Hdecls : a_decls Ξ)
        by (eapply a_extract_decls; eauto).
      assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0)).
      { apply a_wf_aenv_prepend_decls; auto.
        - match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu; solve_uniq end.
        - intros α1 Hα1.
          match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu Hα1; destruct_uniq;
            unfold disjoint in *; fsetdec end. }
      assert (Hmono : forall x (b : abind),
                 binds x b Θ0 -> binds x b (Ξ ++ Θ0))
        by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
      assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
        by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
      simpl.
      eapply a_subtag__forall_l_tagged
        with (L := L `union` LD `union` singleton αv `union` singleton αt
                   `union` ftvar_in_pskl P1)
             (Ξ := Ξ) (P1 := P1);
        [ assumption | assumption | | assumption | assumption | ].
      { intros α1 Hα1.
        replace (⌊ open_uskl_wrt_uskl
                     (subst_bskl_in_uskl ψa αv R0) (uskl_var_f α1) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl
                    (subst_bskl_in_uskl
                       (pskl_to_uskl (uskl_to_pskl ψa)) αv R0)
                    (uskl_var_f α1) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open;
              rewrite ! uskl_to_pskl_subst;
              rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        match goal with
        | Hex : forall a, a `notin` _ -> a_extract _ _ _ _ _ _ _ _ |- _ =>
            apply Hex; clear - Hα1; fsetdec
        end. }
        intros Ψg' ψg' Hfr Hsort Hera.
        assert (Hlcg : lc_uskl ψg')
          by (apply is_tskl_lc; inversion Hsort; assumption).
        assert (Hαtg : αt `notin` ftvar_in_uskl ψg').
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl ψg'). rewrite Hera.
          clear - Hαt; fsetdec. }
        assert (Hsubject :
            subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αt
              (open_uskl_wrt_uskl
                 (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg')
            = open_uskl_wrt_uskl
                (subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0)
                ψg').
        { rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcstrip ].
          rewrite subst_bskl_in_uskl_decompose;
            [ | exact HαvStrip | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_bskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (Hresult :
            subst_bskl_in_uskl ψa αt
              (open_uskl_wrt_uskl
                 (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg')
            = open_uskl_wrt_uskl (subst_bskl_in_uskl ψa αv R0) ψg').
        { rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcψ ].
          rewrite subst_bskl_in_uskl_decompose;
            [ | exact Hαψ | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_bskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (HDg :
            ⌊ open_uskl_wrt_uskl
                (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg' ⌋ˢ
            ≼[ αt , M ] P0 ⤳ Ξc ⨾ C).
        { rewrite uskl_to_pskl_open_gen.
          rewrite uskl_to_pskl_subst. simpl.
          rewrite Hera. exact Dβ0. }
        assert (HlcSg : lc_uskl
            (open_uskl_wrt_uskl
               (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg')).
        { apply lc_body_uskl_wrt_uskl; [ | exact Hlcg ].
          match goal with
          | |- body_uskl_wrt_uskl _ =>
              eapply lc_body_uskl_all_etag_2
                with (ε1 := ε0);
              change (uskl_all_etag ε0
                        (subst_bskl_in_uskl (uskl_var_f αt) αv R0))
                with (subst_bskl_in_uskl (uskl_var_f αt) αv
                        (uskl_all_etag ε0 R0));
              apply subst_bskl_in_uskl_lc_uskl;
                [ exact HlcS0 | constructor ]
          end. }
        assert (HwfSg : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
            ⌊ open_uskl_wrt_uskl
                (subst_bskl_in_uskl
                   (pskl_to_uskl (uskl_to_pskl ψa)) αv R0) ψg' ⌋ˢ).
        { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
          rewrite Hera.
          change (open_pskl_wrt_pskl_rec 0 P1
                    ⌊ subst_bskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ)
            with (open_pskl_wrt_pskl
                    ⌊ subst_bskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ P1).
          simpl in HwfT.
          inversion HwfT; subst.
          match goal with
          | Hbody : forall α, α `notin` ?L0 -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
              apply a_wf_pskl_open with (L := L0);
                [ intros α Hα;
                  eapply a_wf_pskl_weaken;
                    [ exact Hmono | apply Hbody; auto ]
                | assumption ]
          end. }
        rewrite <- Hresult.
        eapply a_subtag_psi_cong;
          [ match goal with
            | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
                eapply (IHfam Ψg' ψg' ltac:(clear - Hfr; fsetdec) Hsort Hera
                          (open_uskl_wrt_uskl
                             (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg')
                          ψa Ψa αt Ξc C);
                [ rewrite Hsubject; reflexivity
                | exact HDg
                | exact Hst
                | exact Hαtψa
                | clear - Hαt; fsetdec
                | exact Hlcψ
                | exact HlcSg
                | exact HwfΞΘ
                | exact HwfP0'
                | exact HwfSg
                | exact Hmod ]
            end
          | clear; fsetdec ].

  - (* ForallL (untagged) *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var : the strip itself is the ∀ source *)
      revert HeqT HwfT.
      destruct_if as [-> | Hc]; intros HeqT HwfT; [ | discriminate HeqT ].
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var : the decoration-var route *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ eapply a_subtag__forall_l_untagged
              with (L := L) (Ξ := Ξ) (P1 := P1); eassumption
          | simpl; exact HeqT
          | eassumption
          | intros α1 g Hb; inversion Hb
          | exact Hlcψ
          | exact Hwf
          | rewrite HeqT;
            apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ
          | exact HwfP0
          | exact HwfT
          | exact Hmod ].
      * (* LS-Absent : the looked variable occurs *)
        match goal with
        | Ha : αv `notin` ftvar_in_pskl (pskl_var_f αv) |- _ =>
            simpl in Ha; exfalso; clear - Ha; fsetdec
        end.
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ eapply a_subtag__forall_l_untagged
              with (L := L) (Ξ := Ξ) (P1 := P1); eassumption
          | reflexivity
          | exact Hlcψ
          | rewrite HeqT; rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
      * (* LS-Check : the source is the looked variable *)
        match goal with
        | Hne : pskl_var_f αv <> pskl_var_f αv |- _ => congruence
        end.
      * (* LS-ForallR : a ∀ input contradicts guarded-or-hole *)
        match goal with
        | Hg : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Hg as [Hg | Hg]; [ inversion Hg | discriminate Hg ]
        end.
    + (* R0 = all_syn R0 *)
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_all_syn R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_all_syn R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ]
                          (uskl_all_syn
                             (subst_bskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                          ⩽˙ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        rewrite subst_bskl_in_uskl_fresh_eq in Hnode; [ | exact HαR' ].
        simpl. rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαR' ].
        inversion Hst; subst.
        eapply a_subtag_psi_cong;
          [ exact Hnode
          | fsetdec_empty ].
      * (* LS-Vacuous *)
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | pskl_hole | Ψ ]
                          (uskl_all_syn
                             (subst_bskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                          ⩽˙ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ exact Hnode | reflexivity
          | apply subst_bskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ∀-headed source is not guarded *)
        match goal with
        | Hg : guarded_pskl ⌊ _ ⌋ˢ |- _ => simpl in Hg; inversion Hg
        end.
      * (* LS-ForallR : a ∀ input contradicts guarded-or-hole *)
        match goal with
        | Hg : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Hg as [Hg | Hg]; [ inversion Hg | discriminate Hg ]
        end.
      * (* LS-ForallL : the structural crux *)
      match goal with
      | HDf : forall b : atom, b `notin` ?L1 -> _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ |- _ =>
          rename HDf into HDbody; rename L1 into LD
      end.
      assert (Hlcstrip : lc_uskl (pskl_to_uskl (uskl_to_pskl ψa)))
        by (apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ).
      assert (HlcP1 : lc_pskl P1)
        by (eapply a_wf_pskl_lc; eauto).
      destruct (atom_fresh (singleton αv `union` ftvar_in_uskl ψa
                  `union` ftvar_in_uskl R0
                  `union` ftvar_in_pskl ⌊ R0 ⌋ˢ
                  `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P1 `union` LD)) as [αt Hαt].
      destruct (atom_fresh (LD `union` singleton αv `union` singleton αt
                  `union` ftvar_in_pskl ⌊ R0 ⌋ˢ
                  `union` ftvar_in_pskl P1)) as [β0 Hβ0].
      pose proof (HDbody β0 ltac:(clear - Hβ0; fsetdec)) as Dβ0.
      apply a_looksub_rename_var with (α' := αt) in Dβ0;
        [ | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          ⌊ R0 ⌋ˢ (pskl_var_f β0)) as Hup;
            simpl in Hup; clear - Hαt Hβ0 Hup; fsetdec ].
      rewrite <- subst_pskl_in_pskl_open_pskl_wrt_pskl_var in Dβ0;
        [ | clear - Hβ0; fsetdec | constructor ].
      apply a_looksub_subst_stable with (β := β0) (P0 := P1) in Dβ0;
        [ | clear - Hβ0; fsetdec
          | clear - Hαt; fsetdec
          | exact HlcP1 ].
      rewrite <- subst_pskl_in_pskl_intro in Dβ0;
        [ | pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          ⌊ R0 ⌋ˢ (pskl_var_f αt) αv) as Hup2;
            simpl in Hup2; clear - Hβ0 Hup2; fsetdec ].
      (* freshness facts for the rebuilt family *)
      assert (Hαtψa : αt `notin` ftvar_in_uskl ψa)
        by (clear - Hαt; fsetdec).
      assert (HαvStrip : αv `notin` ftvar_in_uskl
                           (pskl_to_uskl (uskl_to_pskl ψa))).
      { intro Hin.
        pose proof (ftvar_in_pskl_uskl_to_pskl
                      (pskl_to_uskl (uskl_to_pskl ψa))) as Hf1.
        rewrite uskl_to_pskl_pskl_to_uskl in Hf1.
        pose proof (ftvar_in_pskl_uskl_to_pskl ψa) as Hf2.
        clear - Hin Hf1 Hf2 Hαψ. fsetdec. }
      destruct (atom_fresh L) as [α0 Hα0].
      assert (Hdecls : a_decls Ξ)
        by (eapply a_extract_decls; eauto).
      assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0)).
      { apply a_wf_aenv_prepend_decls; auto.
        - match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu; solve_uniq end.
        - intros α1 Hα1.
          match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu Hα1; destruct_uniq;
            unfold disjoint in *; fsetdec end. }
      assert (Hmono : forall x (b : abind),
                 binds x b Θ0 -> binds x b (Ξ ++ Θ0))
        by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
      assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
        by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
      simpl.
      eapply a_subtag__forall_l_untagged
        with (L := L `union` LD `union` singleton αv `union` singleton αt
                   `union` ftvar_in_pskl P1)
             (Ξ := Ξ) (P1 := P1);
        [ assumption | assumption | | assumption | assumption | ].
      { intros α1 Hα1.
        replace (⌊ open_uskl_wrt_uskl
                     (subst_bskl_in_uskl ψa αv R0) (uskl_var_f α1) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl
                    (subst_bskl_in_uskl
                       (pskl_to_uskl (uskl_to_pskl ψa)) αv R0)
                    (uskl_var_f α1) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open;
              rewrite ! uskl_to_pskl_subst;
              rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        match goal with
        | Hex : forall a, a `notin` _ -> a_extract _ _ _ _ _ _ _ _ |- _ =>
            apply Hex; clear - Hα1; fsetdec
        end. }
        intros Ψg' ψg' Hfr Hsort Hera.
        assert (Hlcg : lc_uskl ψg')
          by (apply is_tskl_lc; inversion Hsort; assumption).
        assert (Hαtg : αt `notin` ftvar_in_uskl ψg').
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl ψg'). rewrite Hera.
          clear - Hαt; fsetdec. }
        assert (Hsubject :
            subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αt
              (open_uskl_wrt_uskl
                 (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg')
            = open_uskl_wrt_uskl
                (subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0)
                ψg').
        { rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcstrip ].
          rewrite subst_bskl_in_uskl_decompose;
            [ | exact HαvStrip | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_bskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (Hresult :
            subst_bskl_in_uskl ψa αt
              (open_uskl_wrt_uskl
                 (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg')
            = open_uskl_wrt_uskl (subst_bskl_in_uskl ψa αv R0) ψg').
        { rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcψ ].
          rewrite subst_bskl_in_uskl_decompose;
            [ | exact Hαψ | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_bskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (HDg :
            ⌊ open_uskl_wrt_uskl
                (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg' ⌋ˢ
            ≼[ αt , M ] P0 ⤳ Ξc ⨾ C).
        { rewrite uskl_to_pskl_open_gen.
          rewrite uskl_to_pskl_subst. simpl.
          rewrite Hera. exact Dβ0. }
        assert (HlcSg : lc_uskl
            (open_uskl_wrt_uskl
               (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg')).
        { apply lc_body_uskl_wrt_uskl; [ | exact Hlcg ].
          match goal with
          | |- body_uskl_wrt_uskl _ =>
              eapply lc_body_uskl_all_syn_1;
              change (uskl_all_syn
                        (subst_bskl_in_uskl (uskl_var_f αt) αv R0))
                with (subst_bskl_in_uskl (uskl_var_f αt) αv
                        (uskl_all_syn R0));
              apply subst_bskl_in_uskl_lc_uskl;
                [ exact HlcS0 | constructor ]
          end. }
        assert (HwfSg : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
            ⌊ open_uskl_wrt_uskl
                (subst_bskl_in_uskl
                   (pskl_to_uskl (uskl_to_pskl ψa)) αv R0) ψg' ⌋ˢ).
        { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
          rewrite Hera.
          change (open_pskl_wrt_pskl_rec 0 P1
                    ⌊ subst_bskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ)
            with (open_pskl_wrt_pskl
                    ⌊ subst_bskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ P1).
          simpl in HwfT.
          inversion HwfT; subst.
          match goal with
          | Hbody : forall α, α `notin` ?L0 -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
              apply a_wf_pskl_open with (L := L0);
                [ intros α Hα;
                  eapply a_wf_pskl_weaken;
                    [ exact Hmono | apply Hbody; auto ]
                | assumption ]
          end. }
        rewrite <- Hresult.
        eapply a_subtag_psi_cong;
          [ match goal with
            | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
                eapply (IHfam Ψg' ψg' ltac:(clear - Hfr; fsetdec) Hsort Hera
                          (open_uskl_wrt_uskl
                             (subst_bskl_in_uskl (uskl_var_f αt) αv R0) ψg')
                          ψa Ψa αt Ξc C);
                [ rewrite Hsubject; reflexivity
                | exact HDg
                | exact Hst
                | exact Hαtψa
                | clear - Hαt; fsetdec
                | exact Hlcψ
                | exact HlcSg
                | exact HwfΞΘ
                | exact HwfP0'
                | exact HwfSg
                | exact Hmod ]
            end
          | clear; fsetdec ].

  - (* Ghost : source ◇ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var *)
      revert HeqT.
      destruct_if as [-> | Hc]; intro HeqT; [ | discriminate HeqT ].
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var : decoration-var at ρ = nil *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ apply a_subtag__ghost; assumption
          | simpl; exact HeqT
          | eassumption
          | intros α1 g Hb; inversion Hb
          | exact Hlcψ
          | exact Hwf
          | rewrite HeqT;
            apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ
          | exact HwfP0
          | exact HwfT
          | exact Hmod ].
      * (* LS-Absent : the looked variable occurs *)
        match goal with
        | Ha : αv `notin` ftvar_in_pskl (pskl_var_f αv) |- _ =>
            simpl in Ha; exfalso; clear - Ha; fsetdec
        end.
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__ghost; assumption
          | reflexivity
          | exact Hlcψ
          | rewrite HeqT; rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
      * (* LS-Check : the source is the looked variable *)
        match goal with
        | Hne : pskl_var_f αv <> pskl_var_f αv |- _ => congruence
        end.
      * (* LS-ForallR : SK ∀-input at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
    + (* R0 = ◇ : nothing to decorate *)
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ HD
                  ltac:(simpl; clear; fsetdec)) as [-> ->].
      inversion Hst; subst.
      simpl.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghost; assumption
        | fsetdec_empty ].
  - (* GhostG : source ◈ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var : the strip is never dotted *)
      revert HeqT.
      destruct_if as [-> | Hc]; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_holeg; symmetry; exact HeqT
      | discriminate HeqT ].
    + (* R0 = ◈ : P0 = ◇ is pinned by the rule *)
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ HD
                  ltac:(simpl; clear; fsetdec)) as [-> ->].
      inversion Hst; subst.
      simpl.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghostg; assumption
        | fsetdec_empty ].
  - (* UnivGhostL : source ∀◇.R̄ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var *)
      revert HeqT HwfT.
      destruct_if as [-> | Hc]; intros HeqT HwfT; [ | discriminate HeqT ].
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var : decoration-var at ρ = nil *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ apply a_subtag__univ_ghost_l; eassumption
          | simpl; exact HeqT
          | eassumption
          | intros α1 g Hb; inversion Hb
          | exact Hlcψ
          | exact Hwf
          | rewrite HeqT;
            apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ
          | exact HwfP0
          | exact HwfT
          | exact Hmod ].
      * (* LS-Absent : the looked variable occurs *)
        match goal with
        | Ha : αv `notin` ftvar_in_pskl (pskl_var_f αv) |- _ =>
            simpl in Ha; exfalso; clear - Ha; fsetdec
        end.
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_l; eassumption
          | reflexivity
          | exact Hlcψ
          | rewrite HeqT; rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
      * (* LS-Check : the source is the looked variable *)
        match goal with
        | Hne : pskl_var_f αv <> pskl_var_f αv |- _ => congruence
        end.
      * (* LS-ForallR : SK ∀-input at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
    + (* R0 = ∀◇.R0 *)
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HD.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_tophole R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_tophole R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        inversion Hst; subst.
        simpl. rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαR' ].
        match goal with
        | Hs' : _ ⊢ᵗ[ _ | _ | _ | _ ]
                  (subst_bskl_in_uskl _ _ _) ⩽˙ _ ⊣ _ |- _ =>
            rewrite subst_bskl_in_uskl_fresh_eq in Hs'; [ | exact HαR' ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__univ_ghost_l; eassumption
          | fsetdec_empty ].
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_l; eassumption
          | reflexivity
          | apply subst_bskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ∀◇-headed source is not guarded *)
        match goal with
        | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
        end.
      * (* LS-ForallR : SK ∀-input at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
      * (* LS-UnivGhostL : the structural mirror *)
        simpl.
        apply a_subtag__univ_ghost_l; [ assumption | ].
        match goal with
        | IH : forall R1 : uskl, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hst | exact Hαψ
              | exact HαP0 | exact Hlcψ | assumption
              | exact Hwf | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_tophole_inv in HwfT;
                exact HwfT
              | exact Hmod ]
        end.
  - (* UnivGhostLG : source ∀◈.R̄ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* R0 = var : the strip is never dotted *)
      revert HeqT.
      destruct_if as [-> | Hc]; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_topholeg; symmetry; exact HeqT
      | discriminate HeqT ].
    + (* R0 = ∀◈.R0 *)
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HD.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_topholeg R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_topholeg R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        inversion Hst; subst.
        simpl. rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαR' ].
        match goal with
        | Hs' : _ ⊢ᵗ[ _ | _ | _ | _ ]
                  (subst_bskl_in_uskl _ _ _) ⩽˙ _ ⊣ _ |- _ =>
            rewrite subst_bskl_in_uskl_fresh_eq in Hs'; [ | exact HαR' ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__univ_ghost_lg; eassumption
          | fsetdec_empty ].
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_lg; eassumption
          | reflexivity
          | apply subst_bskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ∀◇-headed source is not guarded *)
        match goal with
        | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
        end.
      * (* LS-ForallR : SK ∀-input at TC contradicts the mode discipline *)
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
      * (* LS-UnivGhostL : the structural mirror *)
        simpl.
        apply a_subtag__univ_ghost_lg; [ assumption | ].
        match goal with
        | IH : forall R1 : uskl, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hst | exact Hαψ
              | exact HαP0 | exact Hlcψ | assumption
              | exact Hwf | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_tophole_inv in HwfT;
                exact HwfT
              | exact Hmod ]
        end.
  - (* FlexMono : source α̂₀ *)
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    revert HeqT.
    destruct_if as [-> | Hc]; intro HeqT.
    + (* eq : the strip is the flexible variable — decoration-var *)
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ apply a_subtag__flex_mono; eassumption
          | simpl; exact HeqT
          | eassumption
          | intros α1 g Hb; inversion Hb
          | exact Hlcψ
          | exact Hwf
          | rewrite HeqT;
            apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ
          | exact HwfP0
          | exact HwfT
          | exact Hmod ].
      * (* LS-Absent : the looked variable occurs *)
        match goal with
        | Ha : αv `notin` ftvar_in_pskl (pskl_var_f αv) |- _ =>
            simpl in Ha; exfalso; clear - Ha; fsetdec
        end.
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        simpl.
        destruct_if as [_ | Hc];
            [ | exfalso; congruence ].
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__flex_mono; eassumption
          | reflexivity
          | exact Hlcψ
          | rewrite HeqT; rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
    + (* neq : the subject is an untouched variable *)
      inversion HeqT; subst.
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ HD
                  ltac:(simpl; clear - Hc; fsetdec)) as [-> ->].
      inversion Hst; subst.
      simpl.
      destruct_if as [Habs | _];
          [ exfalso; congruence | ].
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__flex_mono; eassumption
        | fsetdec_empty ].
Qed.

(* ===================================================================== *)
(*  §15  Decorating constraint solving                                    *)
(*  (lemma:decorate-constraint-solving, subtyping-proofs.tex:95-127)      *)
(*                                                                        *)
(*  a_extract_decorate is Qed, proved the PAPER's way: induction on the   *)
(*  constraint solving [solve C □ Ps], building [solvetag C ψa Ψa] by     *)
(*  the tag/ghost PROVENANCE relation [dec_ext] — every tagged quantifier *)
(*  of ψa comes from a quantifier of an intermediate skeleton (or is      *)
(*  ABSORBED against a ∀◇ by SE-GhostForall), every dotted ghost (SK)     *)
(*  from a ghost, and every DROPPED ∀◇ sits over a GUARDED erasure.       *)
(*  Coverage is SET MEMBERSHIP (Ψa = ⋃ per-constraint contributions, ⊆    *)
(*  squeezed against solvetag soundness), NOT a per-step growth identity  *)
(*  — so the idempotent re-collection of ∀-tags is harmless.  The only    *)
(*  side condition is the TY prose-wf "against a TYPE (ghost-free)",      *)
(*  which feeds [pskl_top_guarded] of the TY solve output (the guess-drop *)
(*  anchor); SK needs no condition at all.                                *)
(*                                                                        *)
(*  Reusable helpers below (kept from the walk): d_tags_skl congruence /  *)
(*  determinism / is_tskl, guarded+ghost-free skeleton-var rename, and    *)
(*  a_solvetag_sub_eq_rename_var (the ∀-case output uniformity).          *)
(* ===================================================================== *)

(** [d_tags_skl] respects set-equality of the tag context. *)
Lemma d_tags_skl_psi_cong : forall Ψ Ψ' ψ,
  d_tags_skl Ψ ψ -> Ψ [=] Ψ' -> d_tags_skl Ψ' ψ.
Proof.
  intros Ψ Ψ' ψ H; revert Ψ'; induction H; intros Ψ' Heq.
  - apply d_tags_skl__unit; fsetdec.
  - apply d_tags_skl__var; fsetdec.
  - eapply d_tags_skl__arrow;
      [ exact H | exact H0 | exact H1 | clear - H2 Heq; fsetdec ].
  - eapply d_tags_skl__all_etag;
      [ exact H | exact H1 | clear - H2 Heq; fsetdec ].
  - apply d_tags_skl__holeg; fsetdec.
  - apply d_tags_skl__topholeg; apply IHd_tags_skl; exact Heq.
Qed.

(** Determinism of the tag reading (up to set-equality). *)
Lemma d_tags_skl_det : forall Ψ1 Ψ' ψ,
  d_tags_skl Ψ1 ψ -> d_tags_skl Ψ' ψ -> Ψ1 [=] Ψ'.
Proof.
  intros Ψ1 Ψ' ψ H; revert Ψ'; induction H; intros Ψ' HB; inversion HB; subst.
  - (* unit *) fsetdec.
  - (* var *) fsetdec.
  - (* arrow : pin the second derivation's components via [Ψ'] union eqn *)
    match goal with
    | Hd1 : d_tags_skl ?Ψa R1, Hd2 : d_tags_skl ?Ψb R2,
      _ : Ψ' [=] union ?Ψa ?Ψb |- _ =>
        pose proof (IHd_tags_skl1 _ Hd1) as He1;
        pose proof (IHd_tags_skl2 _ Hd2) as He2
    end.
    fsetdec.
  - (* all_etag : match the IH by shape; pin the second body via [Ψ']=add ε _ *)
    match goal with
    | HIH : forall α, α `notin` ?La -> forall Ψx, d_tags_skl Ψx _ -> _ [=] Ψx,
      Hbody : forall α, α `notin` ?Lb -> d_tags_skl ?Ψb _,
      _ : Ψ' [=] add ε ?Ψb |- _ =>
        destruct (atom_fresh (La `union` Lb)) as [α Hα];
        pose proof (HIH α ltac:(clear - Hα; fsetdec)
                      Ψb (Hbody α ltac:(clear - Hα; fsetdec))) as He
    end.
    fsetdec.
  - (* holeg *) fsetdec.
  - (* topholeg *) apply IHd_tags_skl; assumption.
Qed.

(** Guardedness / ghost-freeness survive a skeleton-variable rename. *)
Lemma guarded_uskl_subst_var : forall ψ α β,
  guarded_uskl ψ -> guarded_uskl (subst_bskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros ψ α β H; inversion H; subst; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - apply guarded_uskl__arrow;
      apply subst_bskl_in_uskl_lc_uskl; auto; apply lc_uskl_var_f.
Qed.

Lemma uskl_ghost_free_subst_var : forall ψ α β,
  uskl_ghost_free ψ ->
  uskl_ghost_free (subst_bskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros ψ α β H; induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - auto with frost.
  - apply uskl_ghost_free__all_etag with (L := L `union` singleton α);
      intros α2 Hα2;
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
        [ apply H0; clear - Hα2; fsetdec
        | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
  - apply uskl_ghost_free__all_syn with (L := L `union` singleton α);
      intros α2 Hα2;
      rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
        [ apply H0; clear - Hα2; fsetdec
        | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
Qed.

(** [solvetag] is invariant under a simultaneous skeleton-variable rename of
    subject and target (the tags are ε-markers, untouched). *)
Lemma a_solvetag_sub_eq_rename_var :
  (forall ψ M P Ψ, ψ ≼ᵗ[ M ] P ⤳ Ψ ->
     forall α β0, (subst_bskl_in_uskl (uskl_var_f β0) α ψ) ≼ᵗ[ M ]
                 (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ) /\
  (forall ψ P Ψ, ψ ∼ᵗ P ⤳ Ψ ->
     forall α β0, (subst_bskl_in_uskl (uskl_var_f β0) α ψ) ∼ᵗ
                 (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ).
Proof.
  apply (a_solvetag_sub_eq_mutind
           (fun ψ M P Ψ _ => forall α β0,
              (subst_bskl_in_uskl (uskl_var_f β0) α ψ) ≼ᵗ[ M ]
              (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ)
           (fun ψ P Ψ _ => forall α β0,
              (subst_bskl_in_uskl (uskl_var_f β0) α ψ) ∼ᵗ
              (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ));
    intros; simpl.
  - (* SSub-Var *)
    destruct_if;
      apply a_solvetag_sub__var; assumption.
  - (* SSub-ForallL *)
    apply a_solvetag_sub__forall_l with (L := L `union` singleton α); intros β Hβ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall b, _ |- _ => apply IH; clear - Hβ; fsetdec end.
  - (* SSub-UnivGhostLG *)
    apply a_solvetag_sub__univ_ghost_lg; auto.
  - (* SSub-Vacuous *)
    apply a_solvetag_sub__vacuous; assumption.
  - (* SSub-Check *)
    apply a_solvetag_sub__check;
      [ apply guarded_uskl_subst_var; assumption
      | apply guarded_pskl_subst_var; assumption | auto ].
  - (* SSub-ForallR *)
    apply a_solvetag_sub__forall_r with (L := L `union` singleton α); intros β Hβ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ; fsetdec | apply lc_pskl_var_f ].
    match goal with IH : forall b, _ |- _ => apply IH; clear - Hβ; fsetdec end.
  - (* SSub-Arrow *)
    eapply a_solvetag_sub__arrow; [ auto | auto | eassumption ].
  - (* SEq-Unit *)
    apply a_solvetag_eq__unit; assumption.
  - (* SEq-Var *)
    destruct_if;
      apply a_solvetag_eq__var; assumption.
  - (* SEq-Vacuous *)
    apply a_solvetag_eq__vacuous; assumption.
  - (* SEq-Arrow *)
    eapply a_solvetag_eq__arrow; [ auto | auto | eassumption ].
  - (* SEq-ForallInh *)
    eapply a_solvetag_eq__forall_inh with (L := L `union` singleton α);
      [ intros β Hβ;
        rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
          [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ];
        rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
          [ | clear - Hβ; fsetdec | apply lc_pskl_var_f ];
        match goal with IH : forall b, _ |- _ => apply IH; clear - Hβ; fsetdec end
      | eassumption ].
  - (* SEq-UnivGhostG *)
    apply a_solvetag_eq__univ_ghostg; auto.
  - (* SEq-ForallSyn *)
    apply a_solvetag_eq__forall_syn with (L := L `union` singleton α); intros β Hβ.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall b, _ |- _ =>
      specialize (IH β ltac:(clear - Hβ; fsetdec) α β0); simpl in IH; exact IH end.
  - (* SEq-UnivGhostR *)
    apply a_solvetag_eq__univ_ghost_r;
      [ rewrite uskl_to_pskl_subst; simpl;
        apply guarded_pskl_subst_var; assumption
      | auto ].
  - (* SEq-FlexR : the target var may itself be renamed *)
    destruct_if;
      apply a_solvetag_eq__flex_r;
      first [ apply uskl_ghost_free_subst_var; assumption | assumption ].
Qed.

(** A tag reading witnesses that its subject is a decorated skeleton. *)
Lemma d_tags_skl_is_tskl : forall Ψ ψ, d_tags_skl Ψ ψ -> is_tskl ψ.
Proof.
  intros Ψ ψ H; induction H; eauto with frost.
Qed.

(** SOUNDNESS (paper coverage, direction ⊆): a decorated solvetag collects
    only tags that ψ actually carries.  Mutual over ≼ᵗ / ∼ᵗ. *)
Lemma a_solvetag_sub_eq_sound :
  (forall ψ M P Ψ, ψ ≼ᵗ[ M ] P ⤳ Ψ ->
     forall Ψtot, d_tags_skl Ψtot ψ -> Ψ [<=] Ψtot) /\
  (forall ψ P Ψ, ψ ∼ᵗ P ⤳ Ψ ->
     forall Ψtot, d_tags_skl Ψtot ψ -> Ψ [<=] Ψtot).
Proof.
  apply a_solvetag_sub_eq_mutind.
  - (* SSub-Var *) intros α M P Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SSub-ForallL : subject all_etag ε ψ *)
    intros L ε ψ M P Ψ Hprem IH Ψtot Hdt; inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψ0 _,
      Heq : Ψtot [=] add ?e ?Ψ0 |- _ =>
        destruct (atom_fresh (L `union` L1)) as [β Hβ];
        pose proof (IH β ltac:(clear - Hβ; fsetdec) Ψ0
                      (Hb β ltac:(clear - Hβ; fsetdec))) as Hs;
        clear - Hs Heq; fsetdec
    end.
  - (* SSub-UnivGhostLG : subject topholeg ψ *)
    intros ψ M P Ψ Hprem IH Ψtot Hdt; inversion Hdt; subst.
    match goal with Hd : d_tags_skl ?T ψ |- _ => exact (IH T Hd) end.
  - (* SSub-Vacuous *) intros ψ M Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SSub-Check *) intros ψ B Ψ Hgψ HgB Hprem IH Ψtot Hdt; exact (IH Ψtot Hdt).
  - (* SSub-ForallR *) intros L ψ B Ψ Hprem IH Ψtot Hdt;
      destruct (atom_fresh L) as [β Hβ]; exact (IH β ltac:(clear - Hβ; fsetdec) Ψtot Hdt).
  - (* SSub-Arrow : subject arrow ψ1 ψ2 *)
    intros ψ1 ψ2 M Q1 Q2 Ψ Ψ1 Ψ2 Hp1 IH1 Hp2 IH2 He Ψtot Hdt; inversion Hdt; subst.
    match goal with
    | Ha : d_tags_skl ?T1 ψ1, Hbb : d_tags_skl ?T2 ψ2 |- _ =>
        pose proof (IH1 T1 Ha); pose proof (IH2 T2 Hbb)
    end.
    match goal with Heq : Ψtot [=] _ |- _ => clear - He Heq H H0; fsetdec end.
  - (* SEq-Unit *) intros Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SEq-Var *) intros α P Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SEq-Vacuous *) intros ψ Ψ He Ψtot Hdt; clear - He; fsetdec.
  - (* SEq-Arrow *) intros ψ1 ψ2 Q1 Q2 Ψ Ψ1 Ψ2 Hp1 IH1 Hp2 IH2 He Ψtot Hdt;
      inversion Hdt; subst.
    match goal with
    | Ha : d_tags_skl ?T1 ψ1, Hbb : d_tags_skl ?T2 ψ2 |- _ =>
        pose proof (IH1 T1 Ha); pose proof (IH2 T2 Hbb)
    end.
    match goal with Heq : Ψtot [=] _ |- _ => clear - He Heq H H0; fsetdec end.
  - (* SEq-ForallInh : subject all_etag ε ψ, Ψ = add ε Ψ0 *)
    intros L ε ψ P Ψ Ψ0 Hprem IH He Ψtot Hdt; inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heq : Ψtot [=] add ?e ?Ψt0 |- _ =>
        destruct (atom_fresh (L `union` L1)) as [β Hβ];
        pose proof (IH β ltac:(clear - Hβ; fsetdec) Ψt0
                      (Hb β ltac:(clear - Hβ; fsetdec))) as Hs;
        clear - Hs Heq He; fsetdec
    end.
  - (* SEq-UnivGhostG : subject topholeg ψ *)
    intros ψ P Ψ Hprem IH Ψtot Hdt; inversion Hdt; subst.
    match goal with Hd : d_tags_skl ?T ψ |- _ => exact (IH T Hd) end.
  - (* SEq-ForallSyn : subject all_etag ε ψ *)
    intros L ε ψ P Ψ Hprem IH Ψtot Hdt; inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heq : Ψtot [=] add ?e ?Ψt0 |- _ =>
        destruct (atom_fresh (L `union` L1)) as [β Hβ];
        pose proof (IH β ltac:(clear - Hβ; fsetdec) Ψt0
                      (Hb β ltac:(clear - Hβ; fsetdec))) as Hs;
        clear - Hs Heq; fsetdec
    end.
  - (* SEq-UnivGhostR : subject ψ, target ∀◇P *)
    intros ψ P Ψ Hg Hprem IH Ψtot Hdt; exact (IH Ψtot Hdt).
  - (* SEq-FlexR *) intros ψ α Ψ Hgf He Ψtot Hdt; clear - He; fsetdec.
Qed.

(** The list-level solvetag collects only ψ's tags (per-constraint ⊆ + union). *)
Lemma a_solvetag_sound : forall 𝒞 ψ Ψ Ψtot,
  𝒞 ⊩ᵗ ψ ⤳ Ψ -> d_tags_skl Ψtot ψ -> Ψ [<=] Ψtot.
Proof.
  intros 𝒞 ψ Ψ Ψtot Hc; revert Ψtot; induction Hc; intros Ψtot Hdt.
  - (* empty *) fsetdec_empty.
  - (* sub *) match goal with H : _ ≼ᵗ[ _ ] _ ⤳ _ |- _ =>
      pose proof ((proj1 a_solvetag_sub_eq_sound) _ _ _ _ H Ψtot Hdt) end; fsetdec.
  - (* eq *)
    match goal with
    | Hs : _ ∼ᵗ _ ⤳ ?Ψ1, He : _ [=] union ?Ψ1 ?Ψ2 |- _ =>
        pose proof ((proj2 a_solvetag_sub_eq_sound) _ _ _ Hs Ψtot Hdt) as Hae;
        pose proof (IHHc Ψtot Hdt) as Hai;
        clear - He Hae Hai; fsetdec
    end.
Qed.

(** SELF-SOLVETAG (paper coverage, base shape): a decorated skeleton solves
    against its OWN erasure, collecting EXACTLY its tags.  This is the SK
    guess (⌊ψ⌋=Q, identity) case and the set-membership coverage anchor —
    no ∀◇ frontier (topholeg aligns with ∀◇ via SEq-UnivGhostG) and no ε
    double-count (add ε handled by SEq-ForallInh). *)
Lemma solvetag_eq_self : forall Ψ ψ,
  d_tags_skl Ψ ψ -> ψ ∼ᵗ ⌊ ψ ⌋ˢ ⤳ Ψ.
Proof.
  intros Ψ ψ H; induction H; simpl.
  - apply a_solvetag_eq__unit; assumption.
  - apply a_solvetag_eq__var; assumption.
  - eapply a_solvetag_eq__arrow;
      [ exact IHd_tags_skl1 | exact IHd_tags_skl2 | assumption ].
  - (* all_etag ε R : target ∀⌊R⌋, Ψ = add ε Ψ0 *)
    eapply a_solvetag_eq__forall_inh with (L := L) (Ψ0 := Ψ0); [ | assumption ].
    intros β Hβ. rewrite <- uskl_to_pskl_open.
    match goal with
    | IH : forall α, α `notin` L -> _ ∼ᵗ _ ⤳ Ψ0 |- _ =>
        exact (IH β Hβ)
    end.
  - (* holeg : erasure is ◇ *) apply a_solvetag_eq__vacuous; assumption.
  - (* topholeg R : erasure ∀◇⌊R⌋ *)
    apply a_solvetag_eq__univ_ghostg; exact IHd_tags_skl.
Qed.

(* --------------------------------------------------------------------- *)
(*  PAPER COVERAGE (subtyping-proofs.tex:110-127): [dec_ext P ψ Ψ] is the
    ψ↔skeleton relation making the paper's "provenance observation"
    explicit — ψ (the decoration of the guess output) EXTENDS the
    intermediate solve skeleton P; Ψ = ψ's tags at positions the skeleton
    does not yet account for.  Coverage is SET-MEMBERSHIP (⊆), NOT a
    per-step growth identity, so the idempotent re-collection of ∀-tags
    is harmless.  The ∀◇ constructors are FAITHFUL (no side conditions on
    the against-skeleton P0 anywhere — the paper's lemma has none):
      · topholeg     — SK: the ∀◇ survives to the output, ψ dotted;
      · skip_tophole — the ∀◇ is dropped LATER (by a guarded-target solve
        step, or by the TY guess); in both droppings the subject erasure
        is GUARDED, which is exactly what SEq-UnivGhostR needs;
      · absorb_all   — a ∀ of ψ CREATED against the ∀◇ by SE-GhostForall
        (the skeleton stays ∀◇P0 under the binder, mirroring
        SEq-ForallSyn); its tag ε stays REMAINING (the skeleton has no
        matching quantifier), and SEq-ForallSyn indeed does not collect it. *)
(* --------------------------------------------------------------------- *)

Inductive dec_ext : pskl -> uskl -> atoms -> Prop :=
| dec_ext__hole : forall ψ Ψ,               (* P = ◇ : every tag of ψ remains *)
    is_tskl ψ ->
    d_tags_skl Ψ ψ ->
    dec_ext pskl_hole ψ Ψ
| dec_ext__unit : forall Ψ,
    Ψ [=] empty ->
    dec_ext pskl_unit uskl_unit Ψ
| dec_ext__var : forall α Ψ,
    Ψ [=] empty ->
    dec_ext (pskl_var_f α) (uskl_var_f α) Ψ
| dec_ext__arrow : forall P1 P2 ψ1 ψ2 Ψ Ψ1 Ψ2,
    dec_ext P1 ψ1 Ψ1 ->
    dec_ext P2 ψ2 Ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    dec_ext (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2) Ψ
| dec_ext__all : forall L P0 ψ0 ε Ψ,         (* P's ∀ ; ε accounted, not remaining *)
    (forall α, α `notin` L ->
       dec_ext (open_pskl_wrt_pskl P0 (pskl_var_f α))
               (open_uskl_wrt_uskl ψ0 (uskl_var_f α)) Ψ) ->
    dec_ext (pskl_all_syn P0) (uskl_all_etag ε ψ0) Ψ
| dec_ext__skip_tophole : forall P0 ψ Ψ,     (* P's ∀◇ dropped later; ψ guarded *)
    guarded_pskl ⌊ ψ ⌋ˢ ->
    dec_ext P0 ψ Ψ ->
    dec_ext (pskl_tophole P0) ψ Ψ
| dec_ext__topholeg : forall P0 ψ0 Ψ,        (* SK keeps ∀◇ ; ψ = ∀◈.ψ0 *)
    dec_ext P0 ψ0 Ψ ->
    dec_ext (pskl_tophole P0) (uskl_topholeg ψ0) Ψ
| dec_ext__absorb_all : forall L P0 ψ0 ε Ψ Ψ0,  (* ψ's ∀ created against the ∀◇
                                                   (SE-GhostForall); ε REMAINS *)
    (forall α, α `notin` L ->
       dec_ext (pskl_tophole P0)
               (open_uskl_wrt_uskl ψ0 (uskl_var_f α)) Ψ0) ->
    Ψ [=] add ε Ψ0 ->
    dec_ext (pskl_tophole P0) (uskl_all_etag ε ψ0) Ψ
| dec_ext__flex_forget : forall P α Ψ,       (* P resolved to flex α̂ (untagged) *)
    Ψ [=] empty ->
    dec_ext P (uskl_var_f α) Ψ.

#[export] Hint Constructors dec_ext : frost.

(** [dec_ext] respects set-equality of the remaining-tag context. *)
Lemma dec_ext_psi_cong : forall P ψ Ψ Ψ',
  dec_ext P ψ Ψ -> Ψ [=] Ψ' -> dec_ext P ψ Ψ'.
Proof.
  intros P ψ Ψ Ψ' H; revert Ψ'; induction H; intros Ψ' Heq.
  - apply dec_ext__hole;
      [ assumption | eapply d_tags_skl_psi_cong; [ exact H0 | exact Heq ] ].
  - apply dec_ext__unit; fsetdec.
  - apply dec_ext__var; fsetdec.
  - eapply dec_ext__arrow;
      [ exact H | exact H0 | clear - H1 Heq; fsetdec ].
  - apply dec_ext__all with (L := L). intros α Hα.
    match goal with
    | IH : forall α, α `notin` L -> forall Ψ0, _ -> dec_ext _ _ Ψ0 |- _ =>
        exact (IH α Hα Ψ' Heq)
    end.
  - apply dec_ext__skip_tophole; [ assumption | apply IHdec_ext; exact Heq ].
  - apply dec_ext__topholeg. apply IHdec_ext. exact Heq.
  - eapply dec_ext__absorb_all with (L := L) (Ψ0 := Ψ0);
      [ assumption | clear - H1 Heq; fsetdec ].
  - apply dec_ext__flex_forget; fsetdec.
Qed.

(** SK anchor / self-extension: a decorated skeleton extends its own erasure
    with no remaining tags. *)
Lemma dec_ext_erase_refl : forall ψ,
  is_tskl ψ ->
  dec_ext (uskl_to_pskl ψ) ψ empty.
Proof.
  intros ψ H; induction H; simpl.
  - apply dec_ext__unit; fsetdec.
  - apply dec_ext__var; fsetdec.
  - eapply dec_ext__arrow; [ exact IHis_tskl1 | exact IHis_tskl2 | fsetdec ].
  - apply dec_ext__all with (L := L). intros α Hα.
    rewrite <- uskl_to_pskl_open.
    match goal with
    | IH : forall α, α `notin` L -> dec_ext _ _ empty |- _ =>
        exact (IH α ltac:(clear - Hα; fsetdec))
    end.
  - apply dec_ext__hole; [ apply is_tskl__holeg | apply d_tags_skl__holeg; fsetdec ].
  - auto with frost.
Qed.

(** A guarded skeleton is locally closed. *)
Lemma guarded_pskl_lc : forall P, guarded_pskl P -> lc_pskl P.
Proof.
  intros P H; inversion H; subst; auto.
Qed.

(** Head-shape predicate: the skeleton's head is unit/var/arrow (the shapes
    [guarded_pskl] admits, without its lc payload; bound vars included so the
    predicate is stable under opening). *)
Definition pskl_guarded_head (P : pskl) : Prop :=
  match P with
  | pskl_unit | pskl_var_f _ | pskl_var_b _ | pskl_arrow _ _ => True
  | _ => False
  end.

Lemma lc_head_guarded : forall P,
  lc_pskl P -> pskl_guarded_head P -> guarded_pskl P.
Proof.
  intros P Hlc Hh; destruct P; simpl in Hh; try contradiction.
  - auto with frost.
  - inversion Hlc.
  - auto with frost.
  - inversion Hlc; subst; auto with frost.
Qed.

Lemma guarded_pskl_head : forall P, guarded_pskl P -> pskl_guarded_head P.
Proof. intros P H; inversion H; subst; simpl; exact I. Qed.

(** The TY guess preserves guarded heads (◇ ↦ var, ∀◇ stripped, ∀ kept —
    but a guarded-headed input has no ∀ head). *)
Lemma a_guess_mono_head : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> pskl_guarded_head P ->
  pskl_guarded_head (ptyp_to_pskl A).
Proof.
  intros Θ P Ξ A Hg Hh; inversion Hg; subst; simpl in Hh;
    try contradiction; simpl; exact I.
Qed.

(** [pskl_top_guarded P]: every universal ghost ∀◇ in P heads a guarded-headed
    body.  TY-mode solve outputs satisfy this (the eq-phase against ghost-free
    targets keeps the skeleton ∀◇-free; the terminal sub step only creates ∀◇
    over guarded bodies, SS-GhostL / SS-GhostLF) — it is what lets the TY
    guess-drop anchor use the GUARDED [skip_tophole]. *)
Fixpoint pskl_top_guarded (P : pskl) : Prop :=
  match P with
  | pskl_tophole P0 => pskl_guarded_head P0 /\ pskl_top_guarded P0
  | pskl_arrow P1 P2 => pskl_top_guarded P1 /\ pskl_top_guarded P2
  | pskl_all_syn P0 => pskl_top_guarded P0
  | _ => True
  end.

Lemma pskl_guarded_head_open_rec : forall P α' k,
  pskl_guarded_head P <-> pskl_guarded_head (open_pskl_wrt_pskl_rec k (pskl_var_f α') P).
Proof.
  intros P α' k; destruct P; simpl; try tauto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; tauto.
Qed.

Lemma pskl_top_guarded_open_rec : forall P α' k,
  pskl_top_guarded P <-> pskl_top_guarded (open_pskl_wrt_pskl_rec k (pskl_var_f α') P).
Proof.
  induction P; intros α' k; simpl; try tauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; tauto.
  - rewrite (IHP1 α' k), (IHP2 α' k); tauto.
  - rewrite (IHP α' (S k)); tauto.
  - rewrite (IHP α' k), (pskl_guarded_head_open_rec P α' k); tauto.
Qed.

(** WELL-FORMEDNESS ⟹ [pskl_top_guarded]: [a_wf_pskl__tophole] admits a ∀◇
    ONLY over a [guarded_pskl] body, so every ∀◇ in a wf skeleton heads a
    guarded body.  This is the paper's implicit source-skeleton discipline —
    it supplies exactly what the coverage needs (no [ghost_free]/[no_top]
    hypothesis: a ∀◇ in [P0] is fine, it just wraps a guarded type). *)
Lemma a_wf_pskl_top_guarded : forall Θ Δ P,
  a_wf_pskl Θ Δ P -> pskl_top_guarded P.
Proof.
  intros Θ Δ P H; induction H; simpl; try exact I.
  - (* arrow *) auto.
  - (* all : strip the fresh opener via the open_rec congruence *)
    destruct (atom_fresh L) as [α Hα].
    apply (proj2 (pskl_top_guarded_open_rec P α 0)).
    match goal with IH : forall α, α `notin` L -> pskl_top_guarded _ |- _ =>
      exact (IH α Hα) end.
  - (* tophole : guarded body ⟹ guarded_head + IH *)
    auto using guarded_pskl_head.
Qed.

(** ghost-free (no ghosts at all) ⟹ top-guarded (no ∀◇ to check). *)
Lemma pskl_ghost_free_top_guarded : forall P, pskl_ghost_free P -> pskl_top_guarded P.
Proof. induction P; simpl; intuition. Qed.

(** [pskl_top_guarded] survives monotype substitution (a mono has no ∀/∀◇, so
    it keeps guarded heads and creates no new ∀◇) — for the Flex-Assign case. *)
Lemma pskl_guarded_head_ptyp_mono : forall τ,
  mono_ptyp τ -> pskl_guarded_head (ptyp_to_pskl τ).
Proof. intros τ Hm; induction Hm; simpl; exact I. Qed.

Lemma pskl_guarded_head_subst_mono : forall P τ β,
  pskl_guarded_head P -> mono_ptyp τ ->
  pskl_guarded_head (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros P τ β Hg Hm; destruct P; simpl in Hg |- *; try contradiction; try exact I.
  destruct_if; auto using pskl_guarded_head_ptyp_mono.
Qed.

Lemma pskl_top_guarded_subst_mono : forall P τ β,
  pskl_top_guarded P -> mono_ptyp τ ->
  pskl_top_guarded (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  induction P; intros τ β Hg Hm; simpl in Hg |- *; try exact I.
  - (* var_f : β↦τ or itself, both top_guarded *)
    destruct_if; auto using pskl_ghost_free_top_guarded, ptyp_to_pskl_ghost_free.
  - (* arrow *) destruct Hg as [Hg1 Hg2]; auto using IHP1, IHP2.
  - (* all *) auto using IHP.
  - (* tophole *) destruct Hg as [Hgh Ht];
      auto using pskl_guarded_head_subst_mono, IHP.
Qed.

(** TY anchor: the [a_guess_mono] output painting's decoration extends the
    pre-guess skeleton (◇ ↦ fresh var, ∀◇ dropped onto a guarded remainder —
    supplied by [pskl_top_guarded] of the solve output). *)
(* ⚠️ SIZE INDUCTION (freshness campaign): [a_guess_mono] is exists-fresh
   while the target [dec_ext] is still cofinite, so the ∀ case must turn ONE
   guess instance into a family via [a_guess_mono_all_cofinite] — whose
   output is no sub-derivation, hence no derivation-IH.  See
   [a_guess_mono_rename_tvar_size] (prop_flex.v) for the recipe. *)
Lemma dec_ext_guess_mono_anchor_size : forall n Θ P' Ξ' A ψa,
  size_pskl P' <= n ->
  a_guess_mono Θ P' Ξ' A ->
  pskl_top_guarded P' ->
  is_tskl ψa ->
  uskl_ghost_free ψa ->
  ⌊ ψa ⌋ˢ = ptyp_to_pskl A ->
  dec_ext P' ψa empty.
Proof.
  induction n as [| n IHn]; intros Θ P' Ξ' A ψa Hsz Hg;
    [ destruct Hg; cbn in Hsz; lia | ].
  destruct Hg as [ Θ' α | Θ' Pb Ξb Ab Hgb | Θ' α | Θ'
                 | Θ' Pa Pb Ξa Ξb Aa Ab Hga Hgb
                 | Θ' Pb Ξb Ab b0 Hfr Hgb ];
    cbn in Hsz; intros Htg Histk Hgf Hera.
  - (* hole ↦ fresh α̂ : A = var α *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    apply dec_ext__hole; [ exact Histk | apply d_tags_skl__var; fsetdec ].
  - (* tophole P ↦ guess P : drop the ∀◇ ; the guess output is guarded *)
    simpl in Htg; destruct Htg as [Hhd Htg0].
    apply dec_ext__skip_tophole;
      [ rewrite Hera; apply lc_head_guarded;
          [ rewrite <- Hera; apply lc_uskl_to_pskl_local; apply is_tskl_lc;
            exact Histk
          | eapply a_guess_mono_head; eassumption ]
      | eapply IHn; [ lia | exact Hgb | exact Htg0 | exact Histk | exact Hgf
                    | exact Hera ] ].
  - (* var α ↦ var α *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    inversion Hera; subst. apply dec_ext__var; fsetdec.
  - (* unit ↦ unit *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    apply dec_ext__unit; fsetdec.
  - (* arrow ↦ arrow *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    inversion Hera; subst.
    simpl in Htg; destruct Htg as [Htg1 Htg2].
    inversion Histk; subst. inversion Hgf; subst.
    eapply dec_ext__arrow;
      [ eapply IHn with (P' := Pa); [ lia | exact Hga | .. ]
      | eapply IHn with (P' := Pb); [ lia | exact Hgb | .. ]
      | fsetdec ]; assumption.
  - (* forall P ↦ all A0 : the ghost-free [is_tskl] ∀-decoration is [all_etag].
       EXISTS-FRESH source, COFINITE target: re-open the guess at each α. *)
    destruct ψa; simpl in Hera; try discriminate Hera;
      try (inversion Histk; fail).          (* kill the non-[is_tskl] all_syn survivor *)
    injection Hera as Hera0.
    simpl in Htg.
    inversion Histk; subst. inversion Hgf; subst.
    match goal with
    | Hib : forall α, α `notin` ?Li -> is_tskl (open_uskl_wrt_uskl ?bd _),
      Hgfb : forall α, α `notin` ?Lg -> uskl_ghost_free (open_uskl_wrt_uskl ?bd _)
      |- _ =>
        apply dec_ext__all
          with (L := Li `union` Lg `union` dom Ξb `union` ftvar_in_pskl Pb
                       `union` ftvar_in_ptyp Ab);
        intros α Hα;
        eapply IHn with (P' := open_pskl_wrt_pskl Pb (pskl_var_f α))
                        (A := open_ptyp_wrt_ptyp Ab (ptyp_var_f α));
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | apply a_guess_mono_all_cofinite;
              [ apply a_guess_mono__forall with (β := b0);
                  [ exact Hfr | exact Hgb ]
              | clear - Hα; fsetdec ]
          | apply (proj1 (pskl_top_guarded_open_rec Pb α 0)); exact Htg
          | apply Hib; clear - Hα; fsetdec
          | apply Hgfb; clear - Hα; fsetdec
          | rewrite uskl_to_pskl_open; rewrite Hera0;
            rewrite <- ptyp_to_pskl_open; reflexivity ]
    end.
Qed.

Corollary dec_ext_guess_mono_anchor : forall Θ P' Ξ' A ψa,
  a_guess_mono Θ P' Ξ' A ->
  pskl_top_guarded P' ->
  is_tskl ψa ->
  uskl_ghost_free ψa ->
  ⌊ ψa ⌋ˢ = ptyp_to_pskl A ->
  dec_ext P' ψa empty.
Proof.
  intros. eapply dec_ext_guess_mono_anchor_size; eauto.
Qed.

(** ANCHOR: a decoration of the guess output extends the pre-guess skeleton,
    with NO remaining tags — the guess places untagged fresh flex vars at
    every ◇, so all of ψa's tags sit in the structure of [Q]. *)
Lemma dec_ext_guess_anchor : forall NM P Ξ' P' Ψa ψa,
  a_guess NM P Ξ' P' ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P) ->
  a_tags_sort NM Ψa ψa ->
  ⌊ ψa ⌋ˢ = P' ->
  dec_ext P ψa empty.
Proof.
  intros NM P Ξ' P' Ψa ψa Hg Htg Htags Hera; inversion Hg; subst.
  - (* SK : P' = P ; subst already rewrote P to ⌊ψa⌋ˢ *)
    inversion Htags; subst.
    apply dec_ext_erase_refl; assumption.
  - (* TY : P' = ptyp_to_pskl A ; the solve output is top-guarded *)
    inversion Htags; subst.
    eapply dec_ext_guess_mono_anchor; [ eassumption | apply Htg; reflexivity | .. ];
      eauto.
Qed.

(** Skeleton-variable rename lemmas (for the ∀ case's cofinite reconstruction). *)
Lemma is_tskl_rename_var : forall ψ α β,
  is_tskl ψ -> is_tskl (subst_bskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros ψ α β H; induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - auto with frost.
  - apply is_tskl__all_etag with (L := L `union` singleton α); intros α2 Hα2.
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall α, α `notin` L -> _ |- _ =>
      apply (IH α2 ltac:(clear - Hα2; fsetdec)) end.
  - auto with frost.
  - auto with frost.
Qed.

Lemma d_tags_skl_rename_var : forall Ψ ψ α β,
  d_tags_skl Ψ ψ -> d_tags_skl Ψ (subst_bskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros Ψ ψ α β H; induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - eauto with frost.
  - eapply d_tags_skl__all_etag with (L := L `union` singleton α) (Ψ0 := Ψ0);
      [ intros α2 Hα2 | assumption | assumption ].
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall α, α `notin` L -> _ |- _ =>
      apply (IH α2 ltac:(clear - Hα2; fsetdec)) end.
  - auto with frost.
  - auto with frost.
Qed.

Lemma dec_ext_rename_var : forall P ψ Ψ,
  dec_ext P ψ Ψ ->
  forall α β, dec_ext (subst_pskl_in_pskl (pskl_var_f β) α P)
                      (subst_bskl_in_uskl (uskl_var_f β) α ψ) Ψ.
Proof.
  intros P ψ Ψ H; induction H; intros αr βr; simpl.
  - auto using is_tskl_rename_var, d_tags_skl_rename_var with frost.
  - auto with frost.
  - destruct_if; auto with frost.
  - eapply dec_ext__arrow; [ apply IHdec_ext1 | apply IHdec_ext2 | assumption ].
  - apply dec_ext__all with (L := L `union` singleton αr); intros α2 Hα2.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα2; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall a, a `notin` L -> forall b c, _ |- _ =>
      apply (IH α2 ltac:(clear - Hα2; fsetdec)) end.
  - apply dec_ext__skip_tophole;
      [ rewrite uskl_to_pskl_subst; apply guarded_pskl_subst_var; assumption
      | apply IHdec_ext ].
  - apply dec_ext__topholeg; apply IHdec_ext.
  - eapply dec_ext__absorb_all with (L := L `union` singleton αr);
      [ intros α2 Hα2;
        rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
          [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ];
        match goal with IH : forall a, a `notin` L -> forall b c, _ |- _ =>
          apply (IH α2 ltac:(clear - Hα2; fsetdec)) end
      | assumption ].
  - destruct_if; auto with frost.
Qed.

(** A [dec_ext] subject is a decorated skeleton. *)
Lemma dec_ext_is_tskl : forall P ψ Ψ, dec_ext P ψ Ψ -> is_tskl ψ.
Proof.
  intros P ψ Ψ H; induction H; eauto with frost.
Qed.

(** A solve_eq output against a GUARDED target has a guarded head (no rule
    with a guarded target emits a ∀-, ∀◇- or ◇-headed output). *)
Lemma solve_eq_guarded_r_head : forall Θ P P0 P',
  Θ ⊢ₑ P ∼ P0 ⤳ P' -> guarded_pskl P0 -> pskl_guarded_head P'.
Proof.
  intros Θ P P0 P' H; induction H; intros Hg; simpl;
    try exact I; try (inversion Hg; fail).
  - (* hole_l : P'=P0 *) inversion Hg; subst; simpl; auto.
  - (* tophole_l_guarded *) apply IHa_solve_eq; assumption.
Qed.

(** Symmetrically for a GUARDED subject. *)
Lemma solve_eq_guarded_l_head : forall Θ P P0 P',
  Θ ⊢ₑ P ∼ P0 ⤳ P' -> guarded_pskl P -> pskl_guarded_head P'.
Proof.
  intros Θ P P0 P' H; induction H; intros Hg; simpl;
    try exact I; try (inversion Hg; fail).
  - (* hole_r : P'=P *) inversion Hg; subst; simpl; auto.
  - (* tophole_r_guarded *) apply IHa_solve_eq; assumption.
Qed.

(** A decoration of a guarded-headed skeleton has a GUARDED erasure —
    exactly the [SEq-UnivGhostR] premise, supplied when a solve step drops
    a ∀◇ onto a guarded remainder. *)
Lemma dec_ext_head_guarded_erase : forall P ψ Ψ,
  dec_ext P ψ Ψ -> pskl_guarded_head P -> guarded_pskl ⌊ ψ ⌋ˢ.
Proof.
  intros P ψ Ψ H Hh; inversion H; subst; simpl in Hh; try contradiction; simpl.
  - auto with frost.
  - auto with frost.
  - apply guarded_pskl__arrow;
      apply lc_uskl_to_pskl_local; apply is_tskl_lc;
      eapply dec_ext_is_tskl; eassumption.
  - auto with frost.
Qed.

(** COVERAGE (unconditional — the paper's provenance, with NO side condition
    on the target Q): matching ψ against the skeleton it extends collects a
    Ψi with ψ's full tags Ψtot ⊆ Ψ' ∪ Ψi.  A surviving ∀◇ is matched by a
    dotted ghost (SEq-UnivGhostG); a dropped ∀◇ sits over a GUARDED erasure
    (SEq-UnivGhostR); a ∀ created against a ∀◇ recurses through
    SEq-ForallSyn (whose un-collected ε is REMAINING in [absorb_all]). *)
Lemma dec_ext_cover_eq : forall P ψ Ψ' Ψtot,
  dec_ext P ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi, ψ ∼ᵗ P ⤳ Ψi /\ Ψtot [<=] Ψ' `union` Ψi.
Proof.
  intros P ψ Ψ' Ψtot H; revert Ψtot; induction H; intros Ψtot Hdt.
  - (* hole : SEq-Vacuous, Ψ' = d_tags ψ = Ψtot *)
    exists empty. split; [ apply a_solvetag_eq__vacuous; fsetdec | ].
    match goal with Hh : d_tags_skl ?β2 ψ |- Ψtot [<=] union ?β2 empty =>
      pose proof (d_tags_skl_det Hh Hdt) as Hd; clear - Hd; fsetdec end.
  - (* unit *) exists empty. split; [ apply a_solvetag_eq__unit; fsetdec | ].
    inversion Hdt; subst; fsetdec.
  - (* var *) exists empty. split; [ apply a_solvetag_eq__var; fsetdec | ].
    inversion Hdt; subst; fsetdec.
  - (* arrow *)
    inversion Hdt; subst.
    match goal with
    | Ha : d_tags_skl ?T1 ψ1, Hbb : d_tags_skl ?T2 ψ2, Heq : Ψtot [=] _ |- _ =>
        destruct (IHdec_ext1 T1 Ha) as [Ψi1 [Hs1 Hsub1]];
        destruct (IHdec_ext2 T2 Hbb) as [Ψi2 [Hs2 Hsub2]];
        exists (Ψi1 `union` Ψi2); split;
        [ eapply a_solvetag_eq__arrow; [ exact Hs1 | exact Hs2 | fsetdec ]
        | clear - H1 Heq Hsub1 Hsub2; fsetdec ]
    end.
  - (* all : P=∀P0, ψ=all_etag ε ψ0, Ψtot=add ε Ψt0 *)
    inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heq : Ψtot [=] add ?e ?Ψt0,
      IH : forall α, α `notin` ?Lh -> forall Ψ2, _ -> _ |- _ =>
        destruct (atom_fresh (L `union` L1 `union` ftvar_in_uskl ψ0
                    `union` ftvar_in_pskl P0)) as [α0 HX0];
        destruct (IH α0 ltac:(clear - HX0; fsetdec) Ψt0
                    (Hb α0 ltac:(clear - HX0; fsetdec)))
                  as [Ψi0 [Hs0 Hsub0]];
        exists (add ε Ψi0); split;
        [ eapply a_solvetag_eq__forall_inh with
            (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P0
                  `union` singleton α0) (Ψ0 := Ψi0); [ | reflexivity ];
          intros β Hβ;
          rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                     ltac:(clear - HX0; fsetdec));
          rewrite (subst_pskl_in_pskl_intro α0 P0 (pskl_var_f β)
                     ltac:(clear - HX0; fsetdec));
          exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β)
        | clear - Heq Hsub0; fsetdec ]
    end.
  - (* skip_tophole : P=∀◇P0, guarded ⌊ψ⌋ ; SEq-UnivGhostR *)
    destruct (IHdec_ext Ψtot Hdt) as [Ψi [Hs Hsub]].
    exists Ψi. split;
      [ apply a_solvetag_eq__univ_ghost_r; [ assumption | exact Hs ] | exact Hsub ].
  - (* topholeg : P=∀◇P0, ψ=∀◈ψ0 ; SEq-UnivGhostG *)
    inversion Hdt; subst.
    match goal with Hd0 : d_tags_skl Ψtot ?p0 |- _ =>
      destruct (IHdec_ext Ψtot Hd0) as [Ψi [Hs Hsub]] end.
    exists Ψi. split; [ apply a_solvetag_eq__univ_ghostg; exact Hs | exact Hsub ].
  - (* absorb_all : P=∀◇P0, ψ=all_etag ε ψ0 ; SEq-ForallSyn (ε stays remaining) *)
    inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heqt : Ψtot [=] add ?e ?Ψt0,
      IH : forall α, α `notin` ?Lh -> forall Ψ2, _ -> _ |- _ =>
        destruct (atom_fresh (L `union` L1 `union` ftvar_in_uskl ψ0
                    `union` ftvar_in_pskl P0)) as [α0 HX0];
        destruct (IH α0 ltac:(clear - HX0; fsetdec) Ψt0
                    (Hb α0 ltac:(clear - HX0; fsetdec)))
                  as [Ψi0 [Hs0 Hsub0]];
        exists Ψi0; split;
        [ apply a_solvetag_eq__forall_syn with
            (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P0
                  `union` singleton α0);
          intros β Hβ;
          rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                     ltac:(clear - HX0; fsetdec));
          rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole P0)
                       (pskl_var_f β) α0 ltac:(simpl; clear - HX0; fsetdec));
          exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β)
        | match goal with Heq0 : Ψ [=] add ε _ |- _ =>
            clear - Heqt Heq0 Hsub0; fsetdec end ]
    end.
  - (* flex_forget : ψ = var *) exists empty. split;
      [ apply a_solvetag_eq__var; fsetdec
      | inversion Hdt; subst; fsetdec ].
Qed.

(** FORWARD STEP (eq): one [eq Q] constraint, threaded through
    [solve_eq P ∼ Q ⤳ P'] — UNCONDITIONAL (no side condition on P or Q;
    the paper's lemma has none).  Produces the per-constraint solvetag
    [ψ ∼ᵗ Q ⤳ Ψi] and re-relates ψ to the pre-step P with COVERAGE
    [Ψp ⊆ Ψ' ∪ Ψi] (⊆, set membership).  ∀◇ solve steps decompose by the
    subject's relation to the output: dotted (topholeg ↦ SEq-UnivGhostG),
    guarded-skip (↦ SEq-UnivGhostR), absorbed-∀ (↦ SEq-ForallSyn), flex. *)
Lemma dec_ext_solve_eq_step : forall Θ P P3 P' ψ Ψ' Ψtot,
  Θ ⊢ₑ P ∼ P3 ⤳ P' ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, ψ ∼ᵗ P3 ⤳ Ψi /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  intros Θ P P3 P' ψ Ψ' Ψtot Hs; revert ψ Ψ' Ψtot;
    induction Hs; intros ψ Ψ' Ψtot Hdec Hdt.
  - (* unit *) inversion Hdec; subst.
    + exists empty, empty; split;
        [ apply a_solvetag_eq__unit; fsetdec
        | split; [ apply dec_ext__unit; fsetdec | fsetdec ] ].
    + exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* var : P=P'=var α, Q arbitrary *) inversion Hdec; subst.
    + exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__var; fsetdec | fsetdec ] ].
    + exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* flex_r : Q=var α, P'=var α *) inversion Hdec; subst;
      (exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ]).
  - (* hole_l : P=◇, P'=Q ; the coverage sub-lemma *)
    destruct (dec_ext_cover_eq Hdec Hdt) as [Ψi [Hsi Hsub]].
    exists Ψi, Ψtot; split; [ exact Hsi | split;
      [ apply dec_ext__hole; [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
      | exact Hsub ] ].
  - (* hole_r : Q=◇, P'=P ; SEq-Vacuous *)
    exists empty, Ψ'; split;
      [ apply a_solvetag_eq__vacuous; fsetdec
      | split; [ exact Hdec | fsetdec ] ].
  - (* arrow *)
    inversion Hdec; subst.
    + (* ψ = arrow ψ1 ψ2 *)
      inversion Hdt; subst.
      edestruct IHHs1 as [Ψi1 [Ψp1 [Hsa [Hd1 Hu1]]]];
        [ eassumption | eassumption | ].
      edestruct IHHs2 as [Ψi2 [Ψp2 [Hsb [Hd2 Hu2]]]];
        [ eassumption | eassumption | ].
      exists (Ψi1 `union` Ψi2), (Ψp1 `union` Ψp2); split;
        [ eapply a_solvetag_eq__arrow; [ exact Hsa | exact Hsb | fsetdec ]
        | split; [ eapply dec_ext__arrow; [ exact Hd1 | exact Hd2 | fsetdec ]
                 | match goal with Heq : Ψ' [=] _ `union` _ |- _ =>
                     clear - Heq Hu1 Hu2; fsetdec end ] ].
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* forall : P=∀P0, Q=∀Q0, P'=∀P0' *)
    inversion Hdec; subst.
    + (* ψ = all_etag ε ψ0 ; bodies P Q P', IH = H0, dec_ext cofin = H2,
         d_tags cofin = H4 (tag set Ψ0) *)
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` L1 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)) as [α0 HX0].
      destruct (H0 α0 ltac:(clear - HX0; fsetdec) _ _ _
                  (H2 α0 ltac:(clear - HX0; fsetdec))
                  (H4 α0 ltac:(clear - HX0; fsetdec)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists (add ε Ψi0), Ψp0; split.
      * (* solvetag : SEq-ForallInh, rename α0 ⤳ β *)
        eapply a_solvetag_eq__forall_inh with
          (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0) (Ψ0 := Ψi0); [ | reflexivity ].
        intros β Hβ.
        rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        rewrite (subst_pskl_in_pskl_intro α0 Q (pskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β).
      * split.
        -- (* dec_ext : dec_ext__all, rename α0 ⤳ α2 *)
           apply dec_ext__all with
             (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0).
           intros α2 Hα2.
           rewrite (subst_pskl_in_pskl_intro α0 P (pskl_var_f α2)
                      ltac:(clear - HX0; fsetdec)).
           rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; fsetdec)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* tophole_both : ∀◇P ∼ ∀◇Q ⤳ ∀◇P' ; inner induction on the ψ↔∀◇P'
       relation (the subject may keep absorbing ∀s against the ghost) *)
    remember (pskl_tophole P') as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    + (* skip_tophole : guarded erasure ; SEq-UnivGhostR *)
      injection HeqW as HeqP; subst P0.
      match goal with Hin : dec_ext P' _ _ |- _ =>
        destruct (IHHs _ _ _ Hin Hdt) as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ apply a_solvetag_eq__univ_ghost_r; [ assumption | exact Hsi ]
        | split; [ apply dec_ext__skip_tophole; [ assumption | exact Hdp ]
                 | exact Hsub ] ].
    + (* topholeg : SEq-UnivGhostG *)
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with
      | Hin : dec_ext P' ?p0 _, Hd0 : d_tags_skl _ ?p0 |- _ =>
        destruct (IHHs _ _ _ Hin Hd0) as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ apply a_solvetag_eq__univ_ghostg; exact Hsi
        | split; [ apply dec_ext__topholeg; exact Hdp | exact Hsub ] ].
    + (* absorb_all : SEq-ForallSyn (ε stays remaining on both sides) *)
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; fsetdec) Wt0
                      (Hb α0 ltac:(clear - HX0; fsetdec)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]]
      end.
      exists Ψi0, (add ε Ψp0); split.
      * apply a_solvetag_eq__forall_syn with
          (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0).
        intros β Hβ.
        rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q)
                     (pskl_var_f β) α0 ltac:(simpl; clear - HX0; fsetdec)).
        exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β).
      * split.
        -- eapply dec_ext__absorb_all with
             (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0) (Ψ0 := Ψp0); [ | reflexivity ].
           intros α2 Hα2.
           rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; fsetdec)).
           rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole P)
                        (pskl_var_f α2) α0 ltac:(simpl; clear - HX0; fsetdec)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - HeqAbs Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* tophole_l_all : ∀◇P ∼ ∀Q ⤳ ∀P' (SE-GhostForall) ; the subject's ∀ is
       CREATED against the ghost — absorb_all backward, SEq-ForallInh forward *)
    inversion Hdec; subst.
    + (* ψ = all_etag ε ψ0 *)
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` L1 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)) as [α0 HX0].
      destruct (H0 α0 ltac:(clear - HX0; fsetdec) _ _ _
                  (H2 α0 ltac:(clear - HX0; fsetdec))
                  (H4 α0 ltac:(clear - HX0; fsetdec)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists (add ε Ψi0), (add ε Ψp0); split.
      * eapply a_solvetag_eq__forall_inh with
          (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0) (Ψ0 := Ψi0); [ | reflexivity ].
        intros β Hβ.
        rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        rewrite (subst_pskl_in_pskl_intro α0 Q (pskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β).
      * split.
        -- eapply dec_ext__absorb_all with
             (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0) (Ψ0 := Ψp0); [ | reflexivity ].
           intros α2 Hα2.
           rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; fsetdec)).
           rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole P)
                        (pskl_var_f α2) α0 ltac:(simpl; clear - HX0; fsetdec)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* tophole_l_guarded : ∀◇P ∼ Q (guarded) ⤳ P' ; the ∀◇ is DROPPED onto a
       guarded output — guarded skip backward *)
    destruct (IHHs _ _ _ Hdec Hdt) as [Ψi [Ψp [Hsi [Hdp Hsub]]]].
    exists Ψi, Ψp; split;
      [ exact Hsi
      | split;
        [ apply dec_ext__skip_tophole;
            [ eapply dec_ext_head_guarded_erase;
                [ exact Hdec | eapply solve_eq_guarded_r_head; eassumption ]
            | exact Hdp ]
        | exact Hsub ] ].
  - (* all_l_tophole : ∀P ∼ ∀◇Q ⤳ ∀P' (SE-ForallGhost) ; SEq-ForallSyn keeps
       the ∀◇ target whole, the skeleton ∀ matches the subject ∀ *)
    inversion Hdec; subst.
    + (* ψ = all_etag ε ψ0 *)
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` L1 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)) as [α0 HX0].
      destruct (H0 α0 ltac:(clear - HX0; fsetdec) _ _ _
                  (H2 α0 ltac:(clear - HX0; fsetdec))
                  (H4 α0 ltac:(clear - HX0; fsetdec)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists Ψi0, Ψp0; split.
      * apply a_solvetag_eq__forall_syn with
          (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0).
        intros β Hβ.
        rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole Q)
                     (pskl_var_f β) α0 ltac:(simpl; clear - HX0; fsetdec)).
        exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ Hs0 α0 β).
      * split.
        -- apply dec_ext__all with
             (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0).
           intros α2 Hα2.
           rewrite (subst_pskl_in_pskl_intro α0 P (pskl_var_f α2)
                      ltac:(clear - HX0; fsetdec)).
           rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; fsetdec)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_eq__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* tophole_r_guarded : P (guarded) ∼ ∀◇Q ⤳ P' ; SEq-UnivGhostR *)
    destruct (IHHs _ _ _ Hdec Hdt) as [Ψi [Ψp [Hsi [Hdp Hsub]]]].
    exists Ψi, Ψp; split;
      [ apply a_solvetag_eq__univ_ghost_r;
          [ eapply dec_ext_head_guarded_erase;
              [ exact Hdec | eapply solve_eq_guarded_l_head; eassumption ]
          | exact Hsi ]
      | split; [ exact Hdp | exact Hsub ] ].
Qed.

(** At a ◇-hole, dec_ext's remaining tags are exactly all of ψ's tags. *)
Lemma dec_ext_hole_tags : forall ψ Ψp Ψtot,
  dec_ext pskl_hole ψ Ψp -> d_tags_skl Ψtot ψ -> Ψp [=] Ψtot.
Proof.
  intros ψ Ψp Ψtot H Hdt; inversion H; subst.
  - eapply d_tags_skl_det; eassumption.
  - inversion Hdt; subst; fsetdec.
Qed.

(** A decoration of a guarded skeleton is guarded (unit/var/arrow). *)
Lemma dec_ext_guarded_uskl : forall P ψ Ψ,
  dec_ext P ψ Ψ -> guarded_pskl P -> is_tskl ψ -> guarded_uskl ψ.
Proof.
  intros P ψ Ψ H Hg Hik; inversion H; subst; try (inversion Hg; fail).
  - auto with frost.
  - auto with frost.
  - apply is_tskl_lc in Hik; inversion Hik; subst; auto with frost.
  - auto with frost.
Qed.

(** FORWARD STEP (sub): the terminal [sub m Q] constraint — UNCONDITIONAL. *)
Lemma dec_ext_solve_sub_step : forall Θ m P P3 P' ψ Ψ' Ψtot,
  Θ ⊢ₛ P ≼[ m ] P3 ⤳ P' ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, ψ ≼ᵗ[ m ] P3 ⤳ Ψi /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  intros Θ m P P3 P' ψ Ψ' Ψtot Hs; revert ψ Ψ' Ψtot;
    induction Hs; intros ψ Ψ' Ψtot Hdec Hdt.
  - (* var : P=P'=var α *)
    inversion Hdec; subst;
      (exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ solve [ apply dec_ext__var; fsetdec
                         | apply dec_ext__flex_forget; fsetdec ] | fsetdec ] ]).
  - (* forall_l : subject ∀P, output ∀P' *)
    inversion Hdec; subst.
    + (* all_etag ε ψ0 *)
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` L1 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
                  `union` ftvar_in_pskl Q)) as [α0 HX0].
      destruct (H0 α0 ltac:(clear - HX0; fsetdec) _ _ _
                  (H2 α0 ltac:(clear - HX0; fsetdec))
                  (H4 α0 ltac:(clear - HX0; fsetdec)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists Ψi0, Ψp0; split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` singleton α0). intros β Hβ.
        rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq Q (pskl_var_f β) α0
                     ltac:(clear - HX0; fsetdec)).
        exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ Hs0 α0 β).
      * split.
        -- apply dec_ext__all with
             (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl P `union` singleton α0).
           intros α2 Hα2.
           rewrite (subst_pskl_in_pskl_intro α0 P (pskl_var_f α2)
                      ltac:(clear - HX0; fsetdec)).
           rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; fsetdec)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* univ_ghost_l : ∀◇P ≼[m] Q ⤳ ∀◇P' ; inner induction on the ψ↔∀◇P'
       relation — the target Q is untouched by the ghost *)
    remember (pskl_tophole P') as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    + (* skip_tophole *)
      injection HeqW as HeqP; subst P0.
      match goal with Hin : dec_ext P' _ _ |- _ =>
        destruct (IHHs _ _ _ Hin Hdt) as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ exact Hsi
        | split; [ apply dec_ext__skip_tophole; [ assumption | exact Hdp ]
                 | exact Hsub ] ].
    + (* topholeg : SSub-UnivGhostLG *)
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with
      | Hin : dec_ext P' ?p0 _, Hd0 : d_tags_skl _ ?p0 |- _ =>
        destruct (IHHs _ _ _ Hin Hd0) as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ apply a_solvetag_sub__univ_ghost_lg; exact Hsi
        | split; [ apply dec_ext__topholeg; exact Hdp | exact Hsub ] ].
    + (* absorb_all : SSub-ForallL *)
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; fsetdec) Wt0
                      (Hb α0 ltac:(clear - HX0; fsetdec)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]]
      end.
      exists Ψi0, (add ε Ψp0); split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q `union` singleton α0).
        intros β Hβ.
        rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq Q (pskl_var_f β) α0
                     ltac:(clear - HX0; fsetdec)).
        exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ Hs0 α0 β).
      * split.
        -- eapply dec_ext__absorb_all with
             (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0) (Ψ0 := Ψp0); [ | reflexivity ].
           intros α2 Hα2.
           rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f α2)
                      ltac:(clear - HX0; fsetdec)).
           rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_tophole P)
                        (pskl_var_f α2) α0 ltac:(simpl; clear - HX0; fsetdec)).
           exact (dec_ext_rename_var Hd0 α0 α2).
        -- clear - HeqAbs Hu0; fsetdec.
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* vacuous : Q=◇, P'=P ; SSub-Vacuous *)
    exists empty, Ψ'; split;
      [ apply a_solvetag_sub__vacuous; fsetdec
      | split; [ exact Hdec | fsetdec ] ].
  - (* check : guarded P (H), guarded Q (H0), solve_eq (H1) → eq_step + SSub-Check *)
    edestruct dec_ext_solve_eq_step as [Ψi [Ψp [Hste [Hdp Hup]]]];
      [ exact H1 | exact Hdec | exact Hdt | ].
    exists Ψi, Ψp; split;
      [ apply a_solvetag_sub__check;
          [ eapply dec_ext_guarded_uskl;
              [ exact Hdp | assumption | eapply d_tags_skl_is_tskl; exact Hdt ]
          | assumption
          | exact Hste ]
      | split; [ exact Hdp | exact Hup ] ].
  - (* forall_r : Q=∀B ; subject A fixed, rename target β0 ⤳ β *)
    destruct (atom_fresh (L `union` ftvar_in_pskl B `union` ftvar_in_uskl ψ))
      as [β0 Hβ0].
    destruct (H0 β0 ltac:(clear - Hβ0; fsetdec) _ _ _ Hdec Hdt)
              as [Ψi0 [Ψp0 [Hst0 [Hd0 Hu0]]]].
    exists Ψi0, Ψp0; split.
    + apply a_solvetag_sub__forall_r with
        (L := ftvar_in_pskl B `union` ftvar_in_uskl ψ `union` singleton β0).
      intros β Hβ.
      rewrite <- (subst_bskl_in_uskl_fresh_eq ψ (uskl_var_f β) β0
                   ltac:(clear - Hβ0; fsetdec)).
      rewrite (subst_pskl_in_pskl_intro β0 B (pskl_var_f β)
                 ltac:(clear - Hβ0; fsetdec)).
      exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ Hst0 β0 β).
    + split; [ exact Hd0 | exact Hu0 ].
  - (* arrow : domain via eq_step, codomain via sub IH *)
    inversion Hdec; subst.
    + (* arrow ψ1 ψ2 *)
      inversion Hdt; subst.
      edestruct dec_ext_solve_eq_step as [Ψi1 [Ψp1 [Hst1 [Hd1 Hu1]]]];
        [ exact H | eassumption | eassumption | ].
      edestruct IHHs as [Ψi2 [Ψp2 [Hst2 [Hd2 Hu2]]]];
        [ eassumption | eassumption | ].
      exists (Ψi1 `union` Ψi2), (Ψp1 `union` Ψp2); split;
        [ eapply a_solvetag_sub__arrow; [ exact Hst1 | exact Hst2 | reflexivity ]
        | split; [ eapply dec_ext__arrow; [ exact Hd1 | exact Hd2 | reflexivity ]
                 | match goal with Heq : Ψ' [=] _ `union` _ |- _ =>
                     clear - Heq Hu1 Hu2; fsetdec end ] ].
    + (* flex_forget *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ] ].
  - (* ghost_l_fn : ◇ ≼[fn m] (arrow Q1 Q2) ⤳ ∀◇(arrow P1' P2') ; the pre-step
       skeleton is ◇ (any subject) — inner induction on the ψ↔∀◇(arrow) relation
       for the solvetag, hole for the backward relation *)
    remember (pskl_tophole (pskl_arrow P1' P2')) as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    + (* skip_tophole : dec_ext (arrow P1' P2') ψ _ *)
      injection HeqW as HeqP; subst P0.
      match goal with Hde : dec_ext (pskl_arrow P1' P2') _ _ |- _ =>
        inversion Hde; subst end.
      * (* ψ = arrow ψ1 ψ2 *)
        inversion Hdt; subst.
        edestruct dec_ext_solve_eq_step as [Ψi1 [Ψp1 [Hst1 [Hd1 Hu1]]]];
          [ exact H | eassumption | eassumption | ].
        edestruct IHHs as [Ψi2 [Ψp2 [Hst2 [Hd2 Hu2]]]];
          [ eassumption | eassumption | ].
        match goal with Ha : d_tags_skl _ ψ1, Hb : d_tags_skl _ ψ2 |- _ =>
          pose proof (dec_ext_hole_tags Hd1 Ha) as He1;
          pose proof (dec_ext_hole_tags Hd2 Hb) as He2 end.
        exists (Ψi1 `union` Ψi2), Ψtot; split;
          [ eapply a_solvetag_sub__arrow; [ exact Hst1 | exact Hst2 | reflexivity ]
          | split;
            [ apply dec_ext__hole; [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
            | match goal with Heqt : Ψtot [=] _ |- Ψtot [<=] ?β2 `union` _ =>
                match goal with Heqp : β2 [=] _ |- _ =>
                  clear - Heqt Heqp He1 He2 Hu1 Hu2; fsetdec end end ] ].
      * (* ψ = var (flex_forget under skip) *)
        exists empty, empty; split;
          [ apply a_solvetag_sub__var; fsetdec
          | split; [ apply dec_ext__hole;
                       [ eapply d_tags_skl_is_tskl; exact Hdt
                       | inversion Hdt; subst; apply d_tags_skl__var; fsetdec ]
                   | inversion Hdt; subst; fsetdec ] ].
    + (* topholeg : ψ = ∀◈ψ0, dec_ext (arrow P1' P2') ψ0 *)
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with Hde : dec_ext (pskl_arrow P1' P2') ?p0 _,
                      Hd0t : d_tags_skl Ψtot ?p0 |- _ =>
        inversion Hde; subst end.
      * (* ψ0 = arrow ψ1 ψ2 *)
        match goal with Hd0t : d_tags_skl Ψtot (uskl_arrow _ _) |- _ =>
          inversion Hd0t; subst end.
        edestruct dec_ext_solve_eq_step as [Ψi1 [Ψp1 [Hst1 [Hd1 Hu1]]]];
          [ exact H | eassumption | eassumption | ].
        edestruct IHHs as [Ψi2 [Ψp2 [Hst2 [Hd2 Hu2]]]];
          [ eassumption | eassumption | ].
        match goal with Ha : d_tags_skl _ ψ1, Hb : d_tags_skl _ ψ2 |- _ =>
          pose proof (dec_ext_hole_tags Hd1 Ha) as He1;
          pose proof (dec_ext_hole_tags Hd2 Hb) as He2 end.
        exists (Ψi1 `union` Ψi2), Ψtot; split;
          [ apply a_solvetag_sub__univ_ghost_lg;
            eapply a_solvetag_sub__arrow; [ exact Hst1 | exact Hst2 | reflexivity ]
          | split;
            [ apply dec_ext__hole; [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
            | match goal with Heqt : Ψtot [=] _ |- Ψtot [<=] ?β2 `union` _ =>
                match goal with Heqp : β2 [=] _ |- _ =>
                  clear - Heqt Heqp He1 He2 Hu1 Hu2; fsetdec end end ] ].
      * (* ψ0 = var *)
        exists empty, empty; split;
          [ apply a_solvetag_sub__univ_ghost_lg; apply a_solvetag_sub__var; fsetdec
          | split; [ apply dec_ext__hole;
                       [ eapply d_tags_skl_is_tskl; exact Hdt
                       | apply d_tags_skl__topholeg; apply d_tags_skl__var; fsetdec ]
                   | fsetdec ] ].
    + (* absorb_all : SSub-ForallL down the created ∀-prefix *)
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl Q1 `union` ftvar_in_pskl Q2)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; fsetdec) Wt0
                      (Hb α0 ltac:(clear - HX0; fsetdec)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]];
          pose proof (dec_ext_hole_tags Hd0 (Hb α0 ltac:(clear - HX0; fsetdec)))
            as He0
      end.
      exists Ψi0, Ψtot; split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q1 `union` ftvar_in_pskl Q2
                `union` singleton α0).
        intros β Hβ.
        rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq (pskl_arrow Q1 Q2)
                     (pskl_var_f β) α0 ltac:(simpl; clear - HX0; fsetdec)).
        exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ Hs0 α0 β).
      * split;
          [ apply dec_ext__hole;
              [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
          | match goal with Heqt : Ψtot [=] add _ _ |- _ =>
              clear - Heqt HeqAbs He0 Hu0; fsetdec end ].
    + (* flex_forget : ψ = var *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__hole;
                     [ eapply d_tags_skl_is_tskl; exact Hdt
                     | inversion Hdt; subst; apply d_tags_skl__var; fsetdec ]
                 | inversion Hdt; subst; fsetdec ] ].
  - (* ghost_l : ◇ ≼[tc] B ⤳ ∀◇B, guarded B = H ; inner induction, the target
       B is matched by the coverage lemma (SSub-Check) *)
    remember (pskl_tophole B) as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    + (* skip_tophole : dec_ext B ψ _ *)
      injection HeqW as HeqP; subst P0.
      match goal with Hde : dec_ext B _ _ |- _ =>
        destruct (dec_ext_cover_eq Hde Hdt) as [Ψi [Hsi Hsub]];
        exists Ψi, Ψtot; split;
          [ apply a_solvetag_sub__check;
              [ eapply dec_ext_guarded_uskl;
                  [ exact Hde | exact H | eapply d_tags_skl_is_tskl; exact Hdt ]
              | exact H | exact Hsi ]
          | split; [ apply dec_ext__hole;
                       [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
                   | exact Hsub ] ]
      end.
    + (* topholeg : ψ = ∀◈ψ0, dec_ext B ψ0 _ *)
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with Hde : dec_ext B ?p0 _, Hd0 : d_tags_skl Ψtot ?p0 |- _ =>
        destruct (dec_ext_cover_eq Hde Hd0) as [Ψi [Hsi Hsub]];
        exists Ψi, Ψtot; split;
          [ apply a_solvetag_sub__univ_ghost_lg; apply a_solvetag_sub__check;
              [ eapply dec_ext_guarded_uskl;
                  [ exact Hde | exact H | eapply d_tags_skl_is_tskl; exact Hd0 ]
              | exact H | exact Hsi ]
          | split; [ apply dec_ext__hole;
                       [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
                   | exact Hsub ] ]
      end.
    + (* absorb_all : SSub-ForallL down the created ∀-prefix *)
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl B)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; fsetdec) Wt0
                      (Hb α0 ltac:(clear - HX0; fsetdec)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]];
          pose proof (dec_ext_hole_tags Hd0 (Hb α0 ltac:(clear - HX0; fsetdec)))
            as He0
      end.
      exists Ψi0, Ψtot; split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl B `union` singleton α0).
        intros β Hβ.
        rewrite (subst_bskl_in_uskl_intro α0 ψ0 (uskl_var_f β)
                   ltac:(clear - HX0; fsetdec)).
        rewrite <- (subst_pskl_in_pskl_fresh_eq B (pskl_var_f β) α0
                     ltac:(clear - HX0; fsetdec)).
        exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ Hs0 α0 β).
      * split;
          [ apply dec_ext__hole;
              [ eapply d_tags_skl_is_tskl; exact Hdt | exact Hdt ]
          | match goal with Heqt : Ψtot [=] add _ _ |- _ =>
              clear - Heqt HeqAbs He0 Hu0; fsetdec end ].
    + (* flex_forget : ψ = var *)
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__hole;
                     [ eapply d_tags_skl_is_tskl; exact Hdt
                     | inversion Hdt; subst; apply d_tags_skl__var; fsetdec ]
                 | inversion Hdt; subst; fsetdec ] ].
Qed.

(* --------------------------------------------------------------------- *)
(*  TY-mode prose-wf invariant (paper: in TY mode the against-side P0 is a
    TYPE, hence ghost-free — the mode discipline stated in prose; registry
    docs/WF-SIDE-CONDITIONS.md).  Consequence chain: the look targets are
    ∀◇-free ⟹ the eq-phase skeleton stays ∀◇-free ⟹ every ∀◇ of the final
    solve output was created by SS-GhostL / SS-GhostLF over a GUARDED body
    ⟹ [pskl_top_guarded], which feeds the TY guess-drop anchor.  SK mode
    needs NONE of this.                                                     *)
(* --------------------------------------------------------------------- *)

(** [pskl_no_top P]: no universal ghost ∀◇ anywhere (holes ◇ allowed). *)
Fixpoint pskl_no_top (P : pskl) : Prop :=
  match P with
  | pskl_tophole _ => False
  | pskl_arrow P1 P2 => pskl_no_top P1 /\ pskl_no_top P2
  | pskl_all_syn P0 => pskl_no_top P0
  | _ => True
  end.

Lemma pskl_ghost_free_no_top : forall P, pskl_ghost_free P -> pskl_no_top P.
Proof. induction P; simpl; intuition. Qed.

Lemma pskl_no_top_open_rec : forall P α' k,
  pskl_no_top P <-> pskl_no_top (open_pskl_wrt_pskl_rec k (pskl_var_f α') P).
Proof.
  induction P; intros α' k; simpl; try tauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; tauto.
  - rewrite (IHP1 α' k), (IHP2 α' k); tauto.
  - rewrite (IHP α' (S k)); tauto.
Qed.

Lemma pskl_no_top_top_guarded : forall P, pskl_no_top P -> pskl_top_guarded P.
Proof. induction P; simpl; intuition. Qed.

(** No ∀◇ is created solving (eq) against a ∀◇-free target. *)
Lemma solve_eq_no_top : forall Θ P P0 P',
  Θ ⊢ₑ P ∼ P0 ⤳ P' -> pskl_no_top P -> pskl_no_top P0 -> pskl_no_top P'.
Proof.
  intros Θ P P0 P' H; induction H; intros Hnt Hgf; simpl in Hnt, Hgf; simpl.
  - (* unit *) exact I.
  - (* var *) exact I.
  - (* flex_r *) exact I.
  - (* hole_l : P'=Q *) exact Hgf.
  - (* hole_r : Q=◇, P'=P *) exact Hnt.
  - (* arrow *) destruct Hnt as [Hnt1 Hnt2]; destruct Hgf as [Hgf1 Hgf2];
      split; [ apply IHa_solve_eq1 | apply IHa_solve_eq2 ]; assumption.
  - (* forall *)
    destruct (atom_fresh (L `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
                `union` ftvar_in_pskl Q)) as [β Hβ].
    apply (proj2 (pskl_no_top_open_rec P' β 0)).
    match goal with
    | IH : forall α, α `notin` L -> _ -> _ -> pskl_no_top _ |- _ =>
        apply (IH β ltac:(clear - Hβ; fsetdec));
        [ apply (proj1 (pskl_no_top_open_rec P β 0)); exact Hnt
        | apply (proj1 (pskl_no_top_open_rec Q β 0)); exact Hgf ]
    end.
  - (* tophole_both : P=∀◇ *) contradiction.
  - (* tophole_l_all : P=∀◇ *) contradiction.
  - (* tophole_l_guarded : P=∀◇ *) contradiction.
  - (* all_l_tophole : Q=∀◇ *) contradiction.
  - (* tophole_r_guarded : Q=∀◇ *) contradiction.
Qed.

(** Every ∀◇ a sub-solve creates over a ∀◇-free skeleton/target heads a
    GUARDED body (SS-GhostL: guarded premise; SS-GhostLF: an arrow). *)
Lemma solve_sub_top_guarded : forall Θ m P P0 P',
  Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' -> pskl_no_top P -> pskl_no_top P0 ->
  pskl_top_guarded P'.
Proof.
  intros Θ m P P0 P' Hs; induction Hs; intros Hnt Hgf; simpl in Hnt, Hgf; simpl.
  - (* var *) exact I.
  - (* forall_l : ∀P' *)
    destruct (atom_fresh (L `union` ftvar_in_pskl P')) as [β Hβ].
    apply (proj2 (pskl_top_guarded_open_rec P' β 0)).
    match goal with IH : forall α, α `notin` L -> _ |- _ =>
      apply (IH β ltac:(clear - Hβ; fsetdec));
        [ apply (proj1 (pskl_no_top_open_rec P β 0)); exact Hnt | exact Hgf ] end.
  - (* univ_ghost_l : P=∀◇ *) contradiction.
  - (* vacuous : P'=P *) apply pskl_no_top_top_guarded; exact Hnt.
  - (* check : eq preserves no_top *)
    apply pskl_no_top_top_guarded;
      eapply solve_eq_no_top; [ eassumption | exact Hnt | exact Hgf ].
  - (* forall_r *)
    destruct (atom_fresh (L `union` ftvar_in_pskl B)) as [β Hβ].
    match goal with IH : forall α, α `notin` L -> _ |- _ =>
      apply (IH β ltac:(clear - Hβ; fsetdec));
        [ exact Hnt | apply (proj1 (pskl_no_top_open_rec B β 0)); exact Hgf ] end.
  - (* arrow *)
    destruct Hnt as [Hnt1 Hnt2]; destruct Hgf as [Hgf1 Hgf2].
    split;
      [ apply pskl_no_top_top_guarded;
        eapply solve_eq_no_top; [ eassumption | exact Hnt1 | exact Hgf1 ]
      | apply IHHs; assumption ].
  - (* ghost_l_fn : ∀◇(arrow P1' P2') *)
    destruct Hgf as [Hgf1 Hgf2].
    split; [ exact I | split;
      [ apply pskl_no_top_top_guarded;
        eapply solve_eq_no_top; [ eassumption | exact I | exact Hgf1 ]
      | apply IHHs; [ exact I | exact Hgf2 ] ] ].
  - (* ghost_l : ∀◇B, B guarded *)
    split; [ apply guarded_pskl_head; assumption
           | apply pskl_no_top_top_guarded; exact Hgf ].
Qed.

(** Every constraint target is ∀◇-free. *)
Definition a_cstr_no_top (c : a_cstr) : Prop :=
  match c with
  | a_cstr_sub _ Q => pskl_no_top Q
  | a_cstr_eq Q => pskl_no_top Q
  end.

(** The look's targets are sub-skeletons of P0 (or fresh flex vars) — all
    ∀◇-free when P0 is. *)
Lemma a_look_no_top :
  (forall α m P P0 Ξ 𝒞, P ≼[ α , m ] P0 ⤳ Ξ ⨾ 𝒞 ->
     pskl_no_top P0 -> List.Forall a_cstr_no_top 𝒞) /\
  (forall α P P0 Ξ 𝒞, P ∼[ α ] P0 ⤳ Ξ ⨾ 𝒞 ->
     pskl_no_top P0 -> List.Forall a_cstr_no_top 𝒞).
Proof.
  apply a_looksub_lookeq_mutind; intros; simpl in *;
    try contradiction;                                       (* ∀◇-target *)
    try (apply List.Forall_nil; fail);                       (* nil constraints *)
    try (apply List.Forall_app; split; [ apply H | apply H0 ]; tauto);  (* arrow *)
    try (repeat apply List.Forall_cons;
         solve [ assumption | exact I | apply List.Forall_nil ]);  (* [sub/eq _] *)
    try (apply H; assumption);                               (* same-target recursion *)
    try (match goal with IH : forall β, β `notin` ?LL -> _ |- _ =>  (* cofinite *)
           destruct (atom_fresh LL) as [β Hβ];
           apply (IH β Hβ);
           solve [ assumption | apply (proj1 (pskl_no_top_open_rec _ _ _)); assumption ]
         end).
Qed.

(** The TY solve output is top-guarded (walk the constraint list). *)
Lemma solve_cstr_top_guarded : forall Θ 𝒞 P P',
  Θ ⊩ 𝒞 ⨾ P ⤳ P' -> pskl_no_top P -> List.Forall a_cstr_no_top 𝒞 ->
  pskl_top_guarded P'.
Proof.
  intros Θ 𝒞 P P' Hs; induction Hs; intros Hnt Hntc.
  - apply pskl_no_top_top_guarded; exact Hnt.
  - inversion Hntc as [ | ? ? Hnt0 ]; subst; simpl in Hnt0.
    eapply solve_sub_top_guarded; [ exact H | exact Hnt | exact Hnt0 ].
  - inversion Hntc as [ | ? ? Hnt0 HntC ]; subst; simpl in Hnt0.
    apply IHHs;
      [ eapply solve_eq_no_top; [ exact H | exact Hnt | exact Hnt0 ] | exact HntC ].
Qed.

(* ===================================================================== *)
(*  [top_guarded]-INPUT propagation chain (replaces the [no_top] chain):   *)
(*  a wf [P0] may carry ∀◇ (over GUARDED bodies, a_wf_pskl__tophole), so   *)
(*  the coverage anchor's [pskl_top_guarded Q] must flow from              *)
(*  [pskl_top_guarded P0] (⟸ wf), NOT from [ghost_free]/[no_top].          *)
(* ===================================================================== *)

(** A guarded-headed subject stays guarded-headed through eq-solving. *)
Lemma solve_eq_guarded_head_l : forall Θ P P0 P',
  Θ ⊢ₑ P ∼ P0 ⤳ P' -> pskl_guarded_head P -> pskl_guarded_head P'.
Proof.
  intros Θ P P0 P' H; induction H; intros Hg; simpl in Hg;
    try contradiction; simpl; try exact I.
  - (* hole_r : P'=P *) exact Hg.
  - (* tophole_r_guarded : P guarded, P∼P0⤳P' *) apply IHa_solve_eq; exact Hg.
Qed.

(** A guarded-headed subject stays guarded-headed through sub-solving. *)
Lemma solve_sub_guarded_head_l : forall Θ m P P0 P',
  Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' -> pskl_guarded_head P -> pskl_guarded_head P'.
Proof.
  intros Θ m P P0 P' Hs; induction Hs; intros Hg; simpl in Hg;
    try contradiction; simpl; try exact I.
  - (* vacuous : P'=P *) exact Hg.
  - (* check : eq preserves *) eapply solve_eq_guarded_head_l; eassumption.
  - (* forall_r : same subject/result, recurse *)
    destruct (atom_fresh L) as [β Hβ].
    match goal with IH : forall α, α `notin` L -> _ |- _ => apply (IH β Hβ); exact Hg end.
Qed.

(** [top_guarded] is preserved by eq-solving (∀◇ over guarded stays so). *)
Lemma solve_eq_top_guarded : forall Θ P P0 P',
  Θ ⊢ₑ P ∼ P0 ⤳ P' ->
  pskl_top_guarded P -> pskl_top_guarded P0 -> pskl_top_guarded P'.
Proof.
  intros Θ P P0 P' H; induction H; intros Hnt Hgf; simpl in Hnt, Hgf; simpl.
  - (* unit *) exact I.
  - (* var *) exact I.
  - (* flex_r *) exact I.
  - (* hole_l : P'=Q *) exact Hgf.
  - (* hole_r : P'=P *) exact Hnt.
  - (* arrow *) destruct Hnt as [Hnt1 Hnt2]; destruct Hgf as [Hgf1 Hgf2];
      split; [ apply IHa_solve_eq1 | apply IHa_solve_eq2 ]; assumption.
  - (* forall *)
    destruct (atom_fresh (L `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
                `union` ftvar_in_pskl Q)) as [β Hβ].
    apply (proj2 (pskl_top_guarded_open_rec P' β 0)).
    match goal with IH : forall α, α `notin` L -> _ -> _ -> pskl_top_guarded _ |- _ =>
      apply (IH β ltac:(clear - Hβ; fsetdec));
      [ apply (proj1 (pskl_top_guarded_open_rec P β 0)); exact Hnt
      | apply (proj1 (pskl_top_guarded_open_rec Q β 0)); exact Hgf ] end.
  - (* tophole_both : ∀◇P∼∀◇Q⤳∀◇P' *)
    destruct Hnt as [HgP HtP]; destruct Hgf as [HgQ HtQ].
    split; [ eapply solve_eq_guarded_head_l; [ eassumption | exact HgP ]
           | apply IHa_solve_eq; assumption ].
  - (* tophole_l_all : ∀◇P∼∀Q⤳∀P' *)
    destruct Hnt as [HgP HtP].
    destruct (atom_fresh (L `union` ftvar_in_pskl P' `union` ftvar_in_pskl Q)) as [β Hβ].
    apply (proj2 (pskl_top_guarded_open_rec P' β 0)).
    match goal with IH : forall α, α `notin` L -> _ -> _ -> pskl_top_guarded _ |- _ =>
      apply (IH β ltac:(clear - Hβ; fsetdec));
      [ simpl; split; assumption
      | apply (proj1 (pskl_top_guarded_open_rec Q β 0)); exact Hgf ] end.
  - (* tophole_l_guarded : ∀◇P∼(guarded Q)⤳P' *)
    destruct Hnt as [HgP HtP]; apply IHa_solve_eq; assumption.
  - (* all_l_tophole : ∀P∼∀◇Q⤳∀P' *)
    destruct Hgf as [HgQ HtQ].
    destruct (atom_fresh (L `union` ftvar_in_pskl P' `union` ftvar_in_pskl P)) as [β Hβ].
    apply (proj2 (pskl_top_guarded_open_rec P' β 0)).
    match goal with IH : forall α, α `notin` L -> _ -> _ -> pskl_top_guarded _ |- _ =>
      apply (IH β ltac:(clear - Hβ; fsetdec));
      [ apply (proj1 (pskl_top_guarded_open_rec P β 0)); exact Hnt
      | simpl; split; assumption ] end.
  - (* tophole_r_guarded : (guarded P)∼∀◇Q⤳P' *)
    destruct Hgf as [HgQ HtQ]; apply IHa_solve_eq; assumption.
Qed.

(** [top_guarded] is preserved by sub-solving. *)
Lemma solve_sub_top_guarded_tg : forall Θ m P P0 P',
  Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' ->
  pskl_top_guarded P -> pskl_top_guarded P0 -> pskl_top_guarded P'.
Proof.
  intros Θ m P P0 P' Hs; induction Hs; intros Hnt Hgf; simpl in Hnt, Hgf; simpl.
  - (* var *) exact I.
  - (* forall_l *)
    destruct (atom_fresh (L `union` ftvar_in_pskl P')) as [β Hβ].
    apply (proj2 (pskl_top_guarded_open_rec P' β 0)).
    match goal with IH : forall α, α `notin` L -> _ |- _ =>
      apply (IH β ltac:(clear - Hβ; fsetdec));
        [ apply (proj1 (pskl_top_guarded_open_rec P β 0)); exact Hnt | exact Hgf ] end.
  - (* univ_ghost_l : ∀◇P ≼ P0 ⤳ ∀◇P' *)
    destruct Hnt as [HgP HtP].
    split; [ eapply solve_sub_guarded_head_l; [ eassumption | exact HgP ]
           | apply IHHs; assumption ].
  - (* vacuous : P'=P *) exact Hnt.
  - (* check : eq preserves top_guarded *)
    eapply solve_eq_top_guarded; [ eassumption | exact Hnt | exact Hgf ].
  - (* forall_r *)
    destruct (atom_fresh (L `union` ftvar_in_pskl B)) as [β Hβ].
    match goal with IH : forall α, α `notin` L -> _ |- _ =>
      apply (IH β ltac:(clear - Hβ; fsetdec));
        [ exact Hnt | apply (proj1 (pskl_top_guarded_open_rec B β 0)); exact Hgf ] end.
  - (* arrow *)
    destruct Hnt as [Hnt1 Hnt2]; destruct Hgf as [Hgf1 Hgf2].
    split;
      [ eapply solve_eq_top_guarded; [ eassumption | exact Hnt1 | exact Hgf1 ]
      | apply IHHs; assumption ].
  - (* ghost_l_fn : ∀◇(arrow P1' P2') *)
    destruct Hgf as [Hgf1 Hgf2].
    split; [ exact I | split;
      [ eapply solve_eq_top_guarded; [ eassumption | exact I | exact Hgf1 ]
      | apply IHHs; [ exact I | exact Hgf2 ] ] ].
  - (* ghost_l : ∀◇B, B guarded *)
    split; [ apply guarded_pskl_head; assumption | exact Hgf ].
Qed.

(** Every constraint target is [top_guarded]. *)
Definition a_cstr_tg (c : a_cstr) : Prop :=
  match c with
  | a_cstr_sub _ Q => pskl_top_guarded Q
  | a_cstr_eq Q => pskl_top_guarded Q
  end.

(** The look's targets are sub-skeletons of P0 — all [top_guarded] when P0 is. *)
Lemma a_look_top_guarded :
  (forall α m P P0 Ξ 𝒞, P ≼[ α , m ] P0 ⤳ Ξ ⨾ 𝒞 ->
     pskl_top_guarded P0 -> List.Forall a_cstr_tg 𝒞) /\
  (forall α P P0 Ξ 𝒞, P ∼[ α ] P0 ⤳ Ξ ⨾ 𝒞 ->
     pskl_top_guarded P0 -> List.Forall a_cstr_tg 𝒞).
Proof.
  apply a_looksub_lookeq_mutind; intros; simpl in *;
    (* [simpl] already unfolded top_guarded of ∀◇/arrow into conjunctions;
       split them (fresh names, don't clobber IHs) *)
    repeat match goal with
           | H : _ /\ _ |- _ =>
               let Hg := fresh "Hg" in let Ht := fresh "Ht" in destruct H as [Hg Ht]
           end;
    try (apply List.Forall_nil; fail);                        (* nil constraints *)
    try (apply List.Forall_app; split; [ apply H | apply H0 ]; tauto);  (* arrow *)
    try (repeat apply List.Forall_cons;
         solve [ assumption | exact I | apply List.Forall_nil ]);  (* [sub/eq _] *)
    try (apply H; assumption);                                (* same/∀◇-strip recursion *)
    try (match goal with IH : forall β, β `notin` ?LL -> _ |- _ =>  (* cofinite *)
           destruct (atom_fresh LL) as [β Hβ];
           apply (IH β Hβ);
           solve [ assumption
                 | apply (proj1 (pskl_top_guarded_open_rec _ _ _)); assumption
                 | simpl; split; assumption ]  (* forall_syn: reconstruct ∀◇ target *)
         end).
Qed.

(** The TY solve output is top-guarded (walk the constraints; ∀◇ targets OK). *)
Lemma solve_cstr_top_guarded_tg : forall Θ 𝒞 P P',
  Θ ⊩ 𝒞 ⨾ P ⤳ P' -> pskl_top_guarded P -> List.Forall a_cstr_tg 𝒞 ->
  pskl_top_guarded P'.
Proof.
  intros Θ 𝒞 P P' Hs; induction Hs; intros Hnt Hntc.
  - exact Hnt.
  - inversion Hntc as [ | ? ? Hnt0 ]; subst; simpl in Hnt0.
    eapply solve_sub_top_guarded_tg; [ exact H | exact Hnt | exact Hnt0 ].
  - inversion Hntc as [ | ? ? Hnt0 HntC ]; subst; simpl in Hnt0.
    apply IHHs;
      [ eapply solve_eq_top_guarded; [ exact H | exact Hnt | exact Hnt0 ] | exact HntC ].
Qed.

(** ASSEMBLY: walk the constraint list — UNCONDITIONAL; [dec_ext] re-grows
    toward P with COVERAGE Ψp ⊆ Ψpost ∪ Ψc. *)
Lemma solve_cstr_decorate : forall Θ 𝒞 P P' ψ Ψpost Ψtot,
  Θ ⊩ 𝒞 ⨾ P ⤳ P' ->
  dec_ext P' ψ Ψpost -> d_tags_skl Ψtot ψ ->
  exists Ψc Ψp, 𝒞 ⊩ᵗ ψ ⤳ Ψc /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψpost `union` Ψc.
Proof.
  intros Θ 𝒞 P P' ψ Ψpost Ψtot Hsolve Hdec Hdt; revert Ψpost Hdec;
    induction Hsolve; intros Ψpost Hdec.
  - (* empty *) exists empty, Ψpost; split;
      [ apply a_solvetag__empty; fsetdec | split; [ exact Hdec | fsetdec ] ].
  - (* sub *)
    destruct (dec_ext_solve_sub_step H Hdec Hdt)
      as [Ψi [Ψp [Hs [Hd Hu]]]].
    exists Ψi, Ψp; split;
      [ apply a_solvetag__sub; exact Hs | split; [ exact Hd | exact Hu ] ].
  - (* eq *)
    destruct (IHHsolve Ψpost Hdec) as [Ψc' [Ψp'' [Hstc [Hd'' Hu'']]]].
    destruct (dec_ext_solve_eq_step H Hd'' Hdt)
      as [Ψi [Ψp [Hste [Hd Hu]]]].
    exists (Ψi `union` Ψc'), Ψp; split;
      [ eapply a_solvetag__eq; [ exact Hste | exact Hstc | reflexivity ]
      | split; [ exact Hd | clear - Hu Hu''; fsetdec ] ].
Qed.

(** DECORATING CONSTRAINT SOLVING (lemma:decorate-constraint-solving,
    subtyping-proofs.tex:95-127) — the paper's statement, proved via the ⊆
    set-membership coverage machinery and squeezed against solvetag
    soundness.  Sole hypothesis beyond the paper's: the TY mode discipline
    "the against-side is a TYPE (ghost-free)" — prose-level wf in the paper
    (docs/WF-SIDE-CONDITIONS.md); it is vacuous in SK mode. *)
Lemma a_extract_decorate : forall Θ0 NM αv M P P0 Ξ P1,
  Θ0 ⊢ P ⊳[ NM , αv , M ] P0 ⤳ Ξ ↪ P1 ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P0) ->
  forall Ψa ψa,
    a_tags_sort NM Ψa ψa ->
    ⌊ ψa ⌋ˢ = P1 ->
    exists Ξc 𝒞,
      P ≼[ αv , M ] P0 ⤳ Ξc ⨾ 𝒞 /\
      𝒞 ⊩ᵗ ψa ⤳ Ψa.
Proof.
  intros Θ0 NM αv M P P0 Ξ P1 Hext Htg0 Ψa ψa Htags Hera.
  inversion Hext; subst.
  (* H : look ;  H0 : solve 𝒞 □ Q ;  H1 : guess (output ⌊ψa⌋ˢ) *)
  eexists; eexists; split; [ exact H | ].
  assert (Hda : d_tags_skl Ψa ψa) by (inversion Htags; assumption).
  assert (Htg : NM = a_sub_mode_ty -> pskl_top_guarded Q).
  { intros Hty. specialize (Htg0 Hty).
    eapply solve_cstr_top_guarded_tg;
      [ exact H0 | exact I
      | eapply (proj1 a_look_top_guarded);
          [ exact H | exact Htg0 ] ]. }
  assert (Hanchor : dec_ext Q ψa empty)
    by (eapply dec_ext_guess_anchor;
        [ exact H1 | exact Htg | exact Htags | reflexivity ]).
  destruct (solve_cstr_decorate H0 Hanchor Hda)
    as [Ψc [Ψp [Hstag [Hhole Hsub]]]].
  (* dec_ext □ ψa Ψp pins Ψp = d_tags = Ψa; soundness gives Ψc ⊆ Ψa; squeeze *)
  assert (Hsnd : Ψc [<=] Ψa) by (eapply a_solvetag_sound; [ exact Hstag | exact Hda ]).
  inversion Hhole; subst.
  - (* dec_ext__hole : Ψp = d_tags ψa = Ψa *)
    match goal with Hdtag : d_tags_skl _ ψa |- _ =>
      pose proof (d_tags_skl_det Hda Hdtag) as Hdet end.
    eapply a_solvetag_psi_cong; [ exact Hstag | clear - Hsub Hsnd Hdet; fsetdec ].
  - (* dec_ext__flex_forget : ψa a bare var ⇒ Ψa = ∅ *)
    eapply a_solvetag_psi_cong; [ exact Hstag | ].
    inversion Hda; subst;
      match goal with He : Ψa [=] empty |- _ => clear - Hsnd He; fsetdec end.
Qed.

(* ===================================================================== *)
(*  §16  MAIN: decorating algorithmic subtyping                           *)
(*  (lemma:decorating-algorithmic-subtyping, subtyping-proofs.tex:1019)   *)
(* ===================================================================== *)

Scheme a_sub_mut := Induction for a_sub Sort Prop
  with a_sub_flex_mut := Induction for a_sub_flex Sort Prop.
Combined Scheme a_sub_sub_flex_mutind from a_sub_mut, a_sub_flex_mut.

Definition sub_decorate_concl NM M P0 Θ0 P Q Θ1 : Prop :=
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P0) ->
  Θ0 ⊢ᵗ[ NM | M | P0 | empty ] (pskl_to_uskl P) ⩽˙ Q ⊣ Θ1.

Definition sub_flex_decorate_concl NM M P0 Θ0 Ξw αf Q Θ1 : Prop :=
  a_decls Ξw ->
  a_wf_aenv (Ξw ++ Θ0) ->
  (Ξw ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  a_binds_tvar αf (Ξw ++ Θ0) ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) (mode_fn M)) ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P0) ->
  a_subtag_flex NM M P0 Θ0 Ξw αf Q Θ1.

(** MAIN (lemma:decorating-algorithmic-subtyping) — fully Qed.  The side
    conditions are exactly the sound-bundle's (P3): wf, the SK mode
    compatibility, and the TY "against a TYPE" ghost-freeness — the two
    mode disciplines the paper states in prose (docs/WF-SIDE-CONDITIONS.md).
    The ForallL case consumes [a_extract_decorate] (§15, Qed). *)
Theorem a_sub_decorate_bundle :
  (forall NM M P0 Θ0 P P' Θ1,
     a_sub NM M P0 Θ0 P P' Θ1 ->
     sub_decorate_concl NM M P0 Θ0 P P' Θ1) /\
  (forall NM M P0 Θ0 Ξw αf P' Θ1,
     a_sub_flex NM M P0 Θ0 Ξw αf P' Θ1 ->
     sub_flex_decorate_concl NM M P0 Θ0 Ξw αf P' Θ1).
Proof.
  apply (a_sub_sub_flex_mutind
           (fun NM M P0 Θ0 P P' Θ1 _ =>
              sub_decorate_concl NM M P0 Θ0 P P' Θ1)
           (fun NM M P0 Θ0 Ξw αf P' Θ1 _ =>
              sub_flex_decorate_concl NM M P0 Θ0 Ξw αf P' Θ1));
    unfold sub_decorate_concl, sub_flex_decorate_concl.
  - (* Infer *)
    intros NM P Θ0 Hwf HwfP0 HwfP Hmod Hgf0.
    replace P with (⌊ pskl_to_uskl P ⌋ˢ) at 2
      by apply uskl_to_pskl_pskl_to_uskl.
    apply a_subtag__infer. fsetdec.
  - (* Check : audit-F2 CLOSED — the decorated [a_subtag__check] no longer
       pins the consistency output to [B] (it existentialises it, matching the
       plain [a_consis_chk] and the paper's "output not used / ≡ B"
       convention), so we simply decorate the plain consistency premise. *)
    intros Θ0 Θ1 A B HgA HgB Hchk Hwf HwfP0 HwfP Hmod Hgf0.
    destruct Hchk as [P' Hcns].
    eapply a_subtag__check;
      [ apply pskl_to_uskl_guarded; exact HgA
      | exact HgB
      | exact (a_consis_decorate Hcns) ].
  - (* ForallR (exists-fresh 2026-07-31: the rule's own binder serves) *)
    intros α Θ0 Θ1 Ξ A B Hsuf Huq Hfr Hprem IHprem Hwf HwfP0 HwfP Hmod Hgf0.
    rewrite dom_app in Hfr.
    eapply a_subtag__forall_r with (α := α) (Ξ := Ξ);
      [ exact Hsuf | exact Huq
      | rewrite dom_app;
        pose proof (ftvar_in_uskl_pskl A) as Hfa;
        clear - Hfr Hfa; fsetdec
      | ].
    eapply IHprem.
    { apply a_wf_aenv__tvar; [ clear - Hfr; fsetdec | exact Hwf ]. }
    { eapply a_wf_pskl_all_syn_open_tvar;
        [ exact HwfP0 | clear - Hfr; fsetdec ]. }
    { eapply a_wf_pskl_weaken;
        [ intros x b Hb; unfold binds; simpl; right; exact Hb
        | exact HwfP ]. }
    { intros Hsk; discriminate Hsk. }
    { intros Hty; specialize (Hgf0 Hty); simpl in Hgf0.
      unfold open_pskl_wrt_pskl; apply (proj1 (pskl_top_guarded_open_rec _ _ _)); exact Hgf0. }
  - (* UnivGhostR *)
    intros Θ0 P Hg Hwf HwfP0 HwfP Hmod Hgf0.
    replace (pskl_tophole P)
      with (pskl_tophole ⌊ pskl_to_uskl P ⌋ˢ)
      by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
    apply a_subtag__univ_ghost_r;
      [ apply pskl_to_uskl_guarded; exact Hg | fsetdec ].
  - (* FlexMono *)
    intros NM M P0 Θ0 Θ1 α A Hflex IHflex Hwf HwfP0 HwfP Hmod Hgf0.
    simpl.
    apply a_subtag__flex_mono; [ | fsetdec ].
    apply IHflex.
    { constructor. }
    { simpl. exact Hwf. }
    { simpl. exact HwfP0. }
    { simpl.
      destruct (a_wf_pskl_ftv_tvarish HwfP (α := α)
                  ltac:(simpl; clear; fsetdec))
        as [HΔx | Htx];
        [ exfalso; clear - HΔx; fsetdec | exact Htx ]. }
    { exact Hmod. }
    { simpl. exact Hgf0. }
  - (* Arrow *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs2 IH2 Hwf HwfP0 HwfP Hmod Hgf0.
    apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP0a HwfP0b].
    apply a_wf_pskl_arrow_inv in HwfP as [HwfP1 HwfP2].
    pose proof (a_consis_decorate Hc) as Hct.
    destruct (a_consistag_sound_aux Hct Hwf
                ltac:(apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; eauto)
                HwfP0a
                ltac:(rewrite uskl_to_pskl_pskl_to_uskl; exact HwfP1)
                (@rig_empty _) (@no_flex_dep_empty _) (@faf_empty _))
      as [Hle [HwfΘm _]].
    simpl.
    eapply a_subtag__arrow with (Ψ1 := empty) (Ψ2 := empty) (Θ1 := Θ1);
      [ exact Hct
      | apply IH2;
        [ exact HwfΘm
        | eapply a_wf_pskl_isub; [ exact HwfP0b | exact Hle ]
        | eapply a_wf_pskl_isub; [ exact HwfP2 | exact Hle ]
        | intros Hsk; specialize (Hmod Hsk); simpl in Hmod;
          inversion Hmod; subst; assumption
        | intros Hty; specialize (Hgf0 Hty); simpl in Hgf0; tauto ]
      | fsetdec ].
  - (* ForallL : look-decoration + decorate-constraint-solving + KEY *)
    intros L NM M P0 Θ0 Θ1 P P' Ξ P1 Hne Hgor Hex Huq HwfP1 Hsub IHsub
      Hwf HwfP0 HwfP Hmod Hgf0.
    assert (Hdecls : a_decls Ξ)
      by (destruct (atom_fresh L) as [α0 Hα0];
          eapply a_extract_decls; eauto).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0)).
    { apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros α1 Hα1. clear - Huq Hα1. destruct_uniq.
        unfold disjoint in *. fsetdec. }
    assert (Hmono : forall x (b : abind),
               binds x b Θ0 -> binds x b (Ξ ++ Θ0))
      by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
    assert (HwfP0' : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
    assert (HlcP1 : lc_pskl P1) by (eapply a_wf_pskl_lc; eauto).
    simpl.
    eapply a_subtag__forall_l_untagged
      with (L := L `union` dom Ξ `union` dom Θ0
                 `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
                 `union` ftvar_in_pskl P1)
           (Ξ := Ξ) (P1 := P1);
      [ exact Hne | exact Hgor | | exact Huq | exact HwfP1 | ].
    { intros α Hα.
      replace (⌊ open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α) ⌋ˢ)
        with (open_pskl_wrt_pskl P (pskl_var_f α))
        by (rewrite uskl_to_pskl_open;
            rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      apply Hex. clear - Hα. fsetdec. }
    intros Ψg ψg Hfr Hsort Hera.
    assert (Hlcg : lc_uskl ψg)
      by (apply is_tskl_lc; inversion Hsort; assumption).
    destruct (atom_fresh
                (L `union` dom Ξ `union` dom Θ0
                 `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
                 `union` ftvar_in_pskl P1)) as [α Hα].
    destruct (a_extract_decorate (Hex α ltac:(clear - Hα; fsetdec))
                Hgf0 Hsort Hera) as [Ξc [C [HDlk Hst]]].
    assert (Hαg : α `notin` ftvar_in_uskl ψg).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl ψg). rewrite Hera.
      clear - Hα. fsetdec. }
    assert (HeqSubj :
        pskl_to_uskl (open_pskl_wrt_pskl P P1)
        = subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψg)) α
            (open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α))).
    { rewrite pskl_to_uskl_open.
      rewrite (subst_bskl_in_uskl_intro α);
        [ | rewrite <- (ftvar_in_pskl_uskl_to_pskl (pskl_to_uskl P));
            rewrite uskl_to_pskl_pskl_to_uskl; clear - Hα; fsetdec ].
      rewrite Hera. reflexivity. }
    assert (HDsrc :
        ⌊ open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α) ⌋ˢ
        ≼[ α , M ] P0 ⤳ Ξc ⨾ C).
    { replace (⌊ open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α) ⌋ˢ)
        with (open_pskl_wrt_pskl P (pskl_var_f α))
        by (rewrite uskl_to_pskl_open;
            rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      exact HDlk. }
    assert (Hresult :
        subst_bskl_in_uskl ψg α
          (open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α))
        = open_uskl_wrt_uskl (pskl_to_uskl P) ψg).
    { symmetry. apply subst_bskl_in_uskl_intro.
      rewrite <- (ftvar_in_pskl_uskl_to_pskl (pskl_to_uskl P)).
      rewrite uskl_to_pskl_pskl_to_uskl. clear - Hα. fsetdec. }
    assert (HwfOpen : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ open_pskl_wrt_pskl P P1).
    { inversion HwfP as [ | | | LP ΘP ΔP PP HbodyP HeqP | | ]; subst.
      eapply a_wf_pskl_open with (L := LP);
        [ intros α0 Hα0; eapply a_wf_pskl_weaken;
          [ exact Hmono | apply HbodyP; auto ]
        | exact HwfP1 ]. }
    rewrite <- Hresult.
    eapply a_subtag_psi_cong;
      [ eapply a_subtag_decoration;
        [ apply IHsub;
          [ exact HwfΞΘ
          | exact HwfP0'
          | exact HwfOpen
          | exact Hmod
          | exact Hgf0 ]
        | exact HeqSubj
        | exact HDsrc
        | exact Hst
        | exact Hαg
        | clear - Hα; fsetdec
        | exact Hlcg
        | apply lc_body_uskl_wrt_uskl;
          [ eapply lc_body_uskl_all_syn_1;
            change (uskl_all_syn (pskl_to_uskl P))
              with (pskl_to_uskl (pskl_all_syn P));
            apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; exact HwfP
          | constructor ]
        | exact HwfΞΘ
        | exact HwfP0'
        | rewrite uskl_to_pskl_pskl_to_uskl; exact HwfOpen
        | exact Hmod ]
      | clear; fsetdec ].
  - (* Ghost *)
    intros M Θ0 P0 Hwf HwfP0 HwfP Hmod Hgf0.
    simpl. apply a_subtag__ghost. fsetdec.
  - (* UnivGhostL *)
    intros M Θ0 Θ1 P0 P P' Hne Hs IH Hwf HwfP0 HwfP Hmod Hgf0.
    simpl.
    apply a_subtag__univ_ghost_l; [ exact Hne | ].
    apply IH;
      [ exact Hwf | exact HwfP0
      | apply a_wf_pskl_tophole_inv in HwfP;
        eapply a_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]
      | exact Hmod
      | exact Hgf0 ].
  - (* Flex-Solve : deposit α̂0 := α̂→β̂ and recurse on the arrow; the
       hypotheses lift into the deposited context by ⊴ (mirrors the
       corresponding a_subtag_sound_bundle case). *)
    intros NM M P0 Θ0 Θ1 Ξw α0 α β A Hne Hα Hβ Hs IH
      Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    set (τab := ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
    set (Θmid := (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0).
    set (Θ' := Ξw ++ (α0 ~ abind_flex_mono_def τab) ++ Θmid).
    assert (Huq : uniq (Ξw ++ (α0 ~ abind_flex_mono) ++ Θ0))
      by (apply a_wf_aenv_uniq; exact HwfΞ).
    assert (Hwf0 : a_wf_aenv Θ0).
    { eapply a_wf_aenv_app_r with (Θp := Ξw ++ (α0 ~ abind_flex_mono)).
      simpl_env. exact HwfΞ. }
    assert (Hbα : binds α abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; right; left; reflexivity).
    assert (Hbβ : binds β abind_flex_mono Θmid)
      by (unfold Θmid; unfold binds; simpl; left; reflexivity).
    assert (Hwfmid : a_wf_aenv Θmid).
    { unfold Θmid. apply a_wf_aenv__flex.
      { simpl. clear - Hβ Hne. simpl_env in *. fsetdec. }
      apply a_wf_aenv__flex;
        [ clear - Hα; simpl_env in *; fsetdec | exact Hwf0 ]. }
    assert (Hwfdef : a_wf_aenv ((α0 ~ abind_flex_mono_def τab) ++ Θmid)).
    { apply a_wf_aenv__flex_def.
      - unfold Θmid. simpl. clear - Hα Hβ Huq. simpl_env in *. solve_uniq.
      - apply a_wf_ptyp__arrow; apply a_wf_ptyp__var;
          [ right; left; exact Hbα | right; left; exact Hbβ ].
      - repeat constructor.
      - exact Hwfmid. }
    assert (HwfΘ' : a_wf_aenv Θ').
    { unfold Θ'. apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros α1 Hα1. unfold Θmid. simpl_env.
        clear - Huq Hα Hβ Hα1. destruct_uniq.
        unfold disjoint in *. simpl_env in *. fsetdec. }
    assert (Hbase : Θ0 ⊴ Θ').
    { unfold Θ', Θmid.
      replace (Ξw ++ (α0 ~ abind_flex_mono_def τab)
                 ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
        with ((Ξw ++ (α0 ~ abind_flex_mono_def τab)
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
    assert (Hlift : (Ξw ++ (α0 ~ abind_flex_mono) ++ Θ0) ⊴ Θ').
    { apply a_isub_prepend_decls_src; auto.
      { intros α1 Hb. right; left.
        unfold Θ'. unfold binds. apply in_or_app. left. exact Hb. }
      apply a_isub_prepend_decls_src;
        [ apply (a_decls__cons α0); apply a_decls__nil | | exact Hbase ].
      intros α1 Hb.
      destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> _] | Hb'];
        [ right; right; exists τab; exact Hbα0' | inversion Hb' ]. }
    assert (HwfP0' : Θ' ⨟ empty ⊢ₚₛᵃ P0)
      by (eapply a_wf_pskl_isub; eauto).
    assert (Hwfarr : Θ' ⨟ empty ⊢ₚₛᵃ
                       pskl_arrow (pskl_var_f α) (pskl_var_f β)).
    { apply a_wf_pskl__arrow; apply a_wf_pskl__var;
        right; right; left;
        (unfold Θ'; unfold binds; apply in_or_app; right; simpl;
         right; auto). }
    eapply a_subtag_flex__solve;
      [ exact Hne | exact Hα | exact Hβ | ].
    exact (IH HwfΘ' HwfP0' Hwfarr Hmod Hgf0).
  - (* Flex-Assign : merge and re-enter the decorated MAIN judgment with
       the substituted subject (audit F1; mirrors the sound-bundle case's
       hypothesis transport). *)
    intros NM M P0 Θ0 Θ1 Ξw α β τ A Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    assert (Hwfcons : a_wf_aenv ((β ~ abind_flex_mono_def τ) ++ Θ0))
      by (eapply a_wf_aenv_strip_prefix; eauto).
    inversion Hwfcons as [ | | βz τz Θz HβΘ0 Hwfτ Hm Hwf0 | | | ]; subst.
    assert (HβΞΘ0 : β `notin` dom (Ξw ++ Θ0)).
    { pose proof (a_wf_aenv_uniq HwfΞ) as Huq.
      clear - Huq. simpl_env in Huq. destruct_uniq.
      unfold disjoint in *. simpl_env in *. fsetdec. }
    assert (HwfΞΘ0 : a_wf_aenv (Ξw ++ Θ0))
      by (eapply a_wf_aenv_strip_mid; eauto).
    assert (Hwfpaint : (Ξw ++ Θ0) ⨟ empty ⊢ₚₛᵃ ptyp_to_pskl τ).
    { apply a_scope_pskl_of_ptyp_vis;
        [ apply mono_ptyp_lc; exact Hm | ].
      intros α0 Hα0. right.
      pose proof (a_wf_ptyp_ftv_tvarish Hwfτ Hα0) as Ht.
      destruct Ht as [Hb | [Hb | [τ1 Hb]]];
        [ left | right; left | right; right; exists τ1 ];
        unfold binds in *; apply in_or_app; auto. }
    assert (HwfP0' : (Ξw ++ Θ0) ⨟ empty ⊢ₚₛᵃ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β P0).
    { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
        [ exact HwfP0 | reflexivity | exact HβΞΘ0 | clear; fsetdec
        | apply mono_ptyp_to_pskl_guarded; exact Hm | exact Hwfpaint ]. }
    assert (Hwfvarsub : (Ξw ++ Θ0) ⨟ empty ⊢ₚₛᵃ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)).
    { eapply a_wf_pskl_subst_ctx with (b := abind_flex_mono_def τ);
        [ apply a_wf_pskl__var; right; exact Hαb
        | reflexivity | exact HβΞΘ0 | clear; fsetdec
        | apply mono_ptyp_to_pskl_guarded; exact Hm | exact Hwfpaint ]. }
    apply a_subtag_flex__assign; [ exact Hβ1 | ].
    apply (IH HwfΞΘ0 HwfP0' Hwfvarsub);
      [ intro HSK; specialize (Hmod HSK);
        rewrite <- pskl_to_bskl_inh_subst_mono;
          [ apply mod_comp_sk_subst_mono; [ exact Hmod | exact Hm ]
          | exact Hm ]
      | intros Hty; specialize (Hgf0 Hty);
        apply pskl_top_guarded_subst_mono; [ exact Hgf0 | exact Hm ] ].
  - (* Flex-Depend : β̂ joins the suffix at the Θ0-adjacent end; the
       premise context is the conclusion's up to associativity. *)
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hin Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    apply a_subtag_flex__depend; [ exact Hne | exact Hin | ].
    apply IH.
    { apply a_decls_app;
        [ exact Hsuf | apply (a_decls__cons β); apply a_decls__nil ]. }
    { simpl_env. simpl_env in HwfΞ. exact HwfΞ. }
    { simpl_env. simpl_env in HwfP0. exact HwfP0. }
    { simpl_env. simpl_env in Hαb. exact Hαb. }
    { exact Hmod. }
    { exact Hgf0. }
  - (* Flex-Skip : strip the walked entry (P0 avoids it) and re-cons it
       on the output. *)
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hnin Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    apply a_subtag_flex__skip;
      [ exact Hne | exact Hnin | exact Hβ1 | ].
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; eauto. }
    { eapply a_binds_tvar_strip_mid;
        [ exact Hαb
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intros τ1 He; inversion He; subst; exact (Hne eq_refl) ]. }
    { exact Hmod. }
    { exact Hgf0. }
  - (* Flex-SkipRigid : as Flex-Skip with a rigid head. *)
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hnin Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    apply a_subtag_flex__skip_rigid;
      [ exact Hne | exact Hnin | exact Hβ1 | ].
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; eauto. }
    { eapply a_binds_tvar_strip_mid;
        [ exact Hαb
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intro He; inversion He; subst; exact (Hne eq_refl)
        | intros τ1 He; inversion He; subst; exact (Hne eq_refl) ]. }
    { exact Hmod. }
    { exact Hgf0. }
Qed.

(** The paper-shaped corollary. *)
(** The paper's [P0 :sk M] ([a_sk_mode_compat]) implies the internal
    [mod_comp_sk] on the inhabited [bskl] — so the user-facing statements use the
    direct [pskl] relation and the [bskl] detour stays hidden in the bundle. *)
Lemma a_sk_mode_compat_mod_comp_sk : forall M P0,
  a_sk_mode_compat M P0 -> mod_comp_sk (pskl_to_bskl_inh P0) M.
Proof.
  intros M P0 H; induction H; simpl.
  - apply mod_comp_sk__ti; apply is_sskl__hole.
  - apply mod_comp_sk__tc; apply is_sskl__hole.
  - apply mod_comp_sk__fn; assumption.
Qed.

(** L-A corollary: NO TY side condition — [pskl_top_guarded P0] is DERIVED
    from the wf hypothesis [HwfP0] ([a_wf_pskl__tophole] admits ∀◇ only over a
    guarded body), exactly as the paper's [thm:sound-subtyping] carries no P0
    condition beyond well-formedness.  SK uses the paper's [P0 :sk M]. *)
Lemma a_sub_decorate : forall NM M P0 Θ0 P P' Θ1,
  a_sub NM M P0 Θ0 P P' Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  Θ0 ⊢ᵗ[ NM | M | P0 | empty ] (pskl_to_uskl P) ⩽˙ P' ⊣ Θ1.
Proof.
  intros NM M P0 Θ0 P P' Θ1 Hrun Hwf HwfP0 HwfP Hmod.
  eapply (proj1 a_sub_decorate_bundle); try eassumption.
  - intros HSK; apply a_sk_mode_compat_mod_comp_sk; apply Hmod; exact HSK.
  - intros _; eapply a_wf_pskl_top_guarded; exact HwfP0.
Qed.

(* ===================================================================== *)
(*  §17  thm:sound-subtyping = L-A ∘ L-B                                  *)
(*                                                                        *)
(*  An algorithmic subtyping run yields a (refinement-valid) solution to  *)
(*  its subtyping problem: the output context extends the input, the      *)
(*  input skeleton fills into the output, and the declarative typsub      *)
(*  holds in the output context.  Stated against refinement-valid         *)
(*  solutions per docs/PAPER-GAPS.md (the 2-condition solution notion is  *)
(*  false under capture; soundness yields the refinement conjunct).       *)
(* ===================================================================== *)

Theorem a_sub_sound_thm : forall NM M P0 Θ0 P P' Θ1,
  a_sub NM M P0 Θ0 P P' Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* paper's [P0 :sk M] *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* paper's [P0 :ty M] *)
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  exists Qt,
    bskl_to_pskl Qt = P' /\
    (empty ⨟ Θ1 ⊢ₛᵃ[ NM | M ] (pskl_to_uskl P) ⩽ Qt) /\
    ad_refine_syn_f empty Θ1 empty (pskl_to_bskl_inh P0) Qt.
Proof.
  intros NM M P0 Θ0 P P' Θ1 Hrun Hwf HwfP0 HwfP Hmod Hgf.
  pose proof (a_sub_decorate Hrun Hwf HwfP0 HwfP Hmod) as Htag.
  exact ((proj1 a_subtag_sound_bundle) _ _ _ _ _ _ _ _ Htag
           Hwf
           ltac:(apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; eauto)
           HwfP0
           ltac:(rewrite uskl_to_pskl_pskl_to_uskl; exact HwfP)
           ltac:(intros HSK; apply a_sk_mode_compat_mod_comp_sk; apply Hmod; exact HSK)
           Hgf).
Qed.
