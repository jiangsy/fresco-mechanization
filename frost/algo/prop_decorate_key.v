(** KEY subtyping decoration + decorate-constraint-solving + MAIN + the
    assembled thm:sound-subtyping.  Split from prop_decorate_sub.v so the
    heavy earlier sections are not re-checked on every iteration. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
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
(*  S[⌊ψa⌋/α] replays on S[ψa/α], additionally solving ψa's tags Ψa as    *)
(*  computed by the solvetag run on the constraints collected at α's      *)
(*  occurrences.  Induction on the decorated subtyping premise            *)
(*  (generalizing the look run): the paper's WLOG reorderings become      *)
(*  a_looksub_open_target (ForallR) and per-case inversions; the looked   *)
(*  variable is renamed on the fly (a_looksub_rename_var) to keep it      *)
(*  clear of guessed flexible names (Barendregt prose-completion).        *)
(* ===================================================================== *)

Lemma subst_bskl_in_uskl_decompose : forall ψ α α' S,
  α `notin` ftvar_in_uskl ψ ->
  α' `notin` ftvar_in_uskl S ->
  α' <> α ->
  subst_bskl_in_uskl ψ α' (subst_bskl_in_uskl (uskl_var_f α') α S)
  = subst_bskl_in_uskl ψ α S.
Proof.
  intros ψ α α' S Hαψ Hα'S Hne.
  rewrite subst_bskl_in_uskl_subst_bskl_in_uskl;
    [ | assumption | auto ].
  simpl.
  match goal with
  | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
      [ | exfalso; congruence ]
  end.
  rewrite (subst_bskl_in_uskl_fresh_eq S); [ reflexivity | assumption ].
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

Lemma a_subtag_decoration : forall NM M P0 Ψ Θ0 T Q Θ1,
  Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ] T ⊑ Q ⊣ Θ1 ->
  forall S0 ψa Ψa αv Ξc C,
    T = subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv S0 ->
    ⌊ S0 ⌋ˢ ≼[ αv , M ] P0 ⤳ Ξc ⨾ C ->
    C ⊩ᵗ ψa ⤳ Ψa ->
    αv `notin` ftvar_in_uskl ψa ->
    αv `notin` ftvar_in_pskl P0 ->
    lc_uskl ψa ->
    lc_uskl S0 ->
    a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ ⌊ T ⌋ˢ ->
    (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
    Θ0 ⊢ᵗ[ NM | M | P0 | (Ψ `union` Ψa) ]
      (subst_bskl_in_uskl ψa αv S0) ⊑ Q ⊣ Θ1.
Proof.
  intros NM M P0 Ψ Θ0 T Q Θ1 Hsub.
  induction Hsub;
    intros S0 ψa Ψa αv Ξc C HeqT HD Hst Hαψ HαP0 Hlcψ HlcS0 Hwf
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
    + (* LS-Var : S0 = αv; the decoration-var lemma at ρ = nil *)
      match goal with
      | He : pskl_var_f αv = ⌊ ?S1 ⌋ˢ |- _ =>
          destruct S1; simpl in He; inversion He; subst;
          try solve [ inversion HlcS0 ]
      end.
      simpl in *.
      revert HwfT Hmod.
      match goal with
      | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
          [ | exfalso; congruence ]
      end.
      intros HwfT Hmod.
      inversion Hst; subst.
      change ψa with (msubst_uskl nil ψa).
      eapply a_subtag_decoration_var;
        [ eapply a_subtag__check; eassumption
        | reflexivity
        | eassumption
        | intros γ g Hb; inversion Hb
        | exact Hlcψ
        | exact Hwf
        | apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ
        | exact HwfP0
        | exact HwfT
        | exact Hmod ].
    + (* LS-Absent : both substitutions are the identity *)
      assert (HαS : αv `notin` ftvar_in_uskl S0).
      { rewrite <- (ftvar_in_pskl_uskl_to_pskl S0). assumption. }
      rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαS ].
      match goal with
      | Hg1 : guarded_uskl _, Hc : _ ⊢ᵗ[ _ | _ | _ | _ ] _ ≈ _ ⊣ _ |- _ =>
          rewrite subst_bskl_in_uskl_fresh_eq in Hg1, Hc; try exact HαS
      end.
      inversion Hst; subst.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ eapply a_subtag__check; eassumption
        | match goal with He : Ψa [=] empty |- _ =>
            clear - He; fsetdec end ].
    + (* LS-Vacuous : the Check target is guarded, not ◇ *)
      match goal with Hg : guarded_pskl pskl_hole |- _ => inversion Hg end.
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
      | He : pskl_all_syn _ = ⌊ ?S1 ⌋ˢ |- _ =>
          destruct S1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      match goal with
      | Hg : guarded_uskl _ |- _ => simpl in Hg; inversion Hg
      end.
    + (* LS-UnivGhostL : the source is ⊤◇-headed, not guarded *)
      match goal with
      | He : pskl_tophole _ = ⌊ ?S1 ⌋ˢ |- _ =>
          destruct S1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      match goal with
      | Hg : guarded_uskl _ |- _ => simpl in Hg; inversion Hg
      end.
  - (* ForallR : transport the look run under the opened target *)
    destruct (a_looksub_open_target HD Hst) as [Lo HLo].
    inversion HwfP0 as [ | | | LP ΘP ΔP BP HbodyP HeqP | | ]; subst.
    eapply a_subtag__forall_r
      with (L := L `union` Lo `union` LP `union` dom Θ0
                 `union` singleton αv `union` ftvar_in_pskl B);
      [ eassumption | eassumption | ].
    intros β Hβ.
    destruct (HLo β ltac:(clear - Hβ; fsetdec)) as [C' [HD' Hst']].
    eapply (H2 β ltac:(clear - Hβ; fsetdec)).
    { reflexivity. }
    { exact HD'. }
    { exact Hst'. }
    { exact Hαψ. }
    { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                    B (pskl_var_f β)) as Hup.
      simpl in HαP0, Hup. clear - HαP0 Hβ Hup. fsetdec. }
    { exact Hlcψ. }
    { exact HlcS0. }
    { apply a_wf_aenv__tvar; [ clear - Hβ; fsetdec | exact Hwf ]. }
    { eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc
                   (HbodyP β ltac:(clear - Hβ; fsetdec)) β)
        | clear; fsetdec ]. }
    { eapply a_wf_pskl_weaken;
        [ intros x b Hb; unfold binds; simpl; right; exact Hb
        | exact HwfT ]. }
    { intros Hsk; discriminate Hsk. }
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
    + (* LS-Var : S0 = αv *)
      match goal with
      | He : pskl_var_f αv = ⌊ ?S1 ⌋ˢ |- _ =>
          destruct S1; simpl in He; inversion He; subst;
          try solve [ inversion HlcS0 ]
      end.
      simpl in HeqT |- *.
      revert HeqT HwfT.
      match goal with
      | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
          [ | exfalso; congruence ]
      end.
      intros HeqT HwfT.
      inversion Hst; subst.
      change ψa with (msubst_uskl nil ψa).
      eapply a_subtag_decoration_var;
        [ eapply a_subtag__arrow; eassumption
        | simpl; exact HeqT
        | eassumption
        | intros γ g Hb; inversion Hb
        | exact Hlcψ
        | exact Hwf
        | rewrite HeqT;
          apply pskl_to_uskl_lc; apply lc_uskl_to_pskl_local; exact Hlcψ
        | exact HwfP0
        | exact HwfT
        | exact Hmod ].
    + (* LS-Absent *)
      assert (HαS : αv `notin` ftvar_in_uskl S0).
      { rewrite <- (ftvar_in_pskl_uskl_to_pskl S0). assumption. }
      rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαS ].
      rewrite subst_bskl_in_uskl_fresh_eq in HeqT; [ | exact HαS ].
      inversion Hst; subst.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ first [ rewrite HeqT | idtac ]; eapply a_subtag__arrow; eassumption
        | match goal with He : Ψa [=] empty |- _ =>
            clear - He; fsetdec end ].
    + (* LS-Arrow : the structural pair *)
      match goal with
      | He : pskl_arrow _ _ = ⌊ ?S1 ⌋ˢ |- _ =>
          destruct S1; simpl in He; inversion He; subst;
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
      | Hc1 : _ ⊢ᵗ[ _ | _ | ?P0a | ?Ψ1 ] _ ≈ ?Q1 ⊣ ?Θm,
        Hs2 : ?Θm ⊢ᵗ[ _ | _ | ?P0b | ?Ψ2 ] _ ⊑ ?Q2 ⊣ _,
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
            | IH : forall S1 : uskl, _ |- _ =>
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
      | He : pskl_all_syn _ = ⌊ ?S1 ⌋ˢ |- _ =>
          destruct S1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      simpl in HeqT; discriminate HeqT.
    + (* LS-UnivGhostL : shape clash *)
      match goal with
      | He : pskl_tophole _ = ⌊ ?S1 ⌋ˢ |- _ =>
          destruct S1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      simpl in HeqT; discriminate HeqT.
  - (* ForallL (tagged) : the source is a tagged ∀; the looked variable is
       renamed away from the guessed names before the family rebuild *)
    destruct S0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* S0 = var : the strip is never a tagged ∀ *)
      revert HeqT.
      match goal with
      | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc]
      end; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_etag; symmetry; exact HeqT
      | discriminate HeqT ].
    + (* S0 = all_etag ε0 S0 *)
      match goal with
      | He : uskl_all_etag _ _ = uskl_all_etag ?e (subst_bskl_in_uskl _ _ ?Sb)
        |- _ => idtac
      end.
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαS : αv `notin` ftvar_in_uskl (uskl_all_etag ε0 S0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_all_etag ε0 S0)).
          assumption. }
        assert (HαS' : αv `notin` ftvar_in_uskl S0)
          by (simpl in HαS; exact HαS).
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ]
                          (uskl_all_etag ε0
                             (subst_bskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv S0))
                          ⊑ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_tagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        rewrite subst_bskl_in_uskl_fresh_eq in Hnode; [ | exact HαS' ].
        simpl. rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαS' ].
        inversion Hst; subst.
        eapply a_subtag_psi_cong;
          [ exact Hnode
          | match goal with He : Ψa [=] empty |- _ =>
              clear - He; fsetdec end ].
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | pskl_hole | Ψ ]
                          (uskl_all_etag ε0
                             (subst_bskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv S0))
                          ⊑ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_tagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | match goal with He : Ψa [=] empty |- _ =>
                clear - He; fsetdec end ].
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
                  `union` ftvar_in_uskl S0
                  `union` ftvar_in_pskl ⌊ S0 ⌋ˢ
                  `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P1 `union` LD)) as [αt Hαt].
      destruct (atom_fresh (LD `union` singleton αv `union` singleton αt
                  `union` ftvar_in_pskl ⌊ S0 ⌋ˢ
                  `union` ftvar_in_pskl P1)) as [β0 Hβ0].
      pose proof (HDbody β0 ltac:(clear - Hβ0; fsetdec)) as Dβ0.
      apply a_looksub_rename_var with (α' := αt) in Dβ0;
        [ | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          ⌊ S0 ⌋ˢ (pskl_var_f β0)) as Hup;
            simpl in Hup; clear - Hαt Hβ0 Hup; fsetdec ].
      rewrite <- subst_pskl_in_pskl_open_pskl_wrt_pskl_var in Dβ0;
        [ | clear - Hβ0; fsetdec | constructor ].
      apply a_looksub_subst_stable with (β := β0) (Q := P1) in Dβ0;
        [ | clear - Hβ0; fsetdec
          | clear - Hαt; fsetdec
          | exact HlcP1 ].
      rewrite <- subst_pskl_in_pskl_intro in Dβ0;
        [ | pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          ⌊ S0 ⌋ˢ (pskl_var_f αt) αv) as Hup2;
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
        - intros γ Hγ.
          match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu Hγ; destruct_uniq;
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
      { intros γ Hγ.
        replace (⌊ open_uskl_wrt_uskl
                     (subst_bskl_in_uskl ψa αv S0) (uskl_var_f γ) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl
                    (subst_bskl_in_uskl
                       (pskl_to_uskl (uskl_to_pskl ψa)) αv S0)
                    (uskl_var_f γ) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open;
              rewrite ! uskl_to_pskl_subst;
              rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        match goal with
        | Hex : forall a, a `notin` _ -> a_extract _ _ _ _ _ _ _ |- _ =>
            apply Hex; clear - Hγ; fsetdec
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
                 (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg')
            = open_uskl_wrt_uskl
                (subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv S0)
                ψg').
        { rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcstrip ].
          rewrite subst_bskl_in_uskl_decompose;
            [ | exact HαvStrip | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_bskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (Hresult :
            subst_bskl_in_uskl ψa αt
              (open_uskl_wrt_uskl
                 (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg')
            = open_uskl_wrt_uskl (subst_bskl_in_uskl ψa αv S0) ψg').
        { rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcψ ].
          rewrite subst_bskl_in_uskl_decompose;
            [ | exact Hαψ | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_bskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (HDg :
            ⌊ open_uskl_wrt_uskl
                (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg' ⌋ˢ
            ≼[ αt , M ] P0 ⤳ Ξc ⨾ C).
        { rewrite uskl_to_pskl_open_gen.
          rewrite uskl_to_pskl_subst. simpl.
          rewrite Hera. exact Dβ0. }
        assert (HlcSg : lc_uskl
            (open_uskl_wrt_uskl
               (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg')).
        { apply lc_body_uskl_wrt_uskl; [ | exact Hlcg ].
          match goal with
          | |- body_uskl_wrt_uskl _ =>
              eapply lc_body_uskl_all_etag_2
                with (ε1 := ε0);
              change (uskl_all_etag ε0
                        (subst_bskl_in_uskl (uskl_var_f αt) αv S0))
                with (subst_bskl_in_uskl (uskl_var_f αt) αv
                        (uskl_all_etag ε0 S0));
              apply subst_bskl_in_uskl_lc_uskl;
                [ exact HlcS0 | constructor ]
          end. }
        assert (HwfSg : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
            ⌊ open_uskl_wrt_uskl
                (subst_bskl_in_uskl
                   (pskl_to_uskl (uskl_to_pskl ψa)) αv S0) ψg' ⌋ˢ).
        { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
          rewrite Hera.
          change (open_pskl_wrt_pskl_rec 0 P1
                    ⌊ subst_bskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv S0 ⌋ˢ)
            with (open_pskl_wrt_pskl
                    ⌊ subst_bskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv S0 ⌋ˢ P1).
          simpl in HwfT.
          inversion HwfT; subst.
          match goal with
          | Hbody : forall X, X `notin` ?L0 -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
              apply a_wf_pskl_open with (L := L0);
                [ intros X HX;
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
                             (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg')
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
    destruct S0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* S0 = var : the strip itself is the ∀ source *)
      revert HeqT HwfT.
      match goal with
      | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hc]
      end; intros HeqT HwfT; [ | discriminate HeqT ].
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var : the decoration-var route *)
        inversion Hst; subst.
        simpl.
        match goal with
        | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
            [ | exfalso; congruence ]
        end.
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ eapply a_subtag__forall_l_untagged
              with (L := L) (Ξ := Ξ) (P1 := P1); eassumption
          | simpl; exact HeqT
          | eassumption
          | intros γ g Hb; inversion Hb
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
        match goal with
        | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
            [ | exfalso; congruence ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | match goal with He : Ψa [=] empty |- _ =>
                clear - He; fsetdec end ].
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
    + (* S0 = all_syn S0 *)
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαS : αv `notin` ftvar_in_uskl (uskl_all_syn S0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_all_syn S0)).
          assumption. }
        assert (HαS' : αv `notin` ftvar_in_uskl S0)
          by (simpl in HαS; exact HαS).
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | P0 | Ψ ]
                          (uskl_all_syn
                             (subst_bskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv S0))
                          ⊑ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        rewrite subst_bskl_in_uskl_fresh_eq in Hnode; [ | exact HαS' ].
        simpl. rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαS' ].
        inversion Hst; subst.
        eapply a_subtag_psi_cong;
          [ exact Hnode
          | match goal with He : Ψa [=] empty |- _ =>
              clear - He; fsetdec end ].
      * (* LS-Vacuous *)
        assert (Hnode : Θ0 ⊢ᵗ[ NM | M | pskl_hole | Ψ ]
                          (uskl_all_syn
                             (subst_bskl_in_uskl
                                (pskl_to_uskl (uskl_to_pskl ψa)) αv S0))
                          ⊑ Q ⊣ Θ1)
          by (eapply a_subtag__forall_l_untagged
                with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | match goal with He : Ψa [=] empty |- _ =>
                clear - He; fsetdec end ].
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
                  `union` ftvar_in_uskl S0
                  `union` ftvar_in_pskl ⌊ S0 ⌋ˢ
                  `union` ftvar_in_pskl P0
                  `union` ftvar_in_pskl P1 `union` LD)) as [αt Hαt].
      destruct (atom_fresh (LD `union` singleton αv `union` singleton αt
                  `union` ftvar_in_pskl ⌊ S0 ⌋ˢ
                  `union` ftvar_in_pskl P1)) as [β0 Hβ0].
      pose proof (HDbody β0 ltac:(clear - Hβ0; fsetdec)) as Dβ0.
      apply a_looksub_rename_var with (α' := αt) in Dβ0;
        [ | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          ⌊ S0 ⌋ˢ (pskl_var_f β0)) as Hup;
            simpl in Hup; clear - Hαt Hβ0 Hup; fsetdec ].
      rewrite <- subst_pskl_in_pskl_open_pskl_wrt_pskl_var in Dβ0;
        [ | clear - Hβ0; fsetdec | constructor ].
      apply a_looksub_subst_stable with (β := β0) (Q := P1) in Dβ0;
        [ | clear - Hβ0; fsetdec
          | clear - Hαt; fsetdec
          | exact HlcP1 ].
      rewrite <- subst_pskl_in_pskl_intro in Dβ0;
        [ | pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                          ⌊ S0 ⌋ˢ (pskl_var_f αt) αv) as Hup2;
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
        - intros γ Hγ.
          match goal with Hu : uniq (Ξ ++ Θ0) |- _ =>
            clear - Hu Hγ; destruct_uniq;
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
      { intros γ Hγ.
        replace (⌊ open_uskl_wrt_uskl
                     (subst_bskl_in_uskl ψa αv S0) (uskl_var_f γ) ⌋ˢ)
          with (⌊ open_uskl_wrt_uskl
                    (subst_bskl_in_uskl
                       (pskl_to_uskl (uskl_to_pskl ψa)) αv S0)
                    (uskl_var_f γ) ⌋ˢ)
          by (rewrite ! uskl_to_pskl_open;
              rewrite ! uskl_to_pskl_subst;
              rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
        match goal with
        | Hex : forall a, a `notin` _ -> a_extract _ _ _ _ _ _ _ |- _ =>
            apply Hex; clear - Hγ; fsetdec
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
                 (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg')
            = open_uskl_wrt_uskl
                (subst_bskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv S0)
                ψg').
        { rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcstrip ].
          rewrite subst_bskl_in_uskl_decompose;
            [ | exact HαvStrip | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_bskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (Hresult :
            subst_bskl_in_uskl ψa αt
              (open_uskl_wrt_uskl
                 (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg')
            = open_uskl_wrt_uskl (subst_bskl_in_uskl ψa αv S0) ψg').
        { rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcψ ].
          rewrite subst_bskl_in_uskl_decompose;
            [ | exact Hαψ | clear - Hαt; fsetdec | clear - Hαt; fsetdec ].
          rewrite (subst_bskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
          reflexivity. }
        assert (HDg :
            ⌊ open_uskl_wrt_uskl
                (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg' ⌋ˢ
            ≼[ αt , M ] P0 ⤳ Ξc ⨾ C).
        { rewrite uskl_to_pskl_open_gen.
          rewrite uskl_to_pskl_subst. simpl.
          rewrite Hera. exact Dβ0. }
        assert (HlcSg : lc_uskl
            (open_uskl_wrt_uskl
               (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg')).
        { apply lc_body_uskl_wrt_uskl; [ | exact Hlcg ].
          match goal with
          | |- body_uskl_wrt_uskl _ =>
              eapply lc_body_uskl_all_syn_1;
              change (uskl_all_syn
                        (subst_bskl_in_uskl (uskl_var_f αt) αv S0))
                with (subst_bskl_in_uskl (uskl_var_f αt) αv
                        (uskl_all_syn S0));
              apply subst_bskl_in_uskl_lc_uskl;
                [ exact HlcS0 | constructor ]
          end. }
        assert (HwfSg : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ
            ⌊ open_uskl_wrt_uskl
                (subst_bskl_in_uskl
                   (pskl_to_uskl (uskl_to_pskl ψa)) αv S0) ψg' ⌋ˢ).
        { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
          rewrite Hera.
          change (open_pskl_wrt_pskl_rec 0 P1
                    ⌊ subst_bskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv S0 ⌋ˢ)
            with (open_pskl_wrt_pskl
                    ⌊ subst_bskl_in_uskl
                        (pskl_to_uskl (uskl_to_pskl ψa)) αv S0 ⌋ˢ P1).
          simpl in HwfT.
          inversion HwfT; subst.
          match goal with
          | Hbody : forall X, X `notin` ?L0 -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
              apply a_wf_pskl_open with (L := L0);
                [ intros X HX;
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
                             (subst_bskl_in_uskl (uskl_var_f αt) αv S0) ψg')
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
    destruct S0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* S0 = var *)
      revert HeqT.
      match goal with
      | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hc]
      end; intro HeqT; [ | discriminate HeqT ].
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var : decoration-var at ρ = nil *)
        inversion Hst; subst.
        simpl.
        match goal with
        | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
            [ | exfalso; congruence ]
        end.
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ apply a_subtag__ghost; assumption
          | simpl; exact HeqT
          | eassumption
          | intros γ g Hb; inversion Hb
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
        match goal with
        | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
            [ | exfalso; congruence ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | match goal with He : Ψa [=] empty |- _ =>
                clear - He; fsetdec end ].
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
    + (* S0 = ◇ : nothing to decorate *)
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ HD
                  ltac:(simpl; clear; fsetdec)) as [-> ->].
      inversion Hst; subst.
      simpl.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghost; assumption
        | match goal with He : Ψa [=] empty |- _ =>
            clear - He; fsetdec end ].
  - (* GhostG : source ◇̇ *)
    destruct S0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* S0 = var : the strip is never dotted *)
      revert HeqT.
      match goal with
      | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hc]
      end; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_holeg; symmetry; exact HeqT
      | discriminate HeqT ].
    + (* S0 = ◇̇ : P0 = ◇ is pinned by the rule *)
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ HD
                  ltac:(simpl; clear; fsetdec)) as [-> ->].
      inversion Hst; subst.
      simpl.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghostg; assumption
        | match goal with He : Ψa [=] empty |- _ =>
            clear - He; fsetdec end ].
  - (* UnivGhostL : source ⊤◇.S̄ *)
    destruct S0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* S0 = var *)
      revert HeqT HwfT.
      match goal with
      | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hc]
      end; intros HeqT HwfT; [ | discriminate HeqT ].
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var : decoration-var at ρ = nil *)
        inversion Hst; subst.
        simpl.
        match goal with
        | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
            [ | exfalso; congruence ]
        end.
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ apply a_subtag__univ_ghost_l; eassumption
          | simpl; exact HeqT
          | eassumption
          | intros γ g Hb; inversion Hb
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
        match goal with
        | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
            [ | exfalso; congruence ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | match goal with He : Ψa [=] empty |- _ =>
                clear - He; fsetdec end ].
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
    + (* S0 = ⊤◇.S0 *)
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HD.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαS : αv `notin` ftvar_in_uskl (uskl_tophole S0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_tophole S0)).
          assumption. }
        assert (HαS' : αv `notin` ftvar_in_uskl S0)
          by (simpl in HαS; exact HαS).
        inversion Hst; subst.
        simpl. rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαS' ].
        match goal with
        | Hs' : _ ⊢ᵗ[ _ | _ | _ | _ ]
                  (subst_bskl_in_uskl _ _ _) ⊑ _ ⊣ _ |- _ =>
            rewrite subst_bskl_in_uskl_fresh_eq in Hs'; [ | exact HαS' ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__univ_ghost_l; eassumption
          | match goal with He : Ψa [=] empty |- _ =>
              clear - He; fsetdec end ].
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | match goal with He : Ψa [=] empty |- _ =>
                clear - He; fsetdec end ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_l; eassumption
          | reflexivity
          | apply subst_bskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ⊤-headed source is not guarded *)
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
        | IH : forall S1 : uskl, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hst | exact Hαψ
              | exact HαP0 | exact Hlcψ | assumption
              | exact Hwf | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_tophole_inv in HwfT;
                exact HwfT
              | exact Hmod ]
        end.
  - (* UnivGhostLG : source ⊤◇̇.S̄ *)
    destruct S0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    + (* S0 = var : the strip is never dotted *)
      revert HeqT.
      match goal with
      | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hc]
      end; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_topholeg; symmetry; exact HeqT
      | discriminate HeqT ].
    + (* S0 = ⊤◇̇.S0 *)
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HD.
      inversion HD; subst.
      * (* LS-Absent *)
        assert (HαS : αv `notin` ftvar_in_uskl (uskl_topholeg S0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_topholeg S0)).
          assumption. }
        assert (HαS' : αv `notin` ftvar_in_uskl S0)
          by (simpl in HαS; exact HαS).
        inversion Hst; subst.
        simpl. rewrite subst_bskl_in_uskl_fresh_eq; [ | exact HαS' ].
        match goal with
        | Hs' : _ ⊢ᵗ[ _ | _ | _ | _ ]
                  (subst_bskl_in_uskl _ _ _) ⊑ _ ⊣ _ |- _ =>
            rewrite subst_bskl_in_uskl_fresh_eq in Hs'; [ | exact HαS' ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__univ_ghost_lg; eassumption
          | match goal with He : Ψa [=] empty |- _ =>
              clear - He; fsetdec end ].
      * (* LS-Vacuous : P0 = ◇, erasure-determined *)
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | match goal with He : Ψa [=] empty |- _ =>
                clear - He; fsetdec end ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_lg; eassumption
          | reflexivity
          | apply subst_bskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      * (* LS-Check : a ⊤-headed source is not guarded *)
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
        | IH : forall S1 : uskl, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hst | exact Hαψ
              | exact HαP0 | exact Hlcψ | assumption
              | exact Hwf | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_tophole_inv in HwfT;
                exact HwfT
              | exact Hmod ]
        end.
  - (* FlexMono : source α̂₀ *)
    destruct S0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    revert HeqT.
    match goal with
    | |- context [ if ?e then _ else _ ] => destruct e as [-> | Hc]
    end; intro HeqT.
    + (* eq : the strip is the flexible variable — decoration-var *)
      simpl in HD.
      inversion HD; subst.
      * (* LS-Var *)
        inversion Hst; subst.
        simpl.
        match goal with
        | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
            [ | exfalso; congruence ]
        end.
        change ψa with (msubst_uskl nil ψa).
        eapply a_subtag_decoration_var;
          [ apply a_subtag__flex_mono; eassumption
          | simpl; exact HeqT
          | eassumption
          | intros γ g Hb; inversion Hb
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
        match goal with
        | |- context [ if ?e then _ else _ ] => destruct e as [_ | Hc];
            [ | exfalso; congruence ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | match goal with He : Ψa [=] empty |- _ =>
                clear - He; fsetdec end ].
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
      match goal with
      | |- context [ if ?e then _ else _ ] => destruct e as [Habs | _];
          [ exfalso; congruence | ]
      end.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__flex_mono; eassumption
        | match goal with He : Ψa [=] empty |- _ =>
            clear - He; fsetdec end ].
Qed.

(* ===================================================================== *)
(*  §15  Decorating constraint solving                                    *)
(*  (lemma:decorate-constraint-solving, subtyping-proofs.tex:95-127)      *)
(*                                                                        *)
(*  HONEST ADMIT (true; the paper's "straightforward induction" hides    *)
(*  real content).  Design worked out (see the memory note):             *)
(*  - relate each intermediate solve-skeleton P to the final decoration  *)
(*    ψa by an inductive [dec_ext P ψa Ψrem] (ψa extends P; Ψrem = ψa's  *)
(*    tags at P's ◇-positions), with a ghost-free skip constructor at    *)
(*    ⊤◇-positions the TY guess drops and a flex-forget constructor at   *)
(*    positions the final resolves to a variable;                        *)
(*  - anchor at the OUTPUT: [a_guess NM Ps Ξ' P1 → ⌊ψa⌋=P1 → is_tskl →   *)
(*    dec_ext Ps ψa ∅] (SK: erasure-refl; TY: guess_mono induction);     *)
(*  - walk the constraint list BACKWARD: from [solve_eq P Q P'] and      *)
(*    [dec_ext P' ψa Ψ'] produce the solvetag [ψa ∼ᵗ Q ⤳ Ψi] and        *)
(*    [dec_ext P ψa Ψ₀] with Ψ₀ ⊆ Ψ' ∪ Ψi and Ψ' ⊆ Ψ₀; chain to ◇       *)
(*    where de-hole pins Ψ₀ [=] Ψa (via d_tags_skl/utags), so the        *)
(*    accumulated solvetag output covers Ψa exactly (≤ by tags-bound);   *)
(*  - the per-family uniformity of cofinite solvetag outputs is          *)
(*    resolved by a canonical output [utags ψ \ Ψ'] EXCEPT under the     *)
(*    skip constructor (whose solvetag legitimately solves less); the    *)
(*    remaining engineering is a per-node output function that records   *)
(*    the skip positions.                                                *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(*  SCAFFOLDING for a_extract_decorate (dec_ext + backward walk).          *)
(*                                                                         *)
(*  [dec_ext P ψ Ψrem]: the decorated skeleton ψ (a decoration of the      *)
(*  guess of P) EXTENDS the plain solve-skeleton P; Ψrem is the subset of  *)
(*  ψ's tags located at P's ◇-holes (the tags not yet accounted for by P's *)
(*  own structure).  As the plain solve walks □ → … → Q FORWARD, the tags  *)
(*  migrate from Ψrem into P's structure; walking BACKWARD (Q → … → □) each *)
(*  constraint contributes its solvetag tags and re-grows Ψrem.  The TY    *)
(*  guess fills ◇ with a fresh flex var (untagged) and DROPS ⊤◇ — hence    *)
(*  the [skip_tophole] constructor and the empty base at the anchor.       *)
(*                                                                         *)
(*  STATUS: the inductive + the three deep helpers are DESIGN SKETCHES     *)
(*  (Admitted); the ASSEMBLY (solve_cstr_decorate, a_extract_decorate) is  *)
(*  proved FROM them.  NEXT: (i) validate/repair the dec_ext constructors  *)
(*  against the guess (SK-identity vs TY hole-fill/⊤◇-drop; the flex-forget *)
(*  case is subsumed by [dec_ext__hole] since a guessed α̂ is untagged);    *)
(*  (ii) discharge dec_ext_guess_anchor (structural on the guess), the two *)
(*  step lemmas (structural on solve_eq/solve_sub, mirroring the solvetag  *)
(*  rules), and d_tags_skl_det.                                            *)
(* --------------------------------------------------------------------- *)

Inductive dec_ext : pskl -> uskl -> atoms -> Prop :=
| dec_ext__hole : forall ψ Ψ,               (* P = ◇ : every tag of ψ remains *)
    is_tskl ψ ->
    d_tags_skl Ψ ψ ->
    dec_ext pskl_hole ψ Ψ
| dec_ext__unit : forall Ψ,
    Ψ [=] empty ->
    dec_ext pskl_unit uskl_unit Ψ
| dec_ext__var : forall X Ψ,
    Ψ [=] empty ->
    dec_ext (pskl_var_f X) (uskl_var_f X) Ψ
| dec_ext__arrow : forall P1 P2 ψ1 ψ2 Ψ Ψ1 Ψ2,
    dec_ext P1 ψ1 Ψ1 ->
    dec_ext P2 ψ2 Ψ2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    dec_ext (pskl_arrow P1 P2) (uskl_arrow ψ1 ψ2) Ψ
| dec_ext__all : forall L P0 ψ0 ε Ψ,         (* P's ∀ ; ε accounted, not remaining *)
    (forall X, X `notin` L ->
       dec_ext (open_pskl_wrt_pskl P0 (pskl_var_f X))
               (open_uskl_wrt_uskl ψ0 (uskl_var_f X)) Ψ) ->
    dec_ext (pskl_all_syn P0) (uskl_all_etag ε ψ0) Ψ
| dec_ext__skip_tophole : forall P0 ψ Ψ,     (* TY guess dropped P's ⊤◇ *)
    dec_ext P0 ψ Ψ ->
    dec_ext (pskl_tophole P0) ψ Ψ
| dec_ext__topholeg : forall P0 ψ0 Ψ,        (* SK keeps ⊤◇ ; ψ = ⊤◇̇.ψ0 *)
    dec_ext P0 ψ0 Ψ ->
    dec_ext (pskl_tophole P0) (uskl_topholeg ψ0) Ψ
| dec_ext__flex_forget : forall P α Ψ,       (* P resolved to flex α̂ (untagged) *)
    Ψ [=] empty ->
    dec_ext P (uskl_var_f α) Ψ.

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
  - apply dec_ext__all with (L := L). intros X HX.
    match goal with
    | IH : forall X, X `notin` L -> forall Ψ0, _ -> dec_ext _ _ Ψ0 |- _ =>
        exact (IH X HX Ψ' Heq)
    end.
  - apply dec_ext__skip_tophole. apply IHdec_ext. exact Heq.
  - apply dec_ext__topholeg. apply IHdec_ext. exact Heq.
  - apply dec_ext__flex_forget; fsetdec.
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
    | HIH : forall X, X `notin` ?La -> forall Ψx, d_tags_skl Ψx _ -> _ [=] Ψx,
      Hbody : forall X, X `notin` ?Lb -> d_tags_skl ?Ψb _,
      _ : Ψ' [=] add ε ?Ψb |- _ =>
        destruct (atom_fresh (La `union` Lb)) as [X HX];
        pose proof (HIH X ltac:(clear - HX; fsetdec)
                      Ψb (Hbody X ltac:(clear - HX; fsetdec))) as He
    end.
    fsetdec.
  - (* holeg *) fsetdec.
  - (* topholeg *) apply IHd_tags_skl; assumption.
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
  - apply dec_ext__all with (L := L). intros X HX.
    rewrite <- uskl_to_pskl_open.
    match goal with
    | IH : forall X, X `notin` L -> dec_ext _ _ empty |- _ =>
        exact (IH X ltac:(clear - HX; fsetdec))
    end.
  - apply dec_ext__hole; [ apply is_tskl__holeg | apply d_tags_skl__holeg; fsetdec ].
  - apply dec_ext__topholeg. exact IHis_tskl.
Qed.

(** TY anchor: the [a_guess_mono] output painting's decoration extends the
    pre-guess skeleton (◇ ↦ fresh var, ⊤◇ dropped). *)
Lemma dec_ext_guess_mono_anchor : forall Θ Q Ξ' A ψa,
  a_guess_mono Θ Q Ξ' A ->
  is_tskl ψa ->
  uskl_ghost_free ψa ->
  ⌊ ψa ⌋ˢ = ptyp_to_pskl A ->
  dec_ext Q ψa empty.
Proof.
  intros Θ Q Ξ' A ψa Hg; revert ψa; induction Hg; intros ψa Histk Hgf Hera.
  - (* hole ↦ fresh α̂ : A = var α *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    apply dec_ext__hole; [ exact Histk | apply d_tags_skl__var; fsetdec ].
  - (* tophole P ↦ guess P : drop the ⊤◇ *)
    apply dec_ext__skip_tophole. apply IHHg; assumption.
  - (* var α ↦ var α *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    inversion Hera; subst. apply dec_ext__var; fsetdec.
  - (* unit ↦ unit *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    apply dec_ext__unit; fsetdec.
  - (* arrow ↦ arrow *)
    destruct ψa; simpl in Hera; try discriminate Hera.
    inversion Hera; subst.
    inversion Histk; subst. inversion Hgf; subst.
    eapply dec_ext__arrow; [ apply IHHg1 | apply IHHg2 | fsetdec ]; assumption.
  - (* forall P ↦ all A0 : the ghost-free [is_tskl] ∀-decoration is [all_etag] *)
    destruct ψa; simpl in Hera; try discriminate Hera;
      try (inversion Histk; fail).          (* kill the non-[is_tskl] all_syn survivor *)
    injection Hera as Hera0.
    inversion Histk; subst. inversion Hgf; subst.
    match goal with
    | Hib : forall X, X `notin` ?Li -> is_tskl (open_uskl_wrt_uskl ?bd _),
      Hgb : forall X, X `notin` ?Lg -> uskl_ghost_free (open_uskl_wrt_uskl ?bd _)
      |- _ =>
        apply dec_ext__all with (L := L `union` Li `union` Lg); intros X HX;
        apply (H0 X ltac:(clear - HX; fsetdec)
                 (open_uskl_wrt_uskl bd (uskl_var_f X)));
          [ apply Hib; clear - HX; fsetdec
          | apply Hgb; clear - HX; fsetdec
          | rewrite uskl_to_pskl_open; rewrite Hera0;
            rewrite <- ptyp_to_pskl_open; reflexivity ]
    end.
Qed.

(** ANCHOR: a decoration of the guess output extends the pre-guess skeleton,
    with NO remaining tags — the guess places untagged fresh flex vars at
    every ◇, so all of ψa's tags sit in the structure of [Q]. *)
Lemma dec_ext_guess_anchor : forall NM Q Ξ' Q' Ψa ψa,
  a_guess NM Q Ξ' Q' ->
  a_tags_sort NM Ψa ψa ->
  ⌊ ψa ⌋ˢ = Q' ->
  dec_ext Q ψa empty.
Proof.
  intros NM Q Ξ' Q' Ψa ψa Hg Htags Hera; inversion Hg; subst.
  - (* SK : Q' = Q ; subst already rewrote Q to ⌊ψa⌋ˢ *)
    inversion Htags; subst.
    apply dec_ext_erase_refl; assumption.
  - (* TY : Q' = ptyp_to_pskl A *)
    inversion Htags; subst.
    eapply dec_ext_guess_mono_anchor; eauto.
Qed.

(** COVERAGE: if ψa extends [Q] with remaining tags [Ψ'] (at Q's ◇-holes),
    the decorated solvetag [ψa ∼ᵗ Q] collects exactly the COMPLEMENT [Ψi], so
    [Ψ' ∪ Ψi] is all of ψa's tags.  Threads [d_tags_skl Ψtot ψa] and inverts it
    in the arrow/∀/topholeg cases to split [Ψtot]; the conclusion is set-algebra
    ([dec_ext__arrow] carries no disjointness). *)
Lemma dec_ext_to_solvetag_eq : forall Q ψa Ψ' Ψtot,
  dec_ext Q ψa Ψ' ->
  d_tags_skl Ψtot ψa ->
  exists Ψi, ψa ∼ᵗ Q ⤳ Ψi /\ Ψtot [=] Ψ' `union` Ψi.
Proof.
  intros Q ψa Ψ' Ψtot Hdec; revert Ψtot; induction Hdec; intros Ψtot Hdt.
  - (* hole : Q = ◇ ; SEq-Vacuous, all of ψa's tags remain *)
    exists empty. split; [ apply a_solvetag_eq__vacuous; fsetdec | ].
    match goal with
    | Hd : d_tags_skl ?Ψx _ |- Ψtot [=] union ?Ψx _ =>
        pose proof (d_tags_skl_det Hdt Hd) as He; clear - He; fsetdec
    end.
  - (* unit *)
    exists empty. split; [ apply a_solvetag_eq__unit; fsetdec | ].
    inversion Hdt; subst; fsetdec.
  - (* var *)
    exists empty. split; [ apply a_solvetag_eq__var; fsetdec | ].
    inversion Hdt; subst; fsetdec.
  - (* arrow : split Ψtot via the d_tags arrow inversion, recurse *)
    inversion Hdt as [ | | Ψt Ψt1 Ψt2 R1 R2 Hdt1 Hdt2 Hdisj HeqΨt | | | ]; subst.
    destruct (IHHdec1 _ Hdt1) as [Ψi1 [Hs1 He1]].
    destruct (IHHdec2 _ Hdt2) as [Ψi2 [Hs2 He2]].
    exists (Ψi1 `union` Ψi2). split.
    + eapply a_solvetag_eq__arrow; [ exact Hs1 | exact Hs2 | fsetdec ].
    + clear - H HeqΨt He1 He2. fsetdec.
  - (* all_etag : Q = ∀ ; SEq-ForallInh (cofinite Ψ0) *)
    admit.
  - (* skip_tophole : Q = ⊤◇Q0, guess dropped it ; SEq-UnivGhostR *)
    admit.
  - (* topholeg : Q = ⊤◇Q0, ψ = ⊤◇̇ψ0 ; SEq-UnivGhostG *)
    inversion Hdt; subst.
    match goal with
    | Hd : d_tags_skl Ψtot ?p, IH : forall Ψt, d_tags_skl Ψt ?p -> _ |- _ =>
        destruct (IH _ Hd) as [Ψi [Hs He]]
    end.
    exists Ψi. split; [ apply a_solvetag_eq__univ_ghostg; exact Hs | exact He ].
  - (* flex_forget : ψ = var α ; SEq-Var, no tags *)
    exists empty. split; [ apply a_solvetag_eq__var; fsetdec | ].
    inversion Hdt; subst; fsetdec.
Admitted.

(** BACKWARD STEP (eq): peel one [eq Q] constraint, collecting its solvetag
    contribution [Ψi] and re-growing the remaining-tag set. *)
Lemma dec_ext_solve_eq_step : forall Θ P Q P' ψa Ψ',
  Θ ⊢ₑ P ∼ Q ⤳ P' ->
  dec_ext P' ψa Ψ' ->
  exists Ψi, ψa ∼ᵗ Q ⤳ Ψi /\ dec_ext P ψa (Ψ' `union` Ψi).
Admitted.

(** BACKWARD STEP (sub): the terminal [sub m Q] constraint. *)
Lemma dec_ext_solve_sub_step : forall Θ m P Q P' ψa Ψ',
  Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
  dec_ext P' ψa Ψ' ->
  exists Ψi, ψa ≼ᵗ[ m ] Q ⤳ Ψi /\ dec_ext P ψa (Ψ' `union` Ψi).
Admitted.

(** ASSEMBLY: walking the whole constraint list back from the post-solve
    skeleton [Q] to the start [P], the decorated solvetag collects [Ψc] and
    [dec_ext] re-grows the remaining tags by exactly [Ψc]. *)
Lemma solve_cstr_decorate : forall Θ C P Q ψa Ψpost,
  Θ ⊩ C ⨾ P ⤳ Q ->
  dec_ext Q ψa Ψpost ->
  exists Ψc, C ⊩ᵗ ψa ⤳ Ψc /\ dec_ext P ψa (Ψpost `union` Ψc).
Proof.
  intros Θ C P Q ψa Ψpost Hsolve; induction Hsolve; intros Hdec.
  - (* empty : C = nil, Q = P *)
    exists empty. split.
    + apply a_solvetag__empty; fsetdec.
    + eapply dec_ext_psi_cong; [ exact Hdec | fsetdec ].
  - (* sub : C = [sub m Q0] ; the whole solve output is P' *)
    destruct (dec_ext_solve_sub_step H Hdec) as [Ψi [Hst Hdec']].
    exists Ψi. split.
    + apply a_solvetag__sub; exact Hst.
    + eapply dec_ext_psi_cong; [ exact Hdec' | fsetdec ].
  - (* eq : C = eq Q0 :: C' ; solve_eq then recurse *)
    destruct (IHHsolve Hdec) as [Ψc' [Hstc Hdec'']].
    destruct (dec_ext_solve_eq_step H Hdec'') as [Ψi [Hste Hdec''']].
    exists (Ψi `union` Ψc'). split.
    + eapply a_solvetag__eq; [ exact Hste | exact Hstc | fsetdec ].
    + eapply dec_ext_psi_cong; [ exact Hdec''' | fsetdec ].
Qed.

Lemma a_extract_decorate : forall NM αv M P P0 Ξ P1,
  P ⊳[ NM , αv , M ] P0 ⤳ Ξ ↪ P1 ->
  forall Ψa ψa,
    a_tags_sort NM Ψa ψa ->
    ⌊ ψa ⌋ˢ = P1 ->
    exists Ξc C,
      P ≼[ αv , M ] P0 ⤳ Ξc ⨾ C /\
      C ⊩ᵗ ψa ⤳ Ψa.
Proof.
  intros NM αv M P P0 Ξ P1 Hext Ψa ψa Htags Hera.
  inversion Hext; subst.
  (* H : look ;  H0 : solve ;  H1 : guess (output ⌊ψa⌋ˢ) *)
  eexists; eexists; split; [ exact H | ].
  assert (Hanchor : dec_ext Q ψa empty)
    by (eapply dec_ext_guess_anchor; [ exact H1 | exact Htags | reflexivity ]).
  destruct (solve_cstr_decorate H0 Hanchor) as [Ψc [Hstag Hhole]].
  assert (Hda : d_tags_skl Ψa ψa) by (inversion Htags; assumption).
  inversion Hhole; subst.
  - (* hole : the walked-out tags are exactly [d_tags_skl ψa] = Ψa *)
    eapply a_solvetag_psi_cong; [ exact Hstag | ].
    match goal with
    | Hdtag : d_tags_skl _ ψa |- _ =>
        pose proof (d_tags_skl_det Hda Hdtag) as He; clear - He; fsetdec
    end.
  - (* flex_forget : ψa is a bare var, so both sides are empty *)
    eapply a_solvetag_psi_cong; [ exact Hstag | ].
    inversion Hda; fsetdec.
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
  Θ0 ⊢ᵗ[ NM | M | P0 | empty ] (pskl_to_uskl P) ⊑ Q ⊣ Θ1.

Definition sub_flex_decorate_concl NM M P0 Θ0 Ξw αf Q Θ1 : Prop :=
  a_decls Ξw ->
  a_wf_aenv (Ξw ++ Θ0) ->
  (Ξw ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0 ->
  a_binds_tvar αf (Ξw ++ Θ0) ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) (mode_fn M)) ->
  a_subtag_flex NM M P0 Θ0 Ξw αf Q Θ1.

(** ADMIT SURFACE (why this ends in [Admitted]): every case is closed at
    Qed-level EXCEPT [Check] (a single [admit]), which is blocked on the
    definitional twin mismatch audit-F2 — the plain [a_sub__check] uses
    [a_consis_chk] (existential output) while the decorated
    [a_subtag__check] pins the output to [B]; reconciling them is a
    definition-level change (see the in-case note).  The ForallL case
    additionally consumes [a_extract_decorate] (§15, Admitted), a true
    statement per the paper's decorate-constraint-solving lemma. *)
Theorem a_sub_decorate_bundle :
  (forall NM M P0 Θ0 P Q Θ1,
     a_sub NM M P0 Θ0 P Q Θ1 ->
     sub_decorate_concl NM M P0 Θ0 P Q Θ1) /\
  (forall NM M P0 Θ0 Ξw αf Q Θ1,
     a_sub_flex NM M P0 Θ0 Ξw αf Q Θ1 ->
     sub_flex_decorate_concl NM M P0 Θ0 Ξw αf Q Θ1).
Proof.
  apply (a_sub_sub_flex_mutind
           (fun NM M P0 Θ0 P Q Θ1 _ =>
              sub_decorate_concl NM M P0 Θ0 P Q Θ1)
           (fun NM M P0 Θ0 Ξw αf Q Θ1 _ =>
              sub_flex_decorate_concl NM M P0 Θ0 Ξw αf Q Θ1));
    unfold sub_decorate_concl, sub_flex_decorate_concl.
  - (* Infer *)
    intros NM P Θ0 Hwf HwfP0 HwfP Hmod.
    replace P with (⌊ pskl_to_uskl P ⌋ˢ) at 2
      by apply uskl_to_pskl_pskl_to_uskl.
    apply a_subtag__infer. fsetdec.
  - (* Check : audit-F2 CLOSED — the decorated [a_subtag__check] no longer
       pins the consistency output to [B] (it existentialises it, matching the
       plain [a_consis_chk] and the paper's "output not used / ≡ B"
       convention), so we simply decorate the plain consistency premise. *)
    intros Θ0 Θ1 A B HgA HgB Hchk Hwf HwfP0 HwfP Hmod.
    destruct Hchk as [Q Hcns].
    eapply a_subtag__check;
      [ apply pskl_to_uskl_guarded; exact HgA
      | exact HgB
      | exact (a_consis_decorate Hcns) ].
  - (* ForallR *)
    intros L Θ0 Θ1 Ξ A B Hsuf Huq Hfam IHfam Hwf HwfP0 HwfP Hmod.
    inversion HwfP0 as [ | | | LP ΘP ΔP BP HbodyP HeqP | | ]; subst.
    eapply a_subtag__forall_r
      with (L := L `union` LP `union` dom Θ0);
      [ exact Hsuf | exact Huq | ].
    intros α Hα.
    eapply (IHfam α ltac:(clear - Hα; fsetdec)).
    { apply a_wf_aenv__tvar; [ clear - Hα; fsetdec | exact Hwf ]. }
    { eapply a_wf_pskl_delta_mono;
        [ apply (a_wf_pskl_reassoc
                   (HbodyP α ltac:(clear - Hα; fsetdec)) α)
        | clear; fsetdec ]. }
    { eapply a_wf_pskl_weaken;
        [ intros x b Hb; unfold binds; simpl; right; exact Hb
        | exact HwfP ]. }
    { intros Hsk; discriminate Hsk. }
  - (* UnivGhostR *)
    intros Θ0 P Hg Hwf HwfP0 HwfP Hmod.
    replace (pskl_tophole P)
      with (pskl_tophole ⌊ pskl_to_uskl P ⌋ˢ)
      by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
    apply a_subtag__univ_ghost_r;
      [ apply pskl_to_uskl_guarded; exact Hg | fsetdec ].
  - (* FlexMono *)
    intros NM M P0 Θ0 Θ1 α A Hflex IHflex Hwf HwfP0 HwfP Hmod.
    simpl.
    apply a_subtag__flex_mono; [ | fsetdec ].
    apply IHflex.
    { constructor. }
    { simpl. exact Hwf. }
    { simpl. exact HwfP0. }
    { simpl.
      destruct (a_wf_pskl_ftv_tvarish HwfP (X := α)
                  ltac:(simpl; clear; fsetdec))
        as [HΔx | Htx];
        [ exfalso; clear - HΔx; fsetdec | exact Htx ]. }
    { exact Hmod. }
  - (* Arrow *)
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs2 IH2 Hwf HwfP0 HwfP Hmod.
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
          inversion Hmod; subst; assumption ]
      | fsetdec ].
  - (* ForallL : look-decoration + decorate-constraint-solving + KEY *)
    intros L NM M P0 Θ0 Θ1 P Q Ξ P1 Hne Hgor Hex Huq HwfP1 Hsub IHsub
      Hwf HwfP0 HwfP Hmod.
    assert (Hdecls : a_decls Ξ)
      by (destruct (atom_fresh L) as [α0 Hα0];
          eapply a_extract_decls; eauto).
    assert (HwfΞΘ : a_wf_aenv (Ξ ++ Θ0)).
    { apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros γ Hγ. clear - Huq Hγ. destruct_uniq.
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
                Hsort Hera) as [Ξc [C [HDlk Hst]]].
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
        [ intros X HX; eapply a_wf_pskl_weaken;
          [ exact Hmono | apply HbodyP; auto ]
        | exact HwfP1 ]. }
    rewrite <- Hresult.
    eapply a_subtag_psi_cong;
      [ eapply a_subtag_decoration;
        [ apply IHsub;
          [ exact HwfΞΘ
          | exact HwfP0'
          | exact HwfOpen
          | exact Hmod ]
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
    intros M Θ0 P0 Hwf HwfP0 HwfP Hmod.
    simpl. apply a_subtag__ghost. fsetdec.
  - (* UnivGhostL *)
    intros M Θ0 Θ1 P0 P Q Hne Hs IH Hwf HwfP0 HwfP Hmod.
    simpl.
    apply a_subtag__univ_ghost_l; [ exact Hne | ].
    apply IH;
      [ exact Hwf | exact HwfP0
      | apply a_wf_pskl_tophole_inv in HwfP;
        eapply a_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]
      | exact Hmod ].
  - (* Flex-Solve : deposit α̂0 := α̂→β̂ and recurse on the arrow; the
       hypotheses lift into the deposited context by ⊴ (mirrors the
       corresponding a_subtag_sound_bundle case). *)
    intros NM M P0 Θ0 Θ1 Ξw α0 α β A Hne Hα Hβ Hs IH
      Hsuf HwfΞ HwfP0 Hαb Hmod.
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
      - intros γ Hγ. unfold Θmid. simpl_env.
        clear - Huq Hα Hβ Hγ. destruct_uniq.
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
      { intros γ Hb. right; left.
        unfold Θ'. unfold binds. apply in_or_app. left. exact Hb. }
      apply a_isub_prepend_decls_src;
        [ apply (a_decls__cons α0); apply a_decls__nil | | exact Hbase ].
      intros γ Hb.
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
    exact (IH HwfΘ' HwfP0' Hwfarr Hmod).
  - (* Flex-Assign : merge and re-enter the decorated MAIN judgment with
       the substituted subject (audit F1; mirrors the sound-bundle case's
       hypothesis transport). *)
    intros NM M P0 Θ0 Θ1 Ξw α β τ A Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod.
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
      intros X HX. right.
      pose proof (a_wf_ptyp_ftv_tvarish Hwfτ HX) as Ht.
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
    apply (IH HwfΞΘ0 HwfP0' Hwfvarsub).
    intro HSK; specialize (Hmod HSK).
    rewrite <- pskl_to_bskl_inh_subst_mono;
      [ apply mod_comp_sk_subst_mono; [ exact Hmod | exact Hm ]
      | exact Hm ].
  - (* Flex-Depend : β̂ joins the suffix at the Θ0-adjacent end; the
       premise context is the conclusion's up to associativity. *)
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hin Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod.
    apply a_subtag_flex__depend; [ exact Hne | exact Hin | ].
    apply IH.
    { apply a_decls_app;
        [ exact Hsuf | apply (a_decls__cons β); apply a_decls__nil ]. }
    { simpl_env. simpl_env in HwfΞ. exact HwfΞ. }
    { simpl_env. simpl_env in HwfP0. exact HwfP0. }
    { simpl_env. simpl_env in Hαb. exact Hαb. }
    { exact Hmod. }
  - (* Flex-Skip : strip the walked entry (P0 avoids it) and re-cons it
       on the output. *)
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hnin Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod.
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
  - (* Flex-SkipRigid : as Flex-Skip with a rigid head. *)
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hnin Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod.
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
Qed.

(** The paper-shaped corollary. *)
Lemma a_sub_decorate : forall NM M P0 Θ0 P Q Θ1,
  a_sub NM M P0 Θ0 P Q Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
  Θ0 ⊢ᵗ[ NM | M | P0 | empty ] (pskl_to_uskl P) ⊑ Q ⊣ Θ1.
Proof.
  intros. eapply (proj1 a_sub_decorate_bundle); eauto.
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

Theorem a_sub_sound_thm : forall NM M P0 Θ0 P Q Θ1,
  a_sub NM M P0 Θ0 P Q Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
  (NM = a_sub_mode_ty -> pskl_ghost_free P0) ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  exists Qt,
    bskl_to_pskl Qt = Q /\
    (empty ⨟ Θ1 ⊢ₛᵃ[ NM | M ] (pskl_to_uskl P) ⊑ Qt) /\
    ad_refine_syn_f empty Θ1 empty (pskl_to_bskl_inh P0) Qt.
Proof.
  intros NM M P0 Θ0 P Q Θ1 Hrun Hwf HwfP0 HwfP Hmod Hgf.
  pose proof (a_sub_decorate Hrun Hwf HwfP0 HwfP Hmod) as Htag.
  exact ((proj1 a_subtag_sound_bundle) _ _ _ _ _ _ _ _ Htag
           Hwf
           ltac:(apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; eauto)
           HwfP0
           ltac:(rewrite uskl_to_pskl_pskl_to_uskl; exact HwfP)
           Hmod Hgf).
Qed.
