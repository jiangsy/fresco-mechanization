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
        [ apply a_subtag__check; eassumption
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
        [ apply a_subtag__check; assumption
        | match goal with He : Ψa [=] empty |- _ =>
            clear - He; fsetdec end ].
    + (* LS-Vacuous : the Check target is guarded, not ◇ *)
      match goal with Hg : guarded_pskl pskl_hole |- _ => inversion Hg end.
    + (* LS-Check : decorate the consistency premise *)
      apply a_subtag__check.
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
