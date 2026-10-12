Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_mod_compat.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_consis_rename.
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo_decl.prop_stability.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_soundness_subtag.
Require Import src.fresco.deco_algo.prop_decorate_sub.

Set Implicit Arguments.

Lemma subst_uskl_in_uskl_rename_compose : forall ψ αv αv' R0,
  αv `notin` ftvar_in_uskl ψ ->
  αv' `notin` ftvar_in_uskl R0 ->
  αv <> αv' ->
  subst_uskl_in_uskl ψ αv' (subst_uskl_in_uskl (uskl_var_f αv') αv R0)
  = subst_uskl_in_uskl ψ αv R0.
Proof.
  intros ψ αv αv' R0 Hψ HR Hne.
  rewrite subst_uskl_in_uskl_subst_uskl_in_uskl;
    [ | exact Hψ | exact Hne ].
  simpl. destruct_if; [ | congruence ].
  rewrite (subst_uskl_in_uskl_fresh_eq R0); [ reflexivity | exact HR ].
Qed.

Definition uskl_all_hd (o : option atom) (R : uskl) : uskl :=
  match o with Some ε => uskl_all_tag ε R | None => uskl_all_syn R end.

Lemma uskl_all_hd_erase : forall o R,
  ⌊ uskl_all_hd o R ⌋ˢ = pskl_all_syn ⌊ R ⌋ˢ.
Proof. intros [ε | ] R; reflexivity. Qed.

Lemma subst_uskl_in_uskl_all_hd : forall ψ α o R,
  subst_uskl_in_uskl ψ α (uskl_all_hd o R)
  = uskl_all_hd o (subst_uskl_in_uskl ψ α R).
Proof. intros ψ α [ε | ] R; reflexivity. Qed.

Lemma lc_body_uskl_all_hd : forall o R,
  lc_uskl (uskl_all_hd o R) -> body_uskl_wrt_uskl R.
Proof.
  intros [ε | ] R H;
    [ eapply lc_body_uskl_all_tag_2; exact H
    | eapply lc_body_uskl_all_syn_1; exact H ].
Qed.

Lemma a_subtag__forall_l_hd : forall o L NM M P0 Ψ Θ0 Θ1 R Q Ξ P1,
  M <> mode_ti ->
  (guarded_pskl P0 \/ P0 = pskl_ghost) ->
  (forall α, α `notin` L ->
     a_extract Θ0 NM α M ⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ P0 Ξ P1) ->
  uniq (Ξ ++ Θ0) ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
  (forall Ψg ψg,
     Ψg ∩ L [=] empty ->
     a_tags_sort NM Ψg ψg ->
     ⌊ ψg ⌋ˢ = P1 ->
     {{ (Ξ ++ Θ0) ⊢[ NM | M | P0 | (Ψ `union` Ψg) ]
       (open_uskl_wrt_uskl R ψg) ⩽ Q ⊣ Θ1 }}da) ->
  {{ Θ0 ⊢[ NM | M | P0 | Ψ ] (uskl_all_hd o R) ⩽ Q ⊣ Θ1 }}da.
Proof.
  intros [ε | ] *; intros;
    [ eapply a_subtag__forall_l_tagged | eapply a_subtag__forall_l_untagged ];
    eassumption.
Qed.

Lemma a_subtag_decoration_forall_l_hd :
  forall o L NM M P0 Ψ Θ0 Θ1 R Q Ξ P1 Θl R0 ψa Ψa αv Ξc C,
  R = subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ->
  M <> mode_ti ->
  (guarded_pskl P0 \/ P0 = pskl_ghost) ->
  (forall α, α `notin` L ->
     a_extract Θ0 NM α M ⌊ open_uskl_wrt_uskl R (uskl_var_f α) ⌋ˢ P0 Ξ P1) ->
  uniq (Ξ ++ Θ0) ->
  {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
  (forall Ψg ψg,
     Ψg ∩ L [=] empty ->
     a_tags_sort NM Ψg ψg ->
     ⌊ ψg ⌋ˢ = P1 ->
     {{ (Ξ ++ Θ0) ⊢[ NM | M | P0 | (Ψ `union` Ψg) ]
       (open_uskl_wrt_uskl R ψg) ⩽ Q ⊣ Θ1 }}da) ->
  (forall (Ψg : atoms) (ψg : uskl),
     Ψg ∩ L [=] empty ->
     a_tags_sort NM Ψg ψg ->
     ⌊ ψg ⌋ˢ = P1 ->
     forall Θl R0 ψa Ψa αv Ξc 𝒞,
       open_uskl_wrt_uskl R ψg
         = subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ->
       {{ Θl ⊢ ⌊ R0 ⌋ˢ ≼[ αv , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a ->
       {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
       αv `notin` ftvar_in_uskl ψa ->
       αv `notin` ftvar_in_pskl P0 ->
       lc_uskl ψa ->
       lc_uskl R0 ->
       {{ ⊢ (Ξ ++ Θ0) }}a ->
       {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
       {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ ⌊ open_uskl_wrt_uskl R ψg ⌋ˢ }}a ->
       (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
       {{ (Ξ ++ Θ0) ⊢[ NM | M | P0 | ((Ψ `union` Ψg) `union` Ψa) ]
         (subst_uskl_in_uskl ψa αv R0) ⩽ Q ⊣ Θ1 }}da) ->
  {{ Θl ⊢ ⌊ uskl_all_hd o R0 ⌋ˢ ≼[ αv , M ] P0 ⤳ Ξc ⨾ C }}a ->
  {{ C ⊩ ψa ⤳ Ψa }}da ->
  αv `notin` ftvar_in_uskl ψa ->
  αv `notin` ftvar_in_pskl P0 ->
  lc_uskl ψa ->
  lc_uskl (uskl_all_hd o R0) ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ ⌊ uskl_all_hd o R ⌋ˢ }}a ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
  {{ Θ0 ⊢[ NM | M | P0 | (Ψ `union` Ψa) ]
    (subst_uskl_in_uskl ψa αv (uskl_all_hd o R0)) ⩽ Q ⊣ Θ1 }}da.
Proof.
  intros o L NM M P0 Ψ Θ0 Θ1 R Q Ξ P1 Θl R0 ψa Ψa αv Ξc C HeqR
    HMti Hgd Hex Huq HwfP1 Hfam IHfam HD Hst Hαψ HαP0 Hlcψ HlcS0 Hwf
    HwfP0 HwfT Hmod.
  subst R.
  rewrite uskl_all_hd_erase in HD.
  inversion HD; subst.
  *
    assert (HαR' : αv `notin` ftvar_in_uskl R0).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0).
      match goal with
      | Ha : αv `notin` ftvar_in_pskl (pskl_all_syn _) |- _ => exact Ha
      end. }
    assert (Hnode : {{ Θ0 ⊢[ NM | M | P0 | Ψ ]
                      (uskl_all_hd o
                         (subst_uskl_in_uskl
                            (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                      ⩽ Q ⊣ Θ1 }}da)
      by (eapply a_subtag__forall_l_hd
            with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
    rewrite subst_uskl_in_uskl_fresh_eq in Hnode; [ | exact HαR' ].
    rewrite subst_uskl_in_uskl_all_hd.
    rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR' ].
    inversion Hst; subst.
    eapply a_subtag_psi_cong;
      [ exact Hnode
      | fsetdec_empty ].
  *
    assert (Hnode : {{ Θ0 ⊢[ NM | M | pskl_ghost | Ψ ]
                      (uskl_all_hd o
                         (subst_uskl_in_uskl
                            (pskl_to_uskl (uskl_to_pskl ψa)) αv R0))
                      ⩽ Q ⊣ Θ1 }}da)
      by (eapply a_subtag__forall_l_hd
            with (L := L) (Ξ := Ξ) (P1 := P1); eassumption).
    inversion Hst; subst.
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | fsetdec_empty ].
    eapply a_subtag_vacuous_erasure;
      [ exact Hnode | reflexivity
      | apply subst_uskl_in_uskl_lc_uskl; assumption
      | rewrite subst_uskl_in_uskl_all_hd, !uskl_all_hd_erase;
        f_equal; apply erase_swap_subst ].
  *
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  *
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
        destruct Hg as [Hg | Hg]; [ inversion Hg | discriminate Hg ]
    end.
  *
  match goal with
  | Hp : {{ _ ⊢ (open_pskl_wrt_pskl _ _) ≼[ _ , _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
      rename Hp into Dbody
  end.
  match goal with
  | Hb : _ `notin` add αv _ |- _ => rename Hb into Hbfr
  end.
  assert (Hlcstrip : lc_uskl (pskl_to_uskl (uskl_to_pskl ψa)))
    by (apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ).
  assert (HlcP1 : lc_pskl P1)
    by (eapply a_wf_pskl_lc; eauto).
  match type of Dbody with
  | {{ ((?b ~ abind_tvar) ++ _) ⊢ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ }}a =>
    destruct (atom_fresh (singleton αv `union` ftvar_in_uskl ψa
                `union` ftvar_in_uskl R0
                `union` ftvar_in_pskl ⌊ R0 ⌋ˢ
                `union` ftvar_in_pskl P0
                `union` ftvar_in_pskl P1
                `union` singleton b `union` dom Ξc
                `union` ftvar_in_a_cstrs C)) as [αt Hαt];
    assert (Hbne : b <> αt) by (intros ->; clear - Hαt; solve_notin_auto);
    assert (Hαvb : αv <> b) by (intros ->; clear - Hbfr; fsetdec);
    assert (HbR0 : b `notin` ftvar_in_pskl ⌊ R0 ⌋ˢ)
      by (clear - Hbfr; fsetdec);

    apply a_looksub_rename_var with (α' := αt) in Dbody;
      [ | pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                        ⌊ R0 ⌋ˢ (pskl_var_f b)) as Hup;
          simpl in Hup; clear - Hαt Hup; destruct_notin; fsetdec
        | clear - Hαt; solve_notin_auto
        | clear - Hαt; solve_notin_auto ];
    rewrite <- subst_pskl_in_pskl_open_pskl_wrt_pskl_var in Dbody;
      [ | clear - Hαvb; congruence | constructor ];

    assert (HαtP1 : αt `notin` ftvar_in_pskl P1)
      by (clear - Hαt; solve_notin_auto);
    destruct (a_looksub_subst_gen Dbody Hst Hbne HαtP1 HlcP1)
      as (Ξg & Cg & Dsub & Hstg);
    rewrite <- subst_pskl_in_pskl_intro in Dsub;
      [ | pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper
                        ⌊ R0 ⌋ˢ (pskl_var_f αt) αv) as Hup2;
          simpl in Hup2; clear - Hbne HbR0 Hup2; fsetdec ]
  end.
  rename Dsub into Dβ0.

  assert (Hαtψa : αt `notin` ftvar_in_uskl ψa)
    by (clear - Hαt; solve_notin_auto).
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
  assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a).
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
  assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
    by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
  rewrite subst_uskl_in_uskl_all_hd.
  eapply a_subtag__forall_l_hd

    with (L := L `union` singleton αv `union` singleton αt
               `union` ftvar_in_pskl P1)
         (Ξ := Ξ) (P1 := P1);
    [ assumption | assumption | | assumption | assumption | ].
  { intros α1 Hα1.
    replace (⌊ open_uskl_wrt_uskl
                 (subst_uskl_in_uskl ψa αv R0) (uskl_var_f α1) ⌋ˢ)
      with (⌊ open_uskl_wrt_uskl
                (subst_uskl_in_uskl
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
      by (apply is_dskl_lc; inversion Hsort; assumption).
    assert (Hαtg : αt `notin` ftvar_in_uskl ψg').
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl ψg'). rewrite Hera.
      clear - Hαt; solve_notin_auto. }
    assert (Hsubject :
        subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αt
          (open_uskl_wrt_uskl
             (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')
        = open_uskl_wrt_uskl
            (subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0)
            ψg').
    { rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcstrip ].
      rewrite subst_uskl_in_uskl_rename_compose;
        [ | exact HαvStrip | clear - Hαt; solve_notin_auto | clear - Hαt; solve_notin_auto ].
      rewrite (subst_uskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
      reflexivity. }
    assert (Hresult :
        subst_uskl_in_uskl ψa αt
          (open_uskl_wrt_uskl
             (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')
        = open_uskl_wrt_uskl (subst_uskl_in_uskl ψa αv R0) ψg').
    { rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl; [ | exact Hlcψ ].
      rewrite subst_uskl_in_uskl_rename_compose;
        [ | exact Hαψ | clear - Hαt; solve_notin_auto | clear - Hαt; solve_notin_auto ].
      rewrite (subst_uskl_in_uskl_fresh_eq ψg'); [ | exact Hαtg ].
      reflexivity. }
    match type of Dβ0 with
    | {{ ?Θb ⊢ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ }}a =>
        assert (HDg : {{ Θb ⊢
            ⌊ open_uskl_wrt_uskl
                (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg' ⌋ˢ
            ≼[ αt , M ] P0 ⤳ Ξg ⨾ Cg }}a)
          by (rewrite uskl_to_pskl_open_gen;
              rewrite uskl_to_pskl_subst; simpl;
              rewrite Hera; exact Dβ0)
    end.
    assert (HlcSg : lc_uskl
        (open_uskl_wrt_uskl
           (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')).
    { apply lc_body_uskl_wrt_uskl; [ | exact Hlcg ].
      match goal with
      | |- body_uskl_wrt_uskl _ =>
          apply (@lc_body_uskl_all_hd o);
          rewrite <- subst_uskl_in_uskl_all_hd;
          apply subst_uskl_in_uskl_lc_uskl;
            [ exact HlcS0 | constructor ]
      end. }
    assert (HwfSg : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ
        ⌊ open_uskl_wrt_uskl
            (subst_uskl_in_uskl
               (pskl_to_uskl (uskl_to_pskl ψa)) αv R0) ψg' ⌋ˢ }}a).
    { unfold open_uskl_wrt_uskl. rewrite uskl_to_pskl_open_rec.
      rewrite Hera.
      change (open_pskl_wrt_pskl_rec 0 P1
                ⌊ subst_uskl_in_uskl
                    (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ)
        with (open_pskl_wrt_pskl
                ⌊ subst_uskl_in_uskl
                    (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ⌋ˢ P1).
      rewrite uskl_all_hd_erase in HwfT.
      inversion HwfT; subst.
      match goal with
      | Hbody : forall α, α `notin` ?L0 -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
          apply a_wf_pskl_open with (L := L0);
            [ intros α Hα;
              eapply a_wf_pskl_weaken;
                [ exact (@binds_sub_cons _ _ _ Hmono) | apply Hbody; auto ]
            | assumption ]
      end. }
    rewrite <- Hresult.
    eapply a_subtag_psi_cong;
      [ match goal with
        | IHfam : forall (a : atoms) (b : uskl), _ |- _ =>
            eapply (IHfam Ψg' ψg' ltac:(clear - Hfr; solve_notin_auto) Hsort Hera
                      _
                      (open_uskl_wrt_uskl
                         (subst_uskl_in_uskl (uskl_var_f αt) αv R0) ψg')
                      ψa Ψa αt Ξg Cg);
            [ rewrite Hsubject; reflexivity
            | exact HDg
            | exact Hstg
            | exact Hαtψa
            | clear - Hαt; solve_notin_auto
            | exact Hlcψ
            | exact HlcSg
            | exact HwfΞΘ
            | exact HwfP0'
            | exact HwfSg
            | exact Hmod ]
        end
      | clear; fsetdec ].
Qed.

Lemma a_subtag_decoration_strip_var :
  forall NM M P0 Ψ Θ0 Θ1 R' Q Θl ψa Ψa αv Ξc C,
  {{ Θ0 ⊢[ NM | M | P0 | Ψ ] R' ⩽ Q ⊣ Θ1 }}da ->
  R' = pskl_to_uskl (uskl_to_pskl ψa) ->
  (M = mode_tc -> forall P, P0 <> pskl_all_syn P) ->
  {{ Θl ⊢ (pskl_var_f αv) ≼[ αv , M ] P0 ⤳ Ξc ⨾ C }}a ->
  {{ C ⊩ ψa ⤳ Ψa }}da ->
  lc_uskl ψa ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ ⌊ R' ⌋ˢ }}a ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
  {{ Θ0 ⊢[ NM | M | P0 | (Ψ `union` Ψa) ]
    (subst_uskl_in_uskl ψa αv (uskl_var_f αv)) ⩽ Q ⊣ Θ1 }}da.
Proof.
  intros NM M P0 Ψ Θ0 Θ1 R' Q Θl ψa Ψa αv Ξc C Hnode HeqT HnoAll HD Hst
    Hlcψ Hwf HwfP0 HwfT Hmod.
  subst R'.
  inversion HD; subst.
  -
    inversion Hst; subst.
    simpl.
    destruct_if as [_ | Hc];
        [ | exfalso; congruence ].
    change ψa with (msubst_uskl nil ψa).
    eapply a_subtag_decoration_var;
      [ exact Hnode
      | simpl; reflexivity
      | eassumption
      | intros α1 g Hb; inversion Hb
      | exact Hlcψ
      | exact Hwf
      | apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
      | exact HwfP0
      | exact HwfT
      | exact Hmod ].
  -
    match goal with
    | Ha : αv `notin` ftvar_in_pskl (pskl_var_f αv) |- _ =>
        simpl in Ha; exfalso; clear - Ha; fsetdec
    end.
  -
    inversion Hst; subst.
    simpl.
    destruct_if as [_ | Hc];
        [ | exfalso; congruence ].
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | fsetdec_empty ].
    eapply a_subtag_vacuous_erasure;
      [ exact Hnode
      | reflexivity
      | exact Hlcψ
      | rewrite uskl_to_pskl_pskl_to_uskl; reflexivity ].
  -
    match goal with
    | Hne : pskl_var_f αv <> pskl_var_f αv |- _ => congruence
    end.
  -
    exfalso. exact (HnoAll eq_refl _ eq_refl).
Qed.

Lemma a_subtag_decoration : forall NM M P0 Ψ Θ0 R' P Θ1,
  {{ Θ0 ⊢[ NM | M | P0 | Ψ ] R' ⩽ P ⊣ Θ1 }}da ->
  forall Θl R0 ψa Ψa αv Ξc 𝒞,
    R' = subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa)) αv R0 ->
    {{ Θl ⊢ ⌊ R0 ⌋ˢ ≼[ αv , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a ->
    {{ 𝒞 ⊩ ψa ⤳ Ψa }}da ->
    αv `notin` ftvar_in_uskl ψa ->
    αv `notin` ftvar_in_pskl P0 ->
    lc_uskl ψa ->
    lc_uskl R0 ->
    {{ ⊢ Θ0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ ⌊ R' ⌋ˢ }}a ->
    (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
    {{ Θ0 ⊢[ NM | M | P0 | (Ψ `union` Ψa) ]
      (subst_uskl_in_uskl ψa αv R0) ⩽ P ⊣ Θ1 }}da.
Proof.
  intros NM M P0 Ψ Θ0 R' P Θ1 Hsub.
  induction Hsub;
    intros Θl R0 ψa Ψa αv Ξc C HeqT HD Hst Hαψ HαP0 Hlcψ HlcS0 Hwf
      HwfP0 HwfT Hmod.
  -
    assert (Hemp : Ψa [=] empty)
      by (eapply a_looksub_ghost_solvetag_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite <- erase_swap_subst.
    apply a_subtag__infer; assumption.
  -
    inversion HD; subst.
    +
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
        | apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
        | exact HwfP0
        | exact HwfT
        | exact Hmod ].
    +
      assert (HαR : αv `notin` ftvar_in_uskl R0).
      { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). assumption. }
      rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR ].
      match goal with
      | Hg1 : guarded_uskl _, Hc : {{ _ ⊢[ _ | _ | _ | _ ] _ ∼ _ ⊣ _ }}da |- _ =>
          rewrite subst_uskl_in_uskl_fresh_eq in Hg1, Hc; try exact HαR
      end.
      inversion Hst; subst.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ eapply a_subtag__check; eassumption
        | fsetdec_empty ].
    +
      inv_guarded_ghost.
    +
      eapply a_subtag__check.
      * assumption.
      * apply guarded_subst_decorate; assumption.
      * assumption.
      * eapply a_consistag_decoration;
          [ eassumption | exact Hst | reflexivity | exact Hαψ
          | exact Hlcψ | exact HlcS0 | eassumption | exact Hwf
          | exact HwfP0 | exact HwfT
          | apply rig_empty | apply no_flex_dep_empty | apply faf_empty ].
    +
      match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ =>
        inversion Hg end.
    +
      match goal with
      | He : pskl_all_syn _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      match goal with
      | Hg : guarded_uskl _ |- _ => simpl in Hg; inversion Hg
      end.
    +
      match goal with
      | He : pskl_univ_ghost _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      match goal with
      | Hg : guarded_uskl _ |- _ => simpl in Hg; inversion Hg
      end.
  -
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

    | Hn : forall _ : aenv, _ |- _ => rename Hn into IHprem
    end.
    rewrite dom_app in Hfr.

    assert (HeqE : ⌊ R ⌋ˢ = subst_pskl_in_pskl ⌊ ψa ⌋ˢ αv ⌊ R0 ⌋ˢ)
      by (rewrite HeqT; rewrite uskl_to_pskl_subst;
          rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
    assert (HαR0 : forall γ, γ `notin` ftvar_in_uskl R -> γ <> αv ->
              γ `notin` ftvar_in_uskl R0).
    { intros γ Hγ Hγv Hc.
      apply Hγ. rewrite HeqT.
      pose proof (ftvar_in_uskl_subst_uskl_in_uskl_lower
                    R0 (pskl_to_uskl (uskl_to_pskl ψa)) αv) as Hlo.
      clear - Hlo Hγv Hc. fsetdec. }

    destruct (atom_fresh (singleton α `union` singleton αv
                `union` ftvar_in_uskl R0 `union` ftvar_in_uskl ψa
                `union` ftvar_in_pskl B
                `union` dom Ξc `union` ftvar_in_a_cstrs C)) as [αv' Hαv'].
    assert (HeqT' : R = subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψa))
                          αv' (subst_uskl_in_uskl (uskl_var_f αv') αv R0)).
    { rewrite subst_uskl_in_uskl_rename_compose;
        [ exact HeqT
        | pose proof Hαψ as Hαψ0;
          rewrite <- (ftvar_in_pskl_uskl_to_pskl ψa) in Hαψ0;
          rewrite <- (ftvar_in_pskl_uskl_to_pskl (pskl_to_uskl ⌊ ψa ⌋ˢ));
          rewrite uskl_to_pskl_pskl_to_uskl;
          exact Hαψ0
        | clear - Hαv'; fsetdec
        | intros ->; clear - Hαv'; fsetdec ]. }

    assert (HD1 : {{ Θl ⊢ ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                    ≼[ αv' , mode_tc ] (pskl_all_syn B) ⤳ Ξc ⨾ C }}a).
    { rewrite uskl_to_pskl_subst. simpl.
      apply a_looksub_rename_var;
        [ exact HD
        | rewrite ftvar_in_pskl_uskl_to_pskl; clear - Hαv'; fsetdec
        | clear - Hαv'; fsetdec
        | clear - Hαv'; fsetdec ]. }

    assert (HαR0' : α `notin`
              ftvar_in_uskl (subst_uskl_in_uskl (uskl_var_f αv') αv R0)).
    { pose proof (ftvar_in_uskl_subst_uskl_in_uskl_upper
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
    assert (HαB : α `notin` ftvar_in_pskl (pskl_all_syn B))
      by (cbn; clear - Hfr; fsetdec).
    assert (Hmono0 : ftvar_in_aenv
                       (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                     [<=] ftvar_in_aenv Θl)
      by (apply flex_restrict_dom).
    pose proof (@a_looksub_ctx_ftv_mono _ _ _ _ _ _ _
                  (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                  HD1 Hmono0
                  (fun β Hβ => @flex_restrict_iff _ Θl β Hβ)) as HD1n.
    clear HD1 Hmono0; rename HD1n into HD1.
    assert (HαP : α `notin` ftvar_in_pskl
                    ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ).
    { pose proof (ftvar_in_pskl_uskl_to_pskl
                    (subst_uskl_in_uskl (uskl_var_f αv') αv R0)) as Hepq.
      clear - HαR0' Hepq; fsetdec. }
    assert (Hααv' : α <> αv') by (intros ->; clear - Hαv'; fsetdec).
    pose proof (flex_restrict_ftvar (ftvar_in_pskl (pskl_all_syn B)) Θl)
      as HΘlr.
    destruct (atom_fresh (singleton α `union` singleton αv'
                `union` ftvar_in_pskl
                    ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                `union` ftvar_in_pskl B `union` dom Ξc
                `union` ftvar_in_a_cstrs C)) as [δ Hδ].
    assert (Hδαv' : δ <> αv') by (intros ->; clear - Hδ; fsetdec).
    assert (Hδα : δ <> α) by (intros ->; clear - Hδ; fsetdec).
    assert (Hβin : α `notin` ftvar_in_aenv
                       (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                     `union` ftvar_in_pskl
                         ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                     `union` ftvar_in_pskl (pskl_all_syn B))
      by (cbn in HαB |- *; clear - HαP HαB HΘlr; fsetdec).
    assert (Hδin : δ `notin` ftvar_in_aenv
                       (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                     `union` ftvar_in_pskl
                         ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                     `union` ftvar_in_pskl (pskl_all_syn B)
                     `union` dom Ξc `union` ftvar_in_a_cstrs C)
      by (cbn in HΘlr |- *; clear - Hδ HΘlr; fsetdec).
    destruct (a_looksub_avoid_atom HD1 Hst Hααv' Hδαv' Hδα Hβin Hδin)
      as (Ξf & Cf & HDf & Hstf & Hαf).
    assert (Hopen : α `notin` ftvar_in_aenv
                        (flex_restrict (ftvar_in_pskl (pskl_all_syn B)) Θl)
                      `union` ftvar_in_pskl
                          ⌊ subst_uskl_in_uskl (uskl_var_f αv') αv R0 ⌋ˢ
                      `union` ftvar_in_pskl B
                      `union` dom Ξf `union` ftvar_in_a_cstrs Cf)
      by (cbn in HαB, HΘlr |- *; clear - HαP HαB Hαf HΘlr; fsetdec).
    destruct (a_looksub_open_target_at ltac:(eassumption) HDf Hstf Hααv' Hopen)
      as [C' [HD2 Hst2]].

    assert (Htrans :
        {{ ((α ~ abind_tvar) ++ Θ0)
          ⊢[ a_sub_mode_ty | mode_tc
            | (open_pskl_wrt_pskl B (pskl_var_f α)) | (Ψ `union` Ψa) ]
          (subst_uskl_in_uskl ψa αv'
             (subst_uskl_in_uskl (uskl_var_f αv') αv R0))
          ⩽ (open_pskl_wrt_pskl B (pskl_var_f α))
          ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}da).
    { eapply IHprem.
      { exact HeqT'. }
      { exact HD2. }
      { exact Hst2. }
      { clear - Hαv'; fsetdec. }
      { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                      B (pskl_var_f α)) as Hup.
        simpl in Hup. clear - Hαv' Hup. fsetdec. }
      { exact Hlcψ. }
      { apply subst_uskl_in_uskl_lc_uskl;
          [ exact HlcS0 | constructor ]. }
      { apply a_wf_aenv__tvar; [ clear - Hfr; fsetdec | exact Hwf ]. }
      { eapply a_wf_pskl_all_syn_open_tvar;
          [ exact HwfP0 | clear - Hfr; fsetdec ]. }
      { eapply a_wf_pskl_weaken;
          [ intros x b Hb; unfold binds; simpl; right; exact Hb
          | exact HwfT ]. }
      { intros Hsk; discriminate Hsk. } }

    assert (Hcollapse : subst_uskl_in_uskl ψa αv'
                          (subst_uskl_in_uskl (uskl_var_f αv') αv R0)
                        = subst_uskl_in_uskl ψa αv R0).
    { apply subst_uskl_in_uskl_rename_compose;
        [ exact Hαψ
        | clear - Hαv'; fsetdec
        | intros ->; clear - Hαv'; fsetdec ]. }
    rewrite Hcollapse in Htrans.

    eapply a_subtag__forall_r with (α := α) (Ξ := Ξ);
      [ assumption | exact Hsuf | exact Huq | | exact Htrans ].
    rewrite dom_app.
    assert (Hfteq : ftvar_in_uskl (subst_uskl_in_uskl ψa αv R0)
                    [=] ftvar_in_uskl R).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl
                    (subst_uskl_in_uskl ψa αv R0)).
      rewrite <- (ftvar_in_pskl_uskl_to_pskl R).
      rewrite uskl_to_pskl_subst. rewrite HeqE. reflexivity. }
    clear - Hfr Hfteq. fsetdec.
  -
    assert (Hemp : Ψa [=] empty)
      by (eapply a_looksub_ghost_solvetag_empty; eauto).
    eapply a_subtag_psi_cong with (Ψ := Ψ);
      [ | clear - Hemp; fsetdec ].
    rewrite HeqT. rewrite <- erase_swap_subst.
    apply a_subtag__univ_ghost_r;
      [ | assumption ].
    apply guarded_subst_decorate; try assumption.
    rewrite <- HeqT. assumption.
  -
    inversion HD; subst.
    +
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
          apply pskl_to_uskl_lc; apply lc_uskl_to_pskl; exact Hlcψ
        | exact HwfP0
        | exact HwfT
        | exact Hmod ].
    +
      assert (HαR : αv `notin` ftvar_in_uskl R0).
      { rewrite <- (ftvar_in_pskl_uskl_to_pskl R0). assumption. }
      rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR ].
      rewrite subst_uskl_in_uskl_fresh_eq in HeqT; [ | exact HαR ].
      inversion Hst; subst.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ first [ rewrite HeqT | idtac ]; eapply a_subtag__arrow; eassumption
        | fsetdec_empty ].
    +
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
      | Hc1 : {{ _ ⊢[ _ | _ | ?P0a | ?Ψ1 ] _ ∼ ?Q1 ⊣ ?Θm }}da,
        Hs2 : {{ ?Θm ⊢[ _ | _ | ?P0b | ?Ψ2 ] _ ⩽ ?Q2 ⊣ _ }}da,
        HΨc : _ [=] union ?Ψ1 ?Ψ2 |- _ =>
          destruct (a_consistag_sound_aux Hc1 Hwf
                      ltac:(apply subst_uskl_in_uskl_lc_uskl;
                            [ assumption
                            | apply pskl_to_uskl_lc;
                              apply lc_uskl_to_pskl; assumption ])
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

        | IH : forall R1 : aenv, _ |- _ =>
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
    +
      match goal with
      | He : pskl_all_syn _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      simpl in HeqT; discriminate HeqT.
    +
      match goal with
      | He : pskl_univ_ghost _ = ⌊ ?R1 ⌋ˢ |- _ =>
          destruct R1; simpl in He; try discriminate He;
          try solve [ inversion HlcS0 ]
      end;
      simpl in HeqT; discriminate HeqT.
  -
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    +
      revert HeqT.
      destruct_if as [_ | Hc]; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_tag; symmetry; exact HeqT
      | discriminate HeqT ].
    +
      inversion HeqT; subst. clear HeqT.
      eapply (@a_subtag_decoration_forall_l_hd (Some ε0));
        try eassumption; reflexivity.

  -
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    +
      revert HeqT HwfT.
      destruct_if as [-> | Hc]; intros HeqT HwfT; [ | discriminate HeqT ].
      eapply a_subtag_decoration_strip_var;
      [ eapply a_subtag__forall_l_untagged
          with (L := L) (Ξ := Ξ) (P1 := P1); eassumption
      | exact HeqT
      | intros _ P ->;
        match goal with
        | Hg : guarded_pskl (pskl_all_syn _) \/ _ |- _ =>
            destruct Hg as [Hg | Hg]; [ inversion Hg | discriminate Hg ]
        end
      | exact HD | exact Hst | exact Hlcψ | exact Hwf | exact HwfP0
      | exact HwfT | exact Hmod ].
    +
      inversion HeqT; subst. clear HeqT.
      eapply (@a_subtag_decoration_forall_l_hd None);
        try eassumption; reflexivity.

  -
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    +
      revert HeqT.
      destruct_if as [-> | Hc]; intro HeqT; [ | discriminate HeqT ].
      eapply a_subtag_decoration_strip_var;
      [ apply a_subtag__ghost; assumption
      | exact HeqT
      | intros _ P ->; specialize (Hmod eq_refl); simpl in Hmod;
        inversion Hmod; subst;
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end
      | exact HD | exact Hst | exact Hlcψ | exact Hwf | exact HwfP0
      | exact HwfT | exact Hmod ].
    +
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ HD
                  ltac:(simpl; clear; solve_notin_auto)) as [-> ->].
      inversion Hst; subst.
      simpl.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghost; assumption
        | fsetdec_empty ].
  -
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    +
      revert HeqT.
      destruct_if as [-> | Hc]; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_dot_ghost; symmetry; exact HeqT
      | discriminate HeqT ].
    +
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ HD
                  ltac:(simpl; clear; solve_notin_auto)) as [-> ->].
      inversion Hst; subst.
      simpl.
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__ghostg; assumption
        | fsetdec_empty ].
  -
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    +
      revert HeqT HwfT.
      destruct_if as [-> | Hc]; intros HeqT HwfT; [ | discriminate HeqT ].
      eapply a_subtag_decoration_strip_var;
      [ apply a_subtag__univ_ghost_l; eassumption
      | exact HeqT
      | intros _ P ->; specialize (Hmod eq_refl); simpl in Hmod;
        inversion Hmod; subst;
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end
      | exact HD | exact Hst | exact Hlcψ | exact Hwf | exact HwfP0
      | exact HwfT | exact Hmod ].
    +
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HD.
      inversion HD; subst.
      *
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_univ_ghost R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_univ_ghost R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        inversion Hst; subst.
        simpl. rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR' ].
        match goal with
        | Hs' : {{ _ ⊢[ _ | _ | _ | _ ]
                  (subst_uskl_in_uskl _ _ _) ⩽ _ ⊣ _ }}da |- _ =>
            rewrite subst_uskl_in_uskl_fresh_eq in Hs'; [ | exact HαR' ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__univ_ghost_l; eassumption
          | fsetdec_empty ].
      *
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_l; eassumption
          | reflexivity
          | apply subst_uskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      *
        match goal with
        | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
        end.
      *
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
      *
        simpl.
        apply a_subtag__univ_ghost_l; [ assumption | ].
        match goal with

        | IH : forall R1 : aenv, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hst | exact Hαψ
              | exact HαP0 | exact Hlcψ | assumption
              | exact Hwf | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_univ_ghost_inv in HwfT as [_ HwfT];
                exact HwfT
              | exact Hmod ]
        end.
  -
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    +
      revert HeqT.
      destruct_if as [-> | Hc]; intro HeqT;
      [ exfalso; eapply pskl_to_uskl_not_dot_univ_ghost; symmetry; exact HeqT
      | discriminate HeqT ].
    +
      inversion HeqT; subst. clear HeqT.
      inversion HlcS0; subst.
      simpl in HD.
      inversion HD; subst.
      *
        assert (HαR : αv `notin` ftvar_in_uskl (uskl_dot_univ_ghost R0)).
        { rewrite <- (ftvar_in_pskl_uskl_to_pskl (uskl_dot_univ_ghost R0)).
          assumption. }
        assert (HαR' : αv `notin` ftvar_in_uskl R0)
          by (simpl in HαR; exact HαR).
        inversion Hst; subst.
        simpl. rewrite subst_uskl_in_uskl_fresh_eq; [ | exact HαR' ].
        match goal with
        | Hs' : {{ _ ⊢[ _ | _ | _ | _ ]
                  (subst_uskl_in_uskl _ _ _) ⩽ _ ⊣ _ }}da |- _ =>
            rewrite subst_uskl_in_uskl_fresh_eq in Hs'; [ | exact HαR' ]
        end.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ apply a_subtag__univ_ghost_lg; eassumption
          | fsetdec_empty ].
      *
        inversion Hst; subst.
        eapply a_subtag_psi_cong with (Ψ := Ψ);
          [ | fsetdec_empty ].
        eapply a_subtag_vacuous_erasure;
          [ apply a_subtag__univ_ghost_lg; eassumption
          | reflexivity
          | apply subst_uskl_in_uskl_lc_uskl; assumption
          | apply erase_swap_subst ].
      *
        match goal with
        | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
        end.
      *
        specialize (Hmod eq_refl). simpl in Hmod.
        inversion Hmod; subst.
        match goal with
        | Hs : is_sskl (bskl_all_inh _) |- _ => inversion Hs
        end.
      *
        simpl.
        apply a_subtag__univ_ghost_lg; [ assumption | ].
        match goal with

        | IH : forall R1 : aenv, _ |- _ =>
            eapply IH;
              [ reflexivity | eassumption | exact Hst | exact Hαψ
              | exact HαP0 | exact Hlcψ | assumption
              | exact Hwf | exact HwfP0
              | simpl in HwfT; apply a_wf_pskl_univ_ghost_inv in HwfT as [_ HwfT];
                exact HwfT
              | exact Hmod ]
        end.
  -
    destruct R0; simpl in HeqT;
      try discriminate HeqT;
      try solve [ inversion HlcS0 ].
    revert HeqT.
    destruct_if as [-> | Hc]; intro HeqT.
    +
      eapply a_subtag_decoration_strip_var;
      [ apply a_subtag__flex_mono; eassumption
      | exact HeqT
      | intros Hc0; discriminate Hc0
      | exact HD | exact Hst | exact Hlcψ | exact Hwf | exact HwfP0
      | exact HwfT | exact Hmod ].
    +
      inversion HeqT; subst.
      destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ HD
                  ltac:(simpl; clear - Hc; solve_notin_auto)) as [-> ->].
      inversion Hst; subst.
      simpl.
      destruct_if as [Habs | _];
          [ exfalso; congruence | ].
      eapply a_subtag_psi_cong with (Ψ := Ψ);
        [ apply a_subtag__flex_mono; eassumption
        | fsetdec_empty ].
Qed.

Lemma d_tags_skl_det : forall Ψ1 Ψ' ψ,
  d_tags_skl Ψ1 ψ -> d_tags_skl Ψ' ψ -> Ψ1 [=] Ψ'.
Proof.
  intros Ψ1 Ψ' ψ H1 H2.
  rewrite (d_tags_skl_ftag H1), (d_tags_skl_ftag H2). reflexivity.
Qed.

Lemma guarded_uskl_subst_var : forall ψ α β,
  guarded_uskl ψ -> guarded_uskl (subst_uskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros ψ α β H.
  change (uskl_var_f β) with (ptyp_to_uskl_syn (ptyp_var_f β)).
  apply guarded_uskl_subst_mono; auto with fresco.
Qed.

Lemma uskl_ghost_free_subst_var : forall ψ α β,
  uskl_ghost_free ψ ->
  uskl_ghost_free (subst_uskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros ψ α β H.
  change (uskl_var_f β) with (ptyp_to_uskl_syn (ptyp_var_f β)).
  apply uskl_ghost_free_subst_mono; auto with fresco.
Qed.

Lemma a_solvetag_sub_eq_rename_var :
  (forall ψ M P Ψ, {{ ψ ≼[ M ] P ⤳ Ψ }}da ->
     forall α β0, {{ (subst_uskl_in_uskl (uskl_var_f β0) α ψ) ≼[ M ]
                 (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ }}da) /\
  (forall ψ P Ψ, {{ ψ ∼ P ⤳ Ψ }}da ->
     forall α β0, {{ (subst_uskl_in_uskl (uskl_var_f β0) α ψ) ∼
                 (subst_pskl_in_pskl (pskl_var_f β0) α P) ⤳ Ψ }}da).
Proof.
  apply a_solvetag_sub_eq_mutind;
    intros; simpl.
  -
    destruct_if;
      apply a_solvetag_sub__var; assumption.
  -
    apply a_solvetag_sub__forall_l with (L := L `union` singleton α); intros β Hβ.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall b, _ |- _ => apply IH; clear - Hβ; fsetdec end.
  -
    apply a_solvetag_sub__univ_ghost_lg; auto.
  -
    apply a_solvetag_sub__vacuous; assumption.
  -
    apply a_solvetag_sub__check;
      [ apply pskl_ghost_free_subst_var; assumption
      | apply guarded_uskl_subst_var; assumption
      | apply guarded_pskl_subst_var; assumption | auto ].
  -
    apply a_solvetag_sub__forall_r with (L := L `union` singleton α);
      [ apply pskl_ghost_free_subst_var; assumption | ]; intros β Hβ.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ; fsetdec | apply lc_pskl_var_f ].
    match goal with IH : forall b, _ |- _ => apply IH; clear - Hβ; fsetdec end.
  -
    eapply a_solvetag_sub__arrow; [ auto | auto | eassumption ].
  -
    apply a_solvetag_eq__unit; assumption.
  -
    destruct_if;
      apply a_solvetag_eq__var; assumption.
  -
    apply a_solvetag_eq__vacuous; assumption.
  -
    eapply a_solvetag_eq__arrow; [ auto | auto | eassumption ].
  -
    eapply a_solvetag_eq__forall_inh with (L := L `union` singleton α);
      [ intros β Hβ;
        rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
          [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ];
        rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
          [ | clear - Hβ; fsetdec | apply lc_pskl_var_f ];
        match goal with IH : forall b, _ |- _ => apply IH; clear - Hβ; fsetdec end
      | eassumption ].
  -
    apply a_solvetag_eq__univ_ghostg; auto.
  -
    apply a_solvetag_eq__forall_syn with (L := L `union` singleton α); intros β Hβ.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hβ; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall b, _ |- _ =>
      specialize (IH β ltac:(clear - Hβ; solve_notin_auto) α β0); simpl in IH; exact IH end.
  -
    apply a_solvetag_eq__univ_ghost_r;
      [ rewrite uskl_to_pskl_subst; simpl;
        apply guarded_pskl_subst_var; assumption
      | auto ].
  -
    destruct_if;
      apply a_solvetag_eq__flex_r;
      first [ apply uskl_ghost_free_subst_var; assumption | assumption ].
Qed.

Lemma d_tags_skl_is_dskl : forall Ψ ψ, d_tags_skl Ψ ψ -> is_dskl ψ.
Proof.
  intros Ψ ψ H; induction H; eauto with fresco.
Qed.

Lemma a_solvetag_sub_eq_sound :
  (forall ψ M P Ψ, {{ ψ ≼[ M ] P ⤳ Ψ }}da ->
     forall Ψtot, d_tags_skl Ψtot ψ -> Ψ [<=] Ψtot) /\
  (forall ψ P Ψ, {{ ψ ∼ P ⤳ Ψ }}da ->
     forall Ψtot, d_tags_skl Ψtot ψ -> Ψ [<=] Ψtot).
Proof.
  split; intros * Hs Ψtot Hdt; rewrite (d_tags_skl_ftag Hdt);
    [ exact (proj1 a_solvetag_sub_eq_tags_bound _ _ _ _ Hs)
    | exact (proj2 a_solvetag_sub_eq_tags_bound _ _ _ Hs) ].
Qed.

Lemma a_solvetag_sound : forall 𝒞 ψ Ψ Ψtot,
  {{ 𝒞 ⊩ ψ ⤳ Ψ }}da -> d_tags_skl Ψtot ψ -> Ψ [<=] Ψtot.
Proof.
  intros 𝒞 ψ Ψ Ψtot Hc; revert Ψtot; induction Hc; intros Ψtot Hdt.
  -  fsetdec_empty.
  -  match goal with H : {{ _ ≼[ _ ] _ ⤳ _ }}da |- _ =>
      pose proof ((proj1 a_solvetag_sub_eq_sound) _ _ _ _ H Ψtot Hdt) end; fsetdec.
  -
    match goal with
    | Hs : {{ _ ∼ _ ⤳ ?Ψ1 }}da, He : _ [=] union ?Ψ1 ?Ψ2 |- _ =>
        pose proof ((proj2 a_solvetag_sub_eq_sound) _ _ _ Hs Ψtot Hdt) as Hae;
        pose proof (IHHc Ψtot Hdt) as Hai;
        clear - He Hae Hai; fsetdec
    end.
Qed.

Inductive dec_ext : pskl -> uskl -> atoms -> Prop :=
| dec_ext__ghost : forall ψ Ψ,
    d_tags_skl Ψ ψ ->
    dec_ext pskl_ghost ψ Ψ
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
| dec_ext__all : forall L P0 ψ0 ε Ψ,
    (forall α, α `notin` L ->
       dec_ext (open_pskl_wrt_pskl P0 (pskl_var_f α))
               (open_uskl_wrt_uskl ψ0 (uskl_var_f α)) Ψ) ->
    dec_ext (pskl_all_syn P0) (uskl_all_tag ε ψ0) Ψ
| dec_ext__skip_univ_ghost : forall P0 ψ Ψ,
    guarded_pskl ⌊ ψ ⌋ˢ ->
    dec_ext P0 ψ Ψ ->
    dec_ext (pskl_univ_ghost P0) ψ Ψ
| dec_ext__dot_univ_ghost : forall P0 ψ0 Ψ,
    dec_ext P0 ψ0 Ψ ->
    dec_ext (pskl_univ_ghost P0) (uskl_dot_univ_ghost ψ0) Ψ
| dec_ext__absorb_all : forall L P0 ψ0 ε Ψ Ψ0,
    (forall α, α `notin` L ->
       dec_ext (pskl_univ_ghost P0)
               (open_uskl_wrt_uskl ψ0 (uskl_var_f α)) Ψ0) ->
    Ψ [=] add ε Ψ0 ->
    dec_ext (pskl_univ_ghost P0) (uskl_all_tag ε ψ0) Ψ
| dec_ext__flex_forget : forall P α Ψ,
    Ψ [=] empty ->
    dec_ext P (uskl_var_f α) Ψ.

#[export] Hint Constructors dec_ext : fresco.

Lemma dec_ext_erase_refl : forall ψ,
  is_dskl ψ ->
  dec_ext (uskl_to_pskl ψ) ψ empty.
Proof.
  intros ψ H; induction H; simpl.
  - apply dec_ext__unit; fsetdec.
  - apply dec_ext__var; fsetdec.
  - eapply dec_ext__arrow; [ exact IHis_dskl1 | exact IHis_dskl2 | fsetdec ].
  - apply dec_ext__all with (L := L). intros α Hα.
    rewrite <- uskl_to_pskl_open.
    match goal with
    | IH : forall α, α `notin` L -> dec_ext _ _ empty |- _ =>
        exact (IH α ltac:(clear - Hα; solve_notin_auto))
    end.
  - apply dec_ext__ghost; apply d_tags_skl__dot_ghost; fsetdec.
  - auto with fresco.
Qed.

Definition pskl_guarded_head (P : pskl) : Prop :=
  match P with
  | pskl_unit | pskl_var_f _ | pskl_var_b _ | pskl_arrow _ _ => True
  | _ => False
  end.

Lemma lc_head_guarded : forall P,
  lc_pskl P -> pskl_guarded_head P -> guarded_pskl P.
Proof.
  intros P Hlc Hh; destruct P; simpl in Hh; try contradiction.
  - auto with fresco.
  - inversion Hlc.
  - auto with fresco.
  - inversion Hlc; subst; auto with fresco.
Qed.

Lemma guarded_pskl_head : forall P, guarded_pskl P -> pskl_guarded_head P.
Proof. intros P H; inversion H; subst; simpl; exact I. Qed.

Lemma a_guess_mono_head : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> pskl_guarded_head P ->
  pskl_guarded_head (ptyp_to_pskl A).
Proof.
  intros Θ P Ξ A Hg Hh; inversion Hg; subst; simpl in Hh;
    try contradiction; simpl; exact I.
Qed.

Fixpoint pskl_top_guarded (P : pskl) : Prop :=
  match P with
  | pskl_univ_ghost P0 => pskl_guarded_head P0 /\ pskl_top_guarded P0
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

Lemma pskl_guarded_head_close_rec : forall P β k,
  pskl_guarded_head P -> pskl_guarded_head (close_pskl_wrt_pskl_rec k β P).
Proof.
  induction P; intros β k H; simpl in *; auto.
  - destruct (lt_ge_dec n k); simpl; auto.
  - destruct (β == α); simpl; auto.
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

Lemma pskl_top_guarded_close_rec : forall P β k,
  pskl_top_guarded P -> pskl_top_guarded (close_pskl_wrt_pskl_rec k β P).
Proof.
  induction P; intros β k H; simpl in *; auto.
  - destruct (lt_ge_dec n k); simpl; auto.
  - destruct (β == α); simpl; auto.
  - destruct H; split; auto.
  - destruct H as [Hh Ht]; split;
      [ apply pskl_guarded_head_close_rec; exact Hh | auto ].
Qed.

Lemma pskl_top_guarded_close : forall P β,
  pskl_top_guarded P -> pskl_top_guarded (close_pskl_wrt_pskl β P).
Proof.
  intros P β H; unfold close_pskl_wrt_pskl;
    apply pskl_top_guarded_close_rec; exact H.
Qed.

Lemma a_wf_pskl_top_guarded : forall Θ Δ P,
  a_wf_pskl Θ Δ P -> pskl_top_guarded P.
Proof.
  intros Θ Δ P H; induction H; simpl; try exact I.
  -  auto.
  -
    destruct (atom_fresh L) as [α Hα].
    apply (proj2 (pskl_top_guarded_open_rec P α 0)).
    match goal with IH : forall α, α `notin` L -> pskl_top_guarded _ |- _ =>
      exact (IH α Hα) end.
  -
    auto using guarded_pskl_head.
Qed.

Lemma pskl_ghost_free_top_guarded : forall P, pskl_ghost_free P -> pskl_top_guarded P.
Proof. induction P; simpl; intuition. Qed.

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
  -
    destruct_if; auto using pskl_ghost_free_top_guarded, ptyp_to_pskl_ghost_free.
  -  destruct Hg as [Hg1 Hg2]; auto using IHP1, IHP2.
  -  auto using IHP.
  -  destruct Hg as [Hgh Ht];
      auto using pskl_guarded_head_subst_mono, IHP.
Qed.

Lemma dec_ext_guess_mono_anchor_size : forall n Θ P' Ξ' A ψa,
  size_pskl P' <= n ->
  a_guess_mono Θ P' Ξ' A ->
  pskl_top_guarded P' ->
  is_dskl ψa ->
  uskl_ghost_free ψa ->
  ⌊ ψa ⌋ˢ = ptyp_to_pskl A ->
  dec_ext P' ψa empty.
Proof.
  induction n as [| n IHn]; intros Θ P' Ξ' A ψa Hsz Hg;
    [ destruct Hg; cbn in Hsz; lia | ].
  destruct Hg as [ Θ' α Hα | Θ' Pb Ξb Ab Hgb | Θ' α | Θ'
                 | Θ' Pa Pb Ξa Ξb Aa Ab Hga Hgb
                 | Θ' Pb Ξb Ab b0 Hfr Hgb ];
    cbn in Hsz; intros Htg Histk Hgf Hera.
  -
    destruct ψa; simpl in Hera; try discriminate Hera.
    apply dec_ext__ghost; apply d_tags_skl__var; fsetdec.
  -
    simpl in Htg; destruct Htg as [Hhd Htg0].
    apply dec_ext__skip_univ_ghost;
      [ rewrite Hera; apply lc_head_guarded;
          [ rewrite <- Hera; apply lc_uskl_to_pskl; apply is_dskl_lc;
            exact Histk
          | eapply a_guess_mono_head; eassumption ]
      | eapply IHn; [ lia | exact Hgb | exact Htg0 | exact Histk | exact Hgf
                    | exact Hera ] ].
  -
    destruct ψa; simpl in Hera; try discriminate Hera.
    inversion Hera; subst. apply dec_ext__var; fsetdec.
  -
    destruct ψa; simpl in Hera; try discriminate Hera.
    apply dec_ext__unit; fsetdec.
  -
    destruct ψa; simpl in Hera; try discriminate Hera.
    inversion Hera; subst.
    simpl in Htg; destruct Htg as [Htg1 Htg2].
    inversion Histk; subst. inversion Hgf; subst.
    eapply dec_ext__arrow;
      [ eapply IHn with (P' := Pa); [ lia | exact Hga | .. ]
      | eapply IHn with (P' := Pb); [ lia | exact Hgb | .. ]
      | fsetdec ]; assumption.
  -
    destruct ψa; simpl in Hera; try discriminate Hera;
      try (inversion Histk; fail).
    injection Hera as Hera0.
    simpl in Htg.
    inversion Histk; subst. inversion Hgf; subst.
    match goal with
    | Hib : forall α, α `notin` ?Li -> is_dskl (open_uskl_wrt_uskl ?bd _),
      Hgfb : forall α, α `notin` ?Lg -> uskl_ghost_free (open_uskl_wrt_uskl ?bd _)
      |- _ =>
        apply dec_ext__all
          with (L := Li `union` Lg `union` dom Ξb `union` ftvar_in_pskl Pb
                       `union` ftvar_in_ptyp Ab
                       `union` ftvar_in_aenv Θ');
        intros α Hα;
        eapply IHn with (P' := open_pskl_wrt_pskl Pb (pskl_var_f α))
                        (A := open_ptyp_wrt_ptyp
                                (close_ptyp_wrt_ptyp b0 Ab) (ptyp_var_f α));
          [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia
          | apply a_guess_mono_open_at;
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
  is_dskl ψa ->
  uskl_ghost_free ψa ->
  ⌊ ψa ⌋ˢ = ptyp_to_pskl A ->
  dec_ext P' ψa empty.
Proof.
  intros. eapply dec_ext_guess_mono_anchor_size; eauto.
Qed.

Lemma dec_ext_guess_anchor : forall Θ NM P Ξ' P' Ψa ψa,
  a_guess Θ NM P Ξ' P' ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P) ->
  a_tags_sort NM Ψa ψa ->
  ⌊ ψa ⌋ˢ = P' ->
  dec_ext P ψa empty.
Proof.
  intros Θ NM P Ξ' P' Ψa ψa Hg Htg Htags Hera; inversion Hg; subst.
  -
    inversion Htags; subst.
    apply dec_ext_erase_refl; assumption.
  -
    inversion Htags; subst.
    eapply dec_ext_guess_mono_anchor; [ eassumption | apply Htg; reflexivity | .. ];
      eauto.
Qed.

Lemma d_tags_skl_rename_var : forall Ψ ψ α β,
  d_tags_skl Ψ ψ -> d_tags_skl Ψ (subst_uskl_in_uskl (uskl_var_f β) α ψ).
Proof.
  intros Ψ ψ α β H.
  change (uskl_var_f β) with (ptyp_to_uskl_syn (ptyp_var_f β)).
  apply d_tags_skl_subst_mono; auto with fresco.
Qed.

Lemma dec_ext_rename_var : forall P ψ Ψ,
  dec_ext P ψ Ψ ->
  forall α β, dec_ext (subst_pskl_in_pskl (pskl_var_f β) α P)
                      (subst_uskl_in_uskl (uskl_var_f β) α ψ) Ψ.
Proof.
  intros P ψ Ψ H; induction H; intros αr βr; simpl.
  - auto using d_tags_skl_rename_var with fresco.
  - auto with fresco.
  - destruct_if; auto with fresco.
  - eapply dec_ext__arrow; [ apply IHdec_ext1 | apply IHdec_ext2 | assumption ].
  - apply dec_ext__all with (L := L `union` singleton αr); intros α2 Hα2.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα2; fsetdec | apply lc_pskl_var_f ].
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ].
    match goal with IH : forall a, a `notin` L -> forall b c, _ |- _ =>
      apply (IH α2 ltac:(clear - Hα2; solve_notin_auto)) end.
  - apply dec_ext__skip_univ_ghost;
      [ rewrite uskl_to_pskl_subst; apply guarded_pskl_subst_var; assumption
      | apply IHdec_ext ].
  - apply dec_ext__dot_univ_ghost; apply IHdec_ext.
  - eapply dec_ext__absorb_all with (L := L `union` singleton αr);
      [ intros α2 Hα2;
        rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
          [ | clear - Hα2; fsetdec | apply lc_uskl_var_f ];
        match goal with IH : forall a, a `notin` L -> forall b c, _ |- _ =>
          apply (IH α2 ltac:(clear - Hα2; solve_notin_auto)) end
      | assumption ].
  - destruct_if; auto with fresco.
Qed.

Lemma a_solvetag_eq_open_rename : forall {ψ0 Q Ψ α0 β},
  {{ (open_uskl_wrt_uskl ψ0 (uskl_var_f α0))
     ∼ (open_pskl_wrt_pskl Q (pskl_var_f α0)) ⤳ Ψ }}da ->
  α0 `notin` ftvar_in_uskl ψ0 -> α0 `notin` ftvar_in_pskl Q ->
  {{ (open_uskl_wrt_uskl ψ0 (uskl_var_f β))
     ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ψ }}da.
Proof.
  intros * H Hψ HQ.
  rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β) Hψ),
    (subst_pskl_in_pskl_intro α0 Q (pskl_var_f β) HQ).
  exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ H α0 β).
Qed.

Lemma a_solvetag_eq_open_rename_l : forall {ψ0 P Ψ α0 β},
  {{ (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) ∼ P ⤳ Ψ }}da ->
  α0 `notin` ftvar_in_uskl ψ0 -> α0 `notin` ftvar_in_pskl P ->
  {{ (open_uskl_wrt_uskl ψ0 (uskl_var_f β)) ∼ P ⤳ Ψ }}da.
Proof.
  intros * H Hψ HP.
  rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β) Hψ),
    <- (subst_pskl_in_pskl_fresh_eq P (pskl_var_f β) α0 HP).
  exact ((proj2 a_solvetag_sub_eq_rename_var) _ _ _ H α0 β).
Qed.

Lemma a_solvetag_sub_open_rename_l : forall {ψ0 M P Ψ α0 β},
  {{ (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) ≼[ M ] P ⤳ Ψ }}da ->
  α0 `notin` ftvar_in_uskl ψ0 -> α0 `notin` ftvar_in_pskl P ->
  {{ (open_uskl_wrt_uskl ψ0 (uskl_var_f β)) ≼[ M ] P ⤳ Ψ }}da.
Proof.
  intros * H Hψ HP.
  rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β) Hψ),
    <- (subst_pskl_in_pskl_fresh_eq P (pskl_var_f β) α0 HP).
  exact ((proj1 a_solvetag_sub_eq_rename_var) _ _ _ _ H α0 β).
Qed.

Lemma dec_ext_open_rename : forall {P ψ0 Ψ α0 β},
  dec_ext (open_pskl_wrt_pskl P (pskl_var_f α0))
          (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ ->
  α0 `notin` ftvar_in_uskl ψ0 -> α0 `notin` ftvar_in_pskl P ->
  dec_ext (open_pskl_wrt_pskl P (pskl_var_f β))
          (open_uskl_wrt_uskl ψ0 (uskl_var_f β)) Ψ.
Proof.
  intros * H Hψ HP.
  rewrite (subst_pskl_in_pskl_intro α0 P (pskl_var_f β) HP),
    (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β) Hψ).
  exact (dec_ext_rename_var H α0 β).
Qed.

Lemma dec_ext_open_rename_l : forall {P ψ0 Ψ α0 β},
  dec_ext P (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ ->
  α0 `notin` ftvar_in_uskl ψ0 -> α0 `notin` ftvar_in_pskl P ->
  dec_ext P (open_uskl_wrt_uskl ψ0 (uskl_var_f β)) Ψ.
Proof.
  intros * H Hψ HP.
  rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f β) Hψ),
    <- (subst_pskl_in_pskl_fresh_eq P (pskl_var_f β) α0 HP).
  exact (dec_ext_rename_var H α0 β).
Qed.

Lemma dec_ext_is_dskl : forall P ψ Ψ, dec_ext P ψ Ψ -> is_dskl ψ.
Proof.
  intros P ψ Ψ H; induction H; eauto using d_tags_skl_is_dskl with fresco.
Qed.

Lemma solve_eq_guarded_head_l : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> pskl_guarded_head P -> pskl_guarded_head P'.
Proof.
  intros Θ P P0 Ξ P' H; induction H; intros Hg; simpl in Hg;
    try contradiction; simpl; try exact I;

    try solve [ eapply a_guess_mono_head; eassumption ].
  -  exact Hg.
  -  apply IHa_solve_eq; exact Hg.
Qed.

Lemma dec_ext_head_guarded_erase : forall P ψ Ψ,
  dec_ext P ψ Ψ -> pskl_guarded_head P -> guarded_pskl ⌊ ψ ⌋ˢ.
Proof.
  intros P ψ Ψ H Hh; inversion H; subst; simpl in Hh; try contradiction; simpl.
  - auto with fresco.
  - auto with fresco.
  - apply guarded_pskl__arrow;
      apply lc_uskl_to_pskl; apply is_dskl_lc;
      eapply dec_ext_is_dskl; eassumption.
  - auto with fresco.
Qed.

Lemma dec_ext_cover_eq : forall P ψ Ψ' Ψtot,
  dec_ext P ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi, {{ ψ ∼ P ⤳ Ψi }}da /\ Ψtot [<=] Ψ' `union` Ψi.
Proof.
  intros P ψ Ψ' Ψtot H; revert Ψtot; induction H; intros Ψtot Hdt.
  -
    exists empty. split; [ apply a_solvetag_eq__vacuous; fsetdec | ].
    match goal with Hh : d_tags_skl ?β2 ψ |- Ψtot [<=] union ?β2 empty =>
      pose proof (d_tags_skl_det Hh Hdt) as Hd; clear - Hd; fsetdec end.
  -  exists empty. split; [ apply a_solvetag_eq__unit; fsetdec | ].
    inversion Hdt; subst; fsetdec.
  -  exists empty. split; [ apply a_solvetag_eq__var; fsetdec | ].
    inversion Hdt; subst; fsetdec.
  -
    inversion Hdt; subst.
    match goal with
    | Ha : d_tags_skl ?T1 ψ1, Hbb : d_tags_skl ?T2 ψ2, Heq : Ψtot [=] _ |- _ =>
        destruct (IHdec_ext1 T1 Ha) as [Ψi1 [Hs1 Hsub1]];
        destruct (IHdec_ext2 T2 Hbb) as [Ψi2 [Hs2 Hsub2]];
        exists (Ψi1 `union` Ψi2); split;
        [ eapply a_solvetag_eq__arrow; [ exact Hs1 | exact Hs2 | fsetdec ]
        | clear - H1 Heq Hsub1 Hsub2; fsetdec ]
    end.
  -
    inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heq : Ψtot [=] add ?e ?Ψt0,
      IH : forall α, α `notin` ?Lh -> forall Ψ2, _ -> _ |- _ =>
        destruct (atom_fresh (L `union` L1 `union` ftvar_in_uskl ψ0
                    `union` ftvar_in_pskl P0)) as [α0 HX0];
        destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Ψt0
                    (Hb α0 ltac:(clear - HX0; solve_notin_auto)))
                  as [Ψi0 [Hs0 Hsub0]];
        exists (add ε Ψi0); split;
        [ eapply a_solvetag_eq__forall_inh with
            (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P0
                  `union` singleton α0) (Ψ0 := Ψi0); [ | reflexivity ];
          intros β Hβ;
          apply (a_solvetag_eq_open_rename Hs0); clear - HX0; solve_notin_auto
        | clear - Heq Hsub0; fsetdec ]
    end.
  -
    destruct (IHdec_ext Ψtot Hdt) as [Ψi [Hs Hsub]].
    exists Ψi. split;
      [ apply a_solvetag_eq__univ_ghost_r; [ assumption | exact Hs ] | exact Hsub ].
  -
    inversion Hdt; subst.
    match goal with Hd0 : d_tags_skl Ψtot ?p0 |- _ =>
      destruct (IHdec_ext Ψtot Hd0) as [Ψi [Hs Hsub]] end.
    exists Ψi. split; [ apply a_solvetag_eq__univ_ghostg; exact Hs | exact Hsub ].
  -
    inversion Hdt; subst.
    match goal with
    | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Ψt0 _,
      Heqt : Ψtot [=] add ?e ?Ψt0,
      IH : forall α, α `notin` ?Lh -> forall Ψ2, _ -> _ |- _ =>
        destruct (atom_fresh (L `union` L1 `union` ftvar_in_uskl ψ0
                    `union` ftvar_in_pskl P0)) as [α0 HX0];
        destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Ψt0
                    (Hb α0 ltac:(clear - HX0; solve_notin_auto)))
                  as [Ψi0 [Hs0 Hsub0]];
        exists Ψi0; split;
        [ apply a_solvetag_eq__forall_syn with
            (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P0
                  `union` singleton α0);
          intros β Hβ;
          apply (a_solvetag_eq_open_rename_l Hs0); clear - HX0; simpl; solve_notin_auto
        | match goal with Heq0 : Ψ [=] add ε _ |- _ =>
            clear - Heqt Heq0 Hsub0; fsetdec end ]
    end.
  -  exists empty. split;
      [ apply a_solvetag_eq__var; fsetdec
      | inversion Hdt; subst; fsetdec ].
Qed.

Lemma dec_ext_guess_source_size : forall n Θ P Ξ A ψ Ψ',
  size_pskl P <= n ->
  a_guess_mono Θ P Ξ A ->
  pskl_top_guarded P ->
  dec_ext (ptyp_to_pskl A) ψ Ψ' ->
  exists Ψp, dec_ext P ψ Ψp /\ Ψp [<=] Ψ'.
Proof.
  intros n; induction n as [| n IHn];
    intros Θ P Ξ A ψ Ψ' Hsz Hg Htg Hd;
    [ exfalso; pose proof (size_pskl_min P); lia | ].
  pose proof Hg as Hg0.
  destruct Hg as
    [ Θ α Hfr
    | Θ P0 Ξ A0 Hg
    | Θ α
    | Θ
    | Θ P1 P2 Ξ1 Ξ2 A1 A2 Hg1 Hg2
    | Θ P0 Ξ A0 β Hfr Hg ];
    cbn [ptyp_to_pskl] in Hd.
  -
    exists empty. split; [ | clear; fsetdec ].
    inversion Hd; subst;
      apply dec_ext__ghost;
      solve [ apply is_dskl__var | apply d_tags_skl__var; clear; fsetdec ].
  -
    cbn in Htg. destruct Htg as [Hh Ht].
    assert (Hsz0 : size_pskl P0 <= n) by (cbn in Hsz; lia).
    destruct (IHn _ _ _ _ _ _ Hsz0 Hg Ht Hd) as [Ψp [Hdp Hsub]].
    exists Ψp. split; [ | exact Hsub ].
    apply dec_ext__skip_univ_ghost;
      [ eapply dec_ext_head_guarded_erase; [ exact Hdp | exact Hh ]
      | exact Hdp ].
  -  exists Ψ'; split; [ exact Hd | clear; fsetdec ].
  -  exists Ψ'; split; [ exact Hd | clear; fsetdec ].
  -
    cbn in Htg. destruct Htg as [Ht1 Ht2].
    inversion Hd as [ | | | P1' P2' ψ1 ψ2 Ψ0 Ψ1 Ψ2 Hd1 Hd2 Heq
                    | | | | | P0' α0 Ψ0 Heq ]; subst.
    + assert (Hsz1 : size_pskl P1 <= n) by (cbn in Hsz; lia).
      assert (Hsz2 : size_pskl P2 <= n) by (cbn in Hsz; lia).
      destruct (IHn _ _ _ _ _ _ Hsz1 Hg1 Ht1 Hd1) as [Ψp1 [Hp1 Hs1]].
      destruct (IHn _ _ _ _ _ _ Hsz2 Hg2 Ht2 Hd2) as [Ψp2 [Hp2 Hs2]].
      exists (Ψp1 `union` Ψp2). split;
        [ eapply dec_ext__arrow; [ exact Hp1 | exact Hp2 | clear; fsetdec ]
        | clear - Hs1 Hs2 Heq; fsetdec ].
    +
      exists empty; split;
        [ apply dec_ext__flex_forget; clear; fsetdec
        | clear; fsetdec ].
  -
    cbn in Htg.
    inversion Hd as [ | | | | L' Q0 ψ0 ε Ψ0 Hfam
                    | | | | P0' α0 Ψ0 Heq ]; subst.
    +
      destruct (atom_fresh (L' `union` ftvar_in_aenv Θ `union` ftvar_in_pskl P0
                              `union` dom Ξ `union` ftvar_in_uskl ψ0))
        as [α0 Hα0].
      assert (Hα0g : α0 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P0
                        `union` dom Ξ) by (clear - Hα0; fsetdec).
      assert (Hα0L : α0 `notin` L') by (clear - Hα0; fsetdec).
      pose proof (a_guess_mono_open_at Hg0 Hα0g) as Hgα.
      pose proof (Hfam α0 Hα0L) as Hdα.
      rewrite <- ptyp_to_pskl_open in Hdα.
      assert (Hszα : size_pskl (open_pskl_wrt_pskl P0 (pskl_var_f α0)) <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn in Hsz; lia).
      assert (Htgα : pskl_top_guarded (open_pskl_wrt_pskl P0 (pskl_var_f α0)))
        by (apply (proj1 (pskl_top_guarded_open_rec P0 α0 0)); exact Htg).
      destruct (IHn _ _ _ _ _ _ Hszα Hgα Htgα Hdα) as [Ψp [Hdp Hsub]].
      exists Ψp. split; [ | exact Hsub ].
      apply dec_ext__all with
        (L := ftvar_in_pskl P0 `union` ftvar_in_uskl ψ0 `union` singleton α0)
        (ε := ε).
      intros α1 Hα1.
      rewrite (subst_pskl_in_pskl_intro α0 P0 (pskl_var_f α1))
        by (clear - Hα0; fsetdec).
      rewrite (subst_uskl_in_uskl_intro α0 ψ0 (uskl_var_f α1))
        by (clear - Hα0; fsetdec).
      exact (dec_ext_rename_var Hdp α0 α1).
    +
      exists empty; split;
        [ apply dec_ext__flex_forget; clear; fsetdec | clear; fsetdec ].
Qed.

Lemma dec_ext_ghost_free : forall P ψ Ψ,
  dec_ext P ψ Ψ -> pskl_ghost_free P -> uskl_ghost_free ψ.
Proof.
  intros P ψ Ψ H; induction H; intros Hgf; cbn in Hgf;

    try contradiction;

    try solve [ constructor ].
  -
    destruct Hgf as [Hgf1 Hgf2]. constructor; auto.
  -
    match goal with
    | |- uskl_ghost_free (uskl_all_tag _ ?psi0) =>
        pick fresh α0 for (L `union` ftvar_in_uskl psi0);
        apply uskl_ghost_free__all_tag with (L := ftvar_in_uskl psi0);
        intros α1 Hα1;
        rewrite (subst_uskl_in_uskl_intro α0 psi0 (uskl_var_f α1))
          by (clear - Fr; fsetdec);
        apply uskl_ghost_free_subst_var
    end.
    match goal with
    | IH : forall α, α `notin` L -> pskl_ghost_free _ -> _ |- _ =>
        apply (IH α0 ltac:(clear - Fr; solve_notin_auto));
        apply pskl_ghost_free_open_rec; exact Hgf
    end.
Qed.

Corollary dec_ext_guess_source : forall Θ P Ξ A ψ Ψ',
  a_guess_mono Θ P Ξ A ->
  pskl_top_guarded P ->
  dec_ext (ptyp_to_pskl A) ψ Ψ' ->
  exists Ψp, dec_ext P ψ Ψp /\ Ψp [<=] Ψ'.
Proof. intros; eapply dec_ext_guess_source_size; eauto. Qed.

Lemma dec_ext_solvetag_eq_var : forall α P P3 Ψ',
  exists Ψi Ψp, {{ (uskl_var_f α) ∼ P3 ⤳ Ψi }}da /\
    dec_ext P (uskl_var_f α) Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  intros. exists empty, empty. split; [ apply a_solvetag_eq__var; fsetdec | ].
  split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ].
Qed.

Lemma dec_ext_solvetag_sub_var : forall α m P P3 Ψ',
  exists Ψi Ψp, {{ (uskl_var_f α) ≼[ m ] P3 ⤳ Ψi }}da /\
    dec_ext P (uskl_var_f α) Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  intros. exists empty, empty. split; [ apply a_solvetag_sub__var; fsetdec | ].
  split; [ apply dec_ext__flex_forget; fsetdec | fsetdec ].
Qed.

Lemma dec_ext_solve_eq_step_size : forall n Θ P P3 Ξ P' ψ Ψ' Ψtot,
  2 * (size_pskl P + size_pskl P3) <= n ->
  {{ Θ ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, {{ ψ ∼ P3 ⤳ Ψi }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  induction n as [| n IHn];
    [ intros Θ P P3 Ξ P' ψ Ψ' Ψtot Hsz Hs;
      pose proof (size_pskl_min P); pose proof (size_pskl_min P3); lia | ].
  intros Θ P P3 Ξ P' ψ Ψ' Ψtot Hsz Hs Htg; revert ψ Ψ' Ψtot.
  destruct Hs as
    [ Θ
    | Θ α Q
    | Θ α P Ξ A Hflex Hnf Hng Hgu
    | Θ Q
    | Θ P
    | Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' Hp1 Hp2
    | Θ P Q Ξ P' b Hfr Hp
    | Θ P Q Ξ P' Hp
    | Θ P Q Ξ P' b Hfr Hp
    | Θ P Q Ξ P' Hg Hp
    | Θ P Q Ξ P' b Hfr Hp
    | Θ P Q Ξ P' Hg Hp ];
    intros ψ Ψ' Ψtot Hdec Hdt; cbn in Hsz; cbn in Htg.
  -  inversion Hdec; subst.
    + exists empty, empty; split;
        [ apply a_solvetag_eq__unit; fsetdec
        | split; [ apply dec_ext__unit; fsetdec | fsetdec ] ].
    + apply dec_ext_solvetag_eq_var.
  -
    inversion Hdec; subst; apply dec_ext_solvetag_eq_var.
  -
    destruct (dec_ext_guess_source Hgu Htg Hdec) as [Ψp [Hdp Hsub]].
    exists empty, Ψp; split;
      [ apply a_solvetag_eq__flex_r;
          [ eapply dec_ext_ghost_free;
              [ exact Hdec | apply ptyp_to_pskl_ghost_free ]
          | clear; fsetdec ]
      | split; [ exact Hdp | clear - Hsub; fsetdec ] ].
  -
    destruct (dec_ext_cover_eq Hdec Hdt) as [Ψi [Hsi Hsub]].
    exists Ψi, Ψtot; split; [ exact Hsi | split;
      [ apply dec_ext__ghost; exact Hdt
      | exact Hsub ] ].
  -
    exists empty, Ψ'; split;
      [ apply a_solvetag_eq__vacuous; fsetdec
      | split; [ exact Hdec | fsetdec ] ].
  -
    inversion Hdec; subst.
    +
      inversion Hdt; subst.
      assert (Hsz1 : 2 * (size_pskl P1 + size_pskl Q1) <= n) by lia.
      assert (Hsz2 : 2 * (size_pskl P2 + size_pskl Q2) <= n) by lia.
      destruct Htg as [Htg1 Htg2].
      edestruct IHn as [Ψi1 [Ψp1 [Hsa [Hd1 Hu1]]]];
        [ exact Hsz1 | exact Hp1 | exact Htg1 | eassumption | eassumption | ].
      edestruct IHn as [Ψi2 [Ψp2 [Hsb [Hd2 Hu2]]]];
        [ exact Hsz2 | exact Hp2 | exact Htg2 | eassumption | eassumption | ].
      exists (Ψi1 `union` Ψi2), (Ψp1 `union` Ψp2); split;
        [ eapply a_solvetag_eq__arrow; [ exact Hsa | exact Hsb | fsetdec ]
        | split; [ eapply dec_ext__arrow; [ exact Hd1 | exact Hd2 | fsetdec ]
                 | match goal with Heq : Ψ' [=] _ `union` _ |- _ =>
                     clear - Heq Hu1 Hu2; fsetdec end ] ].
    +  apply dec_ext_solvetag_eq_var.
  -
    inversion Hdec; subst.
    +
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                  `union` ftvar_in_pskl P' `union` dom Θ `union` singleton b))
        as [α0 HX0].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b))
        as HupP.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b))
        as HupQ.
      assert (HbPQ : b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        by (clear - Hfr; fsetdec).
      assert (Hα0PQ : α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
                         `union` ftvar_in_pskl P') by (clear - HX0; fsetdec).
      pose proof (@a_solve_eq_move_binder _ _ _ _ _ _ α0 Hp HbPQ Hα0PQ) as Hr.
      assert (Htgα : pskl_top_guarded (open_pskl_wrt_pskl P (pskl_var_f α0)))
        by (apply (proj1 (pskl_top_guarded_open_rec P α0 0)); exact Htg).
      assert (Hszr : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f α0))
                          + size_pskl (open_pskl_wrt_pskl Q (pskl_var_f α0)))
                     <= n)
        by (rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia).
      assert (Hdecr : dec_ext (subst_pskl_in_pskl (pskl_var_f α0) b P')
                        (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ').
      { rewrite subst_pskl_in_pskl_spec.
        apply H0; clear - HX0; fsetdec. }
      destruct (IHn _ _ _ _ _ _ _ _ Hszr Hr Htgα Hdecr
                  (H2 α0 ltac:(clear - HX0; solve_notin_auto)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists (add ε Ψi0), Ψp0; split.
      *
        eapply a_solvetag_eq__forall_inh with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0) (Ψ0 := Ψi0); [ | reflexivity ].
        intros β Hβ.
        apply (a_solvetag_eq_open_rename Hs0); clear - HX0; solve_notin_auto.
      * split.
        --
           apply dec_ext__all with
             (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0).
           intros α2 Hα2.
           apply (dec_ext_open_rename Hd0); clear - HX0; solve_notin_auto.
        -- clear - Hu0; fsetdec.
    +  apply dec_ext_solvetag_eq_var.
  -
    assert (Hsz0 : 2 * (size_pskl P + size_pskl Q) <= n) by lia.
    remember (pskl_univ_ghost P') as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    +
      injection HeqW as HeqP; subst P0.
      match goal with Hin : dec_ext P' _ _ |- _ =>
        destruct (IHn _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hin Hdt)
          as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ apply a_solvetag_eq__univ_ghost_r; [ assumption | exact Hsi ]
        | split; [ apply dec_ext__skip_univ_ghost; [ assumption | exact Hdp ]
                 | exact Hsub ] ].
    +
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with
      | Hin : dec_ext P' ?p0 _, Hd0 : d_tags_skl _ ?p0 |- _ =>
        destruct (IHn _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hin Hd0)
          as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ apply a_solvetag_eq__univ_ghostg; exact Hsi
        | split; [ apply dec_ext__dot_univ_ghost; exact Hdp | exact Hsub ] ].
    +
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Wt0
                      (Hb α0 ltac:(clear - HX0; solve_notin_auto)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]]
      end.
      exists Ψi0, (add ε Ψp0); split.
      * apply a_solvetag_eq__forall_syn with
          (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0).
        intros β Hβ.
        apply (a_solvetag_eq_open_rename_l Hs0); clear - HX0; simpl; solve_notin_auto.
      * split.
        -- eapply dec_ext__absorb_all with
             (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0) (Ψ0 := Ψp0); [ | reflexivity ].
           intros α2 Hα2.
           apply (dec_ext_open_rename_l Hd0); clear - HX0; simpl; solve_notin_auto.
        -- clear - HeqAbs Hu0; fsetdec.
    +  apply dec_ext_solvetag_eq_var.
  -
    inversion Hdec; subst.
    +
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                  `union` ftvar_in_pskl P' `union` dom Θ `union` singleton b))
        as [α0 HX0].

      assert (HbPQ : b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        by (clear - Hfr; fsetdec).
      assert (Hα0PQ : α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
                         `union` ftvar_in_pskl P') by (clear - HX0; fsetdec).
      pose proof (@a_solve_eq_move_binder_univ_ghost_l _ _ _ _ _ _ α0 Hp HbPQ Hα0PQ)
        as Hr.
      assert (Hszr : 2 * (size_pskl (pskl_univ_ghost P)
                          + size_pskl (open_pskl_wrt_pskl Q (pskl_var_f α0)))
                     <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
      assert (Hdecr : dec_ext (subst_pskl_in_pskl (pskl_var_f α0) b P')
                        (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ').
      { rewrite subst_pskl_in_pskl_spec.
        apply H0; clear - HX0; fsetdec. }
      destruct (IHn _ _ _ _ _ _ _ _ Hszr Hr Htg Hdecr
                  (H2 α0 ltac:(clear - HX0; solve_notin_auto)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists (add ε Ψi0), (add ε Ψp0); split.
      * eapply a_solvetag_eq__forall_inh with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0) (Ψ0 := Ψi0); [ | reflexivity ].
        intros β Hβ.
        apply (a_solvetag_eq_open_rename Hs0); clear - HX0; solve_notin_auto.
      * split.
        -- eapply dec_ext__absorb_all with
             (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0) (Ψ0 := Ψp0); [ | reflexivity ].
           intros α2 Hα2.
           apply (dec_ext_open_rename_l Hd0); clear - HX0; simpl; solve_notin_auto.
        -- clear - Hu0; fsetdec.
    +  apply dec_ext_solvetag_eq_var.
  -
    assert (Hsz0 : 2 * (size_pskl P + size_pskl Q) <= n) by lia.
    destruct (IHn _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hdec Hdt)
      as [Ψi [Ψp [Hsi [Hdp Hsub]]]].
    exists Ψi, Ψp; split;
      [ exact Hsi
      | split;
        [ apply dec_ext__skip_univ_ghost;
            [
              eapply dec_ext_head_guarded_erase;
                [ exact Hdp | exact (proj1 Htg) ]
            | exact Hdp ]
        | exact Hsub ] ].
  -
    inversion Hdec; subst.
    +
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl Q
                  `union` ftvar_in_pskl P' `union` dom Θ `union` singleton b))
        as [α0 HX0].

      assert (HbPQ : b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        by (clear - Hfr; fsetdec).
      assert (Hα0PQ : α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
                         `union` ftvar_in_pskl P') by (clear - HX0; fsetdec).
      pose proof (@a_solve_eq_move_binder_univ_ghost_r _ _ _ _ _ _ α0 Hp HbPQ Hα0PQ)
        as Hr.
      assert (Htgα : pskl_top_guarded (open_pskl_wrt_pskl P (pskl_var_f α0)))
        by (apply (proj1 (pskl_top_guarded_open_rec P α0 0)); exact Htg).
      assert (Hszr : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f α0))
                          + size_pskl (pskl_univ_ghost Q)) <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
      assert (Hdecr : dec_ext (subst_pskl_in_pskl (pskl_var_f α0) b P')
                        (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ').
      { rewrite subst_pskl_in_pskl_spec.
        apply H0; clear - HX0; fsetdec. }
      destruct (IHn _ _ _ _ _ _ _ _ Hszr Hr Htgα Hdecr
                  (H2 α0 ltac:(clear - HX0; solve_notin_auto)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists Ψi0, Ψp0; split.
      * apply a_solvetag_eq__forall_syn with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q
                `union` singleton α0).
        intros β Hβ.
        apply (a_solvetag_eq_open_rename_l Hs0); clear - HX0; simpl; solve_notin_auto.
      * split.
        -- apply dec_ext__all with
             (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0).
           intros α2 Hα2.
           apply (dec_ext_open_rename Hd0); clear - HX0; solve_notin_auto.
        -- clear - Hu0; fsetdec.
    +  apply dec_ext_solvetag_eq_var.
  -
    assert (Hsz0 : 2 * (size_pskl P + size_pskl Q) <= n) by lia.
    destruct (IHn _ _ _ _ _ _ _ _ Hsz0 Hp Htg Hdec Hdt)
      as [Ψi [Ψp [Hsi [Hdp Hsub]]]].
    exists Ψi, Ψp; split;
      [ apply a_solvetag_eq__univ_ghost_r;
          [ eapply dec_ext_head_guarded_erase;
              [ exact Hdec | eapply solve_eq_guarded_head_l;
                [ eassumption | apply guarded_pskl_head; eassumption ] ]
          | exact Hsi ]
      | split; [ exact Hdp | exact Hsub ] ].
Qed.

Lemma dec_ext_solve_eq_step : forall Θ P P3 Ξ P' ψ Ψ' Ψtot,
  {{ Θ ⊢ₑ P ∼ P3 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, {{ ψ ∼ P3 ⤳ Ψi }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  intros Θ P P3 Ξ P' ψ Ψ' Ψtot Hs Htg Hdec Hdt.
  exact (dec_ext_solve_eq_step_size
           (n := 2 * (size_pskl P + size_pskl P3))
           (le_n _) Hs Htg Hdec Hdt).
Qed.

Lemma dec_ext_ghost_tags : forall ψ Ψp Ψtot,
  dec_ext pskl_ghost ψ Ψp -> d_tags_skl Ψtot ψ -> Ψp [=] Ψtot.
Proof.
  intros ψ Ψp Ψtot H Hdt; inversion H; subst.
  - eapply d_tags_skl_det; eassumption.
  - inversion Hdt; subst; fsetdec.
Qed.

Lemma dec_ext_guarded_uskl : forall P ψ Ψ,
  dec_ext P ψ Ψ -> guarded_pskl P -> is_dskl ψ -> guarded_uskl ψ.
Proof.
  intros P ψ Ψ H Hg Hik; inversion H; subst; try (inversion Hg; fail).
  - auto with fresco.
  - auto with fresco.
  - apply is_dskl_lc in Hik; inversion Hik; subst; auto with fresco.
  - auto with fresco.
Qed.

Lemma dec_ext_solve_sub_step_size : forall n Θ m P P3 Ξ P' ψ Ψ' Ψtot,
  2 * (size_pskl P + size_pskl P3) <= n ->
  {{ Θ ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, {{ ψ ≼[ m ] P3 ⤳ Ψi }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  induction n as [| n IHn];
    [ intros Θ m P P3 Ξ P' ψ Ψ' Ψtot Hsz Hs;
      pose proof (size_pskl_min P); pose proof (size_pskl_min P3); lia | ].
  intros Θ m P P3 Ξ P' ψ Ψ' Ψtot Hsz Hs Htg; revert ψ Ψ' Ψtot.
  destruct Hs as
    [ Θ m α Q
    | Θ m P Q Ξ P' b Hfr Hp
    | Θ m P Q Ξ P' Hp
    | Θ m P Hoff
    | Θ P Q Ξ P' Hgf0 H H0 H1
    | Θ A B Ξ P' b Hgf0 Hoff Hfr Hp
    | Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2' H H0
    | Θ m Q1 Q2 Ξ1 Ξ2 P1' P2' H H0
    | Θ B Hgf0 H ];
    intros ψ Ψ' Ψtot Hdec Hdt; cbn in Hsz; cbn in Htg.
  -
    inversion Hdec; subst; apply dec_ext_solvetag_sub_var.
  -
    inversion Hdec; subst.
    +
      inversion Hdt; subst.
      destruct (atom_fresh (L `union` L0 `union` ftvar_in_uskl ψ0
                  `union` ftvar_in_pskl P `union` ftvar_in_pskl P'
                  `union` ftvar_in_pskl Q `union` dom Θ `union` singleton b))
        as [α0 HX0].

      assert (HbPQ : b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q)
        by (clear - Hfr; fsetdec).
      assert (Hα0PQ : α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
                         `union` ftvar_in_pskl P') by (clear - HX0; fsetdec).
      pose proof (@a_solve_sub_move_binder_l _ _ _ _ _ _ _ α0 Hp HbPQ Hα0PQ)
        as Hr.
      assert (Htgα : pskl_top_guarded (open_pskl_wrt_pskl P (pskl_var_f α0)))
        by (apply (proj1 (pskl_top_guarded_open_rec P α0 0)); exact Htg).
      assert (Hszr : 2 * (size_pskl (open_pskl_wrt_pskl P (pskl_var_f α0))
                          + size_pskl Q) <= n)
        by (rewrite size_pskl_open_pskl_wrt_pskl_var; cbn; lia).
      assert (Hdecr : dec_ext (subst_pskl_in_pskl (pskl_var_f α0) b P')
                        (open_uskl_wrt_uskl ψ0 (uskl_var_f α0)) Ψ').
      { rewrite subst_pskl_in_pskl_spec.
        apply H0; clear - HX0; fsetdec. }
      destruct (IHn _ _ _ _ _ _ _ _ _ Hszr Hr Htgα Hdecr
                  (H2 α0 ltac:(clear - HX0; solve_notin_auto)))
                as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]].
      exists Ψi0, Ψp0; split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` singleton α0). intros β Hβ.
        apply (a_solvetag_sub_open_rename_l Hs0); clear - HX0; simpl; solve_notin_auto.
      * split.
        -- apply dec_ext__all with
             (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl P `union` singleton α0).
           intros α2 Hα2.
           apply (dec_ext_open_rename Hd0); clear - HX0; solve_notin_auto.
        -- clear - Hu0; fsetdec.
    +  apply dec_ext_solvetag_sub_var.
  -
    assert (Hsz0 : 2 * (size_pskl P + size_pskl Q) <= n) by lia.
    remember (pskl_univ_ghost P') as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    +
      injection HeqW as HeqP; subst P0.
      match goal with Hin : dec_ext P' _ _ |- _ =>
        destruct (IHn _ _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hin Hdt)
          as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ exact Hsi
        | split; [ apply dec_ext__skip_univ_ghost; [ assumption | exact Hdp ]
                 | exact Hsub ] ].
    +
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with
      | Hin : dec_ext P' ?p0 _, Hd0 : d_tags_skl _ ?p0 |- _ =>
        destruct (IHn _ _ _ _ _ _ _ _ _ Hsz0 Hp (proj2 Htg) Hin Hd0)
          as [Ψi [Ψp [Hsi [Hdp Hsub]]]] end.
      exists Ψi, Ψp; split;
        [ apply a_solvetag_sub__univ_ghost_lg; exact Hsi
        | split; [ apply dec_ext__dot_univ_ghost; exact Hdp | exact Hsub ] ].
    +
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl P `union` ftvar_in_pskl Q)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Wt0
                      (Hb α0 ltac:(clear - HX0; solve_notin_auto)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]]
      end.
      exists Ψi0, (add ε Ψp0); split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q `union` singleton α0).
        intros β Hβ.
        apply (a_solvetag_sub_open_rename_l Hs0); clear - HX0; simpl; solve_notin_auto.
      * split.
        -- eapply dec_ext__absorb_all with
             (L := L `union` ftvar_in_uskl ψ0 `union` ftvar_in_pskl P
                   `union` singleton α0) (Ψ0 := Ψp0); [ | reflexivity ].
           intros α2 Hα2.
           apply (dec_ext_open_rename_l Hd0); clear - HX0; simpl; solve_notin_auto.
        -- clear - HeqAbs Hu0; fsetdec.
    +  apply dec_ext_solvetag_sub_var.
  -
    exists empty, Ψ'; split;
      [ apply a_solvetag_sub__vacuous; fsetdec
      | split; [ exact Hdec | fsetdec ] ].
  -
    edestruct dec_ext_solve_eq_step as [Ψi [Ψp [Hste [Hdp Hup]]]];
      [ exact H1 | exact Htg | exact Hdec | exact Hdt | ].
    exists Ψi, Ψp; split;
      [ apply a_solvetag_sub__check;
          [ assumption
          | eapply dec_ext_guarded_uskl;
              [ exact Hdp | assumption | eapply d_tags_skl_is_dskl; exact Hdt ]
          | assumption
          | exact Hste ]
      | split; [ exact Hdp | exact Hup ] ].
  -
    assert (Hsz0 : 2 * (size_pskl A
                        + size_pskl (open_pskl_wrt_pskl B (pskl_var_f b)))
                   <= n)
      by (rewrite size_pskl_open_pskl_wrt_pskl_var; lia).
    destruct (IHn _ _ _ _ _ _ _ _ _ Hsz0 Hp Htg Hdec Hdt)
              as [Ψi0 [Ψp0 [Hst0 [Hd0 Hu0]]]].
    exists Ψi0, Ψp0; split.
    + apply a_solvetag_sub__forall_r with
        (L := ftvar_in_pskl B `union` singleton b);
        [ assumption | ].
      intros β Hβ.
      rewrite (subst_pskl_in_pskl_intro b B (pskl_var_f β)
                 ltac:(clear - Hfr; solve_notin_auto)).
      exact ((proj1 a_solvetag_sub_eq_target_rename) _ _ _ _ Hst0 b β).
    + split; [ exact Hd0 | exact Hu0 ].
  -
    inversion Hdec; subst.
    +
      inversion Hdt; subst.
      destruct Htg as [Htg1 Htg2].
      edestruct dec_ext_solve_eq_step as [Ψi1 [Ψp1 [Hst1 [Hd1 Hu1]]]];
        [ exact H | exact Htg1 | eassumption | eassumption | ].
      assert (Hsz2 : 2 * (size_pskl P2 + size_pskl Q2) <= n) by lia.
      edestruct IHn as [Ψi2 [Ψp2 [Hst2 [Hd2 Hu2]]]];
        [ exact Hsz2 | exact H0 | exact Htg2 | eassumption | eassumption | ].
      exists (Ψi1 `union` Ψi2), (Ψp1 `union` Ψp2); split;
        [ eapply a_solvetag_sub__arrow; [ exact Hst1 | exact Hst2 | reflexivity ]
        | split; [ eapply dec_ext__arrow; [ exact Hd1 | exact Hd2 | reflexivity ]
                 | match goal with Heq : Ψ' [=] _ `union` _ |- _ =>
                     clear - Heq Hu1 Hu2; fsetdec end ] ].
    +  apply dec_ext_solvetag_sub_var.
  -
    assert (Hsz2 : 2 * (size_pskl pskl_ghost + size_pskl Q2) <= n)
      by (cbn; lia).
    remember (pskl_univ_ghost (pskl_arrow P1' P2')) as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    +
      injection HeqW as HeqP; subst P0.
      match goal with Hde : dec_ext (pskl_arrow P1' P2') _ _ |- _ =>
        inversion Hde; subst end.
      *
        inversion Hdt; subst.

        edestruct dec_ext_solve_eq_step as [Ψi1 [Ψp1 [Hst1 [Hd1 Hu1]]]];
          [ exact H | exact I | eassumption | eassumption | ].
        edestruct IHn as [Ψi2 [Ψp2 [Hst2 [Hd2 Hu2]]]];
          [ exact Hsz2 | exact H0 | exact I | eassumption | eassumption | ].
        match goal with Ha : d_tags_skl _ ψ1, Hb : d_tags_skl _ ψ2 |- _ =>
          pose proof (dec_ext_ghost_tags Hd1 Ha) as He1;
          pose proof (dec_ext_ghost_tags Hd2 Hb) as He2 end.
        exists (Ψi1 `union` Ψi2), Ψtot; split;
          [ eapply a_solvetag_sub__arrow; [ exact Hst1 | exact Hst2 | reflexivity ]
          | split;
            [ apply dec_ext__ghost; exact Hdt
            | match goal with Heqt : Ψtot [=] _ |- Ψtot [<=] ?β2 `union` _ =>
                match goal with Heqp : β2 [=] _ |- _ =>
                  clear - Heqt Heqp He1 He2 Hu1 Hu2; fsetdec end end ] ].
      *
        exists empty, empty; split;
          [ apply a_solvetag_sub__var; fsetdec
          | split; [ apply dec_ext__ghost; inversion Hdt; subst; apply d_tags_skl__var; fsetdec
                   | inversion Hdt; subst; fsetdec ] ].
    +
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with Hde : dec_ext (pskl_arrow P1' P2') ?p0 _,
                      Hd0t : d_tags_skl Ψtot ?p0 |- _ =>
        inversion Hde; subst end.
      *
        match goal with Hd0t : d_tags_skl Ψtot (uskl_arrow _ _) |- _ =>
          inversion Hd0t; subst end.

        edestruct dec_ext_solve_eq_step as [Ψi1 [Ψp1 [Hst1 [Hd1 Hu1]]]];
          [ exact H | exact I | eassumption | eassumption | ].
        edestruct IHn as [Ψi2 [Ψp2 [Hst2 [Hd2 Hu2]]]];
          [ exact Hsz2 | exact H0 | exact I | eassumption | eassumption | ].
        match goal with Ha : d_tags_skl _ ψ1, Hb : d_tags_skl _ ψ2 |- _ =>
          pose proof (dec_ext_ghost_tags Hd1 Ha) as He1;
          pose proof (dec_ext_ghost_tags Hd2 Hb) as He2 end.
        exists (Ψi1 `union` Ψi2), Ψtot; split;
          [ apply a_solvetag_sub__univ_ghost_lg;
            eapply a_solvetag_sub__arrow; [ exact Hst1 | exact Hst2 | reflexivity ]
          | split;
            [ apply dec_ext__ghost; exact Hdt
            | match goal with Heqt : Ψtot [=] _ |- Ψtot [<=] ?β2 `union` _ =>
                match goal with Heqp : β2 [=] _ |- _ =>
                  clear - Heqt Heqp He1 He2 Hu1 Hu2; fsetdec end end ] ].
      *
        exists empty, empty; split;
          [ apply a_solvetag_sub__univ_ghost_lg; apply a_solvetag_sub__var; fsetdec
          | split; [ apply dec_ext__ghost; apply d_tags_skl__dot_univ_ghost; apply d_tags_skl__var; fsetdec
                   | fsetdec ] ].
    +
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl Q1 `union` ftvar_in_pskl Q2)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Wt0
                      (Hb α0 ltac:(clear - HX0; solve_notin_auto)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]];
          pose proof (dec_ext_ghost_tags Hd0 (Hb α0 ltac:(clear - HX0; solve_notin_auto)))
            as He0
      end.
      exists Ψi0, Ψtot; split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl Q1 `union` ftvar_in_pskl Q2
                `union` singleton α0).
        intros β Hβ.
        apply (a_solvetag_sub_open_rename_l Hs0); clear - HX0; simpl; solve_notin_auto.
      * split;
          [ apply dec_ext__ghost; exact Hdt
          | match goal with Heqt : Ψtot [=] add _ _ |- _ =>
              clear - Heqt HeqAbs He0 Hu0; fsetdec end ].
    +
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__ghost; inversion Hdt; subst; apply d_tags_skl__var; fsetdec
                 | inversion Hdt; subst; fsetdec ] ].
  -
    remember (pskl_univ_ghost B) as β2 eqn:HeqW.
    revert Ψtot Hdt HeqW; induction Hdec; intros Ψtot Hdt HeqW;
      try discriminate HeqW.
    +
      injection HeqW as HeqP; subst P0.
      match goal with Hde : dec_ext B _ _ |- _ =>
        destruct (dec_ext_cover_eq Hde Hdt) as [Ψi [Hsi Hsub]];
        exists Ψi, Ψtot; split;
          [ apply a_solvetag_sub__check;
              [ exact Hgf0
              | eapply dec_ext_guarded_uskl;
                  [ exact Hde | exact H | eapply d_tags_skl_is_dskl; exact Hdt ]
              | exact H | exact Hsi ]
          | split; [ apply dec_ext__ghost; exact Hdt
                   | exact Hsub ] ]
      end.
    +
      injection HeqW as HeqP; subst P0.
      inversion Hdt; subst.
      match goal with Hde : dec_ext B ?p0 _, Hd0 : d_tags_skl Ψtot ?p0 |- _ =>
        destruct (dec_ext_cover_eq Hde Hd0) as [Ψi [Hsi Hsub]];
        exists Ψi, Ψtot; split;
          [ apply a_solvetag_sub__univ_ghost_lg; apply a_solvetag_sub__check;
              [ exact Hgf0
              | eapply dec_ext_guarded_uskl;
                  [ exact Hde | exact H | eapply d_tags_skl_is_dskl; exact Hd0 ]
              | exact H | exact Hsi ]
          | split; [ apply dec_ext__ghost; exact Hdt
                   | exact Hsub ] ]
      end.
    +
      injection HeqW as HeqP; subst P0.
      match goal with HeqA : ?a [=] add ε ?b |- _ => rename HeqA into HeqAbs end.
      inversion Hdt; subst.
      match goal with
      | Hb : forall α, α `notin` ?L1 -> d_tags_skl ?Wt0 (open_uskl_wrt_uskl ψ0 _),
        IH : forall α, α `notin` ?Lih -> forall a, d_tags_skl a _ -> _ = _ -> _
        |- _ =>
          destruct (atom_fresh (L `union` L1 `union` Lih `union` ftvar_in_uskl ψ0
                      `union` ftvar_in_pskl B)) as [α0 HX0];
          destruct (IH α0 ltac:(clear - HX0; solve_notin_auto) Wt0
                      (Hb α0 ltac:(clear - HX0; solve_notin_auto)) eq_refl)
                    as [Ψi0 [Ψp0 [Hs0 [Hd0 Hu0]]]];
          pose proof (dec_ext_ghost_tags Hd0 (Hb α0 ltac:(clear - HX0; solve_notin_auto)))
            as He0
      end.
      exists Ψi0, Ψtot; split.
      * apply a_solvetag_sub__forall_l with
          (L := ftvar_in_uskl ψ0 `union` ftvar_in_pskl B `union` singleton α0).
        intros β Hβ.
        apply (a_solvetag_sub_open_rename_l Hs0); clear - HX0; simpl; solve_notin_auto.
      * split;
          [ apply dec_ext__ghost; exact Hdt
          | match goal with Heqt : Ψtot [=] add _ _ |- _ =>
              clear - Heqt HeqAbs He0 Hu0; fsetdec end ].
    +
      exists empty, empty; split;
        [ apply a_solvetag_sub__var; fsetdec
        | split; [ apply dec_ext__ghost; inversion Hdt; subst; apply d_tags_skl__var; fsetdec
                 | inversion Hdt; subst; fsetdec ] ].
Qed.

Lemma dec_ext_solve_sub_step : forall Θ m P P3 Ξ P' ψ Ψ' Ψtot,
  {{ Θ ⊢ₛ P ≼[ m ] P3 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P ->
  dec_ext P' ψ Ψ' -> d_tags_skl Ψtot ψ ->
  exists Ψi Ψp, {{ ψ ≼[ m ] P3 ⤳ Ψi }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψ' `union` Ψi.
Proof.
  intros Θ m P P3 Ξ P' ψ Ψ' Ψtot Hs Htg Hdec Hdt.
  exact (dec_ext_solve_sub_step_size
           (n := 2 * (size_pskl P + size_pskl P3))
           (le_n _) Hs Htg Hdec Hdt).
Qed.

Lemma solve_sub_guarded_head_l : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> pskl_guarded_head P -> pskl_guarded_head P'.
Proof.
  intros Θ m P P0 Ξ P' Hs; induction Hs; intros Hg; simpl in Hg;
    try contradiction; simpl; try exact I.
  -  exact Hg.
  -  eapply solve_eq_guarded_head_l; eassumption.
  -
    apply IHHs; exact Hg.
Qed.

Lemma solve_eq_top_guarded : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P -> pskl_top_guarded P0 -> pskl_top_guarded P'.
Proof.
  intros Θ P P0 Ξ P' H; induction H; intros Hnt Hgf; simpl in Hnt, Hgf; simpl.
  -  exact I.
  -  exact I.
  -
    apply pskl_ghost_free_top_guarded, ptyp_to_pskl_ghost_free.
  -  exact Hgf.
  -  exact Hnt.
  -  destruct Hnt as [Hnt1 Hnt2]; destruct Hgf as [Hgf1 Hgf2];
      split; [ apply IHa_solve_eq1 | apply IHa_solve_eq2 ]; assumption.
  -
    apply pskl_top_guarded_close.
    apply IHa_solve_eq;
      [ apply (proj1 (pskl_top_guarded_open_rec P _ 0)); exact Hnt
      | apply (proj1 (pskl_top_guarded_open_rec Q _ 0)); exact Hgf ].
  -
    destruct Hnt as [HgP HtP]; destruct Hgf as [HgQ HtQ].
    split; [ eapply solve_eq_guarded_head_l; [ eassumption | exact HgP ]
           | apply IHa_solve_eq; assumption ].
  -
    destruct Hnt as [HgP HtP].
    apply pskl_top_guarded_close.
    apply IHa_solve_eq;
      [ simpl; split; assumption
      | apply (proj1 (pskl_top_guarded_open_rec Q _ 0)); exact Hgf ].
  -
    destruct Hnt as [HgP HtP]; apply IHa_solve_eq; assumption.
  -
    destruct Hgf as [HgQ HtQ].
    apply pskl_top_guarded_close.
    apply IHa_solve_eq;
      [ apply (proj1 (pskl_top_guarded_open_rec P _ 0)); exact Hnt
      | simpl; split; assumption ].
  -
    destruct Hgf as [HgQ HtQ]; apply IHa_solve_eq; assumption.
Qed.

Lemma solve_sub_top_guarded_tg : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P -> pskl_top_guarded P0 -> pskl_top_guarded P'.
Proof.
  intros Θ m P P0 Ξ P' Hs; induction Hs; intros Hnt Hgf; simpl in Hnt, Hgf; simpl.
  -  exact I.
  -
    apply pskl_top_guarded_close.
    apply IHHs;
      [ apply (proj1 (pskl_top_guarded_open_rec P _ 0)); exact Hnt | exact Hgf ].
  -
    destruct Hnt as [HgP HtP].
    split; [ eapply solve_sub_guarded_head_l; [ eassumption | exact HgP ]
           | apply IHHs; assumption ].
  -  exact Hnt.
  -
    eapply solve_eq_top_guarded; [ eassumption | exact Hnt | exact Hgf ].
  -
    apply IHHs;
      [ exact Hnt | apply (proj1 (pskl_top_guarded_open_rec B _ 0)); exact Hgf ].
  -
    destruct Hnt as [Hnt1 Hnt2]; destruct Hgf as [Hgf1 Hgf2].
    split;
      [ eapply solve_eq_top_guarded; [ eassumption | exact Hnt1 | exact Hgf1 ]
      | apply IHHs; assumption ].
  -
    destruct Hgf as [Hgf1 Hgf2].
    split; [ exact I | split;
      [ eapply solve_eq_top_guarded; [ eassumption | exact I | exact Hgf1 ]
      | apply IHHs; [ exact I | exact Hgf2 ] ] ].
  -
    split; [ apply guarded_pskl_head; assumption | exact Hgf ].
Qed.

Definition a_cstr_tg (c : a_cstr) : Prop :=
  match c with
  | a_cstr_sub _ Q => pskl_top_guarded Q
  | a_cstr_eq Q => pskl_top_guarded Q
  end.

Lemma a_look_top_guarded :
  (forall Θ α m P P0 Ξ 𝒞, {{ Θ ⊢ P ≼[ α , m ] P0 ⤳ Ξ ⨾ 𝒞 }}a ->
     pskl_top_guarded P0 -> List.Forall a_cstr_tg 𝒞) /\
  (forall Θ α P P0 Ξ 𝒞, {{ Θ ⊢ P ∼[ α ] P0 ⤳ Ξ ⨾ 𝒞 }}a ->
     pskl_top_guarded P0 -> List.Forall a_cstr_tg 𝒞).
Proof.
  apply a_looksub_lookeq_mutind; intros; simpl in *;
    repeat match goal with
           | H : _ /\ _ |- _ =>
               let Hg := fresh "Hg" in let Ht := fresh "Ht" in destruct H as [Hg Ht]
           end;
    try (apply List.Forall_nil; fail);
    try (apply List.Forall_app; split; [ apply H | apply H0 ]; tauto);
    try (repeat apply List.Forall_cons;
         solve [ assumption | exact I | apply List.Forall_nil ]);
    try (apply H; assumption);

    try (apply H;
         solve [ assumption
               | apply (proj1 (pskl_top_guarded_open_rec _ _ _)); assumption
               | simpl; split; assumption ]).
Qed.

Lemma solve_cstr_top_guarded_tg : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a -> pskl_top_guarded P -> List.Forall a_cstr_tg 𝒞 ->
  pskl_top_guarded P'.
Proof.
  intros Θ 𝒞 P Ξ P' Hs; induction Hs; intros Hnt Hntc.
  - exact Hnt.
  - inversion Hntc as [ | ? ? Hnt0 ]; subst; simpl in Hnt0.
    eapply solve_sub_top_guarded_tg; [ exact H | exact Hnt | exact Hnt0 ].
  - inversion Hntc as [ | ? ? Hnt0 HntC ]; subst; simpl in Hnt0.
    apply IHHs;
      [ eapply solve_eq_top_guarded; [ exact H | exact Hnt | exact Hnt0 ] | exact HntC ].
Qed.

Lemma solve_cstr_decorate : forall Θ 𝒞 P Ξ P' ψ Ψpost Ψtot,
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  pskl_top_guarded P -> List.Forall a_cstr_tg 𝒞 ->
  dec_ext P' ψ Ψpost -> d_tags_skl Ψtot ψ ->
  exists Ψc Ψp, {{ 𝒞 ⊩ ψ ⤳ Ψc }}da /\ dec_ext P ψ Ψp /\ Ψp [<=] Ψpost `union` Ψc.
Proof.
  intros Θ 𝒞 P Ξ P' ψ Ψpost Ψtot Hsolve Htg Htgc Hdec Hdt;
    revert Ψpost Hdec; revert Htg Htgc;
    induction Hsolve; intros Htg Htgc Ψpost Hdec.
  -  exists empty, Ψpost; split;
      [ apply a_solvetag__empty; fsetdec | split; [ exact Hdec | fsetdec ] ].
  -
    destruct (dec_ext_solve_sub_step H Htg Hdec Hdt)
      as [Ψi [Ψp [Hs [Hd Hu]]]].
    exists Ψi, Ψp; split;
      [ apply a_solvetag__sub; exact Hs | split; [ exact Hd | exact Hu ] ].
  -
    inversion Htgc as [ | ? ? Htg0 HtgC ]; subst; simpl in Htg0.
    assert (Htg'' : pskl_top_guarded P'')
      by (eapply solve_eq_top_guarded; [ exact H | exact Htg | exact Htg0 ]).
    destruct (IHHsolve Htg'' HtgC Ψpost Hdec)
      as [Ψc' [Ψp'' [Hstc [Hd'' Hu'']]]].
    destruct (dec_ext_solve_eq_step H Htg Hd'' Hdt)
      as [Ψi [Ψp [Hste [Hd Hu]]]].
    exists (Ψi `union` Ψc'), Ψp; split;
      [ eapply a_solvetag__eq; [ exact Hste | exact Hstc | reflexivity ]
      | split; [ exact Hd | clear - Hu Hu''; fsetdec ] ].
Qed.

Lemma a_extract_decorate : forall Θ0 NM αv M P P0 Ξ P1,
  {{ Θ0 ⊢ P ⊳[ NM , αv , M ] P0 ⤳ Ξ ↪ P1 }}a ->
  pskl_top_guarded P0 ->
  forall Ψa ψa,
    a_tags_sort NM Ψa ψa ->
    ⌊ ψa ⌋ˢ = P1 ->
    exists Ξc 𝒞,
      {{ Θ0 ⊢ P ≼[ αv , M ] P0 ⤳ Ξc ⨾ 𝒞 }}a /\
      {{ 𝒞 ⊩ ψa ⤳ Ψa }}da.
Proof.
  intros Θ0 NM αv M P P0 Ξ P1 Hext Htg0 Ψa ψa Htags Hera.
  inversion Hext; subst.

  eexists; eexists; split; [ exact H | ].
  assert (Hda : d_tags_skl Ψa ψa) by (inversion Htags; assumption).
  assert (Htgc : List.Forall a_cstr_tg C)
    by (eapply (proj1 a_look_top_guarded); [ exact H | exact Htg0 ]).
  assert (HtgQ : pskl_top_guarded Q)
    by (eapply solve_cstr_top_guarded_tg;
        [ exact H0 | exact I | exact Htgc ]).
  assert (Htg : NM = a_sub_mode_ty -> pskl_top_guarded Q)
    by (intros _; exact HtgQ).
  assert (Hanchor : dec_ext Q ψa empty)
    by (eapply dec_ext_guess_anchor;
        [ exact H1 | exact Htg | exact Htags | reflexivity ]).
  destruct (solve_cstr_decorate H0 I Htgc Hanchor Hda)
    as [Ψc [Ψp [Hstag [Hhole Hsub]]]].

  assert (Hsnd : Ψc [<=] Ψa) by (eapply a_solvetag_sound; [ exact Hstag | exact Hda ]).
  inversion Hhole; subst.
  -
    match goal with Hdtag : d_tags_skl _ ψa |- _ =>
      pose proof (d_tags_skl_det Hda Hdtag) as Hdet end.
    eapply a_solvetag_psi_cong; [ exact Hstag | clear - Hsub Hsnd Hdet; fsetdec ].
  -
    eapply a_solvetag_psi_cong; [ exact Hstag | ].
    inversion Hda; subst;
      match goal with He : Ψa [=] empty |- _ => clear - Hsnd He; fsetdec end.
Qed.

Scheme a_sub_mut := Induction for a_sub Sort Prop
  with a_sub_flex_mut := Induction for a_sub_flex Sort Prop.
Combined Scheme a_sub_sub_flex_mutind from a_sub_mut, a_sub_flex_mut.

Definition sub_decorate_concl NM M P0 Θ0 P Q Θ1 : Prop :=
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) M) ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P0) ->
  {{ Θ0 ⊢[ NM | M | P0 | empty ] (pskl_to_uskl P) ⩽ Q ⊣ Θ1 }}da.

Definition sub_flex_decorate_concl NM M P0 Θ0 Ξw αf Q Θ1 : Prop :=
  a_decls Ξw ->
  {{ ⊢ (Ξw ++ Θ0) }}a ->
  {{ (Ξw ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a ->
  a_binds_tvar αf (Ξw ++ Θ0) ->
  (NM = a_sub_mode_sk -> mod_comp_sk (pskl_to_bskl_inh P0) (mode_fn M)) ->
  (NM = a_sub_mode_ty -> pskl_top_guarded P0) ->
  a_subtag_flex NM M P0 Θ0 Ξw αf Q Θ1.

Theorem a_sub_decorate_bundle :
  (forall NM M P0 Θ0 P P' Θ1,
     a_sub NM M P0 Θ0 P P' Θ1 ->
     sub_decorate_concl NM M P0 Θ0 P P' Θ1) /\
  (forall NM M P0 Θ0 Ξw αf P' Θ1,
     a_sub_flex NM M P0 Θ0 Ξw αf P' Θ1 ->
     sub_flex_decorate_concl NM M P0 Θ0 Ξw αf P' Θ1).
Proof.
  apply a_sub_sub_flex_mutind;
    unfold sub_decorate_concl, sub_flex_decorate_concl.
  -
    intros NM P Θ0 Hwf HwfP0 HwfP Hmod Hgf0.
    replace P with (⌊ pskl_to_uskl P ⌋ˢ) at 2
      by apply uskl_to_pskl_pskl_to_uskl.
    apply a_subtag__infer. fsetdec.
  -
    intros Θ0 Θ1 A B Hgfa Hgfb HgA HgB Hchk Hwf HwfP0 HwfP Hmod Hgf0.
    destruct Hchk as [P' Hcns].
    eapply a_subtag__check;
      [ exact Hgfb
      | apply pskl_to_uskl_guarded; exact HgA
      | exact HgB
      | exact (a_consis_decorate Hcns (a_wf_aenv_uniq Hwf)) ].
  -
    intros α Θ0 Θ1 Ξ A B Hgfb Hsuf Huq Hfr Hprem IHprem Hwf HwfP0 HwfP Hmod Hgf0.
    rewrite dom_app in Hfr.
    eapply a_subtag__forall_r with (α := α) (Ξ := Ξ);
      [ exact Hgfb | exact Hsuf | exact Huq
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
  -
    intros Θ0 P Hg Hwf HwfP0 HwfP Hmod Hgf0.
    replace (pskl_univ_ghost P)
      with (pskl_univ_ghost ⌊ pskl_to_uskl P ⌋ˢ)
      by (rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
    apply a_subtag__univ_ghost_r;
      [ apply pskl_to_uskl_guarded; exact Hg | fsetdec ].
  -
    intros NM M P0 Θ0 Θ1 α A Hflex IHflex Hwf HwfP0 HwfP Hmod Hgf0.
    simpl.
    apply a_subtag__flex_mono; [ | fsetdec ].
    apply IHflex.
    { constructor. }
    { simpl. exact Hwf. }
    { simpl. exact HwfP0. }
    { simpl.
      pose proof (a_wf_pskl_ftv_binds HwfP (α := α)
                  ltac:(simpl; clear; solve_notin_auto)) as Htx; exact Htx. }
    { exact Hmod. }
    { simpl. exact Hgf0. }
  -
    intros NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2 Hc Hs2 IH2 Hwf HwfP0 HwfP Hmod Hgf0.
    apply a_wf_pskl_arrow_inv in HwfP0 as [HwfP0a HwfP0b].
    apply a_wf_pskl_arrow_inv in HwfP as [HwfP1 HwfP2].
    pose proof (a_consis_decorate Hc (a_wf_aenv_uniq Hwf)) as Hct.
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
  -
    intros α0 NM M P0 Θ0 Θ1 P P' Ξ P1 Hne Hgor Hfr0 Hex Huq HwfP1 Hsub IHsub
      Hwf HwfP0 HwfP Hmod Hgf0.
    destruct (@a_extract_family_of_instance Θ0 NM M α0 P P0 Ξ P1 Hex
                ltac:(clear - Hfr0; solve_notin_auto)) as [L Hfam].
    assert (Hdecls : a_decls Ξ) by (eapply a_extract_decls; eauto).
    assert (HwfΞΘ : {{ ⊢ (Ξ ++ Θ0) }}a).
    { apply a_wf_aenv_prepend_decls; auto.
      - clear - Huq. solve_uniq.
      - intros α1 Hα1. clear - Huq Hα1. destruct_uniq.
        unfold disjoint in *. fsetdec. }
    assert (Hmono : forall x (b : abind),
               binds x b Θ0 -> binds x b (Ξ ++ Θ0))
      by (intros x b Hb; unfold binds in *; apply in_or_app; auto).
    assert (HwfP0' : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_weaken; [ exact Hmono | exact HwfP0 ]).
    assert (HlcP1 : lc_pskl P1) by (eapply a_wf_pskl_lc; eauto).
    simpl.
    eapply a_subtag__forall_l_untagged
      with (L := L `union` singleton α0 `union` dom Ξ `union` dom Θ0
                 `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
                 `union` ftvar_in_pskl P1)
           (Ξ := Ξ) (P1 := P1);
      [ exact Hne | exact Hgor | | exact Huq | exact HwfP1 | ].
    { intros α Hα.
      replace (⌊ open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α) ⌋ˢ)
        with (open_pskl_wrt_pskl P (pskl_var_f α))
        by (rewrite uskl_to_pskl_open;
            rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      apply Hfam. clear - Hα. fsetdec. }
    intros Ψg ψg Hfr Hsort Hera.
    assert (Hlcg : lc_uskl ψg)
      by (apply is_dskl_lc; inversion Hsort; assumption).
    destruct (atom_fresh
                (L `union` singleton α0 `union` dom Ξ `union` dom Θ0
                 `union` ftvar_in_pskl P0 `union` ftvar_in_pskl P
                 `union` ftvar_in_pskl P1)) as [α Hα].
    assert (HtgP0 : pskl_top_guarded P0)
      by (eapply a_wf_pskl_top_guarded; exact HwfP0).
    destruct (a_extract_decorate (Hfam α ltac:(clear - Hα; solve_notin_auto))
                HtgP0 Hsort Hera) as [Ξc [C [HDlk Hst]]].
    assert (Hαg : α `notin` ftvar_in_uskl ψg).
    { rewrite <- (ftvar_in_pskl_uskl_to_pskl ψg). rewrite Hera.
      clear - Hα. fsetdec. }
    assert (HeqSubj :
        pskl_to_uskl (open_pskl_wrt_pskl P P1)
        = subst_uskl_in_uskl (pskl_to_uskl (uskl_to_pskl ψg)) α
            (open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α))).
    { rewrite pskl_to_uskl_open.
      rewrite (subst_uskl_in_uskl_intro α);
        [ | rewrite <- (ftvar_in_pskl_uskl_to_pskl (pskl_to_uskl P));
            rewrite uskl_to_pskl_pskl_to_uskl; clear - Hα; fsetdec ].
      rewrite Hera. reflexivity. }
    assert (HDsrc : {{ Θ0 ⊢
        ⌊ open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α) ⌋ˢ
        ≼[ α , M ] P0 ⤳ Ξc ⨾ C }}a).
    { replace (⌊ open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α) ⌋ˢ)
        with (open_pskl_wrt_pskl P (pskl_var_f α))
        by (rewrite uskl_to_pskl_open;
            rewrite uskl_to_pskl_pskl_to_uskl; reflexivity).
      exact HDlk. }
    assert (Hresult :
        subst_uskl_in_uskl ψg α
          (open_uskl_wrt_uskl (pskl_to_uskl P) (uskl_var_f α))
        = open_uskl_wrt_uskl (pskl_to_uskl P) ψg).
    { symmetry. apply subst_uskl_in_uskl_intro.
      rewrite <- (ftvar_in_pskl_uskl_to_pskl (pskl_to_uskl P)).
      rewrite uskl_to_pskl_pskl_to_uskl. clear - Hα. fsetdec. }
    assert (HwfOpen : {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ open_pskl_wrt_pskl P P1 }}a).
    { inversion HwfP as [ | | | LP ΘP ΔP PP HbodyP HeqP | | ]; subst.
      eapply a_wf_pskl_open with (L := LP);
        [ intros α2 Hα2; eapply a_wf_pskl_weaken;
          [ exact (@binds_sub_cons _ _ _ Hmono) | apply HbodyP; auto ]
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
  -
    intros M Θ0 P0 Hmghost Hwf HwfP0 HwfP Hmod Hgf0.
    simpl. apply a_subtag__ghost. fsetdec.
  -
    intros M Θ0 Θ1 P0 P P' Hne Hs IH Hwf HwfP0 HwfP Hmod Hgf0.
    simpl.
    apply a_subtag__univ_ghost_l; [ exact Hne | ].
    apply IH;
      [ exact Hwf | exact HwfP0
      | apply a_wf_pskl_univ_ghost_inv in HwfP as [_ HwfP];
        eapply a_wf_pskl_delta_mono; [ exact HwfP | clear; fsetdec ]
      | exact Hmod
      | exact Hgf0 ].
  -
    intros NM M P0 Θ0 Θ1 Ξw α0 α β A Hne Hα Hβ Hs IH
      Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    set (τab := ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)).
    set (Θmid := (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0).
    set (Θ' := Ξw ++ (α0 ~ abind_flex_mono_def τab) ++ Θmid).
    destruct (@a_flex_arrow_context Ξw Θ0 α0 α β
                HwfΞ Hsuf Hne Hα Hβ) as [HwfΘ' Hlift].
    assert (HwfP0' : {{ Θ' ⨟ empty ⊢ₚₛ P0 }}a)
      by (eapply a_wf_pskl_isub; eauto).
    assert (Hwfarr : {{ Θ' ⨟ empty ⊢ₚₛ
                       pskl_arrow (pskl_var_f α) (pskl_var_f β) }}a).
    { apply a_wf_pskl__arrow; apply a_wf_pskl__var;
        right; left;
        (unfold Θ'; unfold binds; apply in_or_app; right; simpl;
         right; auto). }
    eapply a_subtag_flex__solve;
      [ exact Hne | exact Hα | exact Hβ | ].
    exact (IH HwfΘ' HwfP0' Hwfarr Hmod Hgf0).
  -
    intros NM M P0 Θ0 Θ1 Ξw α β τ A Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    assert (Hwfcons : {{ ⊢ ((β ~ abind_flex_mono_def τ) ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_prefix; eauto).
    inversion Hwfcons as [ | | βz τz Θz HβΘ0 Hwfτ Hm Hwf0 | | | ]; subst.
    assert (HwfΞΘ0 : {{ ⊢ (Ξw ++ Θ0) }}a)
      by (eapply a_wf_aenv_strip_mid; eauto).

    assert (HwfP0' : {{ (Ξw ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β P0 }}a).
    { eapply a_wf_pskl_subst_mid_def; [ exact HwfΞ | exact HwfP0 ]. }
    assert (Hwfvarsub : {{ (Ξw ++ Θ0) ⨟ empty ⊢ₚₛ
              subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α) }}a).
    { eapply a_wf_pskl_subst_mid_def; [ exact HwfΞ | apply a_wf_pskl__var; exact Hαb ]. }
    apply a_subtag_flex__assign; [ exact Hβ1 | ].
    apply (IH HwfΞΘ0 HwfP0' Hwfvarsub);
      [ intro HSK; specialize (Hmod HSK);
        rewrite <- pskl_to_bskl_inh_subst_mono;
          [ apply mod_comp_sk_subst_mono; [ exact Hmod | exact Hm ]
          | exact Hm ]
      | intros Hty; specialize (Hgf0 Hty);
        apply pskl_top_guarded_subst_mono; [ exact Hgf0 | exact Hm ] ].
  -
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
  -
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hnin Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    apply a_subtag_flex__skip;
      [ exact Hne | exact Hnin | exact Hβ1 | ].
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; eauto. }
    { exact (a_binds_tvar_strip_mid_neq Hne Hαb). }
    { exact Hmod. }
    { exact Hgf0. }
  -
    intros NM M P0 Θ0 Θ1 Ξw α β A Hne Hnin Hβ1 Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    apply a_subtag_flex__skip_rigid;
      [ exact Hne | exact Hnin | exact Hβ1 | ].
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; eauto. }
    { exact (a_binds_tvar_strip_mid_neq Hne Hαb). }
    { exact Hmod. }
    { exact Hgf0. }
  -
    intros NM M P0 Θ0 Θ1 Ξw α x Q A Hnin Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    assert (Hxfr : x `notin` ftvar_in_pskl P0)
      by (eapply a_wf_pskl_tm_entry_fresh; [ exact HwfΞ | exact I | exact HwfP0 ]).
    apply a_subtag_flex__skip_tm_var.
    { exact Hnin. }
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hxfr ]. }
    { exact (a_binds_tvar_strip_mid_tm Hαb I). }
    { exact Hmod. }
    { exact Hgf0. }
  -
    intros NM M P0 Θ0 Θ1 Ξw α x Q A Hnin Hs IH Hsuf HwfΞ HwfP0 Hαb Hmod Hgf0.
    assert (Hxfr : x `notin` ftvar_in_pskl P0)
      by (eapply a_wf_pskl_tm_entry_fresh; [ exact HwfΞ | exact I | exact HwfP0 ]).
    apply a_subtag_flex__skip_tm_skl.
    { exact Hnin. }
    apply IH.
    { exact Hsuf. }
    { eapply a_wf_aenv_strip_mid; eauto. }
    { eapply a_wf_pskl_strip_mid; [ exact HwfP0 | exact Hxfr ]. }
    { exact (a_binds_tvar_strip_mid_tm Hαb I). }
    { exact Hmod. }
    { exact Hgf0. }
Qed.

Lemma a_sub_decorate : forall NM M P0 Θ0 P P' Θ1,
  a_sub NM M P0 Θ0 P P' Θ1 ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  {{ Θ0 ⊢[ NM | M | P0 | empty ] (pskl_to_uskl P) ⩽ P' ⊣ Θ1 }}da.
Proof.
  intros NM M P0 Θ0 P P' Θ1 Hrun Hwf HwfP0 HwfP Hmod.
  eapply (proj1 a_sub_decorate_bundle); try eassumption.
  - intros HSK; apply a_sk_mode_compat_mod_comp_sk; apply Hmod; exact HSK.
  - intros _; eapply a_wf_pskl_top_guarded; exact HwfP0.
Qed.

Theorem a_sub_sound : forall NM M P0 Θ0 P P' Θ1,
  a_sub NM M P0 Θ0 P P' Θ1 ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt,
    bskl_to_pskl Qt = P' /\
    ({{ empty ⨟ Θ1 ⊢ˢ[ NM | M ] (pskl_to_uskl P) ⩽ Qt }}ad) /\
    {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad.
Proof.
  intros NM M P0 Θ0 P P' Θ1 Hrun Hwf HwfP0 HwfP Hmod Hgf.
  pose proof (a_sub_decorate Hrun Hwf HwfP0 HwfP Hmod) as Htag.
  destruct ((proj1 a_subtag_sound_bundle) _ _ _ _ _ _ _ _ Htag
              Hwf
              ltac:(apply pskl_to_uskl_lc; eapply a_wf_pskl_lc; eauto)
              HwfP0
              ltac:(rewrite uskl_to_pskl_pskl_to_uskl; exact HwfP)
              ltac:(intros HSK; apply a_sk_mode_compat_mod_comp_sk;
                    apply Hmod; exact HSK)
              Hgf)
    as (Hisub & Hwf1 & Qt & HeQt & Hjoin & Hrs).

  destruct Hjoin as [njoin Hjoin]; apply ad_pat_sub_of_fuel in Hjoin.
  exact (conj Hisub (conj Hwf1
           (ex_intro _ Qt (conj HeQt (conj Hjoin
              Hrs))))).
Qed.
