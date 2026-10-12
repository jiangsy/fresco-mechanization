Require Import src.fresco.prop_atom_sets.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_swap.

Set Implicit Arguments.

Scheme a_solve_sub_mutind := Induction for a_solve_sub Sort Prop
  with a_solve_eq_mutind  := Induction for a_solve_eq  Sort Prop.
Combined Scheme a_solve_sub_eq_mutind
  from a_solve_sub_mutind, a_solve_eq_mutind.

Lemma a_guess_mono_lc : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> lc_ptyp A.
Proof.
  intros Θ P Ξ A H; induction H;
    try solve [ assumption | constructor; auto ].

  match goal with
  | |- lc_ptyp (ptyp_all (close_ptyp_wrt_ptyp ?b _)) =>
      apply (lc_ptyp_all_exists b);
      rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp; assumption
  end.
Qed.

Corollary a_guess_mono_lc_pskl : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> lc_pskl (ptyp_to_pskl A).
Proof. intros. apply ptyp_to_pskl_lc. eauto using a_guess_mono_lc. Qed.

Lemma a_guess_mono_guarded : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> guarded_pskl P -> guarded_pskl (ptyp_to_pskl A).
Proof.
  intros Θ P Ξ A H Hg; inversion Hg; subst; inversion H; subst; cbn.
  - apply guarded_pskl__unit.
  - apply guarded_pskl__var.
  - apply guarded_pskl__arrow;
      (apply ptyp_to_pskl_lc; eapply a_guess_mono_lc; eassumption).
Qed.

Lemma guarded_pskl_lc : forall P, guarded_pskl P -> lc_pskl P.
Proof. intros P H; inversion H; subst; constructor; assumption. Qed.

Lemma lc_pskl_arrow_inv : forall P1 P2,
  lc_pskl (pskl_arrow P1 P2) -> lc_pskl P1 /\ lc_pskl P2.
Proof. intros P1 P2 H; inversion H; auto. Qed.

Lemma lc_pskl_univ_ghost_inv : forall P,
  lc_pskl (pskl_univ_ghost P) -> lc_pskl P.
Proof. intros P H; inversion H; auto. Qed.

Lemma lc_pskl_all_syn_inv : forall P,
  lc_pskl (pskl_all_syn P) ->
  forall α, lc_pskl (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof. intros P H; inversion H; auto. Qed.

Lemma a_solve_sub_eq_lc :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     lc_pskl P -> lc_pskl P0 -> lc_pskl P') /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     lc_pskl P -> lc_pskl P0 -> lc_pskl P').
Proof.
  apply a_solve_sub_eq_mutind; intros;

    try solve [ eapply a_guess_mono_lc_pskl; eassumption ];

    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_univ_ghost _) |- _ => apply lc_pskl_univ_ghost_inv in H
    | H : guarded_pskl _           |- _ => apply guarded_pskl_lc in H
    end;

    try solve
      [ assumption
      | eauto
      | constructor; eauto
      | apply lc_pskl_univ_ghost; eauto
      | apply lc_pskl_univ_ghost; constructor; eauto ].
  -
    match goal with
    | HP : lc_pskl (pskl_all_syn _) |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply (lc_pskl_all_syn_inv HP) | assumption ]
        end
    end.
  -
    match goal with
    | HQ : lc_pskl (pskl_all_syn _),
      IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
        apply IH; [ assumption | apply (lc_pskl_all_syn_inv HQ) ]
    end.
  -
    match goal with
    | HP : lc_pskl (pskl_all_syn ?p), HQ : lc_pskl (pskl_all_syn ?q)
      |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply (lc_pskl_all_syn_inv HP)
                      | apply (lc_pskl_all_syn_inv HQ) ]
        end
    end.
  -
    match goal with
    | HQ : lc_pskl (pskl_all_syn _)
      |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply lc_pskl_univ_ghost; assumption
                      | apply (lc_pskl_all_syn_inv HQ) ]
        end
    end.
  -
    match goal with
    | HP : lc_pskl (pskl_all_syn _)
      |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply (lc_pskl_all_syn_inv HP)
                      | apply lc_pskl_univ_ghost; assumption ]
        end
    end.
Qed.

Lemma a_solve_sub_lc : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> lc_pskl P -> lc_pskl P0 -> lc_pskl P'.
Proof. intros; eapply (proj1 a_solve_sub_eq_lc); eauto. Qed.

Lemma a_solve_eq_lc : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> lc_pskl P -> lc_pskl P0 -> lc_pskl P'.
Proof. intros; eapply (proj2 a_solve_sub_eq_lc); eauto. Qed.

Lemma a_solve_sub_eq_guarded :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     lc_pskl P -> lc_pskl P0 -> guarded_pskl P -> guarded_pskl P') /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     lc_pskl P -> lc_pskl P0 -> guarded_pskl P -> guarded_pskl P').
Proof.
  apply a_solve_sub_eq_mutind; intros;

    try solve [ eapply a_guess_mono_guarded; eassumption ];

    try solve [ match goal with H : guarded_pskl _ |- _ => inversion H end ];

    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ => apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_univ_ghost _) |- _ => apply lc_pskl_univ_ghost_inv in H
    end;
    try solve
      [ assumption
      | eauto
      | constructor; eauto using a_solve_sub_lc, a_solve_eq_lc ].
  -
    match goal with
    | HQ : lc_pskl (pskl_all_syn _),
      IH : lc_pskl _ -> lc_pskl _ -> guarded_pskl _ -> guarded_pskl _ |- _ =>
        apply IH;
          [ assumption | apply (lc_pskl_all_syn_inv HQ) | assumption ]
    end.
Qed.

Lemma a_solve_sub_eq_decls :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> a_decls Ξ) /\
  (forall Θ P P0 Ξ P',   {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a     -> a_decls Ξ).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    try solve
      [ constructor
      | assumption
      | apply a_decls_app; assumption
      | eapply a_guess_mono_decls; eassumption ].
Qed.

Lemma a_solve_sub_decls : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> a_decls Ξ.
Proof. intros; eapply (proj1 a_solve_sub_eq_decls); eauto. Qed.

Lemma a_solve_eq_decls : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> a_decls Ξ.
Proof. intros; eapply (proj2 a_solve_sub_eq_decls); eauto. Qed.

Lemma a_solve_sub_eq_generated_fresh_set :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     dom Ξ ∩ ftvar_in_aenv Θ [=] empty) /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     dom Ξ ∩ ftvar_in_aenv Θ [=] empty).
Proof.
  apply a_solve_sub_eq_mutind; intros;

    try solve [ simpl; clear; fsetdec ];

    try solve [ assumption ];

    try solve
      [ apply inter_empty_pointwise; intros α0 Hα0;
        eapply a_guess_mono_generated_fresh; eassumption ];
    try solve
      [ match goal with
        | IH : dom ?X ∩ ftvar_in_aenv (_ ++ ?Th) [=] empty
          |- dom ?X ∩ ftvar_in_aenv ?Th [=] empty =>
            simpl in IH; clear - IH; fsetdec
        end ].
  all: match goal with
       | IH1 : dom ?X1 ∩ ftvar_in_aenv ?Th [=] empty,
         IH2 : dom ?X2 ∩ ftvar_in_aenv (?X1 ++ ?Th) [=] empty
         |- dom (?X2 ++ ?X1) ∩ ftvar_in_aenv ?Th [=] empty =>
           rewrite dom_app; rewrite ftvar_in_aenv_app in IH2;
           clear - IH1 IH2; fsetdec
       end.
Qed.

Lemma a_solve_sub_generated_fresh : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ.
Proof.
  intros * H α Hin.
  pose proof ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ H) as Hs.
  clear - Hs Hin; fsetdec.
Qed.

Lemma a_solve_eq_generated_fresh : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ.
Proof.
  intros * H α Hin.
  pose proof ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ H) as Hs.
  clear - Hs Hin; fsetdec.
Qed.

Corollary a_solve_eq_generated_notin_dom : forall Θ P P0 Ξ P' α,
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> α `in` dom Ξ -> α `notin` dom Θ.
Proof.
  intros * H Hin.
  pose proof (a_solve_eq_generated_fresh H Hin) as Hfr.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hd. clear - Hfr Hd. fsetdec.
Qed.

Corollary a_solve_sub_generated_apart_binder : forall β Θ m P P0 Ξ P',
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> β `notin` dom Ξ.
Proof.
  intros * H Hin.
  pose proof (a_solve_sub_generated_fresh H Hin) as Hfr.
  simpl in Hfr. clear - Hfr. fsetdec.
Qed.

Corollary a_solve_eq_generated_apart_binder : forall β Θ P P0 Ξ P',
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> β `notin` dom Ξ.
Proof.
  intros * H Hin.
  pose proof (a_solve_eq_generated_fresh H Hin) as Hfr.
  simpl in Hfr. clear - Hfr. fsetdec.
Qed.

Lemma a_solve_sub_eq_generated_ftvar :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    try solve
      [ simpl; clear; fsetdec
      | assumption
      | eapply a_guess_mono_generated_ftvar; eassumption
      | rewrite ftvar_in_aenv_app, dom_app;
        match goal with
        | IH1 : ftvar_in_aenv ?X1 [<=] dom ?X1,
          IH2 : ftvar_in_aenv ?X2 [<=] dom ?X2 |- _ =>
            clear - IH1 IH2; fsetdec
        end ].
Qed.

Lemma a_solve_sub_eq_ftv :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     forall α, α `in` ftvar_in_pskl P' ->
       α `in` (ftvar_in_pskl P `union` ftvar_in_pskl P0) \/
       α `notin` dom Θ) /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     ftvar_in_pskl P' [<=]
       ftvar_in_pskl P `union` ftvar_in_pskl P0 `union` dom Ξ).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    try solve
      [
        match goal with
        | Hg : a_guess_mono ?Th ?p ?X ?a
          |- ftvar_in_pskl (ptyp_to_pskl ?a) [<=] _ =>
            pose proof (a_guess_mono_ftv Hg) as Hgf;
            pose proof (ftvar_ptyp_to_pskl a) as Hco;
            clear - Hgf Hco; fsetdec
        end
      |
        idtac ];
    try solve
      [
        cbn [ftvar_in_pskl] in *; fsetdec
      |
        cbn [ftvar_in_pskl] in *; left; fsetdec
      |
        match goal with
        | IH : ftvar_in_pskl ?p' [<=] _
          |- ftvar_in_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b ?p')) [<=] _ =>
            pose proof (ftvar_in_pskl_close_pskl_wrt_pskl p' b) as Hcl;
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b));
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b));
            cbn [ftvar_in_pskl] in *; fsetdec
        end ].
  -
    match goal with
    | IH : forall α, α `in` ftvar_in_pskl ?p' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b ?p'))
      |- _ =>
        pose proof (ftvar_in_pskl_close_pskl_wrt_pskl p' b) as Hcl;
        cbn [ftvar_in_pskl] in Hm;
        assert (Hin : a `in` ftvar_in_pskl p') by (clear - Hm Hcl; fsetdec);
        assert (Hne : a `notin` singleton b) by (clear - Hm Hcl; fsetdec);
        destruct (IH a Hin) as [Hl | Hr];
          [ pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b))
              as Hup; cbn [ftvar_in_pskl] in *; left; clear - Hl Hup Hne; fsetdec
          | right; simpl in Hr; clear - Hr; fsetdec ]
    end.
  -
    match goal with
    | IH : forall α, α `in` ftvar_in_pskl ?p' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_univ_ghost ?p') |- _ =>
        cbn [ftvar_in_pskl] in Hm;
        destruct (IH a Hm) as [Hl | Hr];
          [ left; cbn [ftvar_in_pskl] in *; clear - Hl; fsetdec
          | right; simpl in Hr; clear - Hr; fsetdec ]
    end.
  -
    match goal with
    | Hs : {{ _ ⊢ₑ _ ∼ _ ⤳ ?X ⨾ ?p' }}a ,
      He : ftvar_in_pskl ?p' [<=] _ ,
      Hm : ?a `in` ftvar_in_pskl ?p' |- _ =>
        destruct (AtomSetProperties.In_dec a (dom X)) as [Hd | Hd];
          [ right; eapply a_solve_eq_generated_notin_dom; eassumption
          | left; cbn [ftvar_in_pskl] in *; clear - Hm He Hd; fsetdec ]
    end.
  -
    match goal with
    | Hfr : ?b `notin` _ ,
      IH : forall α, α `in` ftvar_in_pskl ?p' -> _ ,
      Hm : ?a `in` ftvar_in_pskl ?p' |- _ =>
        pose proof (dom_subset_ftvar_in_aenv Θ) as Hdf;
        destruct (IH a Hm) as [Hl | Hr];
          [ pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
              as Hup; cbn [ftvar_in_pskl] in *;
            destruct (a == b) as [-> | Hne];
              [ right; clear - Hfr Hdf; fsetdec
              | left;
                assert (Hne' : a `notin` singleton b)
                  by (apply notin_singleton_2; auto);
                clear - Hl Hup Hne'; fsetdec ]
          | right; simpl in Hr; clear - Hr; fsetdec ]
    end.
  -
    match goal with
    | Hs : {{ _ ⊢ₑ _ ∼ _ ⤳ ?X1 ⨾ ?e' }}a ,
      He : ftvar_in_pskl ?e' [<=] _ ,
      IH : forall α, α `in` ftvar_in_pskl ?p2' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_arrow ?e' ?p2') |- _ =>
        cbn [ftvar_in_pskl] in Hm;
        apply union_1 in Hm; destruct Hm as [Hm | Hm];
          [ destruct (AtomSetProperties.In_dec a (dom X1)) as [Hd | Hd];
              [ right; eapply a_solve_eq_generated_notin_dom; eassumption
              | left; cbn [ftvar_in_pskl] in *; clear - Hm He Hd; fsetdec ]
          | destruct (IH a Hm) as [Hl | Hr];
              [ left; cbn [ftvar_in_pskl] in *; clear - Hl; fsetdec
              | right; rewrite dom_app in Hr; clear - Hr; fsetdec ] ]
    end.
  -
    match goal with
    | Hs : {{ _ ⊢ₑ _ ∼ _ ⤳ ?X1 ⨾ ?e' }}a ,
      He : ftvar_in_pskl ?e' [<=] _ ,
      IH : forall α, α `in` ftvar_in_pskl ?p2' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_univ_ghost (pskl_arrow ?e' ?p2')) |- _ =>
        cbn [ftvar_in_pskl] in Hm;
        apply union_1 in Hm; destruct Hm as [Hm | Hm];
          [ destruct (AtomSetProperties.In_dec a (dom X1)) as [Hd | Hd];
              [ right; eapply a_solve_eq_generated_notin_dom; eassumption
              | left; cbn [ftvar_in_pskl] in *; clear - Hm He Hd; fsetdec ]
          | destruct (IH a Hm) as [Hl | Hr];
              [ left; cbn [ftvar_in_pskl] in *; clear - Hl; fsetdec
              | right; rewrite dom_app in Hr; clear - Hr; fsetdec ] ]
    end.
  -
    rewrite dom_app.
    match goal with
    | IH1 : ftvar_in_pskl ?p1' [<=] _ , IH2 : ftvar_in_pskl ?p2' [<=] _
      |- ftvar_in_pskl (pskl_arrow ?p1' ?p2') [<=] _ =>
        cbn [ftvar_in_pskl]; clear - IH1 IH2; fsetdec
    end.
Qed.

Lemma a_solve_sub_ftv : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` ftvar_in_pskl P' ->
    α `in` (ftvar_in_pskl P `union` ftvar_in_pskl P0) \/ α `notin` dom Θ.
Proof. intros; eapply (proj1 a_solve_sub_eq_ftv); eauto. Qed.

Lemma a_solve_eq_ftv : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  ftvar_in_pskl P' [<=]
    ftvar_in_pskl P `union` ftvar_in_pskl P0 `union` dom Ξ.
Proof. intros; eapply (proj2 a_solve_sub_eq_ftv); eauto. Qed.

Lemma subst_pskl_var_same : forall P α,
  subst_pskl_in_pskl (pskl_var_f α) α P = P.
Proof.
  induction P; intros α0; simpl; f_equal; auto.
  destruct (α == α0); subst; reflexivity.
Qed.

Lemma a_guess_mono_ctx_shrink : forall Θ P Ξ A Θ',
  a_guess_mono Θ P Ξ A ->
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  a_guess_mono Θ' P Ξ A.
Proof.
  intros Θ P Ξ A Θ' H; revert Θ'; induction H; intros Θ' Hsub.
  - apply a_guess_mono__ghost. clear - H Hsub; fsetdec.
  - apply a_guess_mono__univ_ghost; auto.
  - apply a_guess_mono__var.
  - apply a_guess_mono__unit.
  - apply a_guess_mono__arrow; auto.
  - apply a_guess_mono__forall with (β := β);
      [ clear - H Hsub; fsetdec
      | apply IHa_guess_mono; simpl; clear - Hsub; fsetdec ].
Qed.

Lemma a_solve_eq_move_binder : forall Θ b P Q Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f b))
    ∼ (open_pskl_wrt_pskl Q (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f α0))
     ∼ (open_pskl_wrt_pskl Q (pskl_var_f α0))
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b P Q Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj2 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  rewrite ! swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 P) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 Q) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr
    by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

Lemma a_solve_sub_move_binder_l : forall Θ b m P Q Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f b))
    ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f α0)) ≼[ m ] Q
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b m P Q Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj1 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 P) in Hr by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 Q) in Hr by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

Lemma a_solve_sub_move_binder_r : forall Θ b A B Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₛ A ≼[ mode_tc ]
    (open_pskl_wrt_pskl B (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl A `union` ftvar_in_pskl B ->
  α0 `notin` ftvar_in_pskl A `union` ftvar_in_pskl B
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₛ A ≼[ mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f α0))
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b A B Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj1 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 A) in Hr by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 B) in Hr by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

Lemma a_solve_eq_move_binder_univ_ghost_l : forall Θ b P Q Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₑ (pskl_univ_ghost P)
    ∼ (open_pskl_wrt_pskl Q (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₑ (pskl_univ_ghost P) ∼ (open_pskl_wrt_pskl Q (pskl_var_f α0))
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b P Q Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj2 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  cbn [swap_pskl] in Hr.
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 P) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 Q) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr
    by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

Lemma a_solve_eq_move_binder_univ_ghost_r : forall Θ b P Q Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f b))
    ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f α0)) ∼ (pskl_univ_ghost Q)
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b P Q Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj2 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  cbn [swap_pskl] in Hr.
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 P) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 Q) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr
    by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

Lemma a_solve_cstr_decls : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a -> a_decls Ξ.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H.
  - constructor.
  - eapply a_solve_sub_decls; eassumption.
  - apply a_decls_app; [ exact IHa_solve_cstr | ].
    eapply a_solve_eq_decls; eassumption.
Qed.

Lemma a_solve_cstr_generated_fresh : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H; intros α Hin.
  - simpl in Hin; exfalso; clear - Hin; fsetdec.
  - eapply a_solve_sub_generated_fresh; eassumption.
  - rewrite dom_app in Hin.
    destruct (AtomSetProperties.In_dec α (dom Ξ2)) as [Hin2 | Hnin2].
    + pose proof (IHa_solve_cstr α Hin2) as Hfr.
      rewrite ftvar_in_aenv_app in Hfr. clear - Hfr; fsetdec.
    + assert (Hin1 : α `in` dom Ξ1) by (clear - Hin Hnin2; fsetdec).
      eapply a_solve_eq_generated_fresh; eassumption.
Qed.

Lemma a_solve_sub_ghost_target_inv : forall Θ m P Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] pskl_ghost ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = P.
Proof.
  intros Θ m P Ξ P' Hd.
  remember pskl_ghost as T eqn:HT.
  induction Hd; inversion HT; subst.
  -  auto.
  -
    destruct IHHd as [-> ->]; [ reflexivity | ].
    split; [ reflexivity | ].
    rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
      [ reflexivity
      | match goal with
        | Hfr : ?b `notin` ftvar_in_aenv _ `union` _ `union` _ |- _ =>
            clear - Hfr; fsetdec
        end ].
  -
    destruct IHHd as [-> ->]; [ reflexivity | ]. auto.
  -  auto.
  -
    match goal with
    | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
    end.
  -
    match goal with
    | Hg : pskl_ghost_free pskl_ghost |- _ => inversion Hg
    end.
Qed.

Lemma a_solve_eq_var_subject : forall Θ P Q Ξ P',
  {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
  forall α, P = pskl_var_f α -> Ξ = nil /\ P' = pskl_var_f α.
Proof.
  intros Θ P Q Ξ P' HD.
  induction HD; intros α0 Heq; try discriminate.
  -  inversion Heq; subst. split; reflexivity.
  -
    subst.
    match goal with
    | G : a_guess_mono _ (pskl_var_f _) _ _ |- _ => inversion G; subst
    end.
    split; reflexivity.
  -  subst. split; reflexivity.
  -  eauto.
Qed.

Lemma a_solve_sub_var_subject : forall Θ m α Q Ξ P',
  {{ Θ ⊢ₛ (pskl_var_f α) ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = pskl_var_f α.
Proof.
  intros * HD; inversion HD; subst.
  -  split; reflexivity.
  -  split; reflexivity.
  -
    match goal with
    | He : a_solve_eq _ _ _ _ _ |- _ =>
        apply (a_solve_eq_var_subject He); reflexivity
    end.
  -
    exfalso.
    match goal with
    | Hoff : solve_l_off (pskl_var_f _) |- _ => exact (proj1 Hoff _ eq_refl)
    end.
Qed.

Lemma a_solve_sub_inv_forall_l : forall Θ m P0 Q Ξ P',
  {{ Θ ⊢ₛ (pskl_all_syn P0) ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
  exists β P'',
    β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl Q
    /\ P' = pskl_all_syn (close_pskl_wrt_pskl β P'')
    /\ {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ (open_pskl_wrt_pskl P0 (pskl_var_f β))
          ≼[ m ] Q ⤳ Ξ ⨾ P'' }}a.
Proof.
  intros * H; inversion H; subst.
  -
    match goal with
    | Hfr : ?b `notin` _, Hp : a_solve_sub _ _ _ _ _ ?y |- _ =>
        exists b, y
    end.
    repeat split; assumption.
  -
    exfalso.
    match goal with
    | Hoff : peel_l_off (pskl_all_syn _) |- _ => exact (proj1 Hoff _ eq_refl)
    end.
  -
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  -
    exfalso.
    match goal with
    | Hoff : solve_l_off (pskl_all_syn _) |- _ =>
        exact (proj1 (proj2 Hoff) _ eq_refl)
    end.
Qed.

Lemma a_solve_sub_inv_univ_ghost_l : forall Θ m P0 Q Ξ P',
  {{ Θ ⊢ₛ (pskl_univ_ghost P0) ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
  exists P'', P' = pskl_univ_ghost P''
    /\ {{ Θ ⊢ₛ P0 ≼[ m ] Q ⤳ Ξ ⨾ P'' }}a.
Proof.
  intros * H; inversion H; subst.
  -
    match goal with
    | Hp : a_solve_sub _ _ P0 _ _ ?y |- _ => exists y
    end.
    split; [ reflexivity | assumption ].
  -
    exfalso.
    match goal with
    | Hoff : peel_l_off (pskl_univ_ghost _) |- _ => exact (proj2 Hoff _ eq_refl)
    end.
  -
    match goal with
    | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
    end.
  -
    exfalso.
    match goal with
    | Hoff : solve_l_off (pskl_univ_ghost _) |- _ =>
        exact (proj2 (proj2 Hoff) _ eq_refl)
    end.
Qed.

Lemma a_solve_eq_no_ghost_p0 : forall Θ Pi P0 Ξ Pa,
  {{ Θ ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a ->
  pskl_no_ghost P0 ->
  pskl_no_ghost Pa.
Proof.
  intros Θ Pi P0 Ξ Pa H; induction H; intros Hnh; simpl in *; auto.
  -  apply ptyp_to_pskl_no_ghost.
  -  contradiction.
  -  destruct Hnh; split; auto.
  -
    apply pskl_no_ghost_close.
    apply IHa_solve_eq. apply pskl_no_ghost_open_rec; simpl; auto.
  -
    apply pskl_no_ghost_close.
    apply IHa_solve_eq. apply pskl_no_ghost_open_rec; simpl; auto.
  -
    apply pskl_no_ghost_close.
    apply IHa_solve_eq; exact Hnh.
Qed.
