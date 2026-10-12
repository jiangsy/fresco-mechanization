Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.def_sub.
Require Import src.fresco.ext_algo.typing.def_pat.
Require Import src.fresco.ext_algo.typing.def_typing.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.prop_termination.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Lemma e_sub_sub_flex_defs_mono :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     aenv_defs_mono Θ0 -> aenv_defs_mono Θ1) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     aenv_defs_mono Θ0 -> aenv_defs_mono Ξ -> aenv_defs_mono Θ1).
Proof.
  apply e_sub_sub_flex_mutind;
    intros;
    simpl in *;

    repeat match goal with
    | H : Forall entry_def_mono (_ ++ _) |- _ =>
        apply Forall_app in H; destruct H
    | H : Forall entry_def_mono (_ :: _) |- _ =>
        inversion H; subst; clear H
    end;

    repeat match goal with
    | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
    end;
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ ?Θ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e,
      Hd : Forall entry_def_mono ?Θ |- _ =>
        lazymatch goal with
        | _ : Forall entry_def_mono _ |- _ =>
            let HH := fresh "Hdm" in
            pose proof (e_consis_defs_mono H Hd) as HH; clear H
        end
    end;
    repeat match goal with
    | IH : Forall entry_def_mono ?Θin -> Forall entry_def_mono (_ ++ _)
      |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(eauto using Forall_app_intro, Forall_cons,
                                 Forall_nil, entry_def_mono_tvar));
        simpl in HH;
        repeat (apply Forall_app in HH; destruct HH as [? HH]);
        repeat match goal with
        | H : Forall entry_def_mono (_ :: _) |- _ =>
            inversion H; subst; clear H
        end;
        clear IH
    end;
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊢ _ ⊳[ _ , _ , _ ] _ ⤳ ?Ξ ↪ _ }}e |- _ =>
        lazymatch goal with
        | _ : all_flex_mono Ξ |- _ => fail
        | _ => pose proof (e_extract_block_flex H)
        end
    end;
    eauto 10 using Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_flex, entry_def_mono_tvar, entry_def_mono_def,
      entry_def_mono_var_typ, entry_def_mono_var_skl,
      all_flex_mono_defs_mono,
      mono_ptyp__var, mono_ptyp__arrow.
Qed.

Corollary e_sub_defs_mono : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> aenv_defs_mono Θ1.
Proof.
  intros. eapply (proj1 e_sub_sub_flex_defs_mono); eassumption.
Qed.

Lemma lc_pskl_all_syn_close : forall α Q,
  lc_pskl Q -> lc_pskl (pskl_all_syn (close_pskl_wrt_pskl α Q)).
Proof.
  intros α Q HQ. apply (lc_pskl_all_syn_exists α).
  rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl. exact HQ.
Qed.

Lemma e_consis_lc : forall Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
  lc_pskl P -> lc_pskl P0 -> lc_pskl Q.
Proof.
  intros Δ1 Δ2 S0 Θ0 P0 P Q S1 Θ1 H.
  revert H.
  apply (e_consis_mind
           (fun S0 Θ Ξ α P S1 Θ' (_ : {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e)
              => True)
           (fun S0 Θ α β S1 Θ' (_ : {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e)
              => True)
           (fun Δ1 Δ2 S0 Θ P0 P Q S1 Θ' _ =>
              lc_pskl P -> lc_pskl P0 -> lc_pskl Q));
    intros; try exact I;

    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        destruct (lc_pskl_arrow_inv H); clear H
    | H : lc_pskl (pskl_univ_ghost _) |- _ =>
        pose proof (lc_pskl_univ_ghost_inv H); clear H
    end;
    eauto using lc_pskl_all_syn_close, lc_pskl_all_syn_inv,
      lc_pskl_var_f, lc_pskl_unit, lc_pskl_arrow, lc_pskl_univ_ghost.
Qed.

Lemma e_sub_sub_flex_lc :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 -> lc_pskl Q) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     lc_pskl P0 -> aenv_defs_mono Θ0 -> aenv_defs_mono Ξ -> lc_pskl Q).
Proof.
  apply e_sub_sub_flex_mutind;
    intros;
    simpl in *;

    repeat match goal with
    | H : Forall entry_def_mono (_ ++ _) |- _ =>
        apply Forall_app in H; destruct H
    | H : Forall entry_def_mono (_ :: _) |- _ =>
        inversion H; subst; clear H
    end;

    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        destruct (lc_pskl_arrow_inv H); clear H
    | H : lc_pskl (pskl_univ_ghost _) |- _ =>
        pose proof (lc_pskl_univ_ghost_inv H); clear H
    end;
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e |- _ =>
        pose proof (e_consis_lc H); pose proof (e_consis_defs_mono H); clear H
    end;
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊢ _ ⊳[ _ , _ , _ ] _ ⤳ _ ↪ _ }}e |- _ =>
        pose proof (e_extract_lc H);
        pose proof (all_flex_mono_defs_mono (e_extract_block_flex H));
        clear H
    end;
    repeat match goal with
    | H : entry_def_mono (_, abind_flex_mono_def ?tau) |- _ =>
        let HH := fresh "Hmono" in
        assert (HH : mono_ptyp tau) by exact H; clear H
    end;
    repeat match goal with
    | |- context [ if ?a == ?b then _ else _ ] => destruct (a == b); subst
    | H : context [ if ?a == ?b then _ else _ ] |- _ =>
        destruct (a == b); subst
    end;
    eauto 12 using lc_pskl_var_f, lc_pskl_unit, lc_pskl_arrow,
      lc_pskl_univ_ghost, lc_pskl_open_graft, lc_pskl_all_syn_inv,
      subst_pskl_in_pskl_lc_pskl, mono_ptyp_to_pskl_lc,
      Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_flex, entry_def_mono_tvar, entry_def_mono_def,
      entry_def_mono_var_typ, entry_def_mono_var_skl,
      mono_ptyp__var, mono_ptyp__arrow.
Qed.

Corollary e_sub_lc : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 -> lc_pskl Q.
Proof. intros. eapply (proj1 e_sub_sub_flex_lc); eassumption. Qed.

Lemma e_split_defs_mono : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> aenv_defs_mono Θ1.
Proof.
  intros * H Hdm. destruct H; try exact Hdm.

  eapply e_consis_defs_mono; [ eassumption | ].
  simpl. eauto using Forall_cons, entry_def_mono_flex.
Qed.

Lemma e_pat_defs_mono : forall S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> aenv_defs_mono Θ1.
Proof.
  intros S0 m Θ0 P0 e Q S1 Θ1 H; induction H; intros Hdm;

    repeat match goal with
    | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
    end;
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊲ _ ▹ _ ⇢ _ ⊣ _ }}e |- _ =>
        pose proof (e_split_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ⩽ _ ⊣ _ }}e |- _ =>
        pose proof (e_sub_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e |- _ =>
        pose proof (e_consis_defs_mono H); clear H
    end;
    repeat match goal with
    | IH : aenv_defs_mono ?Θin -> aenv_defs_mono (_ ++ _) |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(simpl; eauto using Forall_app_intro,
                                 Forall_cons, Forall_nil,
                                 entry_def_mono_var_skl,
                                 entry_def_mono_var_typ));
        simpl in HH;
        repeat (apply Forall_app in HH; destruct HH as [? HH]);
        repeat match goal with
        | H : Forall entry_def_mono (_ :: _) |- _ =>
            inversion H; subst; clear H
        end;
        clear IH
    end;
    eauto 8 using Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_var_skl, entry_def_mono_var_typ.
Qed.

Lemma e_typing_defs_mono : forall S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  aenv_defs_mono Θ0 -> aenv_defs_mono Θ1.
Proof.
  intros S0 m Θ0 P0 e B S1 Θ1 H; induction H; intros Hdm;
    repeat match goal with
    | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
    end;
    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊲ _ ▹ _ ⇢ _ ⊣ _ }}e |- _ =>
        pose proof (e_split_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢ˢ[ _ ; _ ] _ ⦂ _ ⊣ _ }}e |- _ =>
        pose proof (e_pat_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ⩽ _ ⊣ _ }}e |- _ =>
        pose proof (e_sub_defs_mono H); clear H
    | H : {{ _ ↝ _ ⊨ _ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e |- _ =>
        pose proof (e_consis_defs_mono H); clear H
    end;

    repeat match goal with
    | H : e_guess_mono _ _ _ ?Xs _ |- _ =>
        lazymatch goal with
        | _ : all_flex_mono Xs |- _ => fail
        | _ => pose proof (e_guess_mono_block_flex H)
        end
    end;
    repeat match goal with
    | IH : aenv_defs_mono ?Θin -> aenv_defs_mono (_ ++ _) |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(simpl; eauto 8 using Forall_app_intro,
                                 Forall_cons, Forall_nil,
                                 entry_def_mono_var_typ, entry_def_mono_tvar,
                                 all_flex_mono_defs_mono));
        simpl in HH;
        repeat (apply Forall_app in HH; destruct HH as [? HH]);
        repeat match goal with
        | H : Forall entry_def_mono (_ :: _) |- _ =>
            inversion H; subst; clear H
        end;
        clear IH
    end;
    eauto 8 using Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_var_typ, entry_def_mono_tvar,
      all_flex_mono_defs_mono.
Qed.

Lemma lc_abind_tvar : lc_abind abind_tvar.
Proof. exact I. Qed.

Lemma lc_abind_flex_mono : lc_abind abind_flex_mono.
Proof. exact I. Qed.

Lemma lc_abind_def : forall τ, lc_abind (abind_flex_mono_def τ).
Proof. intros; exact I. Qed.

Lemma lc_abind_var_typ : forall A, lc_ptyp A -> lc_abind (abind_var_typ A).
Proof. intros; assumption. Qed.

Lemma lc_abind_var_skl : forall P, lc_pskl P -> lc_abind (abind_var_skl P).
Proof. intros; assumption. Qed.

Lemma lc_aenv_cons {x b} {Θ : aenv} :
  lc_abind b -> lc_aenv Θ -> lc_aenv ((x ~ b) ++ Θ).
Proof. intros. constructor; assumption. Qed.

Lemma aenv_defs_mono_cons {x b} {Θ : aenv} :
  entry_def_mono (x, b) -> aenv_defs_mono Θ -> aenv_defs_mono ((x ~ b) ++ Θ).
Proof. intros. constructor; assumption. Qed.

Lemma all_flex_mono_lc_aenv : forall Ξ, all_flex_mono Ξ -> lc_aenv Ξ.
Proof.
  intros Ξ H. unfold lc_aenv. induction H as [ | [x b] Ξ' Hb Ht IH ];
    [ constructor | ].
  constructor; [ simpl in *; subst; exact I | exact IH ].
Qed.

Lemma a_suffix_lc_aenv : forall Ξ, a_suffix Ξ -> lc_aenv Ξ.
Proof.
  intros Ξ H. unfold lc_aenv. induction H as [ | Ξ' x b Ht IH Hb ];
    [ constructor | ].
  simpl. constructor; [ destruct Hb; exact I | exact IH ].
Qed.

Lemma all_flex_mono_lc_forall : forall Ξ,
  all_flex_mono Ξ -> Forall (fun e : atom * abind => lc_abind (snd e)) Ξ.
Proof. exact all_flex_mono_lc_aenv. Qed.

Lemma a_suffix_lc_forall : forall Ξ,
  a_suffix Ξ -> Forall (fun e : atom * abind => lc_abind (snd e)) Ξ.
Proof. exact a_suffix_lc_aenv. Qed.

Lemma lc_aenv_binds : forall (x : atom) b (Θ : aenv),
  lc_aenv Θ -> binds x b Θ -> lc_abind b.
Proof.
  intros x b Θ H. unfold lc_aenv in H.
  induction H as [ | [y b'] Θ' Hb Ht IH ]; intros Hbd; [ inversion Hbd | ].
  destruct Hbd as [Heq | Hin];
    [ inversion Heq; subst; exact Hb | exact (IH Hin) ].
Qed.

Arguments lc_aenv_binds {x b Θ} _ _.

Lemma e_assign_unify_consis_env_lc :
  (forall S0 Θ Ξ α P S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
     lc_aenv Θ -> lc_aenv Ξ -> lc_aenv Θ') /\
  (forall S0 Θ α β S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e ->
     lc_aenv Θ -> lc_aenv Θ') /\
  (forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
     lc_aenv Θ -> lc_aenv Θ').
Proof.
  apply e_assign_unify_consis_mutind;
    intros;
    unfold lc_aenv in *;
    simpl in *;
    repeat match goal with
    | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H; destruct H
    | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end;

    repeat match goal with
    | IH : Forall ?F ?Θin -> Forall ?F (_ :: _) |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(eauto using Forall_app_intro, Forall_cons,
                                 Forall_nil, lc_abind_tvar,
                                 lc_abind_flex_mono, lc_abind_def));
        inversion HH; subst; clear IH HH
    end;

    repeat match goal with
    | H : e_guess_mono _ _ _ ?Ξ _ |- _ =>
        lazymatch goal with
        | _ : all_flex_mono Ξ |- _ => fail
        | _ => pose proof (e_guess_mono_block_flex H)
        end
    end;
    eauto 8 using Forall_app_intro, Forall_cons, Forall_nil,
      all_flex_mono_lc_forall, a_suffix_lc_forall, lc_abind_tvar,
      lc_abind_flex_mono, lc_abind_def, lc_abind_var_typ, lc_abind_var_skl.
Qed.

Corollary e_consis_env_lc : forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
  {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
  lc_aenv Θ -> lc_aenv Θ'.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_env_lc)); eassumption.
Qed.

Lemma e_sub_sub_flex_env_lc :
  (forall S0 NM M P0 Θ0 P Q S1 Θ1,
     {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
     lc_aenv Θ0 -> lc_aenv Θ1) /\
  (forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
     e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
     lc_aenv Θ0 -> lc_aenv Ξ -> lc_aenv Θ1).
Proof.
  apply e_sub_sub_flex_mutind;
    intros;
    unfold lc_aenv in *;
    simpl in *;
    repeat match goal with
    | H : e_consis_chk _ _ _ _ _ _ |- _ => destruct H as [? H]
    end;
    repeat match goal with
    | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H; destruct H
    | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end;

    repeat match goal with
    | H : {{ _ ↝ _ ⊨ ?Θ ⊢[ _ | _ | _ ] _ ∼ _ ⊣ _ }}e |- _ =>
        let HH := fresh "Hlc" in
        pose proof (e_consis_env_lc H) as HH; unfold lc_aenv in HH; clear H
    end;

    repeat match goal with
    | IH : Forall ?F ?Θin -> Forall ?F (_ ++ _) |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(eauto using Forall_app_intro, Forall_cons,
                                 Forall_nil, lc_abind_tvar,
                                 lc_abind_flex_mono, lc_abind_def));
        simpl in HH;
        repeat (apply Forall_app in HH; destruct HH as [? HH]);
        repeat match goal with
        | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
        end;
        clear IH
    end;

    repeat match goal with
    | H : {{ _ ↝ _ ⊨ _ ⊢ _ ⊳[ _ , _ , _ ] _ ⤳ ?Ξ ↪ _ }}e |- _ =>
        lazymatch goal with
        | _ : all_flex_mono Ξ |- _ => fail
        | _ => pose proof (e_extract_block_flex H)
        end
    end;
    eauto 10 using Forall_app_intro, Forall_cons, Forall_nil,
      all_flex_mono_lc_forall, a_suffix_lc_forall, lc_abind_tvar,
      lc_abind_flex_mono, lc_abind_def, lc_abind_var_typ, lc_abind_var_skl.
Qed.

Corollary e_sub_env_lc : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  lc_aenv Θ0 -> lc_aenv Θ1.
Proof. intros. eapply (proj1 e_sub_sub_flex_env_lc); eassumption. Qed.

Lemma e_split_lc : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  lc_pskl P0 -> lc_pskl P /\ lc_pskl Q.
Proof.
  intros * H Hlc. destruct H.
  - destruct (lc_pskl_arrow_inv Hlc). split; assumption.
  - split; constructor.
  - split; apply lc_pskl_var_f.
Qed.

Lemma e_split_env_lc : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
  lc_aenv Θ0 -> lc_aenv Θ1.
Proof.
  intros * H Hlc. destruct H; [ assumption | assumption | ].
  eapply e_consis_env_lc; [ eassumption | ].
  unfold lc_aenv in *; simpl.
  constructor; [ exact I | ]. constructor; [ exact I | ]. assumption.
Qed.

Ltac open_exp_lc x :=
  match goal with
  | Hx : forall _ : _, lc_exp (open_exp_wrt_exp _ (exp_var_f _)) |- _ =>
      exact (Hx x)
  end.

Local Ltac drop_binder H :=
  unfold lc_aenv in *; simpl in H;
  apply Forall_app in H; destruct H as [? H];
  inversion H; subst;
  solve [ apply Forall_app; split; assumption | assumption ].

Lemma e_pat_lc_env : forall S0 m Θ0 P0 e Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ1 }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 ->
  lc_pskl Q /\ lc_aenv Θ1.
Proof.
  intros S0 m Θ0 P0 e Q S1 Θ1 H.
  induction H; intros HP0 He HΘ Hdm.
  -
    split; [ eapply e_sub_lc | eapply e_sub_env_lc ];
      eauto using lc_pskl_unit.
  -
    assert (HA : lc_ptyp A)
      by (exact (lc_aenv_binds HΘ H)).
    split; [ eapply e_sub_lc | eapply e_sub_env_lc ];
      eauto using ptyp_to_pskl_lc.
  -
    assert (HA : lc_pskl P)
      by (exact (lc_aenv_binds HΘ H)).
    split; [ eapply e_sub_lc | eapply e_sub_env_lc ]; eauto.
  -
    inversion He; subst.
    split; [ eapply e_sub_lc | eapply e_sub_env_lc ];
      eauto using ptyp_to_pskl_lc.
  -
    inversion He; subst. apply IHe_pat; auto.
  -
    inversion He; subst.
    destruct (e_split_lc H0 HP0) as [HPlc HQ0lc].
    pose proof (e_split_env_lc H0 HΘ) as HΘ1.
    pose proof (e_split_defs_mono H0 Hdm) as Hdm1.
    destruct (IHe_pat HQ0lc ltac:(open_exp_lc x)
                (lc_aenv_cons (lc_abind_var_skl HPlc) HΘ1)
                (aenv_defs_mono_cons (entry_def_mono_var_skl _ _) Hdm1))
      as [HQlc HΘout].
    split; [ apply lc_pskl_arrow; assumption | ].
    drop_binder HΘout.
  -
    inversion He; subst.
    destruct (e_split_lc H0 HP0) as [HPlc HQ0lc].
    pose proof (e_split_env_lc H0 HΘ) as HΘ1.
    pose proof (e_split_defs_mono H0 Hdm) as Hdm1.
    destruct H1 as [Qm Hc].
    pose proof (e_consis_env_lc Hc HΘ1) as HΘ2.
    pose proof (e_consis_defs_mono Hc Hdm1) as Hdm2.
    destruct (IHe_pat HQ0lc ltac:(open_exp_lc x) ltac:(unfold lc_aenv in *; simpl;
                constructor; [ simpl; assumption | exact HΘ2 ])
                (aenv_defs_mono_cons (entry_def_mono_var_typ _ _) Hdm2))
      as [HQlc HΘout].
    split; [ apply lc_pskl_arrow;
             [ apply ptyp_to_pskl_lc; assumption | assumption ] | ].
    drop_binder HΘout.
  -
    inversion He; subst.
    destruct (IHe_pat (lc_pskl_ghost) ltac:(open_exp_lc x)
                (lc_aenv_cons (lc_abind_var_skl lc_pskl_ghost) HΘ)
                (aenv_defs_mono_cons (entry_def_mono_var_skl _ _) Hdm))
      as [HQlc HΘout].
    split; [ apply lc_pskl_univ_ghost; apply lc_pskl_arrow;
             [ exact lc_pskl_ghost | exact HQlc ] | ].
    drop_binder HΘout.
  -
    inversion He; subst.
    destruct (IHe_pat (lc_pskl_ghost) ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl;
                      constructor; [ simpl; assumption | exact HΘ ])
                (aenv_defs_mono_cons (entry_def_mono_var_typ _ _) Hdm))
      as [HQlc HΘout].
    split; [ apply lc_pskl_univ_ghost; apply lc_pskl_arrow;
             [ apply ptyp_to_pskl_lc; assumption | exact HQlc ] | ].
    drop_binder HΘout.
  -
    inversion He; subst.
    destruct (IHe_pat1 lc_pskl_ghost ltac:(assumption) HΘ Hdm)
      as [HP0lc HΘ1].
    pose proof (e_pat_defs_mono H Hdm) as Hdm1.
    destruct (IHe_pat2 ltac:(apply lc_pskl_arrow; assumption)
                ltac:(assumption) HΘ1 Hdm1) as [HPQlc HΘ2].
    split; [ exact (proj2 (lc_pskl_arrow_inv HPQlc)) | exact HΘ2 ].
Qed.

Local Ltac paint_lc :=
  repeat match goal with
  | H : lc_pskl (ptyp_to_pskl ?A) |- _ =>
      lazymatch goal with
      | _ : lc_ptyp A |- _ => clear H
      | _ => apply ptyp_to_pskl_lc_inv in H
      end
  end.

Local Ltac open_all_lc :=
  apply ptyp_to_pskl_lc;
  match goal with
  | H : lc_ptyp (ptyp_all _) |- _ => inversion H; subst
  end;
  match goal with
  | Hx : forall _ : _, lc_ptyp (open_ptyp_wrt_ptyp _ (ptyp_var_f _)) |- _ =>
      apply Hx
  end.

Lemma e_typing_lc_env : forall S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 ->
  lc_ptyp B /\ lc_aenv Θ1.
Proof.
  intros S0 m Θ0 P0 e B S1 Θ1 H.
  induction H; intros HP0 He HΘ Hdm.
  -
    pose proof (e_sub_lc H lc_pskl_unit HP0 Hdm) as Hout. paint_lc.
    split; [ assumption | eapply e_sub_env_lc; eassumption ].
  -
    assert (HA : lc_ptyp A) by (exact (lc_aenv_binds HΘ H)).
    pose proof (e_sub_lc H0 (ptyp_to_pskl_lc HA) HP0 Hdm) as Hout. paint_lc.
    split; [ assumption | eapply e_sub_env_lc; eassumption ].
  -
    inversion He; subst.
    destruct (IHe_typing ltac:(apply ptyp_to_pskl_lc; assumption)
                ltac:(assumption) HΘ Hdm) as [HAlc HΘ1].
    pose proof (e_typing_defs_mono H Hdm) as Hdm1.
    pose proof (e_sub_lc H0 (ptyp_to_pskl_lc HAlc) HP0 Hdm1) as Hout.
    paint_lc.
    split; [ assumption | eapply e_sub_env_lc; eassumption ].
  -
    inversion He; subst. paint_lc.
    destruct H0 as [Qm Hc].
    destruct (IHe_typing lc_pskl_ghost ltac:(assumption) HΘ Hdm)
      as [HBlc HΘ1].
    pose proof (e_typing_defs_mono H Hdm) as Hdm1.
    split; [ assumption | eapply e_consis_env_lc; eassumption ].
  -
    inversion He; subst.
    destruct (e_split_lc H0 HP0) as [HPlc HQlc].
    pose proof (e_split_env_lc H0 HΘ) as HΘ1.
    pose proof (e_split_defs_mono H0 Hdm) as Hdm1.
    pose proof (e_guess_mono_lc H1) as HAlc.
    pose proof (e_guess_mono_block_flex H1) as Hflex.
    destruct (IHe_typing HQlc ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ simpl; exact HAlc
                      | apply Forall_app; split;
                        [ apply all_flex_mono_lc_forall; exact Hflex
                        | exact HΘ1 ] ])
                ltac:(simpl; constructor;
                      [ exact I
                      | apply Forall_app; split;
                        [ apply all_flex_mono_defs_mono; exact Hflex
                        | exact Hdm1 ] ])) as [HBlc HΘout].
    split; [ apply lc_ptyp_arrow; assumption | drop_binder HΘout ].
  -
    inversion He; subst.
    destruct (e_split_lc H0 HP0) as [HPlc HQlc].
    pose proof (e_split_env_lc H0 HΘ) as HΘ1.
    pose proof (e_split_defs_mono H0 Hdm) as Hdm1.
    destruct H1 as [Qm Hc].
    pose proof (e_consis_env_lc Hc HΘ1) as HΘ2.
    pose proof (e_consis_defs_mono Hc Hdm1) as Hdm2.
    destruct (IHe_typing HQlc ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ simpl; assumption | exact HΘ2 ])
                (aenv_defs_mono_cons (entry_def_mono_var_typ _ _) Hdm2))
      as [HBlc HΘout].
    split; [ apply lc_ptyp_arrow; assumption | drop_binder HΘout ].
  -
    paint_lc.
    destruct (IHe_typing
                ltac:(open_all_lc)
                ltac:(assumption)
                (lc_aenv_cons lc_abind_tvar HΘ)
                (aenv_defs_mono_cons (entry_def_mono_tvar _) Hdm))
      as [HAlc HΘout].
    split; [ apply (lc_ptyp_all_exists α); exact HAlc | drop_binder HΘout ].
  -
    inversion He; subst. paint_lc.
    destruct (e_split_lc H (ptyp_to_pskl_lc HP0)) as [HAlc HBlc]. paint_lc.
    pose proof (e_split_env_lc H HΘ) as HΘ1.
    pose proof (e_split_defs_mono H Hdm) as Hdm1.
    destruct (IHe_typing ltac:(apply ptyp_to_pskl_lc; assumption)
                ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ simpl; assumption | exact HΘ1 ])
                (aenv_defs_mono_cons (entry_def_mono_var_typ _ _) Hdm1))
      as [HB1lc HΘout].
    split; [ apply lc_ptyp_arrow; assumption | drop_binder HΘout ].
  -
    paint_lc.
    destruct (IHe_typing
                ltac:(open_all_lc)
                ltac:(assumption)
                (lc_aenv_cons lc_abind_tvar HΘ)
                (aenv_defs_mono_cons (entry_def_mono_tvar _) Hdm))
      as [HAlc HΘout].
    split; [ apply (lc_ptyp_all_exists α); exact HAlc | drop_binder HΘout ].
  -
    inversion He; subst. paint_lc.
    destruct (e_split_lc H (ptyp_to_pskl_lc HP0)) as [HA'lc HBlc]. paint_lc.
    pose proof (e_split_env_lc H HΘ) as HΘ1.
    pose proof (e_split_defs_mono H Hdm) as Hdm1.
    destruct H0 as [Qm Hc].
    pose proof (e_consis_env_lc Hc HΘ1) as HΘ2.
    pose proof (e_consis_defs_mono Hc Hdm1) as Hdm2.
    destruct (IHe_typing ltac:(apply ptyp_to_pskl_lc; assumption)
                ltac:(open_exp_lc x)
                ltac:(unfold lc_aenv in *; simpl; constructor;
                      [ simpl; assumption | exact HΘ2 ])
                (aenv_defs_mono_cons (entry_def_mono_var_typ _ _) Hdm2))
      as [HB1lc HΘout].
    split; [ apply lc_ptyp_arrow; assumption | drop_binder HΘout ].
  -
    inversion He; subst.
    destruct (e_pat_lc_env H lc_pskl_ghost ltac:(assumption) HΘ Hdm)
      as [HPlc HΘ1].
    pose proof (e_pat_defs_mono H Hdm) as Hdm1.
    destruct (IHe_typing1 ltac:(apply lc_pskl_arrow; assumption)
                ltac:(assumption) HΘ1 Hdm1) as [HABlc HΘ2].
    pose proof (e_typing_defs_mono H0 Hdm1) as Hdm2.
    inversion HABlc; subst.
    destruct (IHe_typing2 ltac:(apply ptyp_to_pskl_lc; assumption)
                ltac:(assumption) HΘ2 Hdm2) as [HA'lc HΘ3].
    split; [ assumption | exact HΘ3 ].
Qed.
