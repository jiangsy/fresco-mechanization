Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.prop_atom_sets.
Require Import src.fresco.prop_ln.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.prop_dec.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.consistency.prop_consis.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.prop_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.prop_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.prop_extract.
Require Import src.fresco.ext_algo.subtyping.def_sub.
Require Import src.fresco.ext_algo.subtyping.prop_sub.
Require Import src.fresco.ext_algo.typing.def_pat.
Require Import src.fresco.ext_algo.typing.prop_pat.
Require Import src.fresco.ext_algo.typing.def_typing.
Require Import src.fresco.ext_algo.typing.prop_typing.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.prop_run_invariants.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.
Require Import src.fresco.ext_algo.consistency.prop_consis_complete.
Require Import src.fresco.ext_algo.subtyping.def_extract_impl.
Require Import src.fresco.ext_algo.subtyping.prop_extract_det.
Require Import src.fresco.ext_algo.subtyping.def_sub_impl.
Require Import src.fresco.ext_algo.subtyping.prop_sub_complete.
Require Import src.fresco.ext_algo.typing.def_pat_impl.
Require Import src.fresco.ext_algo.typing.prop_pat_complete.
Require Import src.fresco.ext_algo.typing.def_typing_impl.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

Lemma swaps_ptyp_ftv_notin : forall ps A x,
  x `notin` ftvar_in_ptyp A ->
  swaps_atom ps x `notin` ftvar_in_ptyp (swaps_ptyp ps A).
Proof.
  induction ps as [ | [a b] ps IH ]; intros A x Hx; simpl; [ exact Hx | ].
  apply IH. apply swap_ptyp_ftv_notin. exact Hx.
Qed.

Lemma swaps_block_ftv_filter : forall ps (Ξ : aenv) A,
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
  forall γ, γ `in` dom (swaps_aenv ps Ξ) ->
            γ `notin` ftvar_in_ptyp (swaps_ptyp ps A).
Proof.
  induction ps as [ | [a b] ps IH ]; intros Ξ A Hf; simpl; [ exact Hf | ].
  apply IH. apply swap_block_ftv_filter. exact Hf.
Qed.

Lemma e_typing_swaps : forall ps S0 m Θ0 P0 e B S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ B ⊣ Θ1 }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊢[ m ; (swaps_pskl ps P0) ]
       (swaps_exp ps e) ⦂ (swaps_ptyp ps B) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_typing_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_typing_swap (a := a) (b := b) Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

#[local] Arguments ptyp_to_pskl_inj {A B} _.

Lemma swaps_aenv_one_tvar : forall ps x,
  swaps_aenv ps (x ~ abind_tvar) = (swaps_atom ps x ~ abind_tvar).
Proof.
  intros. unfold one.
  rewrite swaps_aenv_cons, swaps_abind_tvar, swaps_aenv_nil. reflexivity.
Qed.

Lemma swaps_ptyp_open : forall ps A1 A2,
  swaps_ptyp ps (open_ptyp_wrt_ptyp A1 A2)
  = open_ptyp_wrt_ptyp (swaps_ptyp ps A1) (swaps_ptyp ps A2).
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; [ reflexivity | ].
  rewrite swap_ptyp_open. apply IH.
Qed.

Lemma lc_ptyp_all_close : forall α A,
  lc_ptyp A -> lc_ptyp (ptyp_all (close_ptyp_wrt_ptyp α A)).
Proof.
  intros α A HA. apply (lc_ptyp_all_exists α).
  rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp. exact HA.
Qed.

Lemma e_guess_mono_lc_type : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> lc_pskl P -> lc_ptyp A.
Proof.
  intros * Hg; induction Hg; intros Hlc.
  - apply lc_ptyp_var_f.
  - apply IHHg. exact (lc_pskl_univ_ghost_inv Hlc).
  - apply lc_ptyp_var_f.
  - apply lc_ptyp_unit.
  - destruct (lc_pskl_arrow_inv Hlc) as [Hl1 Hl2].
    apply lc_ptyp_arrow; auto.
  - apply lc_ptyp_all_close. apply IHHg.
    exact (lc_pskl_all_syn_inv Hlc β).
Qed.

Lemma e_guess_mono_block_binding : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A ->
  forall x b, In (x, b) Ξ -> b = abind_flex_mono.
Proof.
  intros * Hg x b Hin.
  pose proof (e_guess_mono_block_flex Hg) as Hflex.
  unfold src.fresco.algo.basic.prop_metasubst.all_flex_mono in Hflex.
  rewrite Forall_forall in Hflex.
  exact (Hflex (x, b) Hin).
Qed.

Lemma e_guess_mono_block_lc : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> lc_aenv Ξ.
Proof.
  intros * Hg. unfold lc_aenv. apply Forall_forall.
  intros [y b] Hin. rewrite (e_guess_mono_block_binding Hg y b Hin).
  exact I.
Qed.

Lemma e_guess_mono_block_defs_mono : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> aenv_defs_mono Ξ.
Proof.
  intros * Hg. apply Forall_forall.
  intros [y b] Hin. rewrite (e_guess_mono_block_binding Hg y b Hin).
  apply entry_def_mono_flex.
Qed.

Lemma e_guess_mono_ftv_supply : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> ftvar_in_pskl P [<=] S0 ->
  ftvar_in_ptyp A [<=] S1.
Proof.
  intros * Hg Hcov.
  pose proof (e_guess_mono_ftv Hg) as Hftv.
  pose proof (e_guess_mono_generated_in_supply Hg) as Hdom.
  pose proof (e_guess_mono_supply_grows Hg) as Hgr.
  clear - Hftv Hdom Hgr Hcov. fsetdec.
Qed.

Lemma e_typing_inv_unit : forall S0 m Θ0 P0 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] exp_unit ⦂ Bd ⊣ Θd }}e ->
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ a_sub_mode_ty | m | P0 ]
     pskl_unit ⩽ (ptyp_to_pskl Bd) ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. assumption. Qed.

Lemma e_typing_inv_var_b : forall S0 m Θ0 P0 n Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_var_b n) ⦂ Bd ⊣ Θd }}e -> False.
Proof. intros * H. inversion H. Qed.

Lemma e_typing_inv_var : forall S0 m Θ0 P0 x Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_var_f x) ⦂ Bd ⊣ Θd }}e ->
  exists A, binds x (abind_var_typ A) Θ0
    /\ {{ S0 ↝ Sd ⊨ Θ0 ⊢[ a_sub_mode_ty | m | P0 ]
          (ptyp_to_pskl A) ⩽ (ptyp_to_pskl Bd) ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. eauto. Qed.

Lemma e_typing_inv_anno : forall S0 m Θ0 P0 e1 A Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_anno e1 A) ⦂ Bd ⊣ Θd }}e ->
  exists S1 Θ1,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e1 ⦂ A ⊣ Θ1 }}e
    /\ {{ S1 ↝ Sd ⊨ Θ1 ⊢[ a_sub_mode_ty | m | P0 ]
          (ptyp_to_pskl A) ⩽ (ptyp_to_pskl Bd) ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. eauto. Qed.

Lemma e_typing_inv_freeze : forall S0 m Θ0 P0 e1 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_freeze e1) ⦂ Bd ⊣ Θd }}e ->
  m = mode_tc /\ P0 = ptyp_to_pskl Bd
  /\ exists S1 Θ1 B,
       {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_ti ; pskl_ghost ] e1 ⦂ B ⊣ Θ1 }}e
       /\ e_consis_chk S1 Θ1 (ptyp_to_pskl B) (ptyp_to_pskl Bd) Sd Θd.
Proof.
  intros * H. inversion H; subst.
  split; [ reflexivity | ]. split; [ reflexivity | ]. eauto.
Qed.

Lemma e_typing_inv_app : forall S0 m Θ0 P0 e1 e2 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_app e1 e2) ⦂ Bd ⊣ Θd }}e ->
  exists S1 S2 Θ1 Θ2 P A A',
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P ⊣ Θ1 }}e
    /\ {{ S1 ↝ S2 ⊨ Θ1 ⊢[ (mode_fn m) ; (pskl_arrow P P0) ] e1
          ⦂ (ptyp_arrow A Bd) ⊣ Θ2 }}e
    /\ {{ S2 ↝ Sd ⊨ Θ2 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e2 ⦂ A' ⊣ Θd }}e.
Proof. intros * H. inversion H; subst. eauto 12. Qed.

Lemma e_typing_inv_abs_all : forall S0 m Θ0 P0 e1 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_abs e1) ⦂ Bd ⊣ Θd }}e ->
  (m <> mode_tc /\
   exists x S1 S2 Θ1 Θ2 P Q αs A B Ξ,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e
     /\ e_guess_mono S1 P S2 αs A
     /\ a_suffix Ξ /\ x `notin` S2
     /\ {{ (add x S2) ↝ Sd ⊨ ((x ~ abind_var_typ A) ++ αs ++ Θ1)
           ⊢[ (decr_mode m) ; Q ] (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ B
           ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) }}e
     /\ Bd = ptyp_arrow A B /\ Θd = Ξ ++ Θ2)
  \/ (m = mode_tc /\
      exists α A0 A Ξ,
        P0 = ptyp_to_pskl (ptyp_all A0) /\ Bd = ptyp_all A
        /\ a_suffix Ξ /\ uniq (Ξ ++ Θ0)
        /\ (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A)
        /\ α `notin` ftvar_in_ptyp A /\ α `notin` S0
        /\ {{ (add α S0) ↝ Sd ⊨ ((α ~ abind_tvar) ++ Θ0)
              ⊢[ mode_tc ;
                 (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
              (exp_abs e1) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
              ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θd) }}e)
  \/ (m = mode_tc /\
      exists x S1 Θ1 A0 A B B1 Ξ,
        P0 = ptyp_to_pskl A0 /\ Bd = ptyp_arrow A B1
        /\ {{ S0 ↝ S1 ⊨ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A)
              ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}e
        /\ a_suffix Ξ /\ uniq (Ξ ++ Θ1)
        /\ (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1)
        /\ x `notin` S1
        /\ {{ (add x S1) ↝ Sd ⊨ ((x ~ abind_var_typ A) ++ Θ1)
              ⊢[ mode_tc ; (ptyp_to_pskl B) ]
              (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ B1
              ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θd) }}e).
Proof.
  intros * H. inversion H; subst;
    [ left; split; [ assumption | eauto 20 ]
    | right; left; split; [ reflexivity | eauto 20 ]
    | right; right; split; [ reflexivity | eauto 20 ] ].
Qed.

Lemma e_typing_inv_abs_anno_all : forall S0 m Θ0 P0 Aan e1 Bd Sd Θd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] (exp_abs_anno Aan e1) ⦂ Bd ⊣ Θd }}e ->
  (m <> mode_tc /\
   exists x S1 S2 Θ1 Θ2 Θ3 P Q B Ξ,
     {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e
     /\ e_consis_chk S1 Θ1 (ptyp_to_pskl Aan) P S2 Θ2
     /\ a_suffix Ξ /\ x `notin` S2
     /\ {{ (add x S2) ↝ Sd ⊨ ((x ~ abind_var_typ Aan) ++ Θ2)
           ⊢[ (decr_mode m) ; Q ] (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ B
           ⊣ (Ξ ++ (x ~ abind_var_typ Aan) ++ Θ3) }}e
     /\ Bd = ptyp_arrow Aan B /\ Θd = Ξ ++ Θ3)
  \/ (m = mode_tc /\
      exists α A0 A Ξ,
        P0 = ptyp_to_pskl (ptyp_all A0) /\ Bd = ptyp_all A
        /\ a_suffix Ξ /\ uniq (Ξ ++ Θ0)
        /\ (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A)
        /\ α `notin` ftvar_in_ptyp A /\ α `notin` S0
        /\ {{ (add α S0) ↝ Sd ⊨ ((α ~ abind_tvar) ++ Θ0)
              ⊢[ mode_tc ;
                 (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
              (exp_abs_anno Aan e1) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
              ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θd) }}e)
  \/ (m = mode_tc /\
      exists x S1 S2 Θ1 Θ2 A0 A' B B1 Ξ,
        P0 = ptyp_to_pskl A0 /\ Bd = ptyp_arrow A' B1
        /\ {{ S0 ↝ S1 ⊨ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A')
              ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}e
        /\ e_consis_chk S1 Θ1 (ptyp_to_pskl A') (ptyp_to_pskl Aan) S2 Θ2
        /\ a_suffix Ξ /\ uniq (Ξ ++ Θ2)
        /\ (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1)
        /\ x `notin` S2
        /\ {{ (add x S2) ↝ Sd ⊨ ((x ~ abind_var_typ Aan) ++ Θ2)
              ⊢[ mode_tc ; (ptyp_to_pskl B) ]
              (open_exp_wrt_exp e1 (exp_var_f x)) ⦂ B1
              ⊣ (Ξ ++ (x ~ abind_var_typ Aan) ++ Θd) }}e).
Proof.
  intros * H. inversion H; subst;
    [ left; split; [ assumption | eauto 20 ]
    | right; left; split; [ reflexivity | eauto 20 ]
    | right; right; split; [ reflexivity | eauto 25 ] ].
Qed.

Lemma pskl_readback_complete_eq : forall P A,
  P = ptyp_to_pskl A ->
  exists r, pskl_readback P = Some r /\ proj1_sig r = A.
Proof. intros P A ->. apply pskl_readback_complete. Qed.

Arguments pskl_readback_complete_eq {P A} _.

Lemma pskl_readback_all_complete_eq : forall P A0,
  P = ptyp_to_pskl (ptyp_all A0) ->
  exists r, pskl_readback_all P = Some r /\ proj1_sig r = A0.
Proof. intros P A0 ->. apply pskl_readback_all_complete. Qed.

Arguments pskl_readback_all_complete_eq {P A0} _.

Lemma ptyp_arrow_split_complete_eq : forall A A1 A2,
  A = ptyp_arrow A1 A2 ->
  exists r, ptyp_arrow_split A = Some r /\ proj1_sig r = (A1, A2).
Proof. intros A A1 A2 ->. apply ptyp_arrow_split_complete. Qed.

Definition typing_answer {S0 : supply} {m : mode} {Θ0 : aenv} {P0 : pskl}
    {e : exp} (o : option (sig (typing_spec S0 m Θ0 P0 e)))
    : option typing_result :=
  match o with None => None | Some r => Some (proj1_sig r) end.

Definition typing_complete (S0 : supply) (m : mode) (Θ0 : aenv) (P0 : pskl)
    (e : exp) : Prop :=
  forall (H : e_typing_order S0 m Θ0 P0 e),
    lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
    ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
      [<=] S0 ->
    forall Sd Θd Bd,
      {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e ->
    exists r ps,
      typing_answer (e_typing_impl S0 m Θ0 P0 e H) = Some r
      /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
      /\ swaps_atoms ps Sd [=] ty_supply r
      /\ swaps_aenv ps Θd = ty_ctx r
      /\ swaps_ptyp ps Bd = ty_out r.

Local Ltac ck_leaf_ty :=
  solve [ apply defs_mono_ck_complete; assumption
        | apply lc_pskl_ck_complete; assumption
        | apply lc_ptyp_ck_complete; assumption
        | apply suffix_ck_complete; assumption
        | apply uniq_ck_complete; assumption
        | apply pskl_eqb_complete; congruence
        | apply ptyp_eqb_complete; congruence
        | apply inter_is_empty_complete; assumption ].

Local Ltac bool_true_ty := bool_true_with ltac:(idtac; ck_leaf_ty).

Local Ltac kill_sub Hder Hu0 Hcov0 r Hr ps Hav HS HT HQ :=
  match goal with
  | |- context [ e_sub_impl ?S ?nm ?mm ?p0 ?T ?p ?hp ?hp0 ?hd ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let r0 := fresh "r0" in let Heqr := fresh "Heqr" in
      destruct (e_sub_impl_complete hp hp0 hd h Hder Hu0 Hcov0)
        as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_sub_impl S nm mm p0 T p hp hp0 hd h)
        as [ [r Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx;
      [ assert (Heqr : r0 = exist (sub_spec S nm mm p0 T p) r Hr)
          by congruence;
        subst r0; cbn [proj1_sig] in HS, HT, HQ;
        clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

Local Ltac kill_typing Hmot Hp0 He0 HΘ0 HD0 Hu0 Hcov0 Hder r Hr ps
    Hav HS HT HQ :=
  match goal with
  | |- context [ e_typing_impl ?S ?mm ?T ?p0 ?ee ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let r0 := fresh "r0" in let Heqr := fresh "Heqr" in
      destruct (Hmot h Hp0 He0 HΘ0 HD0 Hu0 Hcov0 _ _ _ Hder)
        as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_typing_impl S mm T p0 ee h) as [ [r Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx; cbn [typing_answer proj1_sig] in Hx;
      [ assert (Heqr : r0 = r) by congruence;
        subst r0; clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

Local Ltac kill_pat_call Hp0 He0 HΘ0 HD0 Hu0 Hcov0 Hder r Hr ps
    Hav HS HT HQ :=
  match goal with
  | |- context [ e_pat_impl ?S ?mm ?T ?p0 ?ee ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let r0 := fresh "r0" in let Heqr := fresh "Heqr" in
      destruct (e_pat_impl_complete h Hder Hp0 He0 HΘ0 HD0 Hu0 Hcov0)
        as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_pat_impl S mm T p0 ee h) as [ [r Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx;
      [ assert (Heqr : r0 = exist (pat_spec S mm T p0 ee) r Hr)
          by congruence;
        subst r0; cbn [proj1_sig] in HS, HT, HQ;
        clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

Lemma e_typing_draw_term : forall S m Θ P e A x Sd Ξ Θd B,
  x `notin` S ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_ptyp A
    ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S ->
  {{ (add x S) ↝ Sd ⊨ ((x ~ abind_var_typ A) ++ Θ)
     ⊢[ m ; P ] open_exp_wrt_exp e (exp_var_f x) ⦂ B
     ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θd) }}e ->
  exists Sd', Sd' [=] swaps_atoms ((x, supply_fresh S) :: nil) Sd /\
    swaps_aenv ((x, supply_fresh S) :: nil) Θ = Θ /\
    swaps_ptyp ((x, supply_fresh S) :: nil) A = A /\
    {{ (add (supply_fresh S) S) ↝ Sd' ⊨
       ((supply_fresh S ~ abind_var_typ A) ++ Θ)
       ⊢[ m ; P ] open_exp_wrt_exp e (exp_var_f (supply_fresh S))
       ⦂ swaps_ptyp ((x, supply_fresh S) :: nil) B
       ⊣ (swaps_aenv ((x, supply_fresh S) :: nil) Ξ
           ++ (supply_fresh S ~ abind_var_typ A)
           ++ swaps_aenv ((x, supply_fresh S) :: nil) Θd) }}e.
Proof.
  intros * Hx Hscope Hd.
  destruct (swaps_onto_fresh Hx) as (Hav & Hatom & HSadd).
  assert (HΘ : swaps_aenv ((x, supply_fresh S) :: nil) Θ = Θ)
    by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav);
        clear - Hscope; fsetdec).
  assert (HA : swaps_ptyp ((x, supply_fresh S) :: nil) A = A)
    by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav);
        clear - Hscope; fsetdec).
  destruct (e_typing_swaps ((x, supply_fresh S) :: nil) Hd HSadd)
    as (Sd' & HS & Hd').
  rewrite !swaps_aenv_app_dist, !swaps_aenv_one_var_typ, swaps_exp_open_var,
    Hatom, HΘ, HA, (swaps_pskl_fresh_id _ P), (swaps_exp_fresh_id _ e) in Hd'
    by (apply (swaps_dodge_sub Hav); clear - Hscope; fsetdec).
  exists Sd'. exact (conj HS (conj HΘ (conj HA Hd'))).
Qed.

Arguments e_typing_draw_term {S m Θ P} e {A x Sd Ξ Θd B} _ _ _.

Lemma typing_complete_forall_step : forall S0 Θ0 A0 e Sd Θd A Ξ αd,
  typing_complete (add (supply_fresh S0) S0) mode_tc
    ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
    (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f (supply_fresh S0)))) e ->
  lc_pskl (ptyp_to_pskl (ptyp_all A0)) -> lc_exp e -> lc_aenv Θ0 ->
  aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl (ptyp_to_pskl (ptyp_all A0))
    ∪ fvar_in_exp e ∪ ftvar_in_exp e [<=] S0 ->
  a_suffix Ξ -> uniq (Ξ ++ Θ0) ->
  (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
  αd `notin` ftvar_in_ptyp A -> αd `notin` S0 ->
  {{ (add αd S0) ↝ Sd ⊨ ((αd ~ abind_tvar) ++ Θ0)
     ⊢[ mode_tc ; ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f αd)) ]
     e ⦂ open_ptyp_wrt_ptyp A (ptyp_var_f αd)
     ⊣ (Ξ ++ (αd ~ abind_tvar) ++ Θd) }}e ->
  forall h, exists r Hr ps Ξr Θr,
    e_typing_impl (add (supply_fresh S0) S0) mode_tc
      ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
      (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f (supply_fresh S0)))) e h
      = Some (exist _ r Hr) /\
    uniq (ty_ctx r) /\
    ty_ctx r = Ξr ++ (supply_fresh S0 ~ abind_tvar) ++ Θr /\
    a_suffix Ξr /\ uniq (Ξr ++ Θ0) /\
    dom Ξr ∩ ftvar_in_ptyp (close_ptyp_wrt_ptyp (supply_fresh S0) (ty_out r)) [=] empty /\
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps Sd [=] ty_supply r /\ swaps_aenv ps Θd = Θr /\
    close_ptyp_wrt_ptyp (supply_fresh S0) (ty_out r) = swaps_ptyp ps A.
Proof.
  intros S0 Θ0 A0 e Sd Θd A Ξ αd Hstep HP0 He HΘ HD Hu Hcov
    Hsuf HuΞ Hfil HαA Hαd Db h.
  destruct (swaps_onto_fresh Hαd) as (Hav0 & Hsαd & HSadd).
  assert (HfixΘ : swaps_aenv ((αd, supply_fresh S0) :: nil) Θ0 = Θ0)
    by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav0);
        clear - Hcov; simpl in *; fsetdec).
  assert (HcA0 : ftvar_in_ptyp A0 [<=] S0).
  { pose proof (ftvar_ptyp_to_pskl (ptyp_all A0)) as Hpa.
    simpl in Hpa. clear - Hcov Hpa. simpl in *. fsetdec. }
  assert (HfixA0 : swaps_ptyp ((αd, supply_fresh S0) :: nil) A0 = A0)
    by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav0);
        clear - HcA0; fsetdec).
  assert (Hfixe : swaps_exp ((αd, supply_fresh S0) :: nil)
                    e = e)
    by (apply swaps_exp_fresh_id, (swaps_dodge_sub Hav0);
        clear - Hcov; simpl in *; fsetdec).
  destruct (e_typing_swaps ((αd, supply_fresh S0) :: nil) Db HSadd)
    as [Sd1 [HSd1 Db1]].
  rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_tvar in Db1.
  rewrite ! swaps_pskl_ptyp_to_pskl, ! swaps_ptyp_open,
    ! swaps_ptyp_var_f in Db1.
  rewrite Hsαd, HfixΘ, HfixA0, Hfixe in Db1.

  assert (HA0lc : lc_ptyp (ptyp_all A0))
    by (eapply ptyp_to_pskl_lc_inv; exact HP0).
  assert (Hlcop : lc_pskl (ptyp_to_pskl
            (open_ptyp_wrt_ptyp A0 (ptyp_var_f (supply_fresh S0)))))
    by (apply ptyp_to_pskl_lc; inversion HA0lc; subst; auto).
  assert (HcΘ : ftvar_in_aenv Θ0 [<=] S0) by (clear - Hcov; fsetdec).
  destruct (push_fresh_invariants Hu HΘ HD HcΘ lc_abind_tvar
              (entry_def_mono_tvar _)) as (Hu1 & HΘ1 & HD1).
  pose proof (cover_open_tvar (supply_fresh S0) Hcov) as Hcov1.
  destruct (Hstep h Hlcop He HΘ1 HD1 Hu1 Hcov1 _ _ _ Db1)
    as (r0 & ps2 & Hrun & Hav2 & HS2 & HT2 & HQ2).
  destruct (e_typing_impl _ _ _ _ _ h) as [[r Hr] | ] eqn:Hcall;
    cbn [typing_answer proj1_sig] in Hrun; [ | discriminate ].
  assert (Heqr : r0 = r) by congruence. subst r0.
  unfold typing_spec in Hr.
  destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]].
  assert (Hfix2a : swaps_atom ps2 (supply_fresh S0) = supply_fresh S0)
    by (apply (swaps_atom_dodge_in Hav2); clear; fsetdec).

  assert (Hctx : ty_ctx r
            = swaps_aenv ps2 (swaps_aenv ((αd, supply_fresh S0) :: nil)
                Ξ)
              ++ (supply_fresh S0 ~ abind_tvar)
              ++ swaps_aenv ps2 (swaps_aenv
                   ((αd, supply_fresh S0) :: nil) Θd))
    by (rewrite <- HT2;
        rewrite ! swaps_aenv_app_dist, swaps_aenv_one_tvar;
        rewrite Hfix2a; reflexivity).

  assert (HnotA : supply_fresh S0
            `notin` ftvar_in_ptyp
              (swaps_ptyp ps2 (swaps_ptyp
                 ((αd, supply_fresh S0) :: nil) A))).
  { assert (Hn1 : swaps_atom ((αd, supply_fresh S0) :: nil) αd
              `notin` ftvar_in_ptyp (swaps_ptyp
                 ((αd, supply_fresh S0) :: nil) A))
      by (apply swaps_ptyp_ftv_notin; exact HαA).
    rewrite Hsαd in Hn1.
    assert (Hn2 : swaps_atom ps2 (supply_fresh S0)
              `notin` ftvar_in_ptyp (swaps_ptyp ps2 (swaps_ptyp
                 ((αd, supply_fresh S0) :: nil) A)))
      by (apply swaps_ptyp_ftv_notin; exact Hn1).
    rewrite Hfix2a in Hn2. exact Hn2. }
  assert (Hclose : close_ptyp_wrt_ptyp (supply_fresh S0) (ty_out r)
            = swaps_ptyp ps2 (swaps_ptyp
                ((αd, supply_fresh S0) :: nil) A)).
  { rewrite <- HQ2. rewrite ! swaps_ptyp_open, ! swaps_ptyp_var_f.
    rewrite Hfix2a.
    apply close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp. exact HnotA. }
  assert (Hsufr : a_suffix (swaps_aenv ps2
            (swaps_aenv ((αd, supply_fresh S0) :: nil) Ξ)))
    by (repeat apply a_suffix_swaps; exact Hsuf).
  assert (HuΞr : uniq (swaps_aenv ps2
            (swaps_aenv ((αd, supply_fresh S0) :: nil) Ξ) ++ Θ0)).
  { assert (HfixΘ2 : swaps_aenv ps2 (swaps_aenv
              ((αd, supply_fresh S0) :: nil) Θ0) = Θ0).
    { rewrite HfixΘ. apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2).
      clear - Hcov; simpl in *; fsetdec. }
    rewrite <- HfixΘ2. rewrite <- ! swaps_aenv_app_dist.
    apply swaps_aenv_uniq. apply swaps_aenv_uniq. exact HuΞ. }
  assert (Hfilr : (dom (swaps_aenv ps2 (swaps_aenv
              ((αd, supply_fresh S0) :: nil) Ξ)))
            ∩ (ftvar_in_ptyp (close_ptyp_wrt_ptyp (supply_fresh S0)
                 (ty_out r))) [=] empty)
    by (rewrite Hclose; apply inter_empty_pointwise;
        repeat apply swaps_block_ftv_filter; exact Hfil).
  exists r, Hr, (((αd, supply_fresh S0) :: nil) ++ ps2),
    (swaps_aenv ps2 (swaps_aenv ((αd, supply_fresh S0) :: nil) Ξ)),
    (swaps_aenv ps2 (swaps_aenv ((αd, supply_fresh S0) :: nil) Θd)).
  split; [ reflexivity | ].
  split; [ exact Hur | ].
  split; [ exact Hctx | ].
  split; [ exact Hsufr | ].
  split; [ exact HuΞr | ].
  split; [ exact Hfilr | ].
  split.
  - apply (swaps_dodge_app Hav0 Hav2); fsetdec.
  - split.
    + exact (swaps_atoms_app_transport HSd1 HS2).
    + split; [ rewrite swaps_aenv_app; reflexivity | ].
      rewrite swaps_ptyp_app. exact Hclose.
Qed.

Lemma e_typing_impl_complete_ind : forall S0 m Θ0 P0 e,
  e_typing_order S0 m Θ0 P0 e -> typing_complete S0 m Θ0 P0 e.
Proof.
  intros S0 m Θ0 P0 e H0.
  apply (e_typing_order_ind typing_complete); [ | exact H0 ].
  clear S0 m Θ0 P0 e H0.
  intros S0 m Θ0 P0 e hano Hano hfz Hfz habs Habs habsa Habsa
    hstep Hstep hbase Hbase hbasea Hbasea hpat happ1 Happ1 happ2 Happ2.
  unfold typing_complete.
  intros H HP0 He HΘ HD Hu Hcov Sd Θd Bd Hd.
  destruct e as [ | n0 | x | e1 | A e1 | e1 e2 | e1 A | e1 ].

  -
    rewrite e_typing_impl_equation_1.
    pose proof (e_typing_inv_unit Hd) as Ds.
    bool_true_ty.
    assert (Hcovs : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl pskl_unit [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    kill_sub Ds Hu Hcovs r Hr ps Hav HS HT HQ.
    assert (Hout : sb_out r = ptyp_to_pskl (swaps_ptyp ps Bd))
      by (rewrite <- HQ; apply swaps_pskl_ptyp_to_pskl).
    kill_dec (pskl_readback_complete_eq Hout) A0 HA0.
    eexists; exists ps.
    exact (conj eq_refl (conj Hav (conj HS (conj HT eq_refl)))).

  -
    exfalso. exact (e_typing_inv_var_b Hd).

  -
    rewrite e_typing_impl_equation_3.
    destruct (e_typing_inv_var Hd) as [A [Hbd Ds]].
    assert (HA : lc_ptyp A) by (exact (lc_aenv_binds HΘ Hbd)).
    destruct (lookup_binding_complete _ _ _ Hu Hbd) as [[b Hb] [Hlk Hpr]].
    simpl in Hpr; subst b.
    rewrite Hlk. cbv beta iota.
    destruct (abind_var_typ_get_complete A) as [[A' HA'] [Hgt Hgpr]].
    simpl in Hgpr; subst A'.
    rewrite Hgt. cbv beta iota.
    bool_true_ty.
    pose proof (@ftvar_in_aenv_binds_ftv _ _ _ Hbd) as Hbf. simpl in Hbf.
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    assert (Hcovs : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl (ptyp_to_pskl A) [<=] S0)
      by (clear - Hcov Hbf HAe; simpl in *; fsetdec).
    kill_sub Ds Hu Hcovs r Hr ps Hav HS HT HQ.
    assert (Hout : sb_out r = ptyp_to_pskl (swaps_ptyp ps Bd))
      by (rewrite <- HQ; apply swaps_pskl_ptyp_to_pskl).
    kill_dec (pskl_readback_complete_eq Hout) B0 HB0.
    eexists; exists ps.
    exact (conj eq_refl (conj Hav (conj HS (conj HT eq_refl)))).

  -
    assert (Hbody : forall y, lc_exp (open_exp_wrt_exp e1 (exp_var_f y)))
      by (inversion He; subst; assumption).
    destruct m as [ | | m' ];
      [ rewrite e_typing_impl_equation_4 | | rewrite e_typing_impl_equation_6 ].

    2: {
      rewrite e_typing_impl_equation_5.
      destruct (pskl_readback_all P0) as [ [A0 HA0] | ] eqn:Hrba;
        cbv beta iota.

      -
        destruct (e_typing_inv_abs_all Hd)
          as [ [Hm _] | [ [_ Hstepd] | [_ Hbased] ] ];
          [ exfalso; exact (Hm eq_refl) | | ].
        2: {
          exfalso.
          destruct Hbased
            as [xd [S1 [Θ1 [A0' [A [B [B1 [Ξ [HP0eq [_ [Dsp _]]]]]]]]]]].
          assert (Heqp : ptyp_to_pskl (ptyp_all A0) = ptyp_to_pskl A0')
            by (rewrite <- HA0; exact HP0eq).
          pose proof (ptyp_to_pskl_inj Heqp) as HeqA. subst A0'.
          cbn [ptyp_to_pskl] in Dsp.
          exact (e_split_inv_all_syn Dsp). }
        destruct Hstepd
          as [αd [A0' [A [Ξ [HP0eq [HBd [Hsuf [HuΞ [Hfil [HαA [Hαd Db]]]]]]]]]]].
        assert (Heqp : ptyp_to_pskl (ptyp_all A0)
                       = ptyp_to_pskl (ptyp_all A0'))
          by (rewrite <- HA0; exact HP0eq).
        assert (HeqA : A0' = A0)
          by (pose proof (ptyp_to_pskl_inj Heqp) as He0; congruence).
        subst A0'.
        subst Bd.
        pose proof HP0 as HP0c. rewrite HA0 in HP0c.
        pose proof Hcov as Hcovc. rewrite HA0 in Hcovc.

        match goal with
        | |- context [e_typing_impl ?S ?m ?T ?P ?e ?h] =>
          destruct (@typing_complete_forall_step S0 Θ0 A0 (exp_abs e1)
            Sd Θd A Ξ αd (Hstep A0 HA0)
            HP0c He HΘ HD Hu Hcovc Hsuf HuΞ Hfil HαA Hαd Db h)
            as (r & Hr & ps & Ξr & Θr & Hrun & Hur & Hctx & Hsufr
                & HuΞr & Hfilr & Hav & HS & HT & Hclose)
        end.
        rewrite Hrun. cbv beta iota.
        kill_dec (split_at_tvar_complete Hctx Hur) p Hp.
        cbn [fst snd]. bool_true_ty.
        eexists; exists ps.
        split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
        repeat apply conj; [ exact Hav | exact HS | exact HT | ].
        cbn [ty_out]. rewrite swaps_ptyp_all, Hclose. reflexivity.

      -
        destruct (e_typing_inv_abs_all Hd)
          as [ [Hm _] | [ [_ Hstepd] | [_ Hbased] ] ];
          [ exfalso; exact (Hm eq_refl) | | ].
        1: {
          exfalso.
          destruct Hstepd as [αd [A0' [A [Ξ [HP0eq _]]]]].
          destruct (pskl_readback_all_complete_eq HP0eq) as [rr [Hrr _]].
          rewrite Hrba in Hrr. discriminate. }
        destruct Hbased
          as [xd [S1 [Θ1 [A0 [A [B [B1 [Ξ
             [HP0eq [HBd [Dsp [Hsuf [HuΞ [Hfil [Hxd Db]]]]]]]]]]]]]]].
        subst Bd.
        kill_dec (pskl_readback_complete_eq HP0eq) A0r HA0r.

        assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        rewrite <- HP0eq in Dsp.
        kill_split Dsp HD Hu Hcovsp rs Hrs ps1 Hav1 HS1 HT1 HP1 HQ1.
        destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]].
        pose proof (e_split_defs_mono Hrs HD) as HDs.
        pose proof (e_split_env_lc Hrs HΘ) as HΘs.
        destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc].
        pose proof (e_split_supply_grows Hrs) as Hgrs.
        pose proof (e_split_supply_grows Dsp) as Hgrd.

        assert (HdomR : sp_dom rs = ptyp_to_pskl (swaps_ptyp ps1 A))
          by (rewrite <- HP1; apply swaps_pskl_ptyp_to_pskl).
        assert (HcodR : sp_cod rs = ptyp_to_pskl (swaps_ptyp ps1 B))
          by (rewrite <- HQ1; apply swaps_pskl_ptyp_to_pskl).
        kill_dec (pskl_readback_complete_eq HdomR) Ad HAd.
        kill_dec (pskl_readback_complete_eq HcodR) Bd0 HBd0.

        assert (Hx1S : swaps_atom ps1 xd `notin` sp_supply rs)
          by (eapply swaps_notin_eq; [ symmetry; exact HS1 | exact Hxd ]).
        assert (Hx10 : swaps_atom ps1 xd `notin` S0)
          by (apply swaps_atom_dodge with (S := S0);
              [ exact Hav1 | clear - Hxd Hgrd; fsetdec ]).
        assert (Hfixe1 : swaps_exp ps1 e1 = e1)
          by (apply swaps_exp_fresh_id, (swaps_dodge_sub Hav1);
              clear - Hcov; simpl in *; fsetdec).
        destruct (e_typing_swaps ps1 Db
                    (S0' := add (swaps_atom ps1 xd) (sp_supply rs)))
          as [Sd1 [HSd1 Db1]];
          [ rewrite swaps_atoms_add, HS1; reflexivity | ].
        rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ in Db1.
        rewrite ! swaps_exp_open_var, ! swaps_pskl_ptyp_to_pskl in Db1.
        rewrite HT1, Hfixe1 in Db1.

        assert (HcAd : ftvar_in_ptyp (swaps_ptyp ps1 A) [<=] sp_supply rs).
        { pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 A)) as Hpa.
          rewrite HdomR in Hpqs. clear - Hpqs Hpa. fsetdec. }
        assert (HcBd : ftvar_in_ptyp (swaps_ptyp ps1 B) [<=] sp_supply rs).
        { pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 B)) as Hpb.
          rewrite HcodR in Hpqs. clear - Hpqs Hpb. fsetdec. }
        assert (HdrawScope : ftvar_in_aenv (sp_ctx rs) ∪ ftvar_in_pskl (ptyp_to_pskl (swaps_ptyp ps1 B))
          ∪ ftvar_in_ptyp (swaps_ptyp ps1 A) ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] sp_supply rs)
          by (rewrite ftvar_ptyp_to_pskl; clear - Hcvs HcAd HcBd Hcov Hgrs; simpl in *; fsetdec).
        destruct (e_typing_draw_term e1 Hx1S HdrawScope Db1)
          as (Sd2 & HSd2 & HfixCtx & HfixAd & Db2).

        assert (HlcAd : lc_ptyp (swaps_ptyp ps1 A))
          by (rewrite HdomR in Hlcd; eapply ptyp_to_pskl_lc_inv; exact Hlcd).
        destruct (push_fresh_invariants Hus HΘs HDs Hcvs
                    (lc_abind_var_typ HlcAd) (entry_def_mono_var_typ _ _))
          as (Hu1 & HΘ1 & HD1).
        pose proof (cover_open_body_typ (supply_fresh (sp_supply rs))
                      HdrawScope) as Hcov1.
        assert (Hlccod : lc_pskl (ptyp_to_pskl (swaps_ptyp ps1 B)))
          by (rewrite <- HcodR; exact Hlcc).
        kill_typing (Hbase e1 eq_refl _ _ _ _ Hrs _ _ HdomR HcodR)
          Hlccod (Hbody (supply_fresh (sp_supply rs)))
          HΘ1 HD1 Hu1 Hcov1 Db2 r Hr ps2 Hav2 HS2 HT2 HQ2.
        unfold typing_spec in Hr.
        destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]].
        assert (Hfix2a : swaps_atom ps2 (supply_fresh (sp_supply rs))
                         = supply_fresh (sp_supply rs))
          by (apply (swaps_atom_dodge_in Hav2); clear; fsetdec).
        assert (Hfix2A : swaps_ptyp ps2 (swaps_ptyp ps1 A)
                         = swaps_ptyp ps1 A)
          by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav2);
              clear - HcAd; fsetdec).
        assert (Hfix2C : swaps_aenv ps2 (sp_ctx rs) = sp_ctx rs)
          by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
              clear - Hcvs; fsetdec).
        assert (Hctx : ty_ctx r
                  = swaps_aenv ps2 (swaps_aenv ((swaps_atom ps1 xd,
                        supply_fresh (sp_supply rs)) :: nil)
                        (swaps_aenv ps1 Ξ))
                    ++ (supply_fresh (sp_supply rs)
                          ~ abind_var_typ (swaps_ptyp ps1 A))
                    ++ swaps_aenv ps2 (swaps_aenv ((swaps_atom ps1 xd,
                         supply_fresh (sp_supply rs)) :: nil)
                         (swaps_aenv ps1 Θd)))
          by (rewrite <- HT2;
              rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ;
              rewrite Hfix2a, Hfix2A; reflexivity).
        kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht.
        cbn [fst snd].
        assert (Hsufr : a_suffix (swaps_aenv ps2 (swaps_aenv
                  ((swaps_atom ps1 xd, supply_fresh (sp_supply rs)) :: nil)
                  (swaps_aenv ps1 Ξ))))
          by (repeat apply a_suffix_swaps; exact Hsuf).
        assert (HuΞr : uniq (swaps_aenv ps2 (swaps_aenv
                  ((swaps_atom ps1 xd, supply_fresh (sp_supply rs)) :: nil)
                  (swaps_aenv ps1 Ξ)) ++ sp_ctx rs)).
        { assert (HfixΘ1 : swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom ps1 xd,
                      supply_fresh (sp_supply rs)) :: nil)
                    (swaps_aenv ps1 Θ1)) = sp_ctx rs)
            by (rewrite HT1, HfixCtx; exact Hfix2C).
          rewrite <- HfixΘ1. rewrite <- ! swaps_aenv_app_dist.
          repeat apply swaps_aenv_uniq. exact HuΞ. }
        assert (Hfilr : (dom (swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom ps1 xd,
                      supply_fresh (sp_supply rs)) :: nil)
                    (swaps_aenv ps1 Ξ))))
                  ∩ (ftvar_in_ptyp (ty_out r)) [=] empty).
        { rewrite <- HQ2. apply inter_empty_pointwise.
          repeat apply swaps_block_ftv_filter. exact Hfil. }
        bool_true_ty.
        eexists;
        exists ((ps1 ++ ((swaps_atom ps1 xd,
                  supply_fresh (sp_supply rs)) :: nil)) ++ ps2).
        split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
        repeat apply conj.
        + exact (swaps_dodge_draw Hav1 Hx10 Hgrs Hav2).
        + exact (swaps_atoms_app_transport
            (swaps_atoms_app_compose HSd2 HSd1) HS2).
        + cbn [ty_ctx]. rewrite ! swaps_aenv_app. reflexivity.
        + cbn [ty_out]. rewrite swaps_ptyp_arrow. f_equal.
          * rewrite ! swaps_ptyp_app, HfixAd. exact Hfix2A.
          * rewrite ! swaps_ptyp_app. exact HQ2. }

    all: (

      destruct (e_typing_inv_abs_all Hd) as [ [Hm Hdat] | [ [Hmc _] | [Hmc _] ] ];
        [ | discriminate | discriminate ];
      destruct Hdat as [xd [S1 [S2 [Θ1 [Θ2 [P [Q [αs [A [B [Ξ
        [Dsp [Hg [Hsuf [Hxd [Db [HBd HΘd]]]]]]]]]]]]]]]]];
      subst Bd Θd;

      assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec);
      kill_split Dsp HD Hu Hcovsp rs Hrs ps1 Hav1 HS1 HT1 HP1 HQ1;
      destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]];
      pose proof (e_split_defs_mono Hrs HD) as HDs;
      pose proof (e_split_env_lc Hrs HΘ) as HΘs;
      destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc];
      pose proof (e_split_supply_grows Hrs) as Hgrs;
      pose proof (e_split_supply_grows Dsp) as Hgrd;
      bool_true_ty;
      match goal with
      | |- context [ e_guess_mono_impl ?S ?p ?h ] =>
          destruct (e_guess_mono_impl S p h) as [rg Hrg]
      end;
      cbv beta iota;
      unfold guess_spec in Hrg;
      assert (HcovD : ftvar_in_pskl (sp_dom rs) [<=] sp_supply rs)
        by (clear - Hpqs; fsetdec);
      destruct (e_guess_mono_swaps ps1 Hg (S0' := sp_supply rs))
        as [Sg1 [HSg1 Hg1]]; [ symmetry; exact HS1 | ];
      rewrite HP1 in Hg1;
      destruct (e_guess_mono_rel Hg1 Hrg HcovD)
        as [psg [Havg [HSg [HTg HAg]]]];
      pose proof (e_guess_mono_supply_grows Hrg) as Hgrg;
      pose proof (e_guess_mono_generated_in_supply Hrg) as HdomG;
      pose proof (e_guess_mono_generated_ftvar Hrg) as HftG;
      pose proof (e_guess_mono_ftv_supply Hrg HcovD) as HftyG;

      assert (Hx1S : swaps_atom psg (swaps_atom ps1 xd)
                     `notin` gr_supply rg)
        by (eapply swaps_notin_eq;
            [ symmetry; rewrite <- HSg; apply swaps_atoms_cong;
              symmetry; exact HSg1
            | eapply swaps_notin_eq; [ reflexivity | exact Hxd ] ]);
      assert (Hx10 : swaps_atom psg (swaps_atom ps1 xd) `notin` S0)
        by (rewrite <- swaps_atom_app;
            apply (@swaps_atom_dodge _ _ _
                     (swaps_dodge_app_l Hav1 Havg Hgrs));
            pose proof (e_guess_mono_supply_grows Hg) as Hgg;
            clear - Hxd Hgrd Hgg; fsetdec);
      assert (HfixCtx1 : swaps_aenv psg (sp_ctx rs) = sp_ctx rs)
        by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Havg);
            clear - Hcvs; fsetdec);
      assert (HfixCod1 : swaps_pskl psg (sp_cod rs) = sp_cod rs)
        by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Havg);
            clear - Hpqs; fsetdec);
      assert (Hfixe1 : swaps_exp (ps1 ++ psg) e1 = e1)
        by (apply swaps_exp_fresh_id, (swaps_dodge_app Hav1 Havg);
            clear - Hcov Hgrs; simpl in *; fsetdec);
      destruct (e_typing_swaps (ps1 ++ psg) Db
                  (S0' := add (swaps_atom psg (swaps_atom ps1 xd))
                            (gr_supply rg))) as [Sd1 [HSd1 Db1]];
      [ assert (Heq3 : swaps_atoms psg (swaps_atoms ps1 S2) [=] gr_supply rg)
          by (rewrite <- HSg; apply swaps_atoms_cong; symmetry; exact HSg1);
        rewrite swaps_atoms_add, swaps_atom_app, swaps_atoms_app, Heq3;
        reflexivity
      | ];
      rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ,
        ! swaps_exp_open_var, Hfixe1 in Db1;
      rewrite ! swaps_aenv_app, ! swaps_pskl_app, ! swaps_atom_app,
        ! swaps_ptyp_app in Db1;
      rewrite HT1, HQ1, HTg, HAg, HfixCtx1, HfixCod1 in Db1;

      assert (HdrawScope : ftvar_in_aenv (gr_block rg ++ sp_ctx rs) ∪ ftvar_in_pskl (sp_cod rs)
        ∪ ftvar_in_ptyp (gr_type rg) ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] gr_supply rg)
        by (rewrite ftvar_in_aenv_app; clear - HftG HdomG HftyG Hcvs Hpqs Hgrs Hgrg Hcov; simpl in *; fsetdec);
      destruct (e_typing_draw_term e1 Hx1S HdrawScope Db1)
        as (Sd2 & HSd2 & HfixCtx & HfixTy & Db2);

      assert (Hublk : uniq (gr_block rg ++ sp_ctx rs))
        by (eapply e_guess_mono_uniq_app;
            [ exact Hrg | exact Hcvs | exact Hus ]);
      assert (HcB : ftvar_in_aenv (gr_block rg ++ sp_ctx rs) [<=] gr_supply rg)
        by (rewrite ftvar_in_aenv_app; clear - HftG HdomG Hcvs Hgrg; fsetdec);
      destruct (push_fresh_invariants Hublk
                  (lc_aenv_app_intro (e_guess_mono_block_lc Hrg) HΘs)
                  (Forall_app_intro (e_guess_mono_block_defs_mono Hrg) HDs) HcB
                  (lc_abind_var_typ (e_guess_mono_lc_type Hrg Hlcd))
                  (entry_def_mono_var_typ _ _))
        as (Hu1 & HΘ1 & HD1);
      pose proof (cover_open_body_typ (supply_fresh (gr_supply rg))
                    HdrawScope) as Hcov1;
      kill_typing (Habs e1 eq_refl _ _ _ _ Hrs _ _ _ Hrg) Hlcc
        (Hbody (supply_fresh (gr_supply rg))) HΘ1 HD1 Hu1 Hcov1 Db2
        r Hr ps2 Hav2 HS2 HT2 HQ2;
      unfold typing_spec in Hr;
      destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]];
      assert (Hfix2a : swaps_atom ps2 (supply_fresh (gr_supply rg))
                       = supply_fresh (gr_supply rg))
        by (apply (swaps_atom_dodge_in Hav2); clear; fsetdec);
      assert (Hfix2T : swaps_ptyp ps2 (gr_type rg) = gr_type rg)
        by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav2);
            clear - HftyG; fsetdec);

      assert (Hctx : ty_ctx r
                = swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom psg (swaps_atom ps1 xd),
                      supply_fresh (gr_supply rg)) :: nil)
                    (swaps_aenv psg (swaps_aenv ps1 Ξ)))
                  ++ (supply_fresh (gr_supply rg)
                        ~ abind_var_typ (gr_type rg))
                  ++ swaps_aenv ps2 (swaps_aenv
                       ((swaps_atom psg (swaps_atom ps1 xd),
                         supply_fresh (gr_supply rg)) :: nil)
                       (swaps_aenv psg (swaps_aenv ps1 Θ2))))
        by (rewrite <- HT2;
            rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ;
            rewrite Hfix2a, Hfix2T; reflexivity);
      kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht;
      cbn [fst snd];
      assert (Hsufr : a_suffix (swaps_aenv ps2 (swaps_aenv
                ((swaps_atom psg (swaps_atom ps1 xd),
                  supply_fresh (gr_supply rg)) :: nil)
                (swaps_aenv psg (swaps_aenv ps1 Ξ)))))
        by (repeat apply a_suffix_swaps; exact Hsuf);
      bool_true_ty;
      assert (HS0g : S0 [<=] gr_supply rg) by (clear - Hgrs Hgrg; fsetdec);
      eexists;
      exists (((ps1 ++ psg) ++ ((swaps_atom psg (swaps_atom ps1 xd),
                supply_fresh (gr_supply rg)) :: nil)) ++ ps2);
      split; [ cbn [typing_answer proj1_sig]; reflexivity | ];
      repeat apply conj;
      [ exact (swaps_dodge_draw
          (swaps_dodge_app_l Hav1 Havg Hgrs)
          Hx10 HS0g Hav2)
      | exact (swaps_atoms_app_transport
          (swaps_atoms_app_compose HSd2 HSd1) HS2)
      | cbn [ty_ctx]; rewrite swaps_aenv_app_dist, ! swaps_aenv_app;
        reflexivity
      | cbn [ty_out]; rewrite swaps_ptyp_arrow; f_equal;
        [ rewrite ! swaps_ptyp_app, HAg, HfixTy; exact Hfix2T
        | rewrite ! swaps_ptyp_app; exact HQ2 ] ]
    ).

  -
    assert (Hbody : forall y, lc_exp (open_exp_wrt_exp e1 (exp_var_f y)))
      by (inversion He; subst; assumption).
    assert (HAan : lc_ptyp A) by (inversion He; subst; assumption).
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    destruct m as [ | | m' ];
      [ rewrite e_typing_impl_equation_7 | | rewrite e_typing_impl_equation_9 ].

    2: {
      rewrite e_typing_impl_equation_8.
      destruct (pskl_readback_all P0) as [ [A0 HA0] | ] eqn:Hrba;
        cbv beta iota.

      -
        destruct (e_typing_inv_abs_anno_all Hd)
          as [ [Hm _] | [ [_ Hstepd] | [_ Hbased] ] ];
          [ exfalso; exact (Hm eq_refl) | | ].
        2: { exfalso.
          destruct Hbased
            as [xd [S1 [S2 [Θ1 [Θ2 [A0' [A' [B [B1 [Ξ
               [HP0eq [_ [Dsp _]]]]]]]]]]]]].
          assert (Heqp : ptyp_to_pskl (ptyp_all A0) = ptyp_to_pskl A0')
            by (rewrite <- HA0; exact HP0eq).
          pose proof (ptyp_to_pskl_inj Heqp) as HeqA. subst A0'.
          cbn [ptyp_to_pskl] in Dsp.
          exact (e_split_inv_all_syn Dsp). }
        destruct Hstepd
          as [αd [A0' [A1 [Ξ [HP0eq [HBd [Hsuf [HuΞ [Hfil [HαA [Hαd Db]]]]]]]]]]].
        assert (Heqp : ptyp_to_pskl (ptyp_all A0)
                       = ptyp_to_pskl (ptyp_all A0'))
          by (rewrite <- HA0; exact HP0eq).
        assert (HeqA : A0' = A0)
          by (pose proof (ptyp_to_pskl_inj Heqp) as He0; congruence).
        subst A0'. subst Bd.
        pose proof HP0 as HP0c. rewrite HA0 in HP0c.
        pose proof Hcov as Hcovc. rewrite HA0 in Hcovc.
        match goal with
        | |- context [e_typing_impl ?S ?m ?T ?P ?e ?h] =>
          destruct (@typing_complete_forall_step S0 Θ0 A0 (exp_abs_anno A e1)
            Sd Θd A1 Ξ αd (Hstep A0 HA0)
            HP0c He HΘ HD Hu Hcovc Hsuf HuΞ Hfil HαA Hαd Db h)
            as (r & Hr & ps & Ξr & Θr & Hrun & Hur & Hctx & Hsufr
                & HuΞr & Hfilr & Hav & HS & HT & Hclose)
        end.
        rewrite Hrun. cbv beta iota.
        kill_dec (split_at_tvar_complete Hctx Hur) p Hp.
        cbn [fst snd]. bool_true_ty.
        eexists; exists ps.
        split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
        repeat apply conj; [ exact Hav | exact HS | exact HT | ].
        cbn [ty_out]. rewrite swaps_ptyp_all, Hclose. reflexivity.

      -
        destruct (e_typing_inv_abs_anno_all Hd)
          as [ [Hm _] | [ [_ Hstepd] | [_ Hbased] ] ];
          [ exfalso; exact (Hm eq_refl) | | ].
        1: { exfalso.
          destruct Hstepd as [αd [A0' [A1 [Ξ [HP0eq _]]]]].
          destruct (pskl_readback_all_complete_eq HP0eq) as [rr [Hrr _]].
          rewrite Hrba in Hrr. discriminate. }
        destruct Hbased
          as [xd [S1 [S2 [Θ1 [Θ2 [A0 [A' [B [B1 [Ξ
             [HP0eq [HBd [Dsp [Dch [Hsuf [HuΞ [Hfil [Hxd Db]]]]]]]]]]]]]]]]]].
        subst Bd.
        destruct Dch as [Qc Dc].
        kill_dec (pskl_readback_complete_eq HP0eq) A0r HA0r.
        assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        rewrite <- HP0eq in Dsp.
        kill_split Dsp HD Hu Hcovsp rs Hrs ps1 Hav1 HS1 HT1 HP1 HQ1.
        destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]].
        pose proof (e_split_defs_mono Hrs HD) as HDs.
        pose proof (e_split_env_lc Hrs HΘ) as HΘs.
        destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc].
        pose proof (e_split_supply_grows Hrs) as Hgrs.
        pose proof (e_split_supply_grows Dsp) as Hgrd.
        assert (HdomR : sp_dom rs = ptyp_to_pskl (swaps_ptyp ps1 A'))
          by (rewrite <- HP1; apply swaps_pskl_ptyp_to_pskl).
        assert (HcodR : sp_cod rs = ptyp_to_pskl (swaps_ptyp ps1 B))
          by (rewrite <- HQ1; apply swaps_pskl_ptyp_to_pskl).
        kill_dec (pskl_readback_complete_eq HdomR) Ad HAd.
        kill_dec (pskl_readback_complete_eq HcodR) Bd0 HBd0.
        assert (HcAd : ftvar_in_ptyp (swaps_ptyp ps1 A') [<=] sp_supply rs).
        { pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 A')) as Hpa.
          rewrite HdomR in Hpqs. clear - Hpqs Hpa. fsetdec. }
        assert (HcBd : ftvar_in_ptyp (swaps_ptyp ps1 B) [<=] sp_supply rs).
        { pose proof (ftvar_ptyp_to_pskl (swaps_ptyp ps1 B)) as Hpb.
          rewrite HcodR in Hpqs. clear - Hpqs Hpb. fsetdec. }
        bool_true_ty.

        assert (HfixA1 : swaps_pskl ps1 (ptyp_to_pskl A) = ptyp_to_pskl A)
          by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
              clear - Hcov HAe; simpl in *; fsetdec).
        pose proof (swaps_atoms_empty ps1) as Hemp; symmetry in Hemp;
        pose proof HS1 as HS1r; symmetry in HS1r;
        destruct (e_consis_swaps ps1 Dc Hemp
                    Hemp HS1r)
          as [Sc1 [HSc1 Dc1]];
        rewrite HT1, HfixA1, HP1 in Dc1.
        assert (Hcovc : ftvar_in_aenv (sp_ctx rs)
                        ∪ ftvar_in_pskl (ptyp_to_pskl A)
                        ∪ ftvar_in_pskl (sp_dom rs)
                        ∪ empty ∪ empty [<=] sp_supply rs)
          by (clear - Hcvs Hpqs Hcov HAe Hgrs; simpl in *; fsetdec).
        kill_consis_call Dc1 Hus Hcovc rc Hrc psc Havc HSc HTc HQc.
        unfold consis_spec in Hrc.
        destruct ((proj2 (proj2 e_assign_unify_consis_sound))
                    _ _ _ _ _ _ _ _ _ Hrc Hus Hcovc) as [Hca [Huc Hcvc]].
        pose proof (e_consis_defs_mono Hrc HDs) as HDc.
        pose proof (e_consis_env_lc Hrc HΘs) as HΘc.
        pose proof (e_consis_supply_grows Hrc) as Hgrc.
        pose proof (supply_fresh_notin (cs_supply rc)) as Hsfc.

        assert (HScc : swaps_atoms psc (swaps_atoms ps1 S2) [=] cs_supply rc)
          by (rewrite <- HSc; apply swaps_atoms_cong; symmetry; exact HSc1).
        assert (Hx1S : swaps_atom psc (swaps_atom ps1 xd)
                       `notin` cs_supply rc)
          by (eapply swaps_notin_eq;
              [ symmetry; exact HScc
              | eapply swaps_notin_eq; [ reflexivity | exact Hxd ] ]).
        assert (Hx10 : swaps_atom psc (swaps_atom ps1 xd) `notin` S0)
          by (rewrite <- swaps_atom_app;
              apply (@swaps_atom_dodge _ _ _
                       (swaps_dodge_app_l Hav1 Havc Hgrs));
              pose proof (e_consis_supply_grows Dc) as Hgc0;
              clear - Hxd Hgrd Hgc0; fsetdec).
        assert (Hfixe1 : swaps_exp (ps1 ++ psc) e1 = e1)
          by (apply swaps_exp_fresh_id, (swaps_dodge_app Hav1 Havc);
              clear - Hcov Hgrs; simpl in *; fsetdec).
        assert (HfixA2 : swaps_ptyp (ps1 ++ psc) A = A)
          by (apply swaps_ptyp_fresh_id, (swaps_dodge_app Hav1 Havc);
              clear - Hcov Hgrs; simpl in *; fsetdec).
        assert (HfixB1 : swaps_ptyp psc (swaps_ptyp ps1 B)
                         = swaps_ptyp ps1 B)
          by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Havc);
              clear - HcBd; fsetdec).
        assert (HfixA1c : swaps_ptyp psc (swaps_ptyp ps1 A')
                          = swaps_ptyp ps1 A')
          by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Havc);
              clear - HcAd; fsetdec).
        destruct (e_typing_swaps (ps1 ++ psc) Db
                    (S0' := add (swaps_atom psc (swaps_atom ps1 xd))
                              (cs_supply rc))) as [Sd1 [HSd1 Db1]];
          [ rewrite swaps_atoms_add, swaps_atom_app, swaps_atoms_app, HScc;
            reflexivity
          | ].
        rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ,
          ! swaps_exp_open_var, ! swaps_pskl_ptyp_to_pskl, Hfixe1, HfixA2
          in Db1.
        rewrite ! swaps_aenv_app, ! swaps_atom_app, ! swaps_ptyp_app in Db1.
        rewrite HTc, HfixB1 in Db1.

        assert (HdrawScope : ftvar_in_aenv (cs_ctx rc) ∪ ftvar_in_pskl (ptyp_to_pskl (swaps_ptyp ps1 B))
          ∪ ftvar_in_ptyp (A) ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] cs_supply rc)
          by (rewrite ftvar_ptyp_to_pskl; clear - Hcvc HcBd Hcov Hgrs Hgrc; simpl in *; fsetdec).
        destruct (e_typing_draw_term e1 Hx1S HdrawScope Db1)
          as (Sd2 & HSd2 & HfixCtx & HfixAnn & Db2).

        destruct (push_fresh_invariants Huc HΘc HDc Hcvc
                    (lc_abind_var_typ HAan) (entry_def_mono_var_typ _ _))
          as (Hu1 & HΘ1 & HD1).
        assert (Hlccod : lc_pskl (ptyp_to_pskl (swaps_ptyp ps1 B)))
          by (rewrite <- HcodR; exact Hlcc).
        pose proof (cover_open_body_typ (supply_fresh (cs_supply rc))
                      HdrawScope) as Hcov1.
        kill_typing (Hbasea A e1 eq_refl _ _ _ _ Hrs _ _ _ Hrc _ HcodR)
          Hlccod (Hbody (supply_fresh (cs_supply rc)))
          HΘ1 HD1 Hu1 Hcov1 Db2 r Hr ps2 Hav2 HS2 HT2 HQ2.
        unfold typing_spec in Hr.
        destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]].
        assert (Hfix2a : swaps_atom ps2 (supply_fresh (cs_supply rc))
                         = supply_fresh (cs_supply rc))
          by (apply (swaps_atom_dodge_in Hav2); clear; fsetdec).
        assert (Hfix2A : swaps_ptyp ps2 A = A)
          by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav2);
              clear - Hcov Hgrs Hgrc; simpl in *; fsetdec).
        assert (Hfix2C : swaps_aenv ps2 (cs_ctx rc) = cs_ctx rc)
          by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
              clear - Hcvc; fsetdec).
        assert (Hctx : ty_ctx r
                  = swaps_aenv ps2 (swaps_aenv
                      ((swaps_atom psc (swaps_atom ps1 xd),
                        supply_fresh (cs_supply rc)) :: nil)
                      (swaps_aenv psc (swaps_aenv ps1 Ξ)))
                    ++ (supply_fresh (cs_supply rc) ~ abind_var_typ A)
                    ++ swaps_aenv ps2 (swaps_aenv
                         ((swaps_atom psc (swaps_atom ps1 xd),
                           supply_fresh (cs_supply rc)) :: nil)
                         (swaps_aenv psc (swaps_aenv ps1 Θd))))
          by (rewrite <- HT2;
              rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ;
              rewrite Hfix2a, Hfix2A; reflexivity).
        kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht.
        cbn [fst snd].
        assert (Hsufr : a_suffix (swaps_aenv ps2 (swaps_aenv
                  ((swaps_atom psc (swaps_atom ps1 xd),
                    supply_fresh (cs_supply rc)) :: nil)
                  (swaps_aenv psc (swaps_aenv ps1 Ξ)))))
          by (repeat apply a_suffix_swaps; exact Hsuf).
        assert (HuΞr : uniq (swaps_aenv ps2 (swaps_aenv
                  ((swaps_atom psc (swaps_atom ps1 xd),
                    supply_fresh (cs_supply rc)) :: nil)
                  (swaps_aenv psc (swaps_aenv ps1 Ξ))) ++ cs_ctx rc)).
        { assert (HfixΘ2 : swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom psc (swaps_atom ps1 xd),
                      supply_fresh (cs_supply rc)) :: nil)
                    (swaps_aenv psc (swaps_aenv ps1 Θ2))) = cs_ctx rc)
            by (rewrite HTc, HfixCtx; exact Hfix2C).
          rewrite <- HfixΘ2. rewrite <- ! swaps_aenv_app_dist.
          repeat apply swaps_aenv_uniq. exact HuΞ. }
        assert (Hfilr : (dom (swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom psc (swaps_atom ps1 xd),
                      supply_fresh (cs_supply rc)) :: nil)
                    (swaps_aenv psc (swaps_aenv ps1 Ξ)))))
                  ∩ (ftvar_in_ptyp (ty_out r)) [=] empty).
        { rewrite <- HQ2. apply inter_empty_pointwise.
          repeat apply swaps_block_ftv_filter. exact Hfil. }
        bool_true_ty.
        assert (HS0c : S0 [<=] cs_supply rc) by (clear - Hgrs Hgrc; fsetdec).
        eexists;
        exists (((ps1 ++ psc) ++ ((swaps_atom psc (swaps_atom ps1 xd),
                  supply_fresh (cs_supply rc)) :: nil)) ++ ps2).
        split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
        repeat apply conj.
        + exact (swaps_dodge_draw
            (swaps_dodge_app_l Hav1 Havc Hgrs)
            Hx10 HS0c Hav2).
        + exact (swaps_atoms_app_transport
            (swaps_atoms_app_compose HSd2 HSd1) HS2).
        + cbn [ty_ctx]. rewrite ! swaps_aenv_app. reflexivity.
        + cbn [ty_out]. rewrite swaps_ptyp_arrow. f_equal.
          * rewrite ! swaps_ptyp_app, HfixA1c.
            assert (Hfx : swaps_ptyp ((swaps_atom psc (swaps_atom ps1 xd),
                            supply_fresh (cs_supply rc)) :: nil)
                            (swaps_ptyp ps1 A') = swaps_ptyp ps1 A')
              by (apply swaps_ptyp_fresh_id, swaps_dodge_one;
                  clear - Hx1S Hsfc HcAd Hgrc; fsetdec).
            rewrite Hfx.
            apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav2).
            clear - HcAd Hgrc; fsetdec.
          * rewrite ! swaps_ptyp_app. exact HQ2. }

    all: (

      destruct (e_typing_inv_abs_anno_all Hd)
        as [ [Hm Hdat] | [ [Hmc _] | [Hmc _] ] ];
        [ | discriminate | discriminate ];
      destruct Hdat as [xd [S1 [S2 [Θ1 [Θ2 [Θ3 [P [Q [B [Ξ
        [Dsp [Dch [Hsuf [Hxd [Db [HBd HΘd]]]]]]]]]]]]]]]];
      subst Bd Θd;
      destruct Dch as [Qc Dc];
      assert (Hcovsp : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec);
      kill_split Dsp HD Hu Hcovsp rs Hrs ps1 Hav1 HS1 HT1 HP1 HQ1;
      destruct (e_split_sound Hrs Hu Hcovsp) as [Hsa [Hus [Hcvs Hpqs]]];
      pose proof (e_split_defs_mono Hrs HD) as HDs;
      pose proof (e_split_env_lc Hrs HΘ) as HΘs;
      destruct (e_split_lc Hrs HP0) as [Hlcd Hlcc];
      pose proof (e_split_supply_grows Hrs) as Hgrs;
      pose proof (e_split_supply_grows Dsp) as Hgrd;
      bool_true_ty;
      assert (HfixA1 : swaps_pskl ps1 (ptyp_to_pskl A) = ptyp_to_pskl A)
        by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
            clear - Hcov HAe; simpl in *; fsetdec);
      pose proof (swaps_atoms_empty ps1) as Hemp; symmetry in Hemp;
      pose proof HS1 as HS1r; symmetry in HS1r;
      destruct (e_consis_swaps ps1 Dc Hemp
                  Hemp HS1r)
        as [Sc1 [HSc1 Dc1]];
      rewrite HT1, HP1, HfixA1 in Dc1;
      assert (Hcovc : ftvar_in_aenv (sp_ctx rs) ∪ ftvar_in_pskl (sp_dom rs)
                      ∪ ftvar_in_pskl (ptyp_to_pskl A) ∪ empty ∪ empty
                      [<=] sp_supply rs)
        by (clear - Hcvs Hpqs Hcov HAe Hgrs; simpl in *; fsetdec);
      kill_consis_call Dc1 Hus Hcovc rc Hrc psc Havc HSc HTc HQc;
      unfold consis_spec in Hrc;
      destruct ((proj2 (proj2 e_assign_unify_consis_sound))
                  _ _ _ _ _ _ _ _ _ Hrc Hus Hcovc) as [Hca [Huc Hcvc]];
      pose proof (e_consis_defs_mono Hrc HDs) as HDc;
      pose proof (e_consis_env_lc Hrc HΘs) as HΘc;
      pose proof (e_consis_supply_grows Hrc) as Hgrc;
      assert (HScc : swaps_atoms psc (swaps_atoms ps1 S2) [=] cs_supply rc)
        by (rewrite <- HSc; apply swaps_atoms_cong; symmetry; exact HSc1);
      assert (Hx1S : swaps_atom psc (swaps_atom ps1 xd)
                     `notin` cs_supply rc)
        by (eapply swaps_notin_eq;
            [ symmetry; exact HScc
            | eapply swaps_notin_eq; [ reflexivity | exact Hxd ] ]);
      assert (Hx10 : swaps_atom psc (swaps_atom ps1 xd) `notin` S0)
        by (rewrite <- swaps_atom_app;
            apply (@swaps_atom_dodge _ _ _
                     (swaps_dodge_app_l Hav1 Havc Hgrs));
            pose proof (e_consis_supply_grows Dc) as Hgc0;
            clear - Hxd Hgrd Hgc0; fsetdec);
      assert (Hfixe1 : swaps_exp (ps1 ++ psc) e1 = e1)
        by (apply swaps_exp_fresh_id, (swaps_dodge_app Hav1 Havc);
            clear - Hcov Hgrs; simpl in *; fsetdec);
      assert (HfixA2 : swaps_ptyp (ps1 ++ psc) A = A)
        by (apply swaps_ptyp_fresh_id, (swaps_dodge_app Hav1 Havc);
            clear - Hcov Hgrs; simpl in *; fsetdec);
      assert (HfixQ0 : swaps_pskl psc (sp_cod rs) = sp_cod rs)
        by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Havc);
            clear - Hpqs; fsetdec);
      destruct (e_typing_swaps (ps1 ++ psc) Db
                  (S0' := add (swaps_atom psc (swaps_atom ps1 xd))
                            (cs_supply rc))) as [Sd1 [HSd1 Db1]];
      [ rewrite swaps_atoms_add, swaps_atom_app, swaps_atoms_app, HScc;
        reflexivity
      | ];
      rewrite ! swaps_aenv_app_dist, ! swaps_aenv_one_var_typ,
        ! swaps_exp_open_var, Hfixe1, HfixA2 in Db1;
      rewrite ! swaps_aenv_app, ! swaps_pskl_app, ! swaps_atom_app,
        ! swaps_ptyp_app in Db1;
      rewrite HQ1, HTc, HfixQ0 in Db1;
      assert (HdrawScope : ftvar_in_aenv (cs_ctx rc) ∪ ftvar_in_pskl (sp_cod rs)
        ∪ ftvar_in_ptyp (A) ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] cs_supply rc)
        by ( clear - Hcvc Hpqs Hcov Hgrs Hgrc; simpl in *; fsetdec);
      destruct (e_typing_draw_term e1 Hx1S HdrawScope Db1)
        as (Sd2 & HSd2 & HfixCtx & HfixAnn & Db2);
      destruct (push_fresh_invariants Huc HΘc HDc Hcvc
                  (lc_abind_var_typ HAan) (entry_def_mono_var_typ _ _))
        as (Hu1 & HΘ1 & HD1);
      pose proof (cover_open_body_typ (supply_fresh (cs_supply rc))
                    HdrawScope) as Hcov1;
      kill_typing (Habsa A e1 eq_refl _ _ _ _ Hrs _ _ _ Hrc) Hlcc
        (Hbody (supply_fresh (cs_supply rc))) HΘ1 HD1 Hu1 Hcov1 Db2
        r Hr ps2 Hav2 HS2 HT2 HQ2;
      unfold typing_spec in Hr;
      destruct (e_typing_sound Hr Hu1 Hcov1) as [Hra [Hur [Hcvr Hqr]]];
      assert (Hfix2a : swaps_atom ps2 (supply_fresh (cs_supply rc))
                       = supply_fresh (cs_supply rc))
        by (apply (swaps_atom_dodge_in Hav2); clear; fsetdec);
      assert (Hfix2A : swaps_ptyp ps2 A = A)
        by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav2);
            clear - Hcov Hgrs Hgrc; simpl in *; fsetdec);
      assert (Hctx : ty_ctx r
                = swaps_aenv ps2 (swaps_aenv
                    ((swaps_atom psc (swaps_atom ps1 xd),
                      supply_fresh (cs_supply rc)) :: nil)
                    (swaps_aenv psc (swaps_aenv ps1 Ξ)))
                  ++ (supply_fresh (cs_supply rc) ~ abind_var_typ A)
                  ++ swaps_aenv ps2 (swaps_aenv
                       ((swaps_atom psc (swaps_atom ps1 xd),
                         supply_fresh (cs_supply rc)) :: nil)
                       (swaps_aenv psc (swaps_aenv ps1 Θ3))))
        by (rewrite <- HT2;
            rewrite ! swaps_aenv_app_dist, swaps_aenv_one_var_typ;
            rewrite Hfix2a, Hfix2A; reflexivity);
      kill_dec (split_at_key_typ_complete_eq Hctx Hur) t Ht;
      cbn [fst snd];
      assert (Hsufr : a_suffix (swaps_aenv ps2 (swaps_aenv
                ((swaps_atom psc (swaps_atom ps1 xd),
                  supply_fresh (cs_supply rc)) :: nil)
                (swaps_aenv psc (swaps_aenv ps1 Ξ)))))
        by (repeat apply a_suffix_swaps; exact Hsuf);
      bool_true_ty;
      assert (HS0c : S0 [<=] cs_supply rc) by (clear - Hgrs Hgrc; fsetdec);
      eexists;
      exists (((ps1 ++ psc) ++ ((swaps_atom psc (swaps_atom ps1 xd),
                supply_fresh (cs_supply rc)) :: nil)) ++ ps2);
      split; [ cbn [typing_answer proj1_sig]; reflexivity | ];
      repeat apply conj;
      [ exact (swaps_dodge_draw
          (swaps_dodge_app_l Hav1 Havc Hgrs)
          Hx10 HS0c Hav2)
      | exact (swaps_atoms_app_transport
          (swaps_atoms_app_compose HSd2 HSd1) HS2)
      | cbn [ty_ctx]; rewrite swaps_aenv_app_dist, ! swaps_aenv_app;
        reflexivity
      | cbn [ty_out]; rewrite swaps_ptyp_arrow; f_equal;
        [ rewrite swaps_ptyp_app, swaps_ptyp_app, HfixA2, HfixAnn; exact Hfix2A
        | rewrite ! swaps_ptyp_app; exact HQ2 ] ]
    ).

  -
    rewrite e_typing_impl_equation_10.
    destruct (e_typing_inv_app Hd)
      as [S1 [S2 [Θ1 [Θ2 [P [A [A' [D1 [D2 D3]]]]]]]]].
    assert (He1 : lc_exp e1) by (inversion He; subst; assumption).
    assert (He2 : lc_exp e2) by (inversion He; subst; assumption).

    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl pskl_ghost
                    ∪ fvar_in_exp e2 ∪ ftvar_in_exp e2 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    kill_pat_call lc_pskl_ghost He2 HΘ HD Hu Hcov1 D1
      r2 Hr2 ps1 Hav1 HS1 HT1 HQ1.
    unfold pat_spec in Hr2.
    destruct (e_pat_sound Hr2 Hu Hcov1) as [Ha2 [Hu2 [Hcv2 Hq2]]].
    pose proof (e_pat_defs_mono Hr2 HD) as HD2.
    destruct (e_pat_lc_env Hr2 lc_pskl_ghost He2 HΘ HD) as [Hlc2 HΘ2].
    pose proof (e_pat_supply_grows Hr2) as Hgr2.

    assert (HfixP : forall X, ftvar_in_pskl X [<=] S0 -> swaps_pskl ps1 X = X)
      by (intros X HX; apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          exact HX).
    assert (Hfixe : forall E, fvar_in_exp E ∪ ftvar_in_exp E [<=] S0 ->
              swaps_exp ps1 E = E)
      by (intros E HE; apply swaps_exp_fresh_id, (swaps_dodge_sub Hav1);
          exact HE).
    destruct (e_typing_swaps ps1 D2 (S0' := pt_supply r2))
      as [Sd2 [HSd2 D2t]]; [ symmetry; exact HS1 | ].
    rewrite HT1 in D2t.
    rewrite swaps_pskl_arrow, HQ1 in D2t.
    rewrite (HfixP P0) in D2t by (clear - Hcov; simpl in *; fsetdec).
    rewrite (Hfixe e1) in D2t by (clear - Hcov; simpl in *; fsetdec).
    rewrite swaps_ptyp_arrow in D2t.
    assert (Hcov2 : ftvar_in_aenv (pt_ctx r2)
                    ∪ ftvar_in_pskl (pskl_arrow (pt_skel r2) P0)
                    ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] pt_supply r2)
      by (clear - Hcov Hcv2 Hq2 Hgr2; simpl in *; fsetdec).
    kill_typing (Happ1 e1 e2 eq_refl _ _ _ Hr2)
      (lc_pskl_arrow _ _ Hlc2 HP0) He1 HΘ2 HD2 Hu2 Hcov2 D2t
      r1 Hr1 ps2 Hav2 HS2 HT2 HQ2.
    unfold typing_spec in Hr1.
    destruct (e_typing_sound Hr1 Hu2 Hcov2) as [Ha1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_typing_defs_mono Hr1 HD2) as HD1.
    destruct (e_typing_lc_env Hr1 (lc_pskl_arrow _ _ Hlc2 HP0) He1 HΘ2 HD2)
      as [Hlc1 HΘ1].
    pose proof (e_typing_supply_grows Hr1) as Hgr1.

    assert (Hout : ty_out r1
              = ptyp_arrow (swaps_ptyp ps2 (swaps_ptyp ps1 A))
                  (swaps_ptyp ps2 (swaps_ptyp ps1 Bd)))
      by (rewrite <- HQ2; rewrite ! swaps_ptyp_arrow; reflexivity).
    kill_dec (ptyp_arrow_split_complete_eq Hout) p Hp.
    cbn [fst snd].

    assert (Hfixe2 : swaps_exp ps2 (swaps_exp ps1 e2) = e2).
    { rewrite (Hfixe e2) by (clear - Hcov; simpl in *; fsetdec).
      apply swaps_exp_fresh_id, (swaps_dodge_sub Hav2).
      clear - Hcov Hgr2; simpl in *; fsetdec. }
    destruct (e_typing_swaps (ps1 ++ ps2) D3 (S0' := ty_supply r1))
      as [Sd3 [HSd3 D3t]];
      [ rewrite swaps_atoms_app; rewrite <- HS2;
        apply swaps_atoms_cong; exact HSd2 | ].
    rewrite ! swaps_aenv_app, ! swaps_pskl_app, ! swaps_exp_app in D3t.
    rewrite HT2, ! swaps_pskl_ptyp_to_pskl, Hfixe2 in D3t.
    assert (Hcov3 : ftvar_in_aenv (ty_ctx r1)
                    ∪ ftvar_in_pskl
                        (ptyp_to_pskl (swaps_ptyp ps2 (swaps_ptyp ps1 A)))
                    ∪ fvar_in_exp e2 ∪ ftvar_in_exp e2 [<=] ty_supply r1).
    { pose proof (ftvar_ptyp_to_pskl
                    (swaps_ptyp ps2 (swaps_ptyp ps1 A))) as Hpa.
      rewrite Hout in Hq1. simpl in Hq1.
      clear - Hcov Hcv1 Hq1 Hpa Hgr1 Hgr2; simpl in *; fsetdec. }
    assert (Hlcdom : lc_ptyp (swaps_ptyp ps2 (swaps_ptyp ps1 A))).
    { rewrite Hout in Hlc1. inversion Hlc1; subst; assumption. }
    pose proof Hr1 as Hr1'. unfold typing_spec in Hr1'.
    rewrite Hout in Hr1'.
    kill_typing (Happ2 e1 e2 eq_refl _ _ _ Hr2 _ _ _ _ Hr1')
      (ptyp_to_pskl_lc Hlcdom) He2 HΘ1 HD1 Hu1 Hcov3 D3t
      r3 Hr3 ps3 Hav3 HS3 HT3 HQ3.
    unfold typing_spec in Hr3.
    eexists; exists ((ps1 ++ ps2) ++ ps3).
    split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
    repeat apply conj.
    + intros a0 b0 Hin. repeat (apply in_app_or in Hin;
        destruct Hin as [Hin | Hin]).
      * exact (Hav1 _ _ Hin).
      * destruct (Hav2 _ _ Hin) as [Hka Hkb]. split;
          clear - Hka Hkb Hgr2; fsetdec.
      * destruct (Hav3 _ _ Hin) as [Hka Hkb]. split;
          clear - Hka Hkb Hgr1 Hgr2; fsetdec.
    + exact (swaps_atoms_app_transport HSd3 HS3).
    + cbn [ty_ctx]. rewrite ! swaps_aenv_app. exact HT3.
    + cbn [ty_out].
      assert (Hfix3 : swaps_ptyp ps3 (swaps_ptyp ps2 (swaps_ptyp ps1 Bd))
                      = swaps_ptyp ps2 (swaps_ptyp ps1 Bd)).
      { apply swaps_ptyp_fresh_id. intros a0 b0 Hin.
        destruct (Hav3 a0 b0 Hin) as [Hka Hkb].
        rewrite Hout in Hq1. simpl in Hq1.
        split; clear - Hka Hkb Hq1; fsetdec. }
      rewrite ! swaps_ptyp_app. exact Hfix3.

  -
    rewrite e_typing_impl_equation_11.
    destruct (e_typing_inv_anno Hd) as [S1 [Θ1 [D1 D2]]].
    assert (HA : lc_ptyp A) by (inversion He; subst; assumption).
    assert (He1 : lc_exp e1) by (inversion He; subst; assumption).
    pose proof (ftvar_ptyp_to_pskl A) as HAe.
    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl (ptyp_to_pskl A)
                    ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] S0)
      by (clear - Hcov HAe; simpl in *; fsetdec).
    kill_typing (Hano e1 A eq_refl) (ptyp_to_pskl_lc HA) He1 HΘ HD Hu Hcov1 D1
      r1 Hr1 ps1 Hav1 HS1 HT1 HQ1.
    unfold typing_spec in Hr1.
    destruct (e_typing_sound Hr1 Hu Hcov1) as [Ha1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_typing_defs_mono Hr1 HD) as HD1.
    destruct (e_typing_lc_env Hr1 (ptyp_to_pskl_lc HA) He1 HΘ HD)
      as [Hlc1 HΘ1].
    pose proof (e_typing_supply_grows Hr1) as Hgr1.

    assert (HfixA : swaps_ptyp ps1 A = A)
      by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; simpl in *; fsetdec).
    rewrite HfixA in HQ1.
    bool_true_ty.
    bool_true_ty.
    destruct (e_sub_swaps ps1 D2 (S0' := ty_supply r1))
      as [Sd2 [HSd2 D2t]]; [ symmetry; exact HS1 | ].
    rewrite HT1, ! swaps_pskl_ptyp_to_pskl, HfixA in D2t.
    assert (HfixP0 : swaps_pskl ps1 P0 = P0)
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; simpl in *; fsetdec).
    rewrite HfixP0 in D2t.
    assert (Hcovs : ftvar_in_aenv (ty_ctx r1) ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl (ptyp_to_pskl A) [<=] ty_supply r1)
      by (clear - Hcov Hcv1 HAe Hgr1; simpl in *; fsetdec).
    kill_sub D2t Hu1 Hcovs r Hr ps2 Hav2 HS2 HT2 HQ2.
    assert (Hout : sb_out r
              = ptyp_to_pskl (swaps_ptyp ps2 (swaps_ptyp ps1 Bd)))
      by (rewrite <- HQ2; rewrite ! swaps_pskl_ptyp_to_pskl; reflexivity).
    kill_dec (pskl_readback_complete_eq Hout) B0 HB0.
    eexists; exists (ps1 ++ ps2).
    split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
    repeat apply conj.
    + apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1; fsetdec.
    + exact (swaps_atoms_app_transport HSd2 HS2).
    + cbn [ty_ctx]. rewrite swaps_aenv_app. exact HT2.
    + cbn [ty_out]. rewrite swaps_ptyp_app. reflexivity.

  -
    destruct (e_typing_inv_freeze Hd)
      as [-> [HP0eq [S1 [Θ1 [B [D1 Dc]]]]]].
    subst P0.
    rewrite e_typing_impl_equation_13.
    assert (He1 : lc_exp e1) by (inversion He; subst; assumption).
    assert (HBd : lc_ptyp Bd)
      by (eapply ptyp_to_pskl_lc_inv; exact HP0).
    pose proof (ftvar_ptyp_to_pskl Bd) as HBe.
    kill_dec (pskl_readback_complete_eq
                (eq_refl : ptyp_to_pskl Bd = ptyp_to_pskl Bd)) A0 HA0.
    assert (Hcov1 : ftvar_in_aenv Θ0 ∪ ftvar_in_pskl pskl_ghost
                    ∪ fvar_in_exp e1 ∪ ftvar_in_exp e1 [<=] S0)
      by (clear - Hcov; simpl in *; fsetdec).
    kill_typing (Hfz e1 eq_refl) lc_pskl_ghost He1 HΘ HD Hu Hcov1 D1
      r1 Hr1 ps1 Hav1 HS1 HT1 HQ1.
    unfold typing_spec in Hr1.
    destruct (e_typing_sound Hr1 Hu Hcov1) as [Ha1 [Hu1 [Hcv1 Hq1]]].
    pose proof (e_typing_defs_mono Hr1 HD) as HD1.
    destruct (e_typing_lc_env Hr1 lc_pskl_ghost He1 HΘ HD) as [Hlc1 HΘ1].
    pose proof (e_typing_supply_grows Hr1) as Hgr1.
    bool_true_ty.
    destruct Dc as [Qc Dc].
    pose proof (swaps_atoms_empty ps1) as Hemp; symmetry in Hemp;
    pose proof HS1 as HS1r; symmetry in HS1r;
    destruct (e_consis_swaps ps1 Dc Hemp
                Hemp HS1r)
      as [Sc1 [HSc1 Dc1]];
    rewrite HT1, ! swaps_pskl_ptyp_to_pskl, HQ1 in Dc1.
    assert (HfixBd : swaps_ptyp ps1 Bd = Bd)
      by (apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov HBe; simpl in *; fsetdec).
    rewrite HfixBd in Dc1.
    assert (Hcovc : ftvar_in_aenv (ty_ctx r1)
                    ∪ ftvar_in_pskl (ptyp_to_pskl Bd)
                    ∪ ftvar_in_pskl (ptyp_to_pskl (ty_out r1))
                    ∪ empty ∪ empty [<=] ty_supply r1).
    { pose proof (ftvar_ptyp_to_pskl (ty_out r1)) as Ho1.
      clear - Hcov Hcv1 Hq1 HBe Ho1 Hgr1; simpl in *; fsetdec. }
    kill_consis_call Dc1 Hu1 Hcovc rc Hrc ps2 Hav2 HS2 HT2 HQ2.
    eexists; exists (ps1 ++ ps2).
    split; [ cbn [typing_answer proj1_sig]; reflexivity | ].
    repeat apply conj.
    + apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1; fsetdec.
    + exact (swaps_atoms_app_transport HSc1 HS2).
    + cbn [ty_ctx]. rewrite swaps_aenv_app. exact HT2.
    + cbn [ty_out]. rewrite swaps_ptyp_app, HfixBd.
      apply swaps_ptyp_fresh_id, (swaps_dodge_sub Hav2).
      clear - Hcov HBe Hgr1; simpl in *; fsetdec.
Qed.

Corollary e_typing_impl_complete : forall S0 m Θ0 P0 e
    (H : e_typing_order S0 m Θ0 P0 e) Sd Θd Bd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
    [<=] S0 ->
  exists r ps,
    e_typing_impl S0 m Θ0 P0 e H = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] ty_supply (proj1_sig r)
    /\ swaps_aenv ps Θd = ty_ctx (proj1_sig r)
    /\ swaps_ptyp ps Bd = ty_out (proj1_sig r).
Proof.
  intros * Hd HP0 He HΘ HD Hu Hcov.
  destruct (e_typing_impl_complete_ind H H HP0 He HΘ HD Hu Hcov Hd)
    as [r0 [ps [Hx [Hav [HS [HT HQ]]]]]].
  destruct (e_typing_impl S0 m Θ0 P0 e H) as [ [rr Hrr] | ] eqn:Hcl;
    try rewrite Hcl in Hx; cbn [typing_answer proj1_sig] in Hx;
    [ inversion Hx; subst r0 | discriminate ].
  eexists; exists ps.
  exact (conj eq_refl (conj Hav (conj HS (conj HT HQ)))).
Qed.

Theorem e_typing_run_complete : forall S0 m Θ0 P0 e Sd Θd Bd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ m ; P0 ] e ⦂ Bd ⊣ Θd }}e ->
  lc_pskl P0 -> lc_exp e -> lc_aenv Θ0 -> aenv_defs_mono Θ0 -> uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e
    [<=] S0 ->
  exists r ps,
    e_typing_run S0 m Θ0 P0 e = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] ty_supply r
    /\ swaps_aenv ps Θd = ty_ctx r
    /\ swaps_ptyp ps Bd = ty_out r.
Proof.
  intros * Hd HP0 He HΘ HD Hu Hcov. unfold e_typing_run.
  destruct (e_typing_impl_complete (e_typing_order_total S0 m Θ0 P0 e)
              Hd HP0 He HΘ HD Hu Hcov)
    as [r [ps [Heq [Hav [HS [HT HQ]]]]]].
  rewrite Heq.
  exists (proj1_sig r), ps.
  exact (conj eq_refl (conj Hav (conj HS (conj HT HQ)))).
Qed.
