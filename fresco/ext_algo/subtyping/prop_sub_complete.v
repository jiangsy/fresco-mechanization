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
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_swap.
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
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.basic.prop_termination.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.consistency.def_consis_impl.
Require Import src.fresco.ext_algo.consistency.prop_consis_complete.
Require Import src.fresco.ext_algo.subtyping.def_extract_impl.
Require Import src.fresco.ext_algo.subtyping.prop_extract_det.
Require Import src.fresco.ext_algo.subtyping.prop_extract_complete.
Require Import src.fresco.ext_algo.subtyping.def_sub_impl.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

Lemma e_sub_swaps : forall ps S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊢[ NM | M | (swaps_pskl ps P0) ]
       (swaps_pskl ps P) ⩽ (swaps_pskl ps Q) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  -
    exact (e_sub_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_sub_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma swaps_dodge_one {x y} {T : atoms} :
  x `notin` T -> y `notin` T ->
  forall a b, In (a, b) ((x, y) :: nil) -> a `notin` T /\ b `notin` T.
Proof.
  intros Hx Hy a b [Heq | []]. inversion Heq; subst. split; assumption.
Qed.

Lemma swaps_onto_fresh : forall x (S : atoms),
  x `notin` S ->
  (forall a b, In (a, b) ((x, supply_fresh S) :: nil) ->
     a `notin` S /\ b `notin` S) /\
  swaps_atom ((x, supply_fresh S) :: nil) x = supply_fresh S /\
  add (supply_fresh S) S [=] swaps_atoms ((x, supply_fresh S) :: nil) (add x S).
Proof.
  intros x S Hx. pose proof (supply_fresh_notin S) as Hf.
  repeat apply conj.
  - apply swaps_dodge_one; assumption.
  - apply swap_atom_l.
  - apply swap_atoms_fresh_add; assumption.
Qed.

Lemma a_suffix_swaps : forall ps (Ξ : aenv),
  a_suffix Ξ -> a_suffix (swaps_aenv ps Ξ).
Proof.
  induction ps as [ | [a b] ps IH ]; intros Ξ Hs; simpl; [ exact Hs | ].
  apply IH. apply a_suffix_swap. exact Hs.
Qed.

Local Ltac kill_unguarded :=
  repeat match goal with
         | Hg : guarded_pskl (pskl_all_syn _) |- _ => solve [ inversion Hg ]
         | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => solve [ inversion Hg ]
         | Hg : guarded_pskl pskl_ghost |- _ => solve [ inversion Hg ]
         end.

Local Ltac kill_forall_l_guard :=
  repeat match goal with
         | Hg : guarded_pskl ?X \/ ?X = pskl_ghost |- _ =>
             solve [ destruct Hg as [Hg | Hg];
                     [ inversion Hg | discriminate ] ]
         end.

Lemma e_sub_inv_ti : forall S0 NM P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | mode_ti | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  P0 = pskl_ghost /\ Q = P /\ S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros * Hd. inversion Hd; subst; try congruence.
  repeat split; reflexivity.
Qed.

Lemma e_sub_inv_forall_r : forall S0 Θ0 B P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | mode_tc | (pskl_all_syn B) ]
     P ⩽ Q ⊣ Θ1 }}e ->
  Q = pskl_all_syn B /\ pskl_ghost_free (pskl_all_syn B) /\
  exists α Ξ,
    a_suffix Ξ /\ uniq (Ξ ++ Θ0) /\ α `notin` S0 /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ a_sub_mode_ty | mode_tc | (open_pskl_wrt_pskl B (pskl_var_f α)) ]
       P ⩽ (open_pskl_wrt_pskl B (pskl_var_f α))
       ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}e.
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded; kill_forall_l_guard.
  split; [ reflexivity | split; [ assumption | eauto 10 ] ].
Qed.

Lemma e_sub_inv_check : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | mode_tc | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  (forall B, P0 <> pskl_all_syn B) ->
  (forall B, P <> pskl_all_syn B) ->
  Q = P0 /\ pskl_ghost_free P /\ pskl_ghost_free P0 /\
  guarded_pskl P /\ guarded_pskl P0 /\ e_consis_chk S0 Θ0 P P0 S1 Θ1.
Proof.
  intros * Hd Hn0 Hn. inversion Hd; subst;
    try solve [ exfalso; eapply Hn0; reflexivity
              | exfalso; eapply Hn; reflexivity ].
  repeat split; assumption.
Qed.

Lemma e_sub_inv_forall_l_gen : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] (pskl_all_syn P) ⩽ Q ⊣ Θ1 }}e ->
  M <> mode_ti ->
  (NM = a_sub_mode_sk \/ M <> mode_tc \/ (forall B, P0 <> pskl_all_syn B)) ->
  (guarded_pskl P0 \/ P0 = pskl_ghost) /\
  exists α Sm Ξ P1,
    α `notin` S0 /\
    {{ (add α S0) ↝ Sm ⊨ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α))
       ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}e /\
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a /\
    {{ Sm ↝ S1 ⊨ (Ξ ++ Θ0) ⊢[ NM | M | P0 ]
       (open_pskl_wrt_pskl P P1) ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd Hti Hor. inversion Hd; subst; kill_unguarded;
    try solve [ congruence
              | destruct Hor as [Ho | [Ho | Ho]];
                solve [ discriminate | congruence
                      | exfalso; eapply Ho; reflexivity ] ].
  split; [ assumption | eauto 10 ].
Qed.

Lemma e_sub_inv_ghost : forall S0 M P0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] pskl_ghost ⩽ Q ⊣ Θ1 }}e ->
  M <> mode_ti ->
  Q = P0 /\ S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros * Hd Hti. inversion Hd; subst; kill_unguarded; try congruence.
  repeat split; reflexivity.
Qed.

Lemma e_sub_inv_univ_ghost_l : forall S0 M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] (pskl_univ_ghost P) ⩽ Q ⊣ Θ1 }}e ->
  M <> mode_ti ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] P ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd Hti. inversion Hd; subst; kill_unguarded;
    solve [ congruence | assumption ].
Qed.

Lemma e_sub_inv_univ_ghost_r : forall S0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | mode_tc | pskl_ghost ] P ⩽ Q ⊣ Θ1 }}e ->
  P <> pskl_ghost -> (forall Pb, P <> pskl_univ_ghost Pb) ->
  (forall Pb, P <> pskl_all_syn Pb) ->
  guarded_pskl P /\ Q = pskl_univ_ghost P /\ S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros * Hd Hnh Hnt Hna. inversion Hd; subst;
    try solve [ congruence
              | exfalso; eapply Hnt; reflexivity
              | exfalso; eapply Hna; reflexivity ].
  repeat split; solve [ assumption | reflexivity ].
Qed.

Lemma e_sub_inv_sk_tc_none : forall S0 P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | mode_tc | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  P <> pskl_ghost -> (forall Pb, P <> pskl_univ_ghost Pb) ->
  (forall Pb, P <> pskl_all_syn Pb) -> P0 <> pskl_ghost -> False.
Proof.
  intros * Hd Hnh Hnt Hna Hn0. inversion Hd; subst;
    solve [ congruence
          | exfalso; eapply Hnt; reflexivity
          | exfalso; eapply Hna; reflexivity ].
Qed.

Lemma e_sub_inv_arrow : forall S0 NM M P0a P0b Θ0 P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | (pskl_arrow P0a P0b) ]
     (pskl_arrow P1 P2) ⩽ Q ⊣ Θ1 }}e ->
  exists Sm Θm Q1 Q2,
    Q = pskl_arrow Q1 Q2 /\
    {{ S0 ↝ Sm ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θm }}e /\
    {{ Sm ↝ S1 ⊨ Θm ⊢[ NM | M | P0b ] P2 ⩽ Q2 ⊣ Θ1 }}e.
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded. eauto 10.
Qed.

Lemma e_sub_inv_arrow_none : forall S0 NM M P0 Θ0 P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ] (pskl_arrow P1 P2) ⩽ Q ⊣ Θ1 }}e ->
  (forall A B, P0 <> pskl_arrow A B) -> False.
Proof.
  intros * Hd Hn0. inversion Hd; subst;
    solve [ congruence | exfalso; eapply Hn0; reflexivity ].
Qed.

Lemma e_sub_inv_flex_mono : forall S0 NM M P0 Θ0 α Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ] (pskl_var_f α) ⩽ Q ⊣ Θ1 }}e ->
  e_sub_flex S0 NM M P0 Θ0 nil α Q S1 Θ1.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded. assumption. Qed.

Lemma e_sub_inv_fn_unit_none : forall S0 NM M P0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ] pskl_unit ⩽ Q ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

Lemma e_sub_inv_fn_ty_ghost_none : forall S0 M P0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | (mode_fn M) | P0 ]
     pskl_ghost ⩽ Q ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

Lemma e_sub_inv_fn_ty_univ_ghost_none : forall S0 M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | (mode_fn M) | P0 ]
     (pskl_univ_ghost P) ⩽ Q ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

Lemma e_sub_flex_inv_nil : forall S0 NM M P0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 nil Ξ α Q S1 Θ1 -> False.
Proof. intros * Hd. inversion Hd. Qed.

Lemma e_sub_flex_inv_self : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((α ~ abind_flex_mono) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists a1 b1, a1 `notin` S0 /\ b1 `notin` add a1 S0 /\
    {{ (add b1 (add a1 S0)) ↝ S1 ⊨
       (Ξ ++ (α ~ abind_flex_mono_def
                    (ptyp_arrow (ptyp_var_f a1) (ptyp_var_f b1)))
           ++ (b1 ~ abind_flex_mono) ++ (a1 ~ abind_flex_mono) ++ Θ0)
       ⊢[ NM | (mode_fn M) | P0 ]
       (pskl_arrow (pskl_var_f a1) (pskl_var_f b1)) ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd. inversion Hd; subst; try congruence. eauto 10.
Qed.

Lemma e_sub_flex_inv_other_flex : forall S0 NM M P0 Θ0 Ξ α β Q S1 Θ1,
  α <> β ->
  e_sub_flex S0 NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α Q S1 Θ1 ->
  (β `in` ftvar_in_pskl P0 /\
     e_sub_flex S0 NM M P0 Θ0 (Ξ ++ (β ~ abind_flex_mono)) α Q S1 Θ1)
  \/ (β `notin` ftvar_in_pskl P0 /\ exists Θ1',
        Θ1 = (β ~ abind_flex_mono) ++ Θ1' /\
        e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1').
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence.
  - left; split; assumption.
  - right; split; [ assumption | eauto ].
Qed.

Lemma e_sub_flex_inv_def : forall S0 NM M P0 Θ0 Ξ α β τ Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists Θ1', Θ1 = (β ~ abind_flex_mono_def τ) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ (Ξ ++ Θ0)
       ⊢[ NM | (mode_fn M) | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) ]
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ⩽ Q
       ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_sub_flex_inv_tvar : forall S0 NM M P0 Θ0 Ξ α β Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α Q S1 Θ1 ->
  α <> β /\ β `notin` ftvar_in_pskl P0 /\ exists Θ1',
    Θ1 = (β ~ abind_tvar) ++ Θ1' /\ e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1'.
Proof.
  intros * Hd. inversion Hd; subst.
  split; [ assumption | split; [ assumption | eauto ] ].
Qed.

Lemma e_sub_flex_inv_var_typ : forall S0 NM M P0 Θ0 Ξ α x A Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((x ~ abind_var_typ A) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists Θ1', Θ1 = (x ~ abind_var_typ A) ++ Θ1' /\
    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1'.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_sub_flex_inv_var_skl : forall S0 NM M P0 Θ0 Ξ α x Qp Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((x ~ abind_var_skl Qp) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists Θ1', Θ1 = (x ~ abind_var_skl Qp) ++ Θ1' /\
    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1'.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma swaps_two_onto_fresh : forall (S0 : atoms) ad bd,
  ad `notin` S0 -> bd `notin` add ad S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atom ps ad = supply_fresh S0 /\
    swaps_atom ps bd = supply_fresh (add (supply_fresh S0) S0) /\
    add (supply_fresh (add (supply_fresh S0) S0)) (add (supply_fresh S0) S0)
      [=] swaps_atoms ps (add bd (add ad S0)).
Proof.
  intros S0 ad bd Had Hbd.
  remember (supply_fresh S0) as a1 eqn:Ea1.
  remember (supply_fresh (add a1 S0)) as b1 eqn:Eb1.
  assert (Ha1 : a1 `notin` S0) by (subst a1; apply supply_fresh_notin).
  assert (Hb1 : b1 `notin` add a1 S0) by (subst b1; apply supply_fresh_notin).
  clear Ea1 Eb1.
  remember (swap_atom ad a1 bd) as c eqn:Ec.
  assert (Hc : c `notin` add a1 S0).
  { subst c. unfold swap_atom.
    destruct (bd == ad) as [Hc1 | Hne1].
    { exfalso. clear - Hbd Hc1. fsetdec. }
    destruct (bd == a1) as [Hc2 | Hne2].
    - assert (Hada1 : ad <> a1) by congruence. clear - Had Hada1. fsetdec.
    - clear - Hbd Hne2. fsetdec. }
  assert (Hav : forall a b, In (a, b) ((ad, a1) :: (c, b1) :: nil) ->
                a `notin` S0 /\ b `notin` S0)
    by (intros a b [Heq | [Heq | []]]; inversion Heq; subst;
        split; clear - Had Ha1 Hc Hb1; fsetdec).
  assert (Hsad : swaps_atom ((ad, a1) :: (c, b1) :: nil) ad = a1)
    by (cbn [swaps_atom]; rewrite swap_atom_l;
        apply swap_atom_other; clear - Hc Hb1; fsetdec).
  assert (Hsbd : swaps_atom ((ad, a1) :: (c, b1) :: nil) bd = b1)
    by (cbn [swaps_atom]; rewrite <- Ec; apply swap_atom_l).
  exists ((ad, a1) :: (c, b1) :: nil).
  refine (conj Hav (conj Hsad (conj Hsbd _))).
  rewrite swaps_atoms_add, swaps_atoms_add, Hsad, Hsbd.
  rewrite (swaps_atoms_notin _ _ Hav). reflexivity.
Qed.

Lemma e_sub_flex_solve_realign : forall S0 NM M P0 Θ0' Ξ α Qd Sd Θd ad bd,
  ad `notin` S0 -> bd `notin` add ad S0 ->
  ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0 ∪ singleton α [<=] S0 ->
  {{ (add bd (add ad S0)) ↝ Sd ⊨
     (Ξ ++ (α ~ abind_flex_mono_def
                  (ptyp_arrow (ptyp_var_f ad) (ptyp_var_f bd)))
         ++ (bd ~ abind_flex_mono) ++ (ad ~ abind_flex_mono) ++ Θ0')
     ⊢[ NM | (mode_fn M) | P0 ]
     (pskl_arrow (pskl_var_f ad) (pskl_var_f bd)) ⩽ Qd ⊣ Θd }}e ->
  exists ps0 Sd',
    (forall a b, In (a, b) ps0 -> a `notin` S0 /\ b `notin` S0)
    /\ Sd' [=] swaps_atoms ps0 Sd
    /\ {{ (add (supply_fresh (add (supply_fresh S0) S0))
             (add (supply_fresh S0) S0)) ↝ Sd' ⊨
       (Ξ ++ (α ~ abind_flex_mono_def
                    (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                       (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
           ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
           ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
       ⊢[ NM | (mode_fn M) | P0 ]
       (pskl_arrow (pskl_var_f (supply_fresh S0))
          (pskl_var_f (supply_fresh (add (supply_fresh S0) S0))))
       ⩽ (swaps_pskl ps0 Qd) ⊣ (swaps_aenv ps0 Θd) }}e.
Proof.
  intros * Had Hbd Hcov Ds.
  destruct (swaps_two_onto_fresh Had Hbd) as (ps & Hav & Hsad & Hsbd & HSadd).
  destruct (e_sub_swaps ps Ds HSadd) as [Sd' [HSd' Ds']].
  exists ps, Sd'. refine (conj Hav (conj HSd' _)).

  rewrite ftvar_in_aenv_app in Hcov.
  rewrite !swaps_aenv_app_dist, swaps_aenv_one_def, !swaps_aenv_one_flex,
    swaps_ptyp_arrow, !swaps_ptyp_var_f, swaps_pskl_arrow, !swaps_pskl_var_f,
    Hsad, Hsbd in Ds'.
  rewrite (swaps_atom_dodge_in Hav (α := α)) in Ds' by (clear - Hcov; fsetdec).
  rewrite (swaps_aenv_fresh_id ps Ξ), (swaps_aenv_fresh_id ps Θ0'),
    (swaps_pskl_fresh_id ps P0) in Ds'
    by (apply (swaps_dodge_sub Hav); clear - Hcov; fsetdec).
  exact Ds'.
Qed.

Arguments e_sub_flex_solve_realign {S0 NM M P0 Θ0' Ξ α Qd Sd Θd ad bd} _ _ _ _.

Lemma swaps_pskl_open : forall ps P1 P2,
  swaps_pskl ps (open_pskl_wrt_pskl P1 P2)
  = open_pskl_wrt_pskl (swaps_pskl ps P1) (swaps_pskl ps P2).
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; [ reflexivity | ].
  rewrite swap_pskl_open. apply IH.
Qed.

Lemma a_wf_pskl_swaps : forall ps (Θ : aenv) P,
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  {{ (swaps_aenv ps Θ) ⨟ empty ⊢ₚₛ (swaps_pskl ps P) }}a.
Proof.
  induction ps as [ | [a b] ps IH ]; intros Θ P H; simpl; [ exact H | ].
  apply IH. eapply a_wf_pskl_swap;
    [ exact H | symmetry; apply swap_atoms_empty ].
Qed.

Lemma split_at_tvar_complete : forall α Θ Ξ Θ',
  Θ = Ξ ++ (α ~ abind_tvar) ++ Θ' -> uniq Θ ->
  exists r, split_at_tvar α Θ = Some r /\ proj1_sig r = (Ξ, Θ').
Proof.
  intros α Θ Ξ Θ' -> Hu. revert Θ' Hu.
  induction Ξ as [ | [y b] Ξ' IH ]; intros Θ' Hu.
  - simpl. destruct (abind_is_tvar_dec abind_tvar) as [Hb | Hb];
      [ | congruence ].
    destruct (α == α) as [Heq | Hne]; [ | congruence ].
    eexists. split; reflexivity.
  - simpl in Hu |- *. inversion Hu; subst.
    destruct (IH Θ' ltac:(assumption)) as [[t Ht] [Hr Hpr]].
    simpl in Hpr; subst t.
    change (α ~ abind_tvar ++ Θ') with ((α, abind_tvar) :: Θ') in Hr.
    assert (Hαy : α <> y) by (simpl_env in *; fsetdec).
    destruct (abind_is_tvar_dec b) as [Hb | Hb].
    + destruct (α == y) as [Heq | Hne]; [ congruence | ].
      rewrite Hr. eexists. split; reflexivity.
    + rewrite Hr. eexists. split; reflexivity.
Qed.

Arguments split_at_tvar_complete {α Θ Ξ Θ'} _ _.

Definition sub_call_answer {S0 : supply} {NM : a_sub_mode} {M : mode}
    {P0 : pskl} {Θ0 : aenv} {c : sub_call}
    (o : option (sig (sub_call_spec S0 NM M P0 Θ0 c))) : option sub_result :=
  match o with None => None | Some r => Some (proj1_sig r) end.

Definition sub_call_run (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (c : sub_call)
    (Sd : supply) (Θd : aenv) (Qd : pskl) : Prop :=
  match c with
  | sub_call_sub P    => {{ S0 ↝ Sd ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Qd ⊣ Θd }}e
  | sub_call_flex Ξ α => e_sub_flex S0 NM M P0 Θ0 Ξ α Qd Sd Θd
  end.

Definition sub_call_uniq (Θ0 : aenv) (c : sub_call) : Prop :=
  match c with
  | sub_call_sub _    => uniq Θ0
  | sub_call_flex Ξ _ => uniq (Ξ ++ Θ0)
  end.

Definition sub_call_cover (P0 : pskl) (Θ0 : aenv) (c : sub_call) : atoms :=
  match c with
  | sub_call_sub P    =>
      ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P
  | sub_call_flex Ξ α =>
      ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0 ∪ singleton α
  end.

Definition sub_call_complete (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (c : sub_call) : Prop :=
  forall (HP : sub_call_lc c) (HP0 : lc_pskl P0)
         (HD : sub_call_defs_mono Θ0 c)
         (H : e_sub_call_order S0 NM M P0 Θ0 c),
    sub_call_uniq Θ0 c ->
    sub_call_cover P0 Θ0 c [<=] S0 ->
    forall Sd Θd Qd, sub_call_run S0 NM M P0 Θ0 c Sd Θd Qd ->
    exists r ps,
      sub_call_answer (e_sub_call_impl c S0 NM M P0 Θ0 HP HP0 HD H) = Some r
      /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
      /\ swaps_atoms ps Sd [=] sb_supply r
      /\ swaps_aenv ps Θd = sb_ctx r
      /\ swaps_pskl ps Qd = sb_out r.

Local Ltac kill_scall Hmot Hu Hcov Hder r Hr ps Hav HS HT HQ :=
  match goal with
  | |- context [ e_sub_call_impl ?c ?S ?nm ?m ?p0 ?T ?hp ?hp0 ?hd ?h ] =>
      let Hx := fresh "Hx" in
      let Hcl := fresh "Hcl" in
      let rr := fresh "rr" in
      destruct (Hmot hp hp0 hd h Hu Hcov _ _ _ Hder)
        as [r [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_sub_call_impl c S nm m p0 T hp hp0 hd h)
        as [ [rr Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx; cbn [sub_call_answer] in Hx;
      [ inversion Hx; subst; clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

Local Ltac split_eqdec Hl Hr :=
  lazymatch goal with
  | |- context [ @eq_dec ?T ?E ?x ?y ] =>
      destruct (@eq_dec T E x y) as [ Hl | Hr ]
  end.

Local Ltac kill_consis Hu Hcov Hder r Hr ps Hav HS HT HQ :=
  match goal with
  | |- context [ e_consis_impl ?d1 ?d2 ?S ?T ?p0 ?p ?h0 ?h1 ?hd ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let rr := fresh "rr" in let Ho := fresh "Ho" in
      set (Ho := e_consis_order_to_call d1 d2 S T p0 p h);
      destruct (e_consis_call_impl_complete Ho (conj h0 h1) hd Ho Hu Hcov
                  _ _ _ Hder)
        as [r [ps [Hx [Hav [HS [HT HQ]]]]]];
      unfold e_consis_impl; fold Ho;
      destruct (e_consis_call_impl (consis_call_consis d1 d2 p0 p) S T
                  (conj h0 h1) hd Ho) as [ [rr Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx; cbn [consis_call_answer] in Hx;
      [ inversion Hx; subst; clear Hx Hcl; cbv beta iota;
        cbn [consis_call_out_rel] in HQ
      | discriminate ]
  end.

Local Ltac ck_leaf :=
  solve [ apply ghost_free_ck_complete; assumption
        | apply guarded_shape_ck_complete; assumption
        | apply uniq_ck_complete; assumption
        | apply suffix_ck_complete; assumption
        | apply pskl_eqb_complete; assumption
        | apply wf_pskl_ck_complete_at_size; assumption
        | apply orb_true_intro;
          match goal with
          | H : guarded_pskl _ \/ _ = pskl_ghost |- _ =>
              destruct H as [H | H];
              [ left; apply guarded_shape_ck_complete; exact H
              | right; apply ghost_ck_complete; exact H ]
          end ].

Ltac ck_true_with leaf := repeat (leaf || (apply andb_true_intro; split)).

Ltac bool_true_with leaf :=
  match goal with
  | |- context [ sumbool_of_bool ?b ] =>
      let Hbt := fresh "Hbt" in let Hb := fresh "Hb" in
      assert (Hbt : b = true) by (ck_true_with leaf);
      destruct (sumbool_of_bool b) as [Hb | Hb];
      [ cbv beta iota | congruence ]
  end.
Local Ltac bool_true := bool_true_with ltac:(idtac; ck_leaf).

Local Ltac out_fixed Hav Hcov :=
  apply swaps_pskl_fresh_id; intros a0 b0 Hin;
  let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
  destruct (Hav a0 b0 Hin) as [Ha0 Hb0]; split;
  clear - Ha0 Hb0 Hcov; simpl in *; fsetdec.

Local Ltac answer_id :=
  eexists; exists (@nil (atom * atom));
  split; [ reflexivity | ];
  repeat apply conj; [ intros ? ? []
          | cbn [swaps_atoms sb_supply]; reflexivity
          | cbn [swaps_aenv sb_ctx]; reflexivity
          | cbn [swaps_pskl sb_out]; reflexivity ].

Local Ltac kill_var_b :=
  exfalso;
  match goal with H : lc_pskl (pskl_var_b _) |- _ => inversion H end.

Local Ltac do_check Hd Hu Hcov :=
  let Hgf1 := fresh "Hgf1" in
  let Hgf0 := fresh "Hgf0" in let Hgd1 := fresh "Hgd1" in
  let Hgd0 := fresh "Hgd0" in let Qc0 := fresh "Qc0" in
  let Dc := fresh "Dc" in let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in let ps := fresh "ps" in
  let Hav := fresh "Hav" in let HS := fresh "HS" in
  let HT := fresh "HT" in let HQ := fresh "HQ" in
  destruct (e_sub_inv_check Hd ltac:(intros; discriminate)
              ltac:(intros; discriminate))
    as [-> [Hgf1 [Hgf0 [Hgd1 [Hgd0 [Qc0 Dc]]]]]];
  bool_true;
  match goal with
  | |- context [ e_consis_impl ?d1 ?d2 ?S ?T ?p0 ?p ?h0 ?h1 ?hd ?h ] =>
      assert (Hcov0 : consis_call_cover T (consis_call_consis d1 d2 p0 p)
                      [<=] S)
        by (cbn [consis_call_cover]; clear - Hcov; simpl in *; fsetdec)
  end;
  kill_consis Hu Hcov0 Dc r Hr ps Hav HS HT HQ;
  eexists; exists ps;
  split; [ reflexivity | ];
  repeat apply conj; [ exact Hav | cbn [sb_supply]; exact HS
          | cbn [sb_ctx]; exact HT
          | cbn [sb_out]; out_fixed Hav Hcov ].

Local Ltac do_univ_ghost_l Hd Hu Hcov Hmot :=
  let Ds := fresh "Ds" in let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in let ps := fresh "ps" in
  let Hav := fresh "Hav" in let HS := fresh "HS" in
  let HT := fresh "HT" in let HQ := fresh "HQ" in
  pose proof (e_sub_inv_univ_ghost_l Hd ltac:(discriminate)) as Ds;
  match goal with
  | |- context [ e_sub_call_impl ?c ?S ?nm ?m ?p0 ?T ?hp ?hp0 ?hd ?h ] =>
      assert (Hcov0 : sub_call_cover p0 T c [<=] S)
        by (cbn [sub_call_cover] in *; clear - Hcov; simpl in *; fsetdec)
  end;
  kill_scall Hmot Hu Hcov0 Ds r Hr ps Hav HS HT HQ;
  exists r, ps; split; [ reflexivity | ];
  repeat apply conj; [ exact Hav | exact HS | exact HT | exact HQ ].

Local Ltac do_ghost Hd :=
  destruct (e_sub_inv_ghost Hd ltac:(discriminate)) as [-> [-> ->]];
  answer_id.

Local Ltac do_forall_l Hd Hu Hcov pmot s0 t0 p0 q :=
  let Hg := fresh "Hg" in let ad := fresh "ad" in
  let Sm := fresh "Sm" in let Xd := fresh "Xd" in
  let P1d := fresh "P1d" in let Had := fresh "Had" in
  let Dx := fresh "Dx" in let Hwfd := fresh "Hwfd" in
  let Dsub := fresh "Dsub" in let Ha1 := fresh "Ha1" in
  let Hav0 := fresh "Hav0" in let Hsad := fresh "Hsad" in
  let HfixT := fresh "HfixT" in let HfixQ := fresh "HfixQ" in
  let Smx := fresh "Smx" in let HSmx := fresh "HSmx" in
  let Dx1 := fresh "Dx1" in let Dx2 := fresh "Dx2" in
  let Hcx := fresh "Hcx" in let Hop := fresh "Hop" in
  destruct (e_sub_inv_forall_l_gen Hd ltac:(discriminate)
              ltac:(solve [ left; reflexivity
                          | right; left; discriminate
                          | right; right; intros ? Habs;
                            discriminate Habs ]))
    as [Hg [ad [Sm [Xd [P1d [Had [Dx [Hwfd Dsub]]]]]]]];
  bool_true;
  pose proof (supply_fresh_notin s0) as Ha1;
  assert (Hav0 : forall a b, In (a, b) ((ad, supply_fresh s0) :: nil) ->
                 a `notin` s0 /\ b `notin` s0)
    by (intros a b [Heq | []]; inversion Heq; subst; split; assumption);
  assert (Hsad : swaps_atom ((ad, supply_fresh s0) :: nil) ad
                 = supply_fresh s0)
    by (simpl; unfold swap_atom;
        destruct (ad == ad); [ reflexivity | congruence ]);
  assert (HfixT : forall (X : aenv), ftvar_in_aenv X [<=] s0 ->
            swaps_aenv ((ad, supply_fresh s0) :: nil) X = X)
    by (intros X HX; apply swaps_aenv_fresh_id; intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav0 a b Hin) as [Hza Hzb]; split; fsetdec);
  assert (HfixQ : forall X, ftvar_in_pskl X [<=] s0 ->
            swaps_pskl ((ad, supply_fresh s0) :: nil) X = X)
    by (intros X HX; apply swaps_pskl_fresh_id; intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav0 a b Hin) as [Hza Hzb]; split; fsetdec);

  destruct (e_extract_swaps ((ad, supply_fresh s0) :: nil) Dx
              (S0' := add (supply_fresh s0) s0)) as [Smx [HSmx Dx1]];
  [ simpl; rewrite swap_atoms_add;
    rewrite (swap_atoms_notin ad (supply_fresh s0) s0)
      by (clear - Had Ha1; fsetdec);
    unfold swap_atom; destruct (ad == ad); [ reflexivity | congruence ]
  | ];
  rewrite (HfixT t0) in Dx1 by (clear - Hcov; simpl in *; fsetdec);
  rewrite swaps_pskl_open, swaps_pskl_var_f, Hsad in Dx1;
  rewrite (HfixQ q) in Dx1 by (clear - Hcov; simpl in *; fsetdec);
  rewrite (HfixQ p0) in Dx1 by (clear - Hcov; simpl in *; fsetdec);
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper q
                (pskl_var_f (supply_fresh s0))) as Hop;
  simpl in Hop;
  assert (Hcx : add (supply_fresh s0)
            (ftvar_in_aenv t0
             ∪ ftvar_in_pskl (open_pskl_wrt_pskl q
                  (pskl_var_f (supply_fresh s0)))
             ∪ ftvar_in_pskl p0) [<=] add (supply_fresh s0) s0)
    by (clear - Hcov Hop; simpl in *; fsetdec);

  let rx := fresh "rx" in let Hrx := fresh "Hrx" in
  let Hne := fresh "Hne" in let Hxc := fresh "Hxc" in
  match goal with
  | |- context [ e_extract_impl ?S ?T ?nm ?al ?mm ?pp ?pp' ?h1 ?h2 ?h3 ] =>
      assert (Hne : e_extract_impl S T nm al mm pp pp' h1 h2 h3 <> None)
        by (exact (e_extract_impl_complete h1 h2 h3 Dx1 Hcx));
      destruct (e_extract_impl S T nm al mm pp pp' h1 h2 h3)
        as [ [rx Hrx] | ] eqn:Hxc;
      [ cbv beta iota | exact (False_ind _ (Hne eq_refl)) ]
  end;
  unfold extract_spec in Hrx;

  let ps1 := fresh "ps1" in let Hav1 := fresh "Hav1" in
  let HS1 := fresh "HS1" in let HX1 := fresh "HX1" in
  let HY1 := fresh "HY1" in
  destruct (e_extract_det Dx1 Hrx Hcx) as [ps1 [Hav1 [HS1 [HX1 HY1]]]];

  let Hwf0 := fresh "Hwf0" in let Hwf1 := fresh "Hwf1" in
  pose proof (a_wf_pskl_swaps ((ad, supply_fresh s0) :: nil) Hwfd) as Hwf0;
  rewrite swaps_aenv_app_dist in Hwf0;
  rewrite (HfixT t0) in Hwf0 by (clear - Hcov; simpl in *; fsetdec);
  pose proof (a_wf_pskl_swaps ps1 Hwf0) as Hwf1;
  rewrite swaps_aenv_app_dist, HX1, HY1 in Hwf1;
  rewrite (swaps_aenv_fresh_id ps1 t0) in Hwf1
    by (intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav1 a b Hin) as [Hza Hzb];
        split; clear - Hza Hzb Hcov; simpl in *; fsetdec);
  bool_true;

  let Sd1 := fresh "Sd1" in let HSd1 := fresh "HSd1" in
  let Ds1 := fresh "Ds1" in
  destruct (e_sub_swaps ((ad, supply_fresh s0) :: nil) Dsub (S0' := Smx))
    as [Sd1 [HSd1 Ds1]]; [ exact HSmx | ];
  let Sd2 := fresh "Sd2" in let HSd2 := fresh "HSd2" in
  let Ds2 := fresh "Ds2" in
  destruct (e_sub_swaps ps1 Ds1 (S0' := ex_supply rx)) as [Sd2 [HSd2 Ds2]];
  [ symmetry; exact HS1 | ];
  rewrite ! swaps_aenv_app_dist, HX1 in Ds2;
  rewrite (HfixT t0) in Ds2 by (clear - Hcov; simpl in *; fsetdec);
  rewrite (swaps_aenv_fresh_id ps1 t0) in Ds2
    by (intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav1 a b Hin) as [Hza Hzb];
        split; clear - Hza Hzb Hcov; simpl in *; fsetdec);
  rewrite ! swaps_pskl_open, HY1 in Ds2;
  rewrite (HfixQ q) in Ds2 by (clear - Hcov; simpl in *; fsetdec);
  rewrite (swaps_pskl_fresh_id ps1 q) in Ds2
    by (intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav1 a b Hin) as [Hza Hzb];
        split; clear - Hza Hzb Hcov; simpl in *; fsetdec);
  rewrite (HfixQ p0) in Ds2 by (clear - Hcov; simpl in *; fsetdec);
  rewrite (swaps_pskl_fresh_id ps1 p0) in Ds2
    by (intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav1 a b Hin) as [Hza Hzb];
        split; clear - Hza Hzb Hcov; simpl in *; fsetdec);

  let Hblk := fresh "Hblk" in let Hgrx := fresh "Hgrx" in
  let Houtx := fresh "Houtx" in let Hd0 := fresh "Hd0" in
  pose proof (e_extract_block Hrx) as [Hblk [Hblkf [Hblku Hblkft]]];
  pose proof (e_extract_supply_grows Hrx) as Hgrx;
  pose proof (e_extract_out_ftvar Hrx) as Houtx;
  pose proof (dom_subset_ftvar_in_aenv t0) as Hd0;
  let Hu1 := fresh "Hu1" in let Hcov1 := fresh "Hcov1" in
  assert (Hu1 : uniq (ex_block rx ++ t0));
  [ apply uniq_app_4;
    [ exact Hblku | exact Hu
    | unfold disjoint; clear - Hblkf Hd0 Hcov Ha1; simpl in *; fsetdec ]
  | ];
  assert (Hcov1 : ftvar_in_aenv (ex_block rx ++ t0) ∪ ftvar_in_pskl p0
            ∪ ftvar_in_pskl (open_pskl_wrt_pskl q (ex_out rx))
            [<=] ex_supply rx);
  [ rewrite ftvar_in_aenv_app;
    (let Hoq := fresh in
     pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper q (ex_out rx)) as Hoq;
     clear - Hblk Hblkft Hgrx Houtx Hoq Hop Hcov;
     simpl in *; fsetdec)
  | ];
  let r := fresh "r" in let Hr := fresh "Hr" in let ps := fresh "ps" in
  let Hav := fresh "Hav" in let HS := fresh "HS" in
  let HT := fresh "HT" in let HQ := fresh "HQ" in
  kill_scall (pmot Hg _ _ _ Hrx Hwf1) Hu1 Hcov1 Ds2 r Hr ps Hav HS HT HQ;
  exists r, (((ad, supply_fresh s0) :: nil) ++ ps1 ++ ps);
  split; [ reflexivity | ];
  repeat apply conj;
  [ intros a0 b0 Hin; rewrite ! in_app_iff in Hin;
    destruct Hin as [Hin | [Hin | Hin]];
    [ exact (Hav0 a0 b0 Hin)
    | let Hza := fresh in let Hzb := fresh in
      destruct (Hav1 a0 b0 Hin) as [Hza Hzb]; split; clear - Hza Hzb; fsetdec
    | let Hza := fresh in let Hzb := fresh in
      destruct (Hav a0 b0 Hin) as [Hza Hzb];
      split; clear - Hza Hzb Hgrx Ha1; fsetdec ]
  | rewrite ! swaps_atoms_app; rewrite <- HS;
    apply swaps_atoms_cong; rewrite HSd2;
    apply swaps_atoms_cong; symmetry; exact HSd1
  | rewrite ! swaps_aenv_app; exact HT
  | rewrite ! swaps_pskl_app; exact HQ ].

Local Ltac do_ty_tc_p Hd Hu Hcov hfl p :=
  destruct p as [ | n | γ | Pa Pb | Q | | Pb ]; cbv beta iota;
  [ do_check Hd Hu Hcov
  | kill_var_b
  | do_check Hd Hu Hcov
  | do_check Hd Hu Hcov
  | lazymatch goal with
    | |- context [ e_extract_impl (add (supply_fresh ?ss) ?ss) ?tt _ _ _
                     (open_pskl_wrt_pskl ?qq (pskl_var_f _)) ?pp _ _ _ ] =>
        do_forall_l Hd Hu Hcov
          (hfl qq eq_refl ltac:(discriminate)) ss tt pp qq
    end
  | do_check Hd Hu Hcov
  | do_check Hd Hu Hcov ].

Local Ltac do_sk_tc_p0 Hd p0 :=
  destruct p0 as [ | n0 | γ0 | P0a P0b | B | | P0b ]; cbv beta iota;
  [ | | | |
  | destruct (e_sub_inv_univ_ghost_r Hd ltac:(discriminate)
               ltac:(intros ? Habs; discriminate Habs)
               ltac:(intros ? Habs; discriminate Habs))
      as [Hgd [-> [-> ->]]];
    bool_true; answer_id
  | ];
  try solve [ exfalso; eapply e_sub_inv_sk_tc_none;
              [ exact Hd | discriminate
              | intros ? Habs; discriminate Habs
              | intros ? Habs; discriminate Habs | discriminate ] ].

Lemma e_sub_call_impl_complete : forall S0 NM M P0 Θ0 c
    (H0 : e_sub_call_order S0 NM M P0 Θ0 c),
    sub_call_complete S0 NM M P0 Θ0 c.
Proof.
  intros S0 NM M P0 Θ0 c H0.
  induction H0 as
    [S0 NM M P0 Θ0 P hck hfr Hfr hfm Hfm har hart Har hfl hflt Hfl hug Hug
    |S0 NM M P0 Θ0 Ξ α hsl Hsl hag Hag hdep Hdep hskip Hskip hrg Hrg htv Htv hts Hts];
    unfold sub_call_complete;
    intros HP HP0 HD Hord Hu Hcov Sd Θd Qd Hd;
    cbn [sub_call_lc sub_call_uniq sub_call_cover sub_call_run] in *.
  -
    rewrite e_sub_call_impl_equation_1.
    destruct M as [ | | M' ]; cbv beta iota.
    +
      destruct (e_sub_inv_ti Hd) as [-> [-> [-> ->]]]. cbv beta iota. answer_id.
    +
      destruct NM; cbv beta iota.
      *
        destruct P0 as [ | n0 | γ0 | P0a P0b | B | | P0b ]; cbv beta iota.
        -- do_ty_tc_p Hd Hu Hcov Hfl P.
        -- inversion HP0.
        -- do_ty_tc_p Hd Hu Hcov Hfl P.
        -- do_ty_tc_p Hd Hu Hcov Hfl P.
        --
          destruct (e_sub_inv_forall_r Hd)
            as [-> [Hgf [ad [Xd [Hsuf [HuX [Had Dr]]]]]]].
          bool_true.
          pose proof (supply_fresh_notin S0) as Ha1.
          pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.

          destruct (swaps_onto_fresh Had) as (Hav0 & Hsad & HSadd).
          assert (HfixΘ : forall (X : aenv), ftvar_in_aenv X [<=] S0 ->
                    swaps_aenv ((ad, supply_fresh S0) :: nil) X = X)
            by (intros X HX; apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav0);
                exact HX).
          assert (HfixP : forall X, ftvar_in_pskl X [<=] S0 ->
                    swaps_pskl ((ad, supply_fresh S0) :: nil) X = X)
            by (intros X HX; apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav0);
                exact HX).
          destruct (e_sub_swaps ((ad, supply_fresh S0) :: nil) Dr HSadd)
            as [Sd1 [HSd1 Dr1]].
          rewrite swaps_aenv_cons_tvar, Hsad in Dr1.
          rewrite (HfixΘ Θ0) in Dr1
            by (clear - Hcov; simpl in *; fsetdec).
          rewrite swaps_pskl_open, swaps_pskl_var_f, Hsad in Dr1.
          rewrite (HfixP B) in Dr1 by (clear - Hcov; simpl in *; fsetdec).
          rewrite (HfixP P) in Dr1 by (clear - Hcov; simpl in *; fsetdec).
          rewrite swaps_aenv_app_dist, swaps_aenv_cons_tvar, Hsad in Dr1.

          assert (Ha1d : supply_fresh S0 `notin` dom Θ0)
            by (clear - Ha1 Hd0 Hcov; simpl in *; fsetdec).
          assert (Hu1 : uniq ((supply_fresh S0 ~ abind_tvar) ++ Θ0))
            by (clear - Hu Ha1d; solve_uniq).
          assert (Hcov1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
                          ∪ ftvar_in_pskl (open_pskl_wrt_pskl B
                               (pskl_var_f (supply_fresh S0)))
                          ∪ ftvar_in_pskl P [<=] add (supply_fresh S0) S0).
          { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                          (pskl_var_f (supply_fresh S0))) as Hop.
            simpl in Hop. clear - Hop Hcov. simpl in *. fsetdec. }
          kill_scall (Hfr B eq_refl eq_refl) Hu1 Hcov1 Dr1 r Hr ps Hav HS HT HQ.

          cbn [sub_call_spec sub_spec] in Hr.
          pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ Hr Hu1 Hcov1)
            as [Hra [Huc [Hcvc Hqc]]].

          assert (Hout : sb_out r = open_pskl_wrt_pskl B
                           (pskl_var_f (supply_fresh S0))).
          { rewrite <- HQ. apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav).
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                          (pskl_var_f (supply_fresh S0))) as Hop.
            clear - Hop Hcov; simpl in *; fsetdec. }
          bool_true.

          assert (Hctx : sb_ctx r
                    = swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Xd)
                      ++ (supply_fresh S0 ~ abind_tvar)
                      ++ swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Θd)).
          { rewrite <- HT. rewrite swaps_aenv_app_dist, swaps_aenv_cons_tvar.
            repeat f_equal. apply (swaps_atom_dodge_in Hav). fsetdec. }
          assert (Hsufr : a_suffix
                    (swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Xd)))
            by (apply a_suffix_swaps; apply a_suffix_swaps; exact Hsuf).
          assert (HΘfix : swaps_aenv ps
                    (swaps_aenv ((ad, supply_fresh S0) :: nil) Θ0) = Θ0).
          { rewrite (HfixΘ Θ0) by (clear - Hcov; simpl in *; fsetdec).
            apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav).
            clear - Hcov; simpl in *; fsetdec. }
          assert (HuXr : uniq
                    (swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Xd)
                     ++ Θ0)).
          { rewrite <- HΘfix. rewrite <- ! swaps_aenv_app_dist.
            apply swaps_aenv_uniq. apply swaps_aenv_uniq. exact HuX. }
          destruct (split_at_tvar_complete Hctx Huc)
            as [[pp Hpp] [Hsp Hpr]].
          simpl in Hpr; subst pp.
          rewrite Hsp. cbv beta iota. cbn [fst snd].
          bool_true.
          exists (mk_sub_result (sb_supply r)
                    (swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Θd))
                    (pskl_all_syn B)), (((ad, supply_fresh S0) :: nil) ++ ps).
          split; [ reflexivity | ].
          repeat apply conj.
          ++ apply (swaps_dodge_app Hav0 Hav); fsetdec.
          ++ exact (swaps_atoms_app_transport HSd1 HS).
          ++ cbn [sb_ctx]. rewrite swaps_aenv_app. reflexivity.
          ++ cbn [sb_out]. rewrite swaps_pskl_app, ! swaps_pskl_all_syn.
             rewrite (HfixP B) by (clear - Hcov; simpl in *; fsetdec).
             f_equal. apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav).
             clear - Hcov; simpl in *; fsetdec.
        -- do_ty_tc_p Hd Hu Hcov Hfl P.
        -- do_ty_tc_p Hd Hu Hcov Hfl P.
      *
        destruct P as [ | n | γ | Pa Pb | Q | | Pb ]; cbv beta iota.
        -- do_sk_tc_p0 Hd P0.
        -- kill_var_b.
        -- do_sk_tc_p0 Hd P0.
        -- do_sk_tc_p0 Hd P0.
        --
          do_forall_l Hd Hu Hcov
            (Hfl Q eq_refl ltac:(discriminate)) S0 Θ0 P0 Q.
        --  do_ghost Hd.
        --
          do_univ_ghost_l Hd Hu Hcov (Hug Pb eq_refl ltac:(discriminate)).
    +
      destruct P as [ | n | γ | Pa Pb | Q | | Pb ]; cbv beta iota.
      --  destruct (e_sub_inv_fn_unit_none Hd).
      -- kill_var_b.
      --
        pose proof (e_sub_inv_flex_mono Hd) as Df.
        assert (Hcov0 : ftvar_in_aenv (nil ++ Θ0) ∪ ftvar_in_pskl P0
                        ∪ singleton γ [<=] S0)
          by (clear - Hcov; simpl in *; fsetdec).
        assert (Hu0 : uniq (nil ++ Θ0)) by (clear - Hu; simpl; assumption).
        kill_scall (Hfm γ M' eq_refl eq_refl) Hu0 Hcov0 Df
          r Hr ps Hav HS HT HQ.
        exists r, ps. exact (conj eq_refl (conj Hav (conj HS (conj HT HQ)))).
      --
        destruct P0 as [ | n0 | γ0 | P0a P0b | B | | P0b ]; cbv beta iota;
          [ | | | | | | ];
          try solve [ destruct (e_sub_inv_arrow_none Hd
                        ltac:(intros ? ? Habs; discriminate Habs)) ].
        destruct (e_sub_inv_arrow Hd) as [Sm [Θm [Qd1 [Qd2 [-> [D1 D2]]]]]].
        assert (Hcov1 : consis_call_cover Θ0
                  (consis_call_consis empty empty P0a Pa) [<=] S0)
          by (cbn [consis_call_cover]; clear - Hcov; simpl in *; fsetdec).
        kill_consis Hu Hcov1 D1 r1 Hr1 ps1 Hav1 HS1 HT1 HQ1.
        cbn [consis_call_spec consis_spec] in Hr1.

        pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                      _ _ _ _ _ _ _ _ _ Hr1 Hu
                      ltac:(clear - Hcov; simpl in *; fsetdec))
          as [Da1 [Hu1' Hcov1']].
        pose proof (e_consis_supply_grows Hr1) as Hgr1.
        pose proof ((proj2 (proj2 e_assign_unify_consis_out_ftvar))
                      _ _ _ _ _ _ _ _ _ Hr1 Hu
                      ltac:(clear - Hcov; simpl in *; fsetdec)) as Hout1.

        destruct (e_sub_swaps ps1 D2 (S0' := cs_supply r1)) as [S2t [HS2t D2t]];
          [ symmetry; exact HS1 | ].
        rewrite HT1 in D2t.
        rewrite (swaps_pskl_fresh_id ps1 P0b) in D2t
          by (intros a0 b0 Hin; destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0];
              split; clear - Ha0 Hb0 Hcov; simpl in *; fsetdec).
        rewrite (swaps_pskl_fresh_id ps1 Pb) in D2t
          by (intros a0 b0 Hin; destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0];
              split; clear - Ha0 Hb0 Hcov; simpl in *; fsetdec).
        assert (Hcov2 : ftvar_in_aenv (cs_ctx r1) ∪ ftvar_in_pskl P0b
                        ∪ ftvar_in_pskl Pb [<=] cs_supply r1)
          by (clear - Hcov Hcov1' Hgr1; simpl in *; fsetdec).
        kill_scall (Har M' P0a P0b Pa Pb eq_refl eq_refl eq_refl _ _ _ Hr1)
          Hu1' Hcov2 D2t r2 Hr2 ps2 Hav2 HS2 HT2 HQ2.
        exists (mk_sub_result (sb_supply r2) (sb_ctx r2)
                  (pskl_arrow (cs_out r1) (sb_out r2))), (ps1 ++ ps2).
        split; [ reflexivity | ].
        repeat apply conj.
        ++ intros a0 b0 Hin. apply in_app_or in Hin.
           destruct Hin as [Hin | Hin]; [ exact (Hav1 a0 b0 Hin) | ].
           destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
           split; clear - Ha0 Hb0 Hgr1; fsetdec.
        ++ exact (swaps_atoms_app_transport HS2t HS2).
        ++ cbn [sb_ctx]. rewrite swaps_aenv_app. exact HT2.
        ++ cbn [sb_out]. rewrite swaps_pskl_app, ! swaps_pskl_arrow.
           rewrite HQ1 in *. f_equal; [ | exact HQ2 ].
           apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav2).
           clear - Hout1; fsetdec.

      --
        do_forall_l Hd Hu Hcov
          (Hfl Q eq_refl ltac:(discriminate)) S0 Θ0 P0 Q.
      --
        destruct NM; cbv beta iota;
          [ destruct (e_sub_inv_fn_ty_ghost_none Hd) | do_ghost Hd ].
      --
        destruct NM; cbv beta iota;
          [ destruct (e_sub_inv_fn_ty_univ_ghost_none Hd)
          | do_univ_ghost_l Hd Hu Hcov (Hug Pb eq_refl ltac:(discriminate)) ].
  -
    destruct Θ0 as [ | [γ b] Θ0' ]; [ destruct (e_sub_flex_inv_nil Hd) | ].
    destruct b as [ | A | Qp | | τ ].
    +
      rewrite e_sub_call_impl_equation_3. cbv beta iota.
      destruct (e_sub_flex_inv_tvar Hd) as [Hne [Hnf [Θd' [-> Ds]]]].
      split_eqdec Heq Hne2; [ congruence | ]. cbv beta iota.
      destruct (sumbool_of_bool (mem γ (ftvar_in_pskl P0))) as [Hm | Hm];
        [ exfalso; apply mem_true_in in Hm; contradiction | ].
      cbv beta iota.
      assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                      ∪ singleton α [<=] S0)
        by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
            simpl in *; fsetdec).
      kill_scall (Hrg γ Θ0' eq_refl) Hu0 Hcov0 Ds r Hr ps Hav HS HT HQ.
      exists (mk_sub_result (sb_supply r) ((γ ~ abind_tvar) ++ sb_ctx r)
                (sb_out r)), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
              | | cbn [sb_out proj1_sig]; exact HQ ].
      cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    +
      rewrite e_sub_call_impl_equation_4. cbv beta iota.
      destruct (e_sub_flex_inv_var_typ Hd) as [Θd' [-> Ds]].
      assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                      ∪ singleton α [<=] S0)
        by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
            simpl in *; fsetdec).
      kill_scall (Htv γ A Θ0' eq_refl) Hu0 Hcov0 Ds r Hr ps Hav HS HT HQ.
      exists (mk_sub_result (sb_supply r) ((γ ~ abind_var_typ A) ++ sb_ctx r)
                (sb_out r)), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
              | | cbn [sb_out proj1_sig]; exact HQ ].
      cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    +
      rewrite e_sub_call_impl_equation_5. cbv beta iota.
      destruct (e_sub_flex_inv_var_skl Hd) as [Θd' [-> Ds]].
      assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                      ∪ singleton α [<=] S0)
        by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
            simpl in *; fsetdec).
      kill_scall (Hts γ Qp Θ0' eq_refl) Hu0 Hcov0 Ds r Hr ps Hav HS HT HQ.
      exists (mk_sub_result (sb_supply r) ((γ ~ abind_var_skl Qp) ++ sb_ctx r)
                (sb_out r)), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
              | | cbn [sb_out proj1_sig]; exact HQ ].
      cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
    +
      rewrite e_sub_call_impl_equation_6. cbv beta iota.
      split_eqdec Heq Hne.
      *
        subst γ. cbv beta iota.
        destruct (e_sub_flex_inv_self Hd) as [ad [bd [Had [Hbd Ds]]]].
        assert (Hcov1 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                        ∪ singleton α [<=] S0)
          by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
              simpl in *; fsetdec).
        destruct (e_sub_flex_solve_realign Had Hbd Hcov1 Ds)
          as [ps0 [Sd0 [Hav0 [HS0 Ds0]]]].
        pose proof (supply_fresh_notin S0) as Ha1.
        pose proof (supply_fresh_notin (add (supply_fresh S0) S0)) as Hb1.
        pose proof (dom_subset_ftvar_in_aenv Ξ) as HdΞ.
        pose proof (dom_subset_ftvar_in_aenv Θ0') as HdΘ.
        assert (HΞS : ftvar_in_aenv Ξ [<=] S0)
          by (clear - Hcov1; rewrite ftvar_in_aenv_app in Hcov1; fsetdec).
        assert (HΘS : ftvar_in_aenv Θ0' [<=] S0)
          by (clear - Hcov1; rewrite ftvar_in_aenv_app in Hcov1; fsetdec).
        assert (HαS : α `in` S0) by (clear - Hcov1; fsetdec).
        assert (Hu1 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
        assert (HαΞ : α `notin` dom Ξ)
          by (clear - Hu; destruct_uniq; unfold disjoint in *;
              simpl in *; fsetdec).
        assert (HαΘ : α `notin` dom Θ0')
          by (clear - Hu; destruct_uniq; simpl in *; fsetdec).

        assert (Ha1Ξ : supply_fresh S0 `notin` dom Ξ)
          by (clear - Ha1 HdΞ HΞS; fsetdec).
        assert (Ha1Θ : supply_fresh S0 `notin` dom Θ0')
          by (clear - Ha1 HdΘ HΘS; fsetdec).
        assert (Hb1Ξ : supply_fresh (add (supply_fresh S0) S0)
                       `notin` dom Ξ)
          by (clear - Hb1 HdΞ HΞS; fsetdec).
        assert (Hb1Θ : supply_fresh (add (supply_fresh S0) S0)
                       `notin` dom Θ0')
          by (clear - Hb1 HdΘ HΘS; fsetdec).
        assert (Hu2 : uniq (Ξ ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0'))
          by (apply uniq_insert_mid; assumption).
        assert (Hu3 : uniq (Ξ ++ (supply_fresh (add (supply_fresh S0) S0)
                                    ~ abind_flex_mono)
                               ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')).
        { apply uniq_insert_mid; [ exact Hu2 | exact Hb1Ξ | ].
          clear - Hb1 Hb1Θ. simpl. fsetdec. }
        assert (Hu0 : uniq (Ξ ++ (α ~ abind_flex_mono_def
                         (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                            (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
                       ++ (supply_fresh (add (supply_fresh S0) S0)
                             ~ abind_flex_mono)
                       ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')).
        { apply uniq_insert_mid; [ exact Hu3 | exact HαΞ | ].
          clear - HαΘ HαS Ha1 Hb1. simpl. fsetdec. }
        assert (Hcov0 : ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono_def
                         (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                            (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
                       ++ (supply_fresh (add (supply_fresh S0) S0)
                             ~ abind_flex_mono)
                       ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
                      ∪ ftvar_in_pskl P0
                      ∪ ftvar_in_pskl (pskl_arrow
                           (pskl_var_f (supply_fresh S0))
                           (pskl_var_f (supply_fresh (add (supply_fresh S0) S0))))
                      [<=] add (supply_fresh (add (supply_fresh S0) S0))
                             (add (supply_fresh S0) S0))
          by (clear - Hcov1; repeat rewrite ftvar_in_aenv_app in *;
              simpl in *; fsetdec).
        kill_scall (Hsl Θ0' eq_refl) Hu0 Hcov0 Ds0 r Hr ps Hav HS HT HQ.
        exists r, (ps0 ++ ps).
        split; [ reflexivity | ].
        repeat apply conj.
        -- apply (swaps_dodge_app Hav0 Hav); fsetdec.
        -- rewrite swaps_atoms_app. rewrite <- HS.
          apply swaps_atoms_cong. symmetry. exact HS0.
        -- rewrite swaps_aenv_app. exact HT.
        -- rewrite swaps_pskl_app. exact HQ.
      * cbv beta iota.
        destruct (e_sub_flex_inv_other_flex (not_eq_sym Hne) Hd)
          as [[Hin Dd] | [Hni [Θd' [-> Ds]]]].
        --
          destruct (sumbool_of_bool (mem γ (ftvar_in_pskl P0))) as [Hm | Hm];
            [ | exfalso; apply mem_false_notin in Hm; contradiction ].
          cbv beta iota.
          assert (Hu0 : uniq ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0'))
            by (clear - Hu; solve_uniq).
          assert (Hcov0 : ftvar_in_aenv ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0')
                          ∪ ftvar_in_pskl P0 ∪ singleton α [<=] S0)
            by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
                simpl in *; fsetdec).
          kill_scall (Hdep γ Θ0' eq_refl) Hu0 Hcov0 Dd
            r Hr ps Hav HS HT HQ.
          exists r, ps. exact (conj eq_refl (conj Hav (conj HS (conj HT HQ)))).
        --
          destruct (sumbool_of_bool (mem γ (ftvar_in_pskl P0))) as [Hm | Hm];
            [ exfalso; apply mem_true_in in Hm; contradiction | ].
          cbv beta iota.
          assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
          assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                          ∪ singleton α [<=] S0)
            by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
                simpl in *; fsetdec).
          kill_scall (Hskip γ Θ0' eq_refl) Hu0 Hcov0 Ds
            r Hr ps Hav HS HT HQ.
          exists (mk_sub_result (sb_supply r)
                    ((γ ~ abind_flex_mono) ++ sb_ctx r) (sb_out r)), ps.
          split; [ reflexivity | ].
          repeat apply conj; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
                  | | cbn [sb_out proj1_sig]; exact HQ ].
          cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
          head_fresh Hav Hcov.
    +
      rewrite e_sub_call_impl_equation_7. cbv beta iota.
      destruct (e_sub_flex_inv_def Hd) as [Θd' [-> Dc]].
      assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0')
                      ∪ ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) γ P0)
                      ∪ ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) γ
                            (pskl_var_f α)) [<=] S0)
        by (apply subst_pskl_preserves_cover; rewrite ftvar_ptyp_to_pskl;
            clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
            simpl in *; fsetdec).
      kill_scall (Hag γ τ Θ0' eq_refl) Hu0 Hcov0 Dc r Hr ps Hav HS HT HQ.
      exists (mk_sub_result (sb_supply r)
                ((γ ~ abind_flex_mono_def τ) ++ sb_ctx r) (sb_out r)), ps.
      split; [ reflexivity | ].
      repeat apply conj; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
              | | cbn [sb_out proj1_sig]; exact HQ ].
      cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
      head_fresh Hav Hcov.
Qed.

Corollary e_sub_impl_complete : forall S0 NM M P0 Θ0 P
    (HP : lc_pskl P) (HP0 : lc_pskl P0) (HD : aenv_defs_mono Θ0)
    (H : e_sub_order S0 NM M P0 Θ0 P) Sd Θd Qd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Qd ⊣ Θd }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P [<=] S0 ->
  exists r ps,
    e_sub_impl S0 NM M P0 Θ0 P HP HP0 HD H = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] sb_supply (proj1_sig r)
    /\ swaps_aenv ps Θd = sb_ctx (proj1_sig r)
    /\ swaps_pskl ps Qd = sb_out (proj1_sig r).
Proof.
  intros * Hd Hu Hcov.
  set (Ho := e_sub_order_to_call _ _ _ _ _ _ H).
  destruct (e_sub_call_impl_complete Ho HP HP0 HD Ho Hu Hcov Sd Θd Qd Hd)
    as [r0 [ps [Heq [Hav [HS [HT HQ]]]]]].
  unfold e_sub_impl. fold Ho.
  destruct (e_sub_call_impl (sub_call_sub P) S0 NM M P0 Θ0 HP HP0 HD Ho)
    as [ [rr Hrr] | ] eqn:Hcl;
    try rewrite Hcl in Heq; cbn [sub_call_answer proj1_sig] in Heq;
    [ inversion Heq; subst | discriminate ].
  eexists; exists ps.
  exact (conj eq_refl (conj Hav (conj HS (conj HT HQ)))).
Qed.
