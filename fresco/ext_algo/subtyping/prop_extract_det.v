Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.

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
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.prop_guess.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.prop_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.prop_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.prop_extract.
Require Import src.fresco.ext_algo.subtyping.prop_solve_det.
Require Import src.fresco.ext_algo.consistency.prop_consis_complete.

Set Implicit Arguments.

Local Open Scope fresco_e_scope.

Lemma e_looksub_swaps : forall ps S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊢ (swaps_pskl ps P)
       ≼[ (swaps_atom ps α) , m ] (swaps_pskl ps P')
       ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_cstrs ps C) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact ((proj1 e_looksub_lookeq_supply_respect)
             _ _ _ _ _ _ _ _ _ Hd _ Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct ((proj1 (e_looksub_lookeq_swap a b))
                _ _ _ _ _ _ _ _ _ Hd _ Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_lookeq_swaps : forall ps S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊢ (swaps_pskl ps P)
       ∼[ (swaps_atom ps α) ] (swaps_pskl ps P')
       ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_cstrs ps C) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact ((proj2 e_looksub_lookeq_supply_respect)
             _ _ _ _ _ _ _ _ Hd _ Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct ((proj2 (e_looksub_lookeq_swap a b))
                _ _ _ _ _ _ _ _ Hd _ Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_solve_sub_swaps : forall ps S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊢ₛ (swaps_pskl ps P) ≼[ m ]
       (swaps_pskl ps Q) ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_pskl ps P') }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_solve_sub_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_solve_sub_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_solve_eq_swaps : forall ps S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊢ₑ (swaps_pskl ps P) ∼
       (swaps_pskl ps Q) ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_pskl ps P') }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_solve_eq_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_solve_eq_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_solve_cstr_swaps : forall ps S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ) ⊩ (swaps_cstrs ps C) ⨾ (swaps_pskl ps P)
       ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_pskl ps Q) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_solve_cstr_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_solve_cstr_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_guess_swaps : forall ps S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    e_guess S0' NM (swaps_pskl ps Q) S1' (swaps_aenv ps Ξ)
      (swaps_pskl ps Q').
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_guess_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_guess_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma e_extract_swaps : forall ps S0 Θ0 NM α m P P' S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊢ (swaps_pskl ps P)
       ⊳[ NM , (swaps_atom ps α) , m ] (swaps_pskl ps P')
       ⤳ (swaps_aenv ps Ξ) ↪ (swaps_pskl ps Q) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - exact (e_extract_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_extract_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

Lemma swaps_cstrs_app : forall ps1 ps2 C,
  swaps_cstrs (ps1 ++ ps2) C = swaps_cstrs ps2 (swaps_cstrs ps1 C).
Proof.
  induction ps1 as [ | [a b] ps1 IH ]; intros; simpl; auto.
Qed.

Lemma swaps_cstrs_app_dist : forall ps C1 C2,
  swaps_cstrs ps (C1 ++ C2) = swaps_cstrs ps C1 ++ swaps_cstrs ps C2.
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; auto.
  rewrite swap_cstrs_app. apply IH.
Qed.

Local Ltac le_kill :=
  try solve
    [ assumption
    | auto
    | exfalso; congruence
    | exfalso;
      match goal with
      | Hn : ?a `notin` ftvar_in_pskl (pskl_var_f ?a) |- _ =>
          simpl in Hn; clear - Hn; fsetdec
      end
    | exfalso;
      match goal with
      | Hn : ?a `notin` ftvar_in_pskl _, Hi : ?a `in` ftvar_in_pskl _ |- _ =>
          simpl in Hn, Hi; clear - Hn Hi; fsetdec
      end
    | exfalso;
      match goal with
      | Hoff : flex_r_off _ (pskl_var_f ?b), Hf : a_flex_tvar _ ?b |- _ =>
          exact (Hoff b eq_refl Hf)
      end
    | exfalso;
      match goal with
      | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      end ].

Lemma e_lookeq_inv_var : forall S0 Θ α P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_var_f α) ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  S1 = S0 /\ Ξ = nil /\ C = a_cstr_eq P' :: nil.
Proof.
  intros * H; inversion H; subst; le_kill.
Qed.

Lemma e_lookeq_inv_ghost : forall S0 Θ α P S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] pskl_ghost ⤳ Ξ ⨾ C }}e ->
  P <> pskl_var_f α ->
  α `in` ftvar_in_pskl P ->
  S1 = S0 /\ Ξ = nil /\ C = nil.
Proof.
  intros * H Hne Hα; inversion H; subst; le_kill.
Qed.

Lemma e_lookeq_inv_flex_r : forall S0 Θ α P β S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] (pskl_var_f β) ⤳ Ξ ⨾ C }}e ->
  P <> pskl_var_f α ->
  a_flex_tvar Θ β ->
  α `in` ftvar_in_pskl P ->
  exists α1, α1 `notin` S0 /\ S1 = add α1 S0
    /\ Ξ = (α1 ~ abind_flex_mono) ++ nil
    /\ C = a_cstr_eq (pskl_var_f α1) :: nil.
Proof.
  intros * H Hne Hflx Hα; inversion H; subst; le_kill.
  match goal with
  | Hfr : ?a1 `notin` S0 |- _ => exists a1
  end.
  repeat split; solve [ assumption | reflexivity ].
Qed.

Lemma e_lookeq_inv_ug2 : forall S0 Θ α Q P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost Q) ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  guarded_pskl P' ->
  flex_r_off Θ P' ->
  α `in` ftvar_in_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ Q ∼[ α ] P' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hg Hoff Hα; inversion H; subst; le_kill.
Qed.

Lemma e_lookeq_inv_ug : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost Q) ∼[ α ] (pskl_univ_ghost Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ Q ∼[ α ] Q' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
Qed.

Lemma e_lookeq_inv_ug1 : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost Q) ∼[ α ] (pskl_all_syn Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl Q ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ (pskl_univ_ghost Q)
       ∼[ α ] (open_pskl_wrt_pskl Q' (pskl_var_f β)) ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

Lemma e_lookeq_inv_forall_inh : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn Q) ∼[ α ] (pskl_all_syn Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl (pskl_all_syn Q) ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl Q (pskl_var_f β))
       ∼[ α ] (open_pskl_wrt_pskl Q' (pskl_var_f β)) ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

Lemma e_lookeq_inv_forall_syn : forall S0 Θ α Q Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn Q) ∼[ α ] (pskl_univ_ghost Q') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl (pskl_all_syn Q) ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl Q (pskl_var_f β))
       ∼[ α ] (pskl_univ_ghost Q') ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hα; inversion H; subst; le_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

Lemma e_lookeq_inv_arrow : forall S0 Θ α P1 P2 P1' P2' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_arrow P1 P2) ∼[ α ] (pskl_arrow P1' P2')
     ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl (pskl_arrow P1 P2) ->
  exists Sm Ξ1 Ξ2 C1 C2,
    Ξ = Ξ1 ++ Ξ2 /\ C = C1 ++ C2 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e /\
    {{ Sm ↝ S1 ⊨ Θ ⊢ P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 }}e.
Proof.
  intros * H Hα; inversion H; subst;
    try solve [ exfalso;
                match goal with
                | Hn : ?a `notin` ftvar_in_pskl _,
                  Hi : ?a `in` ftvar_in_pskl _ |- _ =>
                    simpl in Hn, Hi; clear - Hn Hi; fsetdec
                end ].
  match goal with
  | Ha : e_lookeq S0 _ _ P1 P1' ?sm ?x1 ?c1,
    Hb : e_lookeq ?sm _ _ P2 P2' S1 ?x2 ?c2 |- _ =>
      exists sm, x1, x2, c1, c2
  end.
  repeat split; assumption.
Qed.

Lemma e_lookeq_inv_ug_r : forall S0 Θ α P Q' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] (pskl_univ_ghost Q') ⤳ Ξ ⨾ C }}e ->
  P <> pskl_var_f α ->
  guarded_pskl P ->
  α `in` ftvar_in_pskl P ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] Q' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hne Hg Hα; inversion H; subst; le_kill.
Qed.

Lemma e_lookeq_rel : forall S0 Θ α P P' S1 Ξ C S1' Ξ' C',
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  {{ S0 ↝ S1' ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ' ⨾ C' }}e ->
  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_cstrs ps C = C'.
Proof.
  intros S0 Θ α P P' S1 Ξ C S1' Ξ' C' D1 D2.
  revert S1 Ξ C D1. generalize D2.
  induction D2 as
    [S0 Θ α P'
    |S0 Θ α P P' Habs
    |S0 Θ α P Hnev
    |S0 Θ α P β γ2 Hγ2 Hflx Hnev Hocc
    |S0 Sm' S1' Θ α Pa Pb Pa' Pb' X1' X2' Cc1' Cc2' D2a IH1 D2b IH2
    |S0 S1' Θ α Qs Qt Ξ' C' β2 Hβ2 Hocc Dp' IH
    |S0 S1' Θ α Qs Qt Ξ' C' β2 Hβ2 Hocc Dp' IH
    |S0 S1' Θ α Qs Qt Ξ' C' Dp' IH
    |S0 S1' Θ α Qs Qt Ξ' C' β2 Hβ2 Hocc Dp' IH
    |S0 S1' Θ α Qs P' Ξ' C' Hgd Hoff Dp' IH
    |S0 S1' Θ α P Qt Ξ' C' Hnev Hgd Dp' IH];
    intros D2 S1 Ξ C D1 Hcov;
    match type of D1 with
    | e_lookeq _ _ _ ?P _ _ _ _ =>
        destruct (sumbool_of_bool (mem α (ftvar_in_pskl P))) as [Hmem | Hmem]
    end.
  all: try (apply mem_false_notin in Hmem;
    destruct (e_lookeq_absent_pins D1 Hmem) as [HX [HC HS]];
    destruct (e_lookeq_absent_pins D2 Hmem) as [HX' [HC' HS']];
    exists nil; repeat apply conj; simpl;
    [intros ? ? [] | clear - HS HS'; fsetdec | congruence | congruence]).
  all: apply mem_true_in in Hmem; rename Hmem into HαP.
  -
    destruct (e_lookeq_inv_var D1) as [-> [-> ->]].
    exists nil. repeat apply conj; simpl; try reflexivity. intros ? ? [].

  -
    exfalso. clear - Habs HαP; fsetdec.

  -
    destruct (e_lookeq_inv_ghost D1 Hnev HαP) as [-> [-> ->]].
    exists nil. repeat apply conj; simpl; try reflexivity. intros ? ? [].

  -
    destruct (e_lookeq_inv_flex_r D1 Hnev Hflx HαP)
      as (γ1 & Hα1 & -> & -> & ->).
    exists ((γ1, γ2) :: nil). repeat apply conj.
    + intros ? ? [Heqp | []]. inversion Heqp; subst. split; assumption.
    + cbn [swaps_atoms]. rewrite swap_atoms_add.
      rewrite (swap_atoms_notin γ1 γ2 S0 Hα1 Hγ2).
      rewrite swap_atom_l.
      reflexivity.
    + rewrite swaps_aenv_app_dist, swaps_aenv_one_flex, swaps_aenv_nil.
      cbn [swaps_atom].
      rewrite swap_atom_l.
      reflexivity.
    + cbn [swaps_cstrs swap_cstrs List.map swap_cstr swaps_pskl swap_pskl].
      rewrite swap_atom_l.
      reflexivity.

  -
    destruct (e_lookeq_inv_arrow D1 HαP)
      as (Sm & X1 & X2 & Cc1 & Cc2 & -> & -> & D1a & D1b).
    simpl in Hcov, HαP.

    destruct (IH1 D2a _ _ _ D1a
                 ltac:(clear - Hcov; fsetdec))
      as [ps1 [Hav1 [HS1 [HX1 HC1]]]].

    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    assert (Hα1 : swaps_atom ps1 α = α)
      by (apply (swaps_atom_dodge_in Hav1); clear - Hcov; fsetdec).
    assert (HPb : swaps_pskl ps1 Pb = Pb)
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    assert (HPb' : swaps_pskl ps1 Pb' = Pb')
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    pose proof HS1 as HS1r. symmetry in HS1r.
    destruct (e_lookeq_swaps ps1 D1b HS1r) as [S2t [HS2t D1bt]].
    rewrite HΘ1, Hα1, HPb, HPb' in D1bt.

    pose proof (e_lookeq_supply_grows D2a) as Hgr1'.
    destruct (IH2 D2b _ _ _ D1bt
                 ltac:(clear - Hcov Hgr1'; fsetdec))
      as [ps2 [Hav2 [HS2 [HX2 HC2]]]].

    pose proof (e_lookeq_generated_in_supply D2a) as Hdom1'.
    pose proof (e_lookeq_block_ftvar D2a) as Hftv1'.
    pose proof ((proj2 e_looksub_lookeq_cstr_ftvar) _ _ _ _ _ _ _ _ D2a)
      as Hcs1'.
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hdom1' Hftv1'; fsetdec).
    assert (HC1' : swaps_cstrs ps2 Cc1' = Cc1')
      by (apply swaps_cstrs_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hcs1' Hcov Hgr1'; fsetdec).
    exists (ps1 ++ ps2). repeat apply conj.
    + apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1'; fsetdec.
    + exact (swaps_atoms_app_transport HS2t HS2).
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_cstrs_app, !swaps_cstrs_app_dist, HC1, HC2, HC1'.
      reflexivity.

  -
    destruct (e_lookeq_inv_forall_inh D1 HαP) as (β1 & Hβ1 & Dp).
    simpl in Hcov, HαP.
    destruct (e_lookeq_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ), (@swap_pskl_fresh_id β1 β2 Qs),
      (@swap_pskl_fresh_id β1 β2 Qt), (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Qs (pskl_var_f β2))
      as Hup1.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Qt (pskl_var_f β2))
      as Hup2.
    destruct (IH Dp' _ _ _ Dpt
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup1 Hup2; simpl in *; fsetdec)
)
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  -
    destruct (e_lookeq_inv_forall_syn D1 HαP) as (β1 & Hβ1 & Dp).
    simpl in Hcov, HαP.
    destruct (e_lookeq_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ), (@swap_pskl_fresh_id β1 β2 Qs),
      (@swap_pskl_fresh_id β1 β2 (pskl_univ_ghost Qt)),
      (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Qs (pskl_var_f β2))
      as Hup1.
    destruct (IH Dp' _ _ _ Dpt
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup1; simpl in *; fsetdec)
)
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  -
    assert (Hα' : α `in` ftvar_in_pskl Qs) by (simpl in HαP; exact HαP).
    pose proof (e_lookeq_inv_ug D1 Hα') as Dp.
    simpl in Hcov.
    exact (IH Dp' _ _ _ Dp
              ltac:(clear - Hcov; simpl in *; fsetdec)).

  -
    assert (Hα' : α `in` ftvar_in_pskl Qs) by (simpl in HαP; exact HαP).
    destruct (e_lookeq_inv_ug1 D1 Hα') as (β1 & Hβ1 & Dp).
    simpl in Hcov, HαP.
    destruct (e_lookeq_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ),
      (@swap_pskl_fresh_id β1 β2 (pskl_univ_ghost Qs)),
      (@swap_pskl_fresh_id β1 β2 Qt), (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Qt (pskl_var_f β2))
      as Hup2.
    destruct (IH Dp' _ _ _ Dpt
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup2; simpl in *; fsetdec)
)
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  -
    assert (Hα' : α `in` ftvar_in_pskl Qs) by (simpl in HαP; exact HαP).
    pose proof (e_lookeq_inv_ug2 D1 Hgd Hoff Hα') as Dp.
    simpl in Hcov.
    exact (IH Dp' _ _ _ Dp
              ltac:(clear - Hcov; simpl in *; fsetdec)).

  -
    pose proof (e_lookeq_inv_ug_r D1 Hnev Hgd HαP) as Dp.
    simpl in Hcov.
    exact (IH Dp' _ _ _ Dp
              ltac:(clear - Hcov; simpl in *; fsetdec)).
Qed.

Local Ltac ls_kill :=
  try solve
    [ assumption
    | auto
    | exfalso; congruence
    | exfalso;
      match goal with
      | Hn : ?a `notin` ftvar_in_pskl (pskl_var_f ?a) |- _ =>
          simpl in Hn; clear - Hn; fsetdec
      end
    | exfalso;
      match goal with
      | Hn : ?a `notin` ftvar_in_pskl _, Hi : ?a `in` ftvar_in_pskl _ |- _ =>
          simpl in Hn, Hi; clear - Hn Hi; fsetdec
      end
    | exfalso;
      match goal with
      | Hoff : forall_r_off _ (pskl_all_syn ?B),
        Hgf : pskl_ghost_free (pskl_all_syn ?B) |- _ =>
          exact (Hoff B eq_refl eq_refl Hgf)
      end
    | exfalso;
      match goal with
      | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      end ].

Lemma e_looksub_inv_var : forall S0 Θ α m P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_var_f α) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  S1 = S0 /\ Ξ = nil /\ C = a_cstr_sub m P' :: nil.
Proof.
  intros * H; inversion H; subst; ls_kill.
Qed.

Lemma e_looksub_inv_ghost : forall S0 Θ α m P S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] pskl_ghost ⤳ Ξ ⨾ C }}e ->
  P <> pskl_var_f α ->
  α `in` ftvar_in_pskl P ->
  S1 = S0 /\ Ξ = nil /\ C = nil.
Proof.
  intros * H Hne Hα; inversion H; subst; ls_kill.
Qed.

Lemma e_looksub_inv_check : forall S0 Θ α A B S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ A ≼[ α , mode_tc ] B ⤳ Ξ ⨾ C }}e ->
  A <> pskl_var_f α ->
  guarded_pskl A ->
  guarded_pskl B ->
  α `in` ftvar_in_pskl A ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ A ∼[ α ] B ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H HneA HgA HgB Hα; inversion H; subst; ls_kill.
Qed.

Lemma e_looksub_inv_forall_r : forall S0 Θ α A B S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C }}e ->
  pskl_ghost_free (pskl_all_syn B) ->
  A <> pskl_var_f α ->
  α `in` ftvar_in_pskl A ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ A ≼[ α , mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hgf HneA Hα; inversion H; subst; ls_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

Lemma e_looksub_inv_arrow : forall S0 Θ α m P1 P2 P1' P2' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_arrow P1 P2) ≼[ α , (mode_fn m) ]
     (pskl_arrow P1' P2') ⤳ Ξ ⨾ C }}e ->
  α `in` ftvar_in_pskl (pskl_arrow P1 P2) ->
  exists Sm Ξ1 Ξ2 C1 C2,
    Ξ = Ξ1 ++ Ξ2 /\ C = C1 ++ C2 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e /\
    {{ Sm ↝ S1 ⊨ Θ ⊢ P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 }}e.
Proof.
  intros * H Hα; inversion H; subst;
    try solve [ exfalso;
                match goal with
                | Hn : ?a `notin` ftvar_in_pskl _,
                  Hi : ?a `in` ftvar_in_pskl _ |- _ =>
                    simpl in Hn, Hi; clear - Hn Hi; fsetdec
                end ].
  match goal with
  | Ha : e_lookeq S0 _ _ P1 P1' ?sm ?x1 ?c1,
    Hb : e_looksub ?sm _ _ _ P2 P2' S1 ?x2 ?c2 |- _ =>
      exists sm, x1, x2, c1, c2
  end.
  repeat split; assumption.
Qed.

Lemma e_looksub_inv_forall_l : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  P' <> pskl_ghost ->
  forall_r_off m P' ->
  α `in` ftvar_in_pskl (pskl_all_syn P) ->
  exists β, β `notin` S0 /\
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hnh Hoff Hα; inversion H; subst; ls_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

Lemma e_looksub_inv_univ_ghost_l : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  P' <> pskl_ghost ->
  forall_r_off m P' ->
  α `in` ftvar_in_pskl P ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e.
Proof.
  intros * H Hnh Hoff Hα; inversion H; subst; ls_kill.
Qed.

Lemma e_looksub_rel : forall S0 Θ α m P P' S1 Ξ C S1' Ξ' C',
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  {{ S0 ↝ S1' ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ' ⨾ C' }}e ->
  add α (ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_cstrs ps C = C'.
Proof.
  intros S0 Θ α m P P' S1 Ξ C S1' Ξ' C' D1 D2.
  revert S1 Ξ C D1. generalize D2.
  induction D2 as
    [S0 Θ α m P'
    |S0 Θ α m P P' Habs
    |S0 Θ α m P Hnev
    |S0 S1' Θ α A B Ξ' C' Hgf Hnev HgA HgB Dp'
    |S0 S1' Θ α As Bt Ξ' C' β2 Hghf Hβ2 Hocc Hnev Dp' IH
    |S0 Sm' S1' Θ α m Pa Pb Pa' Pb' X1' X2' Cc1' Cc2' D2a D2b IH
    |S0 S1' Θ α m Ps Pt Ξ' C' β2 Hβ2 Hocc Hnhl Hoff Dp' IH
    |S0 S1' Θ α m Ps P' Ξ' C' Hnhl Hoff Dp' IH];
    intros D2 S1 Ξ C D1 Hcov;
    match type of D1 with
    | e_looksub _ _ _ _ ?P _ _ _ _ =>
        destruct (sumbool_of_bool (mem α (ftvar_in_pskl P))) as [Hmem | Hmem]
    end.
  all: try (apply mem_false_notin in Hmem;
    destruct (e_looksub_absent_pins D1 Hmem) as [HX [HC HS]];
    destruct (e_looksub_absent_pins D2 Hmem) as [HX' [HC' HS']];
    exists nil; repeat apply conj; simpl;
    [intros ? ? [] | clear - HS HS'; fsetdec | congruence | congruence]).
  all: apply mem_true_in in Hmem; rename Hmem into HαP.
  -
    destruct (e_looksub_inv_var D1) as [-> [-> ->]].
    exists nil. repeat apply conj; simpl; try reflexivity. intros ? ? [].

  -
    exfalso. clear - Habs HαP; fsetdec.

  -
    destruct (e_looksub_inv_ghost D1 Hnev HαP) as [-> [-> ->]].
    exists nil. repeat apply conj; simpl; try reflexivity. intros ? ? [].

  -
    pose proof (e_looksub_inv_check D1 Hnev HgA HgB HαP) as Dp.
    exact (e_lookeq_rel Dp Dp' Hcov).

  -
    destruct (e_looksub_inv_forall_r D1 Hghf Hnev HαP) as (β1 & Hβ1 & Dp).
    simpl in Hcov.
    destruct (e_looksub_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ), (@swap_pskl_fresh_id β1 β2 As),
      (@swap_pskl_fresh_id β1 β2 Bt), (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Bt (pskl_var_f β2))
      as Hup.
    destruct (IH Dp' _ _ _ Dpt
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup; simpl in *; fsetdec)
)
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  -
    destruct (e_looksub_inv_arrow D1 HαP)
      as (Sm & X1 & X2 & Cc1 & Cc2 & -> & -> & D1a & D1b).
    simpl in Hcov, HαP.
    destruct (e_lookeq_rel D1a D2a ltac:(clear - Hcov; fsetdec))
      as [ps1 [Hav1 [HS1 [HX1 HC1]]]].
    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    assert (Hα1 : swaps_atom ps1 α = α)
      by (apply (swaps_atom_dodge_in Hav1); clear - Hcov; fsetdec).
    assert (HPb : swaps_pskl ps1 Pb = Pb)
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    assert (HPb' : swaps_pskl ps1 Pb' = Pb')
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    pose proof HS1 as HS1r. symmetry in HS1r.
    destruct (e_looksub_swaps ps1 D1b HS1r) as [S2t [HS2t D1bt]].
    rewrite HΘ1, Hα1, HPb, HPb' in D1bt.
    pose proof (e_lookeq_supply_grows D2a) as Hgr1'.
    destruct (IH D2b _ _ _ D1bt
                 ltac:(clear - Hcov Hgr1'; fsetdec))
      as [ps2 [Hav2 [HS2 [HX2 HC2]]]].
    pose proof (e_lookeq_generated_in_supply D2a) as Hdom1'.
    pose proof (e_lookeq_block_ftvar D2a) as Hftv1'.
    pose proof ((proj2 e_looksub_lookeq_cstr_ftvar) _ _ _ _ _ _ _ _ D2a)
      as Hcs1'.
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hdom1' Hftv1'; fsetdec).
    assert (HC1' : swaps_cstrs ps2 Cc1' = Cc1')
      by (apply swaps_cstrs_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hcs1' Hcov Hgr1'; fsetdec).
    exists (ps1 ++ ps2). repeat apply conj.
    + apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1'; fsetdec.
    + exact (swaps_atoms_app_transport HS2t HS2).
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_cstrs_app, !swaps_cstrs_app_dist, HC1, HC2, HC1'.
      reflexivity.

  -
    destruct (e_looksub_inv_forall_l D1 Hnhl Hoff HαP) as (β1 & Hβ1 & Dp).
    simpl in Hcov, HαP.
    destruct (e_looksub_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ), (@swap_pskl_fresh_id β1 β2 Ps),
      (@swap_pskl_fresh_id β1 β2 Pt), (@swap_atom_other β1 β2 α) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Ps (pskl_var_f β2))
      as Hup.
    destruct (IH Dp' _ _ _ Dpt
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hup; simpl in *; fsetdec)
)
      as [ps' [Hav' [HS' [HX' HC']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_cstrs]. exact HC'.

  -
    assert (Hα' : α `in` ftvar_in_pskl Ps) by (simpl in HαP; exact HαP).
    pose proof (e_looksub_inv_univ_ghost_l D1 Hnhl Hoff Hα') as Dp.
    simpl in Hcov.
    exact (IH Dp' _ _ _ Dp
              ltac:(clear - Hcov; simpl in *; fsetdec)).
Qed.

Lemma e_solve_eq_var_subject : forall S0 Θ α Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_var_f α) ∼ Q ⤳ Ξ ⨾ Y }}e ->
  S1 = S0 /\ Ξ = nil /\ Y = pskl_var_f α.
Proof.
  intros S0 Θ α Q S1 Ξ Y HD.
  remember (pskl_var_f α) as Ps eqn:HP.
  revert α HP.
  induction HD; intros α0 HP; try discriminate.
  -  inversion HP; subst. repeat split; reflexivity.
  -
    subst.
    match goal with
    | G : e_guess_mono _ (pskl_var_f _) _ _ _ |- _ =>
        destruct (e_guess_mono_inv_var G) as [-> [-> ->]]
    end.
    repeat split; reflexivity.
  -  subst. repeat split; reflexivity.
  -  exact (IHHD α0 HP).
Qed.

Local Ltac se_kill :=
  try solve
    [ assumption
    | exfalso;
      match goal with
      | Hg : nonghost_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      | Hg : nonghost_pskl pskl_ghost |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
      end ].

Lemma e_solve_eq_inv_arrow : forall S0 Θ P1 P2 Q1 Q2 S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2)
     ⤳ Ξ ⨾ Y }}e ->
  exists Sm Ξ1 Ξ2 Y1 Y2,
    Ξ = Ξ2 ++ Ξ1 /\ Y = pskl_arrow Y1 Y2 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ Y1 }}e /\
    {{ Sm ↝ S1 ⊨ (Ξ1 ++ Θ) ⊢ₑ P2 ∼ Q2 ⤳ Ξ2 ⨾ Y2 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Ha : e_solve_eq S0 _ P1 Q1 ?sm ?x1 ?y1,
    Hb : e_solve_eq ?sm _ P2 Q2 S1 ?x2 ?y2 |- _ =>
      exists sm, x1, x2, y1, y2
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_eq_inv_forall : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_all_syn Q) ⤳ Ξ ⨾ Y }}e ->
  exists β Y0, β `notin` S0
    /\ Y = pskl_all_syn (close_pskl_wrt_pskl β Y0)
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
          ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
          ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Hfr : ?b `notin` S0, Hp : e_solve_eq _ _ _ _ _ _ ?y |- _ =>
      exists b, y
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_eq_inv_univ_ghost : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y }}e ->
  exists Y0, Y = pskl_univ_ghost Y0
    /\ {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Hp : e_solve_eq S0 _ P Q S1 Ξ ?y |- _ => exists y
  end.
  split; [ reflexivity | assumption ].
Qed.

Lemma e_solve_eq_inv_ghost_forall : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_all_syn Q) ⤳ Ξ ⨾ Y }}e ->
  exists β Y0, β `notin` S0
    /\ Y = pskl_all_syn (close_pskl_wrt_pskl β Y0)
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (pskl_univ_ghost P)
          ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Hfr : ?b `notin` S0, Hp : e_solve_eq _ _ _ _ _ _ ?y |- _ =>
      exists b, y
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_eq_inv_forall_ghost : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y }}e ->
  exists β Y0, β `notin` S0
    /\ Y = pskl_all_syn (close_pskl_wrt_pskl β Y0)
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
          ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
          ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
  match goal with
  | Hfr : ?b `notin` S0, Hp : e_solve_eq _ _ _ _ _ _ ?y |- _ =>
      exists b, y
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_eq_inv_ghost_guarded : forall S0 Θ P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ Q ⤳ Ξ ⨾ Y }}e ->
  guarded_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * H Hg; inversion H; subst; se_kill.
Qed.

Lemma e_solve_eq_inv_guarded_ghost_unit : forall S0 Θ Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_unit ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y }}e ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_unit ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
Qed.

Lemma e_solve_eq_inv_guarded_ghost_arrow : forall S0 Θ P1 P2 Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ Y }}e ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * H; inversion H; subst; se_kill.
Qed.

Local Ltac rel_nil :=
  exists (@nil (atom * atom)); repeat apply conj;
  solve [ intros ? ? [] | simpl; reflexivity ].

Definition solve_eq_rel_stmt (n : nat) : Prop :=
  forall S0 Θ P Q S1 Ξ Y,
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ Y }}e ->
    size_pskl P + size_pskl Q <= n ->
    ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
    forall S1' Ξ' Y',
      {{ S0 ↝ S1' ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ' ⨾ Y' }}e ->
      exists ps,
        (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
        swaps_atoms ps S1 [=] S1' /\
        swaps_aenv ps Ξ = Ξ' /\
        swaps_pskl ps Y = Y'.

Lemma e_solve_eq_rel_n : forall n, solve_eq_rel_stmt n.
Proof.
  induction n as [ | n IH ]; unfold solve_eq_rel_stmt in *.
  { intros S0 Θ P Q S1 Ξ Y D1 Hsz; exfalso; destruct P; simpl in Hsz; lia. }
  intros S0 Θ P Q S1 Ξ Y D1 Hsz Hcov S1' Ξ' Y' D2.
  inversion D1; subst.

  -
    inversion D2; subst; se_kill; rel_nil.

  -
    destruct (e_solve_eq_var_subject D2) as [-> [-> ->]]. rel_nil.

  -
    match goal with
    | G : e_guess_mono S0 _ S1 Ξ _ |- _ => rename G into G1
    end.
    inversion D2; subst; se_kill.
    +
      destruct (e_guess_mono_inv_var G1) as [-> [-> ->]]. rel_nil.
    +
      match goal with
      | G : e_guess_mono S0 _ S1' Ξ' _ |- _ => rename G into G2
      end.
      destruct (e_guess_mono_rel G1 G2 ltac:(clear - Hcov; fsetdec))
        as [ps [Hav [HS [HX HA]]]].
      exists ps. repeat apply conj; [ exact Hav | exact HS | exact HX | ].
      rewrite swaps_pskl_ptyp_to_pskl, HA. reflexivity.

  -
    inversion D2; subst; se_kill; rel_nil.

  -
    inversion D2; subst; se_kill; rel_nil.

  -
    match type of D1 with
    | e_solve_eq _ _ (pskl_arrow ?p1 ?p2) (pskl_arrow ?q1 ?q2) _ _ _ =>
        rename p1 into Pa; rename p2 into Pb;
        rename q1 into Qa; rename q2 into Qb
    end.
    destruct (e_solve_eq_inv_arrow D1)
      as (Sm & X1 & X2 & Y1 & Y2 & -> & -> & D1a & D1b).
    destruct (e_solve_eq_inv_arrow D2)
      as (Sm' & X1' & X2' & Y1' & Y2' & -> & -> & D2a & D2b).
    simpl in Hsz, Hcov.
    destruct (IH _ _ _ _ _ _ _ D1a ltac:(simpl; lia)
                 ltac:(clear - Hcov; fsetdec) _ _ _ D2a)
      as [ps1 [Hav1 [HS1 [HX1 HY1]]]].
    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    assert (HPb : swaps_pskl ps1 Pb = Pb)
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    assert (HQb : swaps_pskl ps1 Qb = Qb)
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    pose proof HS1 as HS1r. symmetry in HS1r.
    destruct (e_solve_eq_swaps ps1 D1b HS1r) as [S2t [HS2t D1bt]].
    rewrite swaps_aenv_app_dist, HX1, HΘ1, HPb, HQb in D1bt.
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1'.
    pose proof (e_solve_eq_block_in_supply D2a) as Hdom1'.
    pose proof (e_solve_eq_block_ftvar D2a) as Hftv1'.
    pose proof (e_solve_eq_out_ftvar D2a ltac:(clear - Hcov; fsetdec))
      as Hout1'.
    destruct (IH _ _ _ _ _ _ _ D1bt ltac:(simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_app;
                       clear - Hcov Hgr1' Hdom1' Hftv1'; fsetdec)
                 _ _ _ D2b)
      as [ps2 [Hav2 [HS2 [HX2 HY2]]]].
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hdom1' Hftv1'; fsetdec).
    assert (HY1' : swaps_pskl ps2 Y1' = Y1')
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hout1'; fsetdec).
    exists (ps1 ++ ps2). repeat apply conj.
    + apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1'; fsetdec.
    + exact (swaps_atoms_app_transport HS2t HS2).
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_pskl_app, !swaps_pskl_arrow, HY1, HY2, HY1'.
      reflexivity.

  -
    match type of D1 with
    | e_solve_eq _ _ (pskl_all_syn ?p) (pskl_all_syn ?q) _ _ _ =>
        rename p into P0; rename q into Q0
    end.
    destruct (e_solve_eq_inv_forall D1) as (β1 & Y1 & Hβ1 & -> & Dp).
    destruct (e_solve_eq_inv_forall D2) as (β2 & Y2 & Hβ2 & -> & Dp').
    simpl in Hsz, Hcov.
    destruct (e_solve_eq_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ), (@swap_pskl_fresh_id β1 β2 P0),
      (@swap_pskl_fresh_id β1 β2 Q0) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f β2))
      as Hu1.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0 (pskl_var_f β2))
      as Hu2.
    destruct (IH _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite ! size_pskl_open_pskl_wrt_pskl_var; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu1 Hu2; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + eapply swaps_pskl_close_binder; eassumption.

  -
    match type of D1 with
    | e_solve_eq _ _ (pskl_univ_ghost ?p) (pskl_univ_ghost ?q) _ _ _ =>
        rename p into P0; rename q into Q0
    end.
    destruct (e_solve_eq_inv_univ_ghost D1) as (Y1 & -> & Dp).
    destruct (e_solve_eq_inv_univ_ghost D2) as (Y2 & -> & Dp').
    simpl in Hsz, Hcov.
    destruct (IH _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
                 ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ps'. repeat apply conj; [ exact Hav' | exact HS' | exact HX' | ].
    rewrite swaps_pskl_univ_ghost, HY'. reflexivity.

  -
    match type of D1 with
    | e_solve_eq _ _ (pskl_univ_ghost ?p) (pskl_all_syn ?q) _ _ _ =>
        rename p into P0; rename q into Q0
    end.
    destruct (e_solve_eq_inv_ghost_forall D1) as (β1 & Y1 & Hβ1 & -> & Dp).
    destruct (e_solve_eq_inv_ghost_forall D2) as (β2 & Y2 & Hβ2 & -> & Dp').
    simpl in Hsz, Hcov.
    destruct (e_solve_eq_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ),
      (@swap_pskl_fresh_id β1 β2 (pskl_univ_ghost P0)),
      (@swap_pskl_fresh_id β1 β2 Q0) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0 (pskl_var_f β2))
      as Hu2.
    destruct (IH _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu2; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + eapply swaps_pskl_close_binder; eassumption.

  -
    match goal with
    | Hg : guarded_pskl _ |- _ => rename Hg into Hgd
    end.
    pose proof (e_solve_eq_inv_ghost_guarded D1 Hgd) as Dp.
    pose proof (e_solve_eq_inv_ghost_guarded D2 Hgd) as Dp'.
    simpl in Hsz, Hcov.
    exact (IH _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
              ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').

  -
    match type of D1 with
    | e_solve_eq _ _ (pskl_all_syn ?p) (pskl_univ_ghost ?q) _ _ _ =>
        rename p into P0; rename q into Q0
    end.
    destruct (e_solve_eq_inv_forall_ghost D1) as (β1 & Y1 & Hβ1 & -> & Dp).
    destruct (e_solve_eq_inv_forall_ghost D2) as (β2 & Y2 & Hβ2 & -> & Dp').
    simpl in Hsz, Hcov.
    destruct (e_solve_eq_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ), (@swap_pskl_fresh_id β1 β2 P0),
      (@swap_pskl_fresh_id β1 β2 (pskl_univ_ghost Q0)) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f β2))
      as Hu1.
    destruct (IH _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu1; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + eapply swaps_pskl_close_binder; eassumption.

  -
    match goal with
    | Hg : guarded_pskl _ |- _ => rename Hg into Hgd
    end.
    inversion Hgd; subst.
    +
      pose proof (e_solve_eq_inv_guarded_ghost_unit D1) as Dp.
      pose proof (e_solve_eq_inv_guarded_ghost_unit D2) as Dp'.
      simpl in Hsz, Hcov.
      exact (IH _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
                ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').
    +
      destruct (e_solve_eq_var_subject D1) as [-> [-> ->]].
      destruct (e_solve_eq_var_subject D2) as [-> [-> ->]].
      rel_nil.
    +
      pose proof (e_solve_eq_inv_guarded_ghost_arrow D1) as Dp.
      pose proof (e_solve_eq_inv_guarded_ghost_arrow D2) as Dp'.
      simpl in Hsz, Hcov.
      exact (IH _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
                ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp').
Qed.

Corollary e_solve_eq_rel : forall S0 Θ P Q S1 Ξ Y S1' Ξ' Y',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ Y }}e ->
  {{ S0 ↝ S1' ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ' ⨾ Y' }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_pskl ps Y = Y'.
Proof.
  intros * D1 D2 Hcov.
  exact (e_solve_eq_rel_n D1 (le_n _) Hcov D2).
Qed.

Lemma e_guess_rel : forall S0 NM Q S1 Ξ Y S1' Ξ' Y',
  e_guess S0 NM Q S1 Ξ Y ->
  e_guess S0 NM Q S1' Ξ' Y' ->
  ftvar_in_pskl Q [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_pskl ps Y = Y'.
Proof.
  intros * D1 D2 Hcov.
  inversion D1; subst; inversion D2; subst.
  -
    exists (@nil (atom * atom)). repeat apply conj; simpl; try reflexivity.
    intros ? ? [].
  -
    match goal with
    | G1 : e_guess_mono S0 Q S1 Ξ _, G2 : e_guess_mono S0 Q S1' Ξ' _ |- _ =>
        destruct (e_guess_mono_rel G1 G2 Hcov) as [ps [Hav [HS [HX HA]]]]
    end.
    exists ps. repeat apply conj; [ exact Hav | exact HS | exact HX | ].
    rewrite swaps_pskl_ptyp_to_pskl, HA. reflexivity.
Qed.

Lemma e_solve_sub_var_subject : forall S0 Θ m α Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_var_f α) ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
  S1 = S0 /\ Ξ = nil /\ Y = pskl_var_f α.
Proof.
  intros * HD; inversion HD; subst.
  -  repeat split; reflexivity.
  -  repeat split; reflexivity.
  -
    match goal with
    | He : e_solve_eq _ _ _ _ _ _ _ |- _ => exact (e_solve_eq_var_subject He)
    end.
  -
    exfalso.
    match goal with
    | Hoff : solve_l_off (pskl_var_f _) |- _ => exact (proj1 Hoff _ eq_refl)
    end.
Qed.

Local Ltac ss_kill :=
  try solve
    [ assumption
    | exfalso;
      match goal with
      | Hg : guarded_pskl pskl_ghost |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
      | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => inversion Hg
      end
    | exfalso;
      match goal with
      | Hoff : peel_l_off (pskl_all_syn _) |- _ => exact (proj1 Hoff _ eq_refl)
      | Hoff : peel_l_off (pskl_univ_ghost _) |- _ => exact (proj2 Hoff _ eq_refl)
      end
    | exfalso;
      match goal with
      | Hoff : solve_l_off (pskl_var_f _) |- _ => exact (proj1 Hoff _ eq_refl)
      | Hoff : solve_l_off (pskl_all_syn _) |- _ =>
          exact (proj1 (proj2 Hoff) _ eq_refl)
      | Hoff : solve_l_off (pskl_univ_ghost _) |- _ =>
          exact (proj2 (proj2 Hoff) _ eq_refl)
      end ].

Lemma e_solve_sub_inv_ghost : forall S0 Θ m P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] pskl_ghost ⤳ Ξ ⨾ Y }}e ->
  peel_l_off P ->
  S1 = S0 /\ Ξ = nil /\ Y = P.
Proof.
  intros * HD Hoff; inversion HD; subst; ss_kill;
    repeat split; reflexivity.
Qed.

Lemma e_solve_sub_inv_forall_l : forall S0 Θ m P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
  exists β Y0, β `notin` S0
    /\ Y = pskl_all_syn (close_pskl_wrt_pskl β Y0)
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
          ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ m ] Q ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * HD; inversion HD; subst; ss_kill.
  match goal with
  | Hfr : ?b `notin` S0, Hp : e_solve_sub _ _ _ _ _ _ _ ?y |- _ =>
      exists b, y
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_sub_inv_univ_ghost_l : forall S0 Θ m P Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_univ_ghost P) ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
  exists Y0, Y = pskl_univ_ghost Y0
    /\ {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ Y0 }}e.
Proof.
  intros * HD; inversion HD; subst; ss_kill.
  match goal with
  | Hp : e_solve_sub S0 _ _ P Q S1 Ξ ?y |- _ => exists y
  end.
  split; [ reflexivity | assumption ].
Qed.

Lemma e_solve_sub_inv_forall_r : forall S0 Θ P B S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ Y }}e ->
  solve_l_off P ->
  exists β, β `notin` S0
    /\ {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
          (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * HD Hoff; inversion HD; subst; ss_kill.
  match goal with
  | Hfr : ?b `notin` S0 |- _ => exists b
  end.
  split; assumption.
Qed.

Lemma e_solve_sub_inv_arrow : forall S0 Θ m P1 P2 Q1 Q2 S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
     ⤳ Ξ ⨾ Y }}e ->
  exists Sm Ξ1 Ξ2 Y1 Y2,
    Ξ = Ξ2 ++ Ξ1 /\ Y = pskl_arrow Y1 Y2 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ Y1 }}e /\
    {{ Sm ↝ S1 ⊨ (Ξ1 ++ Θ) ⊢ₛ P2 ≼[ m ] Q2 ⤳ Ξ2 ⨾ Y2 }}e.
Proof.
  intros * HD; inversion HD; subst; ss_kill.
  match goal with
  | Ha : e_solve_eq S0 _ P1 Q1 ?sm ?x1 ?y1,
    Hb : e_solve_sub ?sm _ _ P2 Q2 S1 ?x2 ?y2 |- _ =>
      exists sm, x1, x2, y1, y2
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_sub_inv_ghost_l_fn : forall S0 Θ m Q1 Q2 S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ pskl_ghost ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
     ⤳ Ξ ⨾ Y }}e ->
  exists Sm Ξ1 Ξ2 Y1 Y2,
    Ξ = Ξ2 ++ Ξ1 /\ Y = pskl_univ_ghost (pskl_arrow Y1 Y2) /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ₑ pskl_ghost ∼ Q1 ⤳ Ξ1 ⨾ Y1 }}e /\
    {{ Sm ↝ S1 ⊨ (Ξ1 ++ Θ) ⊢ₛ pskl_ghost ≼[ m ] Q2 ⤳ Ξ2 ⨾ Y2 }}e.
Proof.
  intros * HD; inversion HD; subst; ss_kill.
  match goal with
  | Ha : e_solve_eq S0 _ pskl_ghost Q1 ?sm ?x1 ?y1,
    Hb : e_solve_sub ?sm _ _ pskl_ghost Q2 S1 ?x2 ?y2 |- _ =>
      exists sm, x1, x2, y1, y2
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_sub_inv_ghost_l : forall S0 Θ B S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ pskl_ghost ≼[ mode_tc ] B ⤳ Ξ ⨾ Y }}e ->
  guarded_pskl B ->
  S1 = S0 /\ Ξ = nil /\ Y = pskl_univ_ghost B.
Proof.
  intros * HD Hg; inversion HD; subst; ss_kill;
    repeat split; reflexivity.
Qed.

Lemma e_solve_sub_inv_check_unit : forall S0 Θ Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ pskl_unit ≼[ mode_tc ] Q ⤳ Ξ ⨾ Y }}e ->
  guarded_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_unit ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * HD Hg; inversion HD; subst; ss_kill.
Qed.

Lemma e_solve_sub_inv_check_arrow : forall S0 Θ P1 P2 Q S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ mode_tc ] Q ⤳ Ξ ⨾ Y }}e ->
  guarded_pskl Q ->
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * HD Hg; inversion HD; subst; ss_kill.
Qed.

Definition solve_sub_rel_stmt (n : nat) : Prop :=
  forall S0 Θ m P Q S1 Ξ Y,
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
    size_pskl P + size_pskl Q <= n ->
    ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
    forall S1' Ξ' Y',
      {{ S0 ↝ S1' ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ' ⨾ Y' }}e ->
      exists ps,
        (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
        swaps_atoms ps S1 [=] S1' /\
        swaps_aenv ps Ξ = Ξ' /\
        swaps_pskl ps Y = Y'.

Lemma e_solve_sub_rel_n : forall n, solve_sub_rel_stmt n.
Proof.
  induction n as [ | n IH ]; unfold solve_sub_rel_stmt in *.
  { intros S0 Θ m P Q S1 Ξ Y D1 Hsz; exfalso;
      destruct P; simpl in Hsz; lia. }
  intros S0 Θ m P Q S1 Ξ Y D1 Hsz Hcov S1' Ξ' Y' D2.
  inversion D1; subst.

  -
    destruct (e_solve_sub_var_subject D2) as [-> [-> ->]]. rel_nil.

  -
    match type of D1 with
    | e_solve_sub _ _ _ (pskl_all_syn ?p) _ _ _ _ => rename p into P0
    end.
    destruct (e_solve_sub_inv_forall_l D1) as (β1 & Y1 & Hβ1 & -> & Dp).
    destruct (e_solve_sub_inv_forall_l D2) as (β2 & Y2 & Hβ2 & -> & Dp').
    simpl in Hsz, Hcov.
    destruct (e_solve_sub_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ), (@swap_pskl_fresh_id β1 β2 P0),
      (@swap_pskl_fresh_id β1 β2 Q) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f β2))
      as Hu1.
    destruct (IH _ _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu1; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + eapply swaps_pskl_close_binder; eassumption.

  -
    match type of D1 with
    | e_solve_sub _ _ _ (pskl_univ_ghost ?p) _ _ _ _ => rename p into P0
    end.
    destruct (e_solve_sub_inv_univ_ghost_l D1) as (Y1 & -> & Dp).
    destruct (e_solve_sub_inv_univ_ghost_l D2) as (Y2 & -> & Dp').
    simpl in Hsz, Hcov.
    destruct (IH _ _ _ _ _ _ _ _ Dp ltac:(simpl; lia)
                 ltac:(clear - Hcov; simpl in *; fsetdec) _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ps'. repeat apply conj; [ exact Hav' | exact HS' | exact HX' | ].
    rewrite swaps_pskl_univ_ghost, HY'. reflexivity.

  -
    match goal with
    | Hoff : peel_l_off _ |- _ => rename Hoff into Hpo
    end.
    destruct (e_solve_sub_inv_ghost D2 Hpo) as [-> [-> ->]]. rel_nil.

  -
    match goal with
    | Hg1 : guarded_pskl ?A, Hg2 : guarded_pskl ?B |- _ =>
        rename Hg1 into HgP; rename Hg2 into HgQ
    end.
    inversion HgP; subst.
    +
      pose proof (e_solve_sub_inv_check_unit D1 HgQ) as Dp.
      pose proof (e_solve_sub_inv_check_unit D2 HgQ) as Dp'.
      exact (e_solve_eq_rel Dp Dp' Hcov).
    +
      destruct (e_solve_sub_var_subject D1) as [-> [-> ->]].
      destruct (e_solve_sub_var_subject D2) as [-> [-> ->]].
      rel_nil.
    +
      pose proof (e_solve_sub_inv_check_arrow D1 HgQ) as Dp.
      pose proof (e_solve_sub_inv_check_arrow D2 HgQ) as Dp'.
      exact (e_solve_eq_rel Dp Dp' Hcov).

  -
    match type of D1 with
    | e_solve_sub _ _ _ _ (pskl_all_syn ?b) _ _ _ => rename b into B0
    end.
    match goal with
    | Hoff : solve_l_off _ |- _ => rename Hoff into Hso
    end.
    destruct (e_solve_sub_inv_forall_r D1 Hso) as (β1 & Hβ1 & Dp).
    destruct (e_solve_sub_inv_forall_r D2 Hso) as (β2 & Hβ2 & Dp').
    simpl in Hsz, Hcov.
    destruct (e_solve_sub_swap Dp (swap_atoms_fresh_add _ _ _ Hβ1 Hβ2))
      as [S1t [HS1t Dpt]].
    rewrite swap_aenv_app, swap_aenv_one_tvar, ! swap_pskl_open_var,
      swap_atom_l in Dpt.
    rewrite (@swap_aenv_fresh_id β1 β2 Θ), (@swap_pskl_fresh_id β1 β2 P),
      (@swap_pskl_fresh_id β1 β2 B0) in Dpt
      by (clear - Hcov Hβ1 Hβ2; simpl in *; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B0 (pskl_var_f β2))
      as Hu1.
    destruct (IH _ _ _ _ _ _ _ _ Dpt
                 ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_cons_tvar;
                       clear - Hcov Hu1; simpl in *; fsetdec)
                 _ _ _ Dp')
      as [ps' [Hav' [HS' [HX' HY']]]].
    exists ((β1, β2) :: ps'). repeat apply conj.
    + eapply swaps_fresh_cons; eassumption.
    + eapply swaps_atoms_cons_transport; eassumption.
    + cbn [swaps_aenv]. exact HX'.
    + cbn [swaps_pskl]. exact HY'.

  -
    match type of D1 with
    | e_solve_sub _ _ _ (pskl_arrow ?p1 ?p2) (pskl_arrow ?q1 ?q2) _ _ _ =>
        rename p1 into Pa; rename p2 into Pb;
        rename q1 into Qa; rename q2 into Qb
    end.
    destruct (e_solve_sub_inv_arrow D1)
      as (Sm & X1 & X2 & Y1 & Y2 & -> & -> & D1a & D1b).
    destruct (e_solve_sub_inv_arrow D2)
      as (Sm' & X1' & X2' & Y1' & Y2' & -> & -> & D2a & D2b).
    simpl in Hsz, Hcov.
    destruct (e_solve_eq_rel D1a D2a ltac:(clear - Hcov; fsetdec))
      as [ps1 [Hav1 [HS1 [HX1 HY1]]]].
    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    assert (HPb : swaps_pskl ps1 Pb = Pb)
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    assert (HQb : swaps_pskl ps1 Qb = Qb)
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    pose proof HS1 as HS1r. symmetry in HS1r.
    destruct (e_solve_sub_swaps ps1 D1b HS1r) as [S2t [HS2t D1bt]].
    rewrite swaps_aenv_app_dist, HX1, HΘ1, HPb, HQb in D1bt.
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1'.
    pose proof (e_solve_eq_block_in_supply D2a) as Hdom1'.
    pose proof (e_solve_eq_block_ftvar D2a) as Hftv1'.
    pose proof (e_solve_eq_out_ftvar D2a ltac:(clear - Hcov; fsetdec))
      as Hout1'.
    destruct (IH _ _ _ _ _ _ _ _ D1bt ltac:(simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_app;
                       clear - Hcov Hgr1' Hdom1' Hftv1'; fsetdec)
                 _ _ _ D2b)
      as [ps2 [Hav2 [HS2 [HX2 HY2]]]].
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hdom1' Hftv1'; fsetdec).
    assert (HY1' : swaps_pskl ps2 Y1' = Y1')
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hout1'; fsetdec).
    exists (ps1 ++ ps2). repeat apply conj.
    + apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1'; fsetdec.
    + exact (swaps_atoms_app_transport HS2t HS2).
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_pskl_app, !swaps_pskl_arrow, HY1, HY2, HY1'.
      reflexivity.

  -
    match type of D1 with
    | e_solve_sub _ _ _ _ (pskl_arrow ?q1 ?q2) _ _ _ =>
        rename q1 into Qa; rename q2 into Qb
    end.
    destruct (e_solve_sub_inv_ghost_l_fn D1)
      as (Sm & X1 & X2 & Y1 & Y2 & -> & -> & D1a & D1b).
    destruct (e_solve_sub_inv_ghost_l_fn D2)
      as (Sm' & X1' & X2' & Y1' & Y2' & -> & -> & D2a & D2b).
    simpl in Hsz, Hcov.
    destruct (e_solve_eq_rel D1a D2a ltac:(clear - Hcov; simpl; fsetdec))
      as [ps1 [Hav1 [HS1 [HX1 HY1]]]].
    assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    assert (HQb : swaps_pskl ps1 Qb = Qb)
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav1);
          clear - Hcov; fsetdec).
    pose proof HS1 as HS1r. symmetry in HS1r.
    destruct (e_solve_sub_swaps ps1 D1b HS1r) as [S2t [HS2t D1bt]].
    rewrite swaps_aenv_app_dist, HX1, HΘ1, HQb in D1bt.
    rewrite swaps_pskl_ghost in D1bt.
    pose proof (e_solve_eq_supply_grows D2a) as Hgr1'.
    pose proof (e_solve_eq_block_in_supply D2a) as Hdom1'.
    pose proof (e_solve_eq_block_ftvar D2a) as Hftv1'.
    pose proof (e_solve_eq_out_ftvar D2a ltac:(clear - Hcov; simpl; fsetdec))
      as Hout1'.
    destruct (IH _ _ _ _ _ _ _ _ D1bt ltac:(simpl; lia)
                 ltac:(rewrite ftvar_in_aenv_app;
                       clear - Hcov Hgr1' Hdom1' Hftv1'; simpl in *; fsetdec)
                 _ _ _ D2b)
      as [ps2 [Hav2 [HS2 [HX2 HY2]]]].
    assert (HX1' : swaps_aenv ps2 X1' = X1')
      by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hdom1' Hftv1'; fsetdec).
    assert (HY1' : swaps_pskl ps2 Y1' = Y1')
      by (apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav2);
          clear - Hout1'; simpl in *; fsetdec).
    exists (ps1 ++ ps2). repeat apply conj.
    + apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1'; fsetdec.
    + exact (swaps_atoms_app_transport HS2t HS2).
    + rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
      reflexivity.
    + rewrite swaps_pskl_app, !swaps_pskl_univ_ghost, !swaps_pskl_arrow,
        HY1, HY2, HY1'.
      reflexivity.

  -
    match goal with
    | Hg : guarded_pskl _ |- _ => rename Hg into HgB
    end.
    destruct (e_solve_sub_inv_ghost_l D2 HgB) as [-> [-> ->]]. rel_nil.
Qed.

Corollary e_solve_sub_rel : forall S0 Θ m P Q S1 Ξ Y S1' Ξ' Y',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ Y }}e ->
  {{ S0 ↝ S1' ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ' ⨾ Y' }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S1 [=] S1' /\
    swaps_aenv ps Ξ = Ξ' /\
    swaps_pskl ps Y = Y'.
Proof.
  intros * D1 D2 Hcov.
  exact (e_solve_sub_rel_n D1 (le_n _) Hcov D2).
Qed.

Lemma e_solve_cstr_inv_nil : forall S0 Θ P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊩ nil ⨾ P ⤳ Ξ ⨾ Y }}e ->
  S1 = S0 /\ Ξ = nil /\ Y = P.
Proof.
  intros * H; inversion H; subst; repeat split; reflexivity.
Qed.

Lemma e_solve_cstr_inv_sub : forall S0 Θ m Q C P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊩ (a_cstr_sub m Q :: C) ⨾ P ⤳ Ξ ⨾ Y }}e ->
  C = nil /\ {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ Y }}e.
Proof.
  intros * H; inversion H; subst. split; [ reflexivity | assumption ].
Qed.

Lemma e_solve_cstr_inv_eq : forall S0 Θ Q C P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ Ξ ⨾ Y }}e ->
  exists Sm Ξ1 Ξ2 Y0,
    Ξ = Ξ2 ++ Ξ1 /\
    {{ S0 ↝ Sm ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ Y0 }}e /\
    {{ Sm ↝ S1 ⊨ (Ξ1 ++ Θ) ⊩ C ⨾ Y0 ⤳ Ξ2 ⨾ Y }}e.
Proof.
  intros * H; inversion H; subst.
  match goal with
  | Ha : e_solve_eq S0 _ P Q ?sm ?x1 ?y0,
    Hb : e_solve_cstr ?sm _ C ?y0 S1 ?x2 _ |- _ =>
      exists sm, x1, x2, y0
  end.
  repeat split; assumption.
Qed.

Lemma e_solve_cstr_rel : forall C S0 Θ P S1 Ξ Y,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Y }}e ->
  ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_a_cstrs C [<=] S0 ->
  forall S1' Ξ' Y',
    {{ S0 ↝ S1' ⊨ Θ ⊩ C ⨾ P ⤳ Ξ' ⨾ Y' }}e ->
    exists ps,
      (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
      swaps_atoms ps S1 [=] S1' /\
      swaps_aenv ps Ξ = Ξ' /\
      swaps_pskl ps Y = Y'.
Proof.
  induction C as [ | c C IHC ];
    intros S0 Θ P S1 Ξ Y D1 Hcov S1' Ξ' Y' D2.
  -
    destruct (e_solve_cstr_inv_nil D1) as [-> [-> ->]].
    destruct (e_solve_cstr_inv_nil D2) as [-> [-> ->]]. rel_nil.
  - destruct c as [ m Q | Q ].
    +
      destruct (e_solve_cstr_inv_sub D1) as [-> Dp].
      destruct (e_solve_cstr_inv_sub D2) as [_ Dp'].
      apply (e_solve_sub_rel Dp Dp').
      simpl in Hcov. clear - Hcov. fsetdec.
    +
      destruct (e_solve_cstr_inv_eq D1) as (Sm & X1 & X2 & Y0 & -> & D1a & D1b).
      destruct (e_solve_cstr_inv_eq D2)
        as (Sm' & X1' & X2' & Y0' & -> & D2a & D2b).
      simpl in Hcov.
      destruct (e_solve_eq_rel D1a D2a ltac:(clear - Hcov; fsetdec))
        as [ps1 [Hav1 [HS1 [HX1 HY1]]]].
      assert (HΘ1 : swaps_aenv ps1 Θ = Θ)
        by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav1);
            clear - Hcov; fsetdec).
      assert (HC1 : swaps_cstrs ps1 C = C)
        by (apply swaps_cstrs_fresh_id, (swaps_dodge_sub Hav1);
            clear - Hcov; fsetdec).
      pose proof HS1 as HS1r. symmetry in HS1r.
      destruct (e_solve_cstr_swaps ps1 D1b HS1r)
        as [S2t [HS2t D1bt]].
      rewrite swaps_aenv_app_dist, HX1, HΘ1, HC1, HY1 in D1bt.
      pose proof (e_solve_eq_supply_grows D2a) as Hgr1'.
      pose proof (e_solve_eq_block_in_supply D2a) as Hdom1'.
      pose proof (e_solve_eq_block_ftvar D2a) as Hftv1'.
      pose proof (e_solve_eq_out_ftvar D2a ltac:(clear - Hcov; fsetdec))
        as Hout1'.
      destruct (IHC _ _ _ _ _ _ D1bt
                   ltac:(rewrite ftvar_in_aenv_app;
                         clear - Hcov Hgr1' Hdom1' Hftv1' Hout1'; fsetdec)
                   _ _ _ D2b)
        as [ps2 [Hav2 [HS2 [HX2 HY2]]]].
      assert (HX1' : swaps_aenv ps2 X1' = X1')
        by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
            clear - Hdom1' Hftv1'; fsetdec).
      exists (ps1 ++ ps2). repeat apply conj.
      * apply (swaps_dodge_app Hav1 Hav2); clear - Hgr1'; fsetdec.
      * exact (swaps_atoms_app_transport HS2t HS2).
      * rewrite swaps_aenv_app, !swaps_aenv_app_dist, HX1, HX2, HX1'.
        reflexivity.
      * rewrite swaps_pskl_app, HY2. reflexivity.
Qed.

Lemma e_extract_inv : forall S0 Θ0 NM α m P P' S3 Ξt Y,
  {{ S0 ↝ S3 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξt ↪ Y }}e ->
  exists S1 S2 Ξ Ξs Ξg C Q,
    Ξt = Ξ ++ Ξs ++ Ξg /\
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e /\
    {{ S1 ↝ S2 ⊨ (Ξ ++ Θ0) ⊩ C ⨾ pskl_ghost ⤳ Ξs ⨾ Q }}e /\
    e_guess S2 NM Q S3 Ξg Y.
Proof.
  intros * H; inversion H; subst.
  match goal with
  | Hl : e_looksub S0 _ _ _ _ _ ?s1 ?x ?c,
    Hf : e_solve_cstr ?s1 _ _ _ ?s2 ?xs ?q,
    Hg : e_guess ?s2 _ _ S3 ?xg _ |- _ =>
      exists s1, s2, x, xs, xg, c, q
  end.
  repeat split; assumption.
Qed.

Theorem e_extract_det : forall S0 Θ0 NM α m P P' S3 Ξt Y S3' Ξt' Y',
  {{ S0 ↝ S3 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξt ↪ Y }}e ->
  {{ S0 ↝ S3' ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξt' ↪ Y' }}e ->
  add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
  exists ps,
    (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0) /\
    swaps_atoms ps S3 [=] S3' /\
    swaps_aenv ps Ξt = Ξt' /\
    swaps_pskl ps Y = Y'.
Proof.
  intros * D1 D2 Hcov.
  destruct (e_extract_inv D1)
    as (S1a & S2a & X & Xs & Xg & C & Q & -> & L1 & F1 & G1).
  destruct (e_extract_inv D2)
    as (S1b & S2b & X' & Xs' & Xg' & C' & Q' & -> & L2 & F2 & G2).

  destruct (e_looksub_rel L1 L2 Hcov) as [ps1 [Hav1 [HS1 [HX1 HC1]]]].

  pose proof (e_looksub_supply_grows L2) as HgrL.
  pose proof (e_looksub_generated_in_supply L2) as HdomL.
  pose proof (e_looksub_block_ftvar L2) as HftL.
  pose proof (e_looksub_cstr_ftvar L2 ltac:(clear - Hcov; fsetdec)) as HcsL.

  assert (HΘ0 : swaps_aenv ps1 Θ0 = Θ0)
    by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav1);
        clear - Hcov; fsetdec).
  pose proof HS1 as HS1r. symmetry in HS1r.
  destruct (e_solve_cstr_swaps ps1 F1 HS1r) as [S2t [HS2t F1t]].
  rewrite swaps_aenv_app_dist, HX1, HΘ0, HC1, swaps_pskl_ghost in F1t.
  destruct (e_solve_cstr_rel F1t
              ltac:(rewrite ftvar_in_aenv_app;
                    clear - Hcov HgrL HdomL HftL HcsL; simpl; fsetdec)
              F2)
    as [ps2 [Hav2 [HS2 [HX2 HY2]]]].

  pose proof (e_solve_cstr_supply_grows F2) as HgrF.
  pose proof (e_solve_cstr_block F2) as [HdomF [_ [_ HftF]]].
  pose proof (e_solve_cstr_out_ftvar F2) as HoutF.

  destruct (e_guess_swaps ps1 G1 HS2t) as [S3t1 [HS3t1 G1t]].
  pose proof HS2 as HS2r. symmetry in HS2r.
  destruct (e_guess_swaps ps2 G1t HS2r) as [S3t2 [HS3t2 G1tt]].
  rewrite HY2 in G1tt.
  destruct (e_guess_rel G1tt G2
              ltac:(clear - HoutF HcsL HgrF HgrL Hcov; simpl in *; fsetdec))
    as [ps3 [Hav3 [HS3 [HXg HYg]]]].

  assert (HXfix2 : swaps_aenv ps2 X' = X')
    by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav2);
        clear - HdomL HftL; fsetdec).
  assert (HXfix3 : swaps_aenv ps3 X' = X')
    by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav3);
        clear - HdomL HftL HgrF; fsetdec).
  assert (HXsfix3 : swaps_aenv ps3 Xs' = Xs')
    by (apply swaps_aenv_fresh_id, (swaps_dodge_sub Hav3);
        clear - HdomF HftF; fsetdec).
  exists (ps1 ++ ps2 ++ ps3). repeat apply conj.
  - intros a0 b0 Hin. rewrite ? in_app_iff in Hin.
    destruct Hin as [Hin | [Hin | Hin]].
    + exact (Hav1 a0 b0 Hin).
    + destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0 HgrL; fsetdec.
    + destruct (Hav3 a0 b0 Hin) as [Ha0 Hb0].
      split; clear - Ha0 Hb0 HgrL HgrF; fsetdec.
  - rewrite ! swaps_atoms_app. rewrite <- HS3.
    apply swaps_atoms_cong. rewrite HS3t2.
    apply swaps_atoms_cong. symmetry. exact HS3t1.
  - rewrite ! swaps_aenv_app, ! swaps_aenv_app_dist,
      HX1, HX2, HXg, HXfix2, HXfix3, HXsfix3.
    reflexivity.
  - rewrite ! swaps_pskl_app, HYg. reflexivity.
Qed.
