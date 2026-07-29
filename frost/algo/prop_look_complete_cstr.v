(** P6-Cs — completeness of consistency CONSTRAINT COLLECTION AND SOLVING
    ([lemma:complete-consistency-constraint-collection-solving],
    consistency-proofs.tex:920).

    Companion of [a_solve_eq_complete_var] (P6-Cv,
    [frost/algo/prop_look_complete_var.v]), which this file's α-leaf case
    delegates to: where P6-Cv handles the single lookup variable, this lemma
    walks the whole source skeleton, emitting the constraint set 𝒞 and the
    collected flexibles Ξc and solving them against the input Pi.

    Structure of the file:
      §1  small transports reused throughout (retagging, [msubst_uskl_syn] and its
          kit, constraint/solve plumbing);
      §2  the ∀-BINDER KIT — run the induction hypothesis under a fresh rigid
          binder β added to BOTH Θ and Θ0, then strip β from every output
          (the paper's "these judgements hold without β");
      §3  the two ftv transports behind the paper's "Pi and 𝒞 cannot contain
          β", which is semantic rather than syntactic;
      §4  the theorem itself, by strong induction on
          [size_uskl R + size_pskl P0].

    The statement carries ONE well-formedness premise beyond the paper's list —
    well-formedness of the CONSISTENCY SUBJECT.  It is the paper's prose "all
    inputs are well-formed", and it is load-bearing: without it the lemma is
    FALSE, as machine-checked in [frost/algo/cex/cex_p6cs_subject_wf.v].
    See docs/WF-SIDE-CONDITIONS.md. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_consis_complete.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_decorate_sub.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_consis_precise.
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_sub_complete.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_look_complete_var.

Set Implicit Arguments.

(* Reusable: retag the tag index of a partial-precision derivation.
   (mirror of [ad_partial_precise_delta_cong]; migrate to prop_precise.v). *)
Lemma ad_partial_precise_psi_cong : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall Ψ', Ψ [=] Ψ' ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ' ] ψ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros Ψ' Heq.
  - apply ad_ppre__unit; fsetdec.
  - apply ad_ppre__var; [ fsetdec | assumption ].
  - apply ad_ppre__arrow with (Ψ1 := Ψ1) (Ψ2 := Ψ2);
      [ exact H | exact H0 | fsetdec ].
  - apply ad_ppre__forall with (L := L) (Ψ0 := Ψ0);
      [ intros α Hα; exact (H α Hα) | fsetdec ].
  - apply ad_ppre__hole; [ fsetdec | assumption ].
  - apply ad_ppre__tophole_remove; apply IHad_partial_precise; assumption.
  - apply ad_ppre__tophole_fill with (L := L);
      intros α Hα; apply (H0 α Hα); assumption.
  - apply ad_ppre__tophole_keep; apply IHad_partial_precise; assumption.
  - apply ad_ppre__flex_l with (τ := τ); [ exact H | apply IHad_partial_precise; assumption ].
  - apply ad_ppre__flex_r with (τ := τ); [ exact H | apply IHad_partial_precise; assumption ].
Qed.

(* ===================================================================== *)
(*  msubst on DECORATED skeletons (uskl) — the κ of the paper's [κ R].     *)
(*  R is κ-free (erase R = P); the subject is [(κR)[ψa/α]].               *)
(*  (migrate to algo/def_meta.v alongside msubst_pskl.)                    *)
(* Erasure commutes with msubst (⌊κ R⌋ = κ⌊R⌋). *)
Lemma uskl_to_pskl_msubst_uskl_syn : forall κ R',
  ⌊ msubst_uskl_syn κ R' ⌋ˢ = msubst_pskl κ (⌊ R' ⌋ˢ).
Proof.
  intros κ R'; induction R'; simpl;
    try reflexivity;
    try (rewrite IHR'; reflexivity);
    try (rewrite IHR'1, IHR'2; reflexivity).
  apply uskl_to_pskl_ptyp.
Qed.

(* msubst preserves the syntactic ε-tags (var images are tag-free paints). *)
Lemma ftag_in_uskl_ptyp_to_uskl_syn : forall A,
  ftag_in_uskl (ptyp_to_uskl_syn A) [=] empty.
Proof.
  intro A. unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn.
  induction A; simpl; fsetdec.
Qed.

Lemma ptyp_to_uskl_syn_var : forall α, ptyp_to_uskl_syn (ptyp_var_f α) = uskl_var_f α.
Proof. reflexivity. Qed.

(* Prepending fresh entries (dom ρ avoids S's ftvs) does not change msubst.
   This mechanizes the paper's "equivalence of metasubstitutions" step
   (κ₁ = ρ ++ κ) as a SYNTACTIC rewrite. *)
Lemma msubst_uskl_syn_prepend_fresh : forall κ' κ R',
  (forall α, α `in` dom κ' -> α `notin` ftvar_in_uskl R') ->
  msubst_uskl_syn (κ' ++ κ) R' = msubst_uskl_syn κ R'.
Proof.
  intros κ' κ R'; induction R' as [ | n | α | R1 IHR'1 R2 IHR'2 | R0 IHR'0
                               | ε R0 IHR'0 | | R0 IHR'0 | | R0 IHR'0 ];
    intros Hfr; simpl in *; try reflexivity.
  - (* var α : α ∉ dom ρ' (else α ∉ {α}) *)
    f_equal. apply msubst_lookup_app_notin.
    intro Hc. apply (Hfr α Hc). fsetdec.
  - rewrite IHR'1, IHR'2; [ reflexivity | | ];
      intros α Hα; specialize (Hfr α Hα); fsetdec.
  - rewrite IHR'0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
  - rewrite IHR'0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
  - rewrite IHR'0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
  - rewrite IHR'0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
Qed.

(* Same fact on plain [pskl] — used to thread [κ → ρc1 ++ κ] on the
   refinement premise of the right IH (dom ρc1 avoids P02 ⊆ dom Θ0). *)
Lemma msubst_pskl_prepend_fresh : forall κ' κ P,
  (forall α, α `in` dom κ' -> α `notin` ftvar_in_pskl P) ->
  msubst_pskl (κ' ++ κ) P = msubst_pskl κ P.
Proof.
  intros κ' κ P; induction P as [ | n | α | P1 IHP1 P2 IHP2 | P0 IHP0 | | P0 IHP0 ];
    intros Hfr; simpl in *; try reflexivity.
  - (* var α *)
    f_equal. apply msubst_lookup_app_notin.
    intro Hc. apply (Hfr α Hc). fsetdec.
  - rewrite IHP1, IHP2; [ reflexivity | | ];
      intros α Hα; specialize (Hfr α Hα); fsetdec.
  - rewrite IHP0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
  - rewrite IHP0; [ reflexivity | intros α Hα; apply Hfr; assumption ].
Qed.

(* Tags of a var-substitution are bounded by the target's ∪ the payload's. *)
Lemma ftag_in_uskl_subst_bskl_in_uskl : forall R0 α R',
  ftag_in_uskl (subst_bskl_in_uskl R0 α R')
    [<=] ftag_in_uskl R' `union` ftag_in_uskl R0.
Proof.
  intros R0 α R'; induction R' as [ | n | α0 | β1 IHR'1 β2 IHR'2 | β0 IHR'0
                               | ε β0 IHR'0 | | β0 IHR'0 | | β0 IHR'0 ];
    simpl; try fsetdec.
  (* var α0 : subst is [if α0 = α then u else var α0] *)
  match goal with |- context [if ?c then _ else _] => destruct c end;
    simpl; fsetdec.
Qed.

Lemma ftag_in_uskl_msubst_uskl_syn : forall κ R',
  ftag_in_uskl (msubst_uskl_syn κ R') [=] ftag_in_uskl R'.
Proof.
  intros κ R'; induction R' as [ | n | α | R1 IHR'1 R2 IHR'2 | R0 IHR'0
                             | ε R0 IHR'0 | | R0 IHR'0 | | R0 IHR'0 ];
    simpl; try fsetdec.
  pose proof (ftag_in_uskl_ptyp_to_uskl_syn (msubst_lookup κ α)) as Hgf.
  fsetdec.
Qed.
Lemma a_lookeq_cstr_eq : forall α P P' Ξ 𝒞,
  P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  Forall (fun c => exists Q, c = a_cstr_eq Q) 𝒞.
Proof.
  intros α P P' Ξ 𝒞 H; induction H.
  - constructor; [ eexists; reflexivity | constructor ].  (* var *)
  - constructor.                                          (* absent *)
  - constructor.                                          (* vacuous *)
  - constructor; [ eexists; reflexivity | constructor ].  (* flex_r *)
  - apply Forall_app; split; assumption.                 (* arrow *)
  - match goal with H : forall β, β `notin` ?L -> _ |- _ =>
      pick fresh β for L; apply (H β ltac:(auto)) end.    (* forall_inh *)
  - match goal with H : forall β, β `notin` ?L -> _ |- _ =>
      pick fresh β for L; apply (H β ltac:(auto)) end.    (* forall_syn *)
  - assumption.                                           (* univ_ghost *)
  - match goal with H : forall β, β `notin` ?L -> _ |- _ =>
      pick fresh β for L; apply (H β ltac:(auto)) end.    (* univ_ghost1 *)
  - assumption.                                           (* univ_ghost2 *)
  - assumption.                                           (* univ_ghost_r *)
Qed.

(* Compose two constraint solves over an appended EQ-only list. *)
Lemma a_solve_cstr_app : forall Θ C1 𝒞2 Pi Pmid Pa,
  Forall (fun c => exists Q, c = a_cstr_eq Q) C1 ->
  Θ ⊩ C1 ⨾ Pi ⤳ Pmid ->
  Θ ⊩ 𝒞2 ⨾ Pmid ⤳ Pa ->
  Θ ⊩ (C1 ++ 𝒞2) ⨾ Pi ⤳ Pa.
Proof.
  intros Θ C1; induction C1 as [ | c C1' IH ];
    intros 𝒞2 Pi Pmid Pa Hall H1 H2.
  - inversion H1; subst. exact H2.
  - inversion Hall as [ | ? ? [Q ->] Hall' ]; subst.
    inversion H1 as [ | | ? ? ? ? P'' ? Heq Htail ]; subst.
    simpl. eapply a_solve_cstr__eq;
      [ exact Heq | eapply IH; [ exact Hall' | exact Htail | exact H2 ] ].
Qed.

(* Case-split helpers for the paper's three special cases. *)
Lemma pskl_hole_dec : forall (P : pskl), P = pskl_hole \/ P <> pskl_hole.
Proof. destruct P; solve [ left; reflexivity | right; discriminate ]. Qed.

Lemma pskl_var_dec : forall (P : pskl) (a : atom),
  P = pskl_var_f a \/ P <> pskl_var_f a.
Proof.
  intros P a.
  destruct P as [ | n | b | P1 P2 | P1 | | P1 ]; try (right; discriminate).
  destruct (b == a) as [-> | Hne]; [ left; reflexivity | right; congruence ].
Qed.

(* ===================================================================== *)
(*  Homogeneous-flex_mono REORDER KIT (arrow-case assembly)                *)
(*  Ξc1, Ξc2 from [a_lookeq] are all [abind_flex_mono]; the arrow case     *)
(*  must reconcile the LE-Arrow order (Ξc1++Ξc2) with the solve/inc        *)
(*  natural orders (Ξc1++Θ0 for the left, Ξc2++Ξc1++Θ0 for the right).     *)
(* ===================================================================== *)

Definition keys {A : Type} (l : list (atom * A)) : list atom := List.map fst l.

Lemma keys_app : forall (A : Type) (l1 l2 : list (atom * A)),
  keys (l1 ++ l2) = keys l1 ++ keys l2.
Proof.
  intros A l1 l2; induction l1 as [ | p l1' IH ]; unfold keys in *; simpl;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma keys_eq_dom : forall (A B : Type) (l1 : list (atom * A)) (l2 : list (atom * B)),
  keys l1 = keys l2 -> dom l1 [=] dom l2.
Proof.
  induction l1 as [ | [x a] l1' IH ]; intros [ | [y b] l2' ] Hk;
    unfold keys in *; simpl in *; try discriminate; try reflexivity.
  injection Hk as Hxy Hk'; subst y.
  pose proof (IH l2' Hk') as Hd. simpl_env in *. fsetdec.
Qed.

Definition all_flex_mono (Ξ : aenv) : Prop :=
  Forall (fun p => snd p = abind_flex_mono) Ξ.

Lemma all_flex_mono_app : forall A B,
  all_flex_mono A -> all_flex_mono B -> all_flex_mono (A ++ B).
Proof. intros A B HA HB. apply Forall_app; split; assumption. Qed.

Lemma a_lookeq_all_flex_mono : forall α P P0 Ξ 𝒞,
  P ∼[ α ] P0 ⤳ Ξ ⨾ 𝒞 -> all_flex_mono Ξ.
Proof.
  intros α P P0 Ξ 𝒞 H; unfold all_flex_mono; induction H.
  - constructor.                                          (* var *)
  - constructor.                                          (* absent *)
  - constructor.                                          (* vacuous *)
  - constructor; [ reflexivity | constructor ].          (* flex_r *)
  - apply Forall_app; split; assumption.                 (* arrow *)
  - match goal with H : forall β, β `notin` ?L -> _ |- _ =>
      pick fresh β for L; exact (H β ltac:(auto)) end.    (* forall_inh *)
  - match goal with H : forall β, β `notin` ?L -> _ |- _ =>
      pick fresh β for L; exact (H β ltac:(auto)) end.    (* forall_syn *)
  - assumption.                                           (* univ_ghost *)
  - match goal with H : forall β, β `notin` ?L -> _ |- _ =>
      pick fresh β for L; exact (H β ltac:(auto)) end.    (* univ_ghost1 *)
  - assumption.                                           (* univ_ghost2 *)
  - assumption.                                           (* univ_ghost_r *)
Qed.

(* Split off an all-flex_mono prefix from an [a_inc]: the aligned images are
   wf monotypes in the target, and the remaining substitution increments Θ0. *)
Lemma a_inc_flex_prefix_split : forall Ξ κa Θ0 κb Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa /\ κb ∷ Θ0 ⊑ Θ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros κa Θ0 κb Θ Hfm Hmap Hinc.
  - destruct κa as [ | ? ? ]; simpl in Hmap; [ | discriminate ].
    simpl in Hinc. split; [ constructor | exact Hinc ].
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    destruct κa as [ | [y τ] κa' ]; simpl in Hmap; [ discriminate | ].
    injection Hmap as Hxy Hmap'; subst y.
    simpl in Hinc.
    inversion Hinc as [ | Θ2 κ2 Θ3 x2 τ2 Hinc2 Hwf2 Hmono2 | | | | ]; subst.
    destruct (IH κa' Θ0 κb Θ Hfm' Hmap' Hinc2) as [Hfa Hrest].
    split; [ constructor; [ split; assumption | exact Hfa ] | exact Hrest ].
Qed.

(* Prepend an aligned, wf-mono flex_mono prefix onto an [a_inc]. *)
Lemma a_inc_flex_prefix_build : forall Ξ κa Θ0 κb Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa ->
  κb ∷ Θ0 ⊑ Θ ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros κa Θ0 κb Θ Hfm Hmap Hwm Hinc.
  - destruct κa as [ | ? ? ]; simpl in Hmap; [ | discriminate ].
    simpl. exact Hinc.
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    destruct κa as [ | [y τ] κa' ]; simpl in Hmap; [ discriminate | ].
    injection Hmap as Hxy Hmap'; subst y.
    inversion Hwm as [ | ph2 pt2 Hwmh Hwm' ]; subst; destruct Hwmh as [Hwfτ Hmτ].
    simpl. apply a_inc__flex; [ apply IH; assumption | exact Hwfτ | exact Hmτ ].
Qed.

(* msubst_pskl is a function of the lookup: agreeing lookups agree on outputs. *)
Lemma msubst_pskl_lookup_congr : forall κ σ P,
  (forall α, msubst_lookup κ α = msubst_lookup σ α) ->
  msubst_pskl κ P = msubst_pskl σ P.
Proof.
  intros κ σ P Heq;
    induction P as [ | n | α | P1 IHP1 P2 IHP2 | P0 IHP0 | | P0 IHP0 ];
    simpl; try reflexivity.
  - rewrite Heq; reflexivity.
  - rewrite IHP1, IHP2; reflexivity.
  - rewrite IHP0; reflexivity.
  - rewrite IHP0; reflexivity.
Qed.

(* Swap two disjoint-domain metasubst prefixes in a lookup / pskl-msubst. *)
Lemma msubst_lookup_app_swap : forall κa κb κ α,
  (forall β, β `in` dom κa -> β `notin` dom κb) ->
  msubst_lookup (κa ++ κb ++ κ) α = msubst_lookup (κb ++ κa ++ κ) α.
Proof.
  intros κa κb κ α Hdisj.
  destruct (AtomSetProperties.In_dec α (dom κa)) as [Hina | Hnina].
  - rewrite (@msubst_lookup_app_in κa (κb ++ κ) α Hina).
    rewrite (@msubst_lookup_app_notin κb (κa ++ κ) α (Hdisj α Hina)).
    rewrite (@msubst_lookup_app_in κa κ α Hina). reflexivity.
  - rewrite (@msubst_lookup_app_notin κa (κb ++ κ) α Hnina).
    destruct (AtomSetProperties.In_dec α (dom κb)) as [Hinb | Hninb].
    + rewrite (@msubst_lookup_app_in κb (κa ++ κ) α Hinb).
      rewrite (@msubst_lookup_app_in κb κ α Hinb). reflexivity.
    + rewrite (@msubst_lookup_app_notin κb (κa ++ κ) α Hninb).
      rewrite (@msubst_lookup_app_notin κb κ α Hninb).
      rewrite (@msubst_lookup_app_notin κa κ α Hnina). reflexivity.
Qed.

Lemma msubst_pskl_app_swap : forall κa κb κ P,
  (forall β, β `in` dom κa -> β `notin` dom κb) ->
  msubst_pskl (κa ++ κb ++ κ) P = msubst_pskl (κb ++ κa ++ κ) P.
Proof.
  intros κa κb κ P Hdisj. apply msubst_pskl_lookup_congr.
  intro α. apply msubst_lookup_app_swap; exact Hdisj.
Qed.

(* Reorder / weaken the aenv of well-formedness (binds-based). *)
Lemma binds_swap_app : forall (x : atom) (b : abind) A B C,
  binds x b (A ++ B ++ C) -> binds x b (B ++ A ++ C).
Proof. intros x b A B C H. analyze_binds H. Qed.

Lemma a_wf_pskl_swap_app : forall A B C Δ P,
  (A ++ B ++ C) ⨟ Δ ⊢ₚₛᵃ P -> (B ++ A ++ C) ⨟ Δ ⊢ₚₛᵃ P.
Proof.
  intros A B C Δ P H. eapply a_wf_pskl_weaken; [ | exact H ].
  intros x b Hb. apply binds_swap_app. exact Hb.
Qed.

(* Build [a_wf_aenv] of an all-flex_mono prefix over a wf tail. *)
Lemma a_wf_aenv_flex_prefix : forall Ξ Θ0,
  all_flex_mono Ξ -> uniq (Ξ ++ Θ0) -> a_wf_aenv Θ0 -> a_wf_aenv (Ξ ++ Θ0).
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros Θ0 Hfm Huq Hwf0.
  - simpl. exact Hwf0.
  - inversion Hfm as [ | ph pt Hb Hfm' ]; subst; simpl in Hb; subst b.
    simpl. apply a_wf_aenv__flex.
    + simpl_env in Huq; solve_uniq.
    + apply IH; [ exact Hfm' | simpl_env in Huq; solve_uniq | exact Hwf0 ].
Qed.

(* Move the aenv of a constraint solve by a binds-preserving map (both flex
   directions), lifting [a_solve_sub_eq_ctx_change] over the constraint list. *)
Lemma a_solve_cstr_ctx_change : forall Θ 𝒞 P P',
  Θ ⊩ 𝒞 ⨾ P ⤳ P' ->
  forall Θ',
  (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
  (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
  Θ' ⊩ 𝒞 ⨾ P ⤳ P'.
Proof.
  intros Θ 𝒞 P P' H; induction H; intros Θ' Hft Hfl.
  - apply a_solve_cstr__empty.
  - apply a_solve_cstr__sub. eapply (proj1 a_solve_sub_eq_ctx_change); eauto.
  - eapply a_solve_cstr__eq;
      [ eapply (proj2 a_solve_sub_eq_ctx_change); [ eassumption | eauto | eauto ]
      | apply IHa_solve_cstr; auto ].
Qed.

(* Weaken a constraint SUBJECT-SOLVE by a fresh all-flex_mono MID prefix.
   The subject-ftv side conditions are LOAD-BEARING: SE-FlexR's [a_non_flex]
   leg would break if a subject var lay in [dom Ξm] (a fresh key could turn a
   non-flex var flexible), so the statement WITHOUT them is FALSE. *)
Lemma binds_weaken_mid : forall (x : atom) (b : abind) Ξl Ξm Θ0,
  binds x b (Ξl ++ Θ0) -> binds x b (Ξl ++ Ξm ++ Θ0).
Proof.
  intros x b Ξl Ξm Θ0 H. apply binds_app_1 in H as [H | H].
  - apply binds_app_2; exact H.
  - apply binds_app_3; apply binds_app_3; exact H.
Qed.

Lemma binds_strengthen_mid : forall (x : atom) (b : abind) Ξl Ξm Θ0,
  binds x b (Ξl ++ Ξm ++ Θ0) -> x `notin` dom Ξm -> binds x b (Ξl ++ Θ0).
Proof.
  intros x b Ξl Ξm Θ0 H Hx. apply binds_app_1 in H as [H | H].
  - apply binds_app_2; exact H.
  - apply binds_app_1 in H as [H | H].
    + exfalso. apply Hx. eapply binds_In; exact H.
    + apply binds_app_3; exact H.
Qed.

Lemma a_flex_tvar_weaken_mid : forall Ξl Ξm Θ0 α,
  a_flex_tvar (Ξl ++ Θ0) α -> a_flex_tvar (Ξl ++ Ξm ++ Θ0) α.
Proof.
  intros Ξl Ξm Θ0 α [Hb | [τ Hb]];
    [ left | right; exists τ ]; apply binds_weaken_mid; exact Hb.
Qed.

Lemma a_non_flex_weaken_mid : forall Ξl Ξm Θ0 P,
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  a_non_flex (Ξl ++ Θ0) P -> a_non_flex (Ξl ++ Ξm ++ Θ0) P.
Proof.
  intros Ξl Ξm Θ0 P Hftv [Hlc Hnf]. split; [ exact Hlc | ].
  intro Hf. apply Hnf. inversion Hf as [ Θx αx Hb | Θx αx τ Hb ]; subst.
  - assert (Hin : αx `notin` dom Ξm)
      by (intro Hc; apply (Hftv _ Hc); simpl; fsetdec).
    apply a_flex__var with (α := αx).
    eapply binds_strengthen_mid; [ exact Hb | exact Hin ].
  - assert (Hin : αx `notin` dom Ξm)
      by (intro Hc; apply (Hftv _ Hc); simpl; fsetdec).
    apply a_flex__var_def with (α := αx) (τ := τ).
    eapply binds_strengthen_mid; [ exact Hb | exact Hin ].
Qed.

(* The mutual subject-solve weakening.  Non-flex / non-binder rules
   reconstruct with the IHs; SE-FlexR uses [a_non_flex_weaken_mid]; the
   subject-opening binder rules freshen β away from [dom Ξm ∪ ftv]. *)
Lemma a_solve_sub_eq_weaken_mid_flex :
  (forall Θ m P P0 P', Θ ⊢ₛ P ≼[ m ] P0 ⤳ P' ->
     forall Ξl Ξm Θ0, Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
     (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
     (Ξl ++ Ξm ++ Θ0) ⊢ₛ P ≼[ m ] P0 ⤳ P') /\
  (forall Θ P P0 P', Θ ⊢ₑ P ∼ P0 ⤳ P' ->
     forall Ξl Ξm Θ0, Θ = Ξl ++ Θ0 -> all_flex_mono Ξm ->
     (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
     (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
     (Ξl ++ Ξm ++ Θ0) ⊢ₑ P ∼ P0 ⤳ P').
Proof.
  Ltac p6cs_ih Hfm Hdisj :=
    match goal with
    | |- _ ⊢ₑ ?p ∼ ?q ⤳ ?r =>
        match goal with
          IH : forall _ _ _, _ = _ -> _ -> _ -> _ -> _ ⊢ₑ p ∼ q ⤳ r |- _ =>
            eapply IH; [ reflexivity | exact Hfm | exact Hdisj | ]
        end
    | |- _ ⊢ₛ ?p ≼[ ?m ] ?q ⤳ ?r =>
        match goal with
          IH : forall _ _ _, _ = _ -> _ -> _ -> _ -> _ ⊢ₛ p ≼[ m ] q ⤳ r |- _ =>
            eapply IH; [ reflexivity | exact Hfm | exact Hdisj | ]
        end
    end.
  apply a_solve_sub_eq_mutind; intros; subst;
    match goal with H : all_flex_mono _ |- _ => rename H into Hfm end;
    match goal with H : forall x, _ -> _ `notin` dom _ |- _ => rename H into Hdisj end;
    match goal with H : forall x, _ -> _ `notin` ftvar_in_pskl _ |- _ => rename H into Hftv end.
  - (* SS-Var *) apply a_solve_sub__var.
  - (* SS-ForallL *)
    apply a_solve_sub__forall_l with (L := L `union` dom Ξm `union` ftvar_in_pskl P);
      intros β Hβ.
    match goal with IH : forall b, b `notin` _ -> forall _ _ _, _ = _ -> _ |- _ =>
      specialize (IH β ltac:(fsetdec)) end.
    p6cs_ih Hfm Hdisj.
    intros x Hx. specialize (Hftv x Hx).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
    simpl in *. clear - Hftv Hx Hβ Hup. fsetdec.
  - (* SS-UnivGhostL *)
    apply a_solve_sub__univ_ghost_l. p6cs_ih Hfm Hdisj.
    intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
  - (* SS-Vacuous *) apply a_solve_sub__vacuous.
  - (* SS-Check *)
    apply a_solve_sub__check; [ assumption | assumption | ]. p6cs_ih Hfm Hdisj.
    intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
  - (* SS-ForallR *)
    apply a_solve_sub__forall_r with (L := L `union` dom Ξm); intros β Hβ.
    match goal with IH : forall b, b `notin` _ -> forall _ _ _, _ = _ -> _ |- _ =>
      specialize (IH β ltac:(fsetdec)) end.
    p6cs_ih Hfm Hdisj.
    intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
  - (* SS-Arrow *)
    apply a_solve_sub__arrow.
    + p6cs_ih Hfm Hdisj.
      intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
    + p6cs_ih Hfm Hdisj.
      intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
  - (* SS-GhostLF *)
    apply a_solve_sub__ghost_l_fn.
    + p6cs_ih Hfm Hdisj. intros x Hx; simpl; fsetdec.
    + p6cs_ih Hfm Hdisj. intros x Hx; simpl; fsetdec.
  - (* SS-GhostL *) apply a_solve_sub__ghost_l; assumption.
  - (* SE-Unit *) apply a_solve_eq__unit.
  - (* SE-Var *) apply a_solve_eq__var.
  - (* SE-FlexR *)
    apply a_solve_eq__flex_r;
      [ apply a_flex_tvar_weaken_mid; assumption
      | apply a_non_flex_weaken_mid; assumption ].
  - (* SE-GhostL *) apply a_solve_eq__hole_l.
  - (* SE-VacuousR *) apply a_solve_eq__hole_r.
  - (* SE-Arrow *)
    apply a_solve_eq__arrow.
    + p6cs_ih Hfm Hdisj.
      intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
    + p6cs_ih Hfm Hdisj.
      intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
  - (* SE-Forall *)
    apply a_solve_eq__forall with (L := L `union` dom Ξm `union` ftvar_in_pskl P);
      intros β Hβ.
    match goal with IH : forall b, b `notin` _ -> forall _ _ _, _ = _ -> _ |- _ =>
      specialize (IH β ltac:(fsetdec)) end.
    p6cs_ih Hfm Hdisj.
    intros x Hx. specialize (Hftv x Hx).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
    simpl in *. clear - Hftv Hx Hβ Hup. fsetdec.
  - (* SE-UnivGhost *)
    apply a_solve_eq__tophole_both. p6cs_ih Hfm Hdisj.
    intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
  - (* SE-GhostForall *)
    apply a_solve_eq__tophole_l_all with (L := L `union` dom Ξm); intros β Hβ.
    match goal with IH : forall b, b `notin` _ -> forall _ _ _, _ = _ -> _ |- _ =>
      specialize (IH β ltac:(fsetdec)) end.
    p6cs_ih Hfm Hdisj.
    intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
  - (* SE-GhostGuarded *)
    apply a_solve_eq__tophole_l_guarded; [ assumption | ]. p6cs_ih Hfm Hdisj.
    intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
  - (* SE-ForallGhost *)
    apply a_solve_eq__all_l_tophole with (L := L `union` dom Ξm `union` ftvar_in_pskl P);
      intros β Hβ.
    match goal with IH : forall b, b `notin` _ -> forall _ _ _, _ = _ -> _ |- _ =>
      specialize (IH β ltac:(fsetdec)) end.
    p6cs_ih Hfm Hdisj.
    intros x Hx. specialize (Hftv x Hx).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β)) as Hup.
    simpl in *. clear - Hftv Hx Hβ Hup. fsetdec.
  - (* SE-GuardedGhost *)
    apply a_solve_eq__tophole_r_guarded; [ assumption | ]. p6cs_ih Hfm Hdisj.
    intros x Hx; specialize (Hftv x Hx); simpl in Hftv; clear - Hftv; fsetdec.
Qed.

Lemma a_solve_cstr_weaken_mid_flex : forall Ξl Ξm Θ0 𝒞 P P',
  all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_cstrs 𝒞) ->
  (Ξl ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ P' ->
  (Ξl ++ Ξm ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ P'.
Proof.
  intros Ξl Ξm Θ0 𝒞 P P' Hfm Hdisj HP HC Hsolve.
  remember (Ξl ++ Θ0) as Θ eqn:HeqΘ.
  revert Ξl Θ0 HeqΘ Hdisj HP HC.
  induction Hsolve; intros Ξl Θ0 HeqΘ Hdisj HP HC; subst.
  - apply a_solve_cstr__empty.
  - (* sub *)
    apply a_solve_cstr__sub.
    eapply (proj1 a_solve_sub_eq_weaken_mid_flex);
      [ eassumption | reflexivity | exact Hfm | exact Hdisj | exact HP ].
  - (* eq *)
    eapply a_solve_cstr__eq.
    + eapply (proj2 a_solve_sub_eq_weaken_mid_flex);
        [ eassumption | reflexivity | exact Hfm | exact Hdisj | exact HP ].
    + apply IHHsolve; [ reflexivity | exact Hdisj | | ].
      * (* ftv P'' avoids Ξm : P'' ⊆ P ∪ Q *)
        intros x Hx.
        pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ H) as Hf.
        specialize (HP x Hx). specialize (HC x Hx). simpl in HC.
        clear - Hf HP HC; fsetdec.
      * (* ftv 𝒞 avoids Ξm : 𝒞 ⊆ (eq Q :: 𝒞) *)
        intros x Hx. specialize (HC x Hx). simpl in HC. clear - HC; fsetdec.
Qed.

(* ===================================================================== *)
(*  Flex-P0 support (the FLEX-P0 / __flex_r crux).                          *)
(* ===================================================================== *)

(* α positions in [R] survive [msubst_uskl_syn κ] when [α ∉ dom κ]. *)
Lemma ftvar_in_uskl_msubst_uskl_syn_notin_dom : forall κ R α,
  α `notin` dom κ ->
  α `in` ftvar_in_uskl R ->
  α `in` ftvar_in_uskl (msubst_uskl_syn κ R).
Proof.
  intros κ R α Hdom Hin.
  rewrite <- (ftvar_in_pskl_uskl_to_pskl (msubst_uskl_syn κ R)).
  rewrite uskl_to_pskl_msubst_uskl_syn.
  apply msubst_pskl_ftv_notin_dom; [ exact Hdom | ].
  rewrite ftvar_in_pskl_uskl_to_pskl; exact Hin.
Qed.

(* A rigid variable cannot refine into an arrow (only [flex_l] could fire,
   and its [α] is a defined flexible, clashing with rigidity). *)
Lemma ad_refine_syn_rigid_var_arrow_absurd : forall Θ Δ α Q1 Q2,
  a_wf_aenv Θ ->
  binds α abind_tvar Θ ->
  Θ ⨟ Δ ⊢ᵣᵃ (bskl_var_f α) ⊳ (bskl_arrow Q1 Q2) ->
  False.
Proof.
  intros Θ Δ α Q1 Q2 Hwf Hb H; inversion H; subst;
    match goal with
    | Hbd : binds _ (abind_flex_mono_def _) _ |- _ =>
        pose proof (binds_unique _ _ _ _ _ Hb Hbd (a_wf_aenv_uniq Hwf)) as Hc;
        discriminate Hc
    end.
Qed.

Lemma subst_bskl_in_uskl_var_self : forall R α,
  subst_bskl_in_uskl R α (uskl_var_f α) = R.
Proof. intros; simpl; destruct (eq_var α α); [ reflexivity | contradiction ]. Qed.

(* A mono-paint consistency subject is well-formed as a monotype: every
   variable leaf is [a_binds_tvar] (from [__var] / [__flex_l]). *)
Lemma ad_pat_consis_mono_paint_subj_wf : forall Ψs Θ ψ Q,
  Ψs ⨟ Θ ⊢ₛᵃ ψ ∼ Q ->
  a_wf_aenv Θ ->
  forall τm, mono_ptyp τm -> ψ = ptyp_to_uskl_syn τm -> a_wf_ptyp Θ τm.
Proof.
  intros Ψs Θ ψ Q H HwfΘ; induction H; intros τm Hmono Heq;
    try (destruct τm; try (solve [ inversion Hmono ]); simpl in Heq; discriminate).
  - (* unit *) symmetry in Heq; apply ptyp_to_uskl_syn_unit_inv in Heq as ->; constructor.
  - (* var *) symmetry in Heq; apply ptyp_to_uskl_syn_var_inv in Heq as ->; constructor; assumption.
  - (* arrow *)
    symmetry in Heq;
      destruct (ptyp_to_uskl_syn_arrow_inv _ Heq) as (τ1 & τ2 & -> & Heq1 & Heq2).
    inversion Hmono; subst.
    constructor; [ eapply IHad_pat_consis1; eauto | eapply IHad_pat_consis2; eauto ].
  - (* flex_l: subject var α0 *)
    symmetry in Heq; apply ptyp_to_uskl_syn_var_inv in Heq as ->.
    constructor; right; right; eexists; eassumption.
  - (* flex_r *) eapply IHad_pat_consis; eauto.
Qed.

(* closes an α-leaf: the whole subject IS ψa, faced with mono-ish Q. *)
Ltac psia_leaf Hrec :=
  match goal with
  | HwfΘ : a_wf_aenv ?Θ, Htsk : is_tskl ?ψa, Hmi : bskl_monoish ?Q |- _ =>
      let τψ := fresh "τψ" in let Hmn := fresh "Hmn" in let Heqψ := fresh "Heqψ" in
      destruct (ad_pat_consis_monoish_counterpart Hrec HwfΘ Htsk Hmi)
        as (_ & τψ & Hmn & Heqψ);
      exists τψ; repeat split;
        [ exact Hmn | exact Heqψ
        | eapply ad_pat_consis_mono_paint_subj_wf;
            [ exact Hrec | exact HwfΘ | exact Hmn | exact Heqψ ] ]
  end.

(* THE ψa-MONO EXTRACTION (the flex-P0 crux).  When the whole consistency
   subject [(κR)[ψa/αs]] faces a MONO-ISH [Q] (the case of a flexible P0,
   whose κ-image is a monotype pinning Q mono-ish), the instantiation
   [ψa] sitting at the αs-positions is itself a mono paint.  Induction on the
   consistency: at an αs-leaf ([T = var αs], subject = ψa) it is
   [ad_pat_consis_monoish_counterpart]; at an arrow it recurses into the side
   carrying αs; flex_r/tophole_drop recurse on the sub-derivation; ghost/∀
   counterparts are excluded by [bskl_monoish Q]. *)
Lemma ad_pat_consis_subst_psia_mono : forall Ψs Θ Rsubj Q,
  Ψs ⨟ Θ ⊢ₛᵃ Rsubj ∼ Q ->
  a_wf_aenv Θ ->
  bskl_monoish Q ->
  forall R' ψa αs,
    Rsubj = subst_bskl_in_uskl ψa αs R' ->
    is_tskl ψa ->
    αs `in` ftvar_in_uskl R' ->
    exists τψ, mono_ptyp τψ /\ ψa = ptyp_to_uskl_syn τψ /\ a_wf_ptyp Θ τψ.
Proof.
  intros Ψs Θ Rsubj Q H. induction H;
    intros HwfΘ Hmi R' ψa αs HeqSubj Htsk Hα.
  - (* unit : Q = bskl_unit *)
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    + simpl in Hα; clear - Hα; exfalso; fsetdec.
    + destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa | discriminate HeqSubj ].
      assert (Hrec : Ψ ⨟ Θ ⊢ₛᵃ uskl_unit ∼ bskl_unit)
        by (apply ad_pat_consis__unit; assumption).
      psia_leaf Hrec.
  - (* var α : Q = bskl_var α *)
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj.
    + subst ψa.
      assert (Hrec : Ψ ⨟ Θ ⊢ₛᵃ (uskl_var_f α) ∼ (bskl_var_f α))
        by (apply ad_pat_consis__var; assumption).
      psia_leaf Hrec.
    + injection HeqSubj as ->. simpl in Hα.
      exfalso; apply Hβ; clear - Hα; fsetdec.
  - (* arrow : Q = bskl_arrow Q1 Q2 *)
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    + (* R' = var β : αs-leaf or absurd *)
      destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa | discriminate HeqSubj ].
      assert (Hrec : Ψ ⨟ Θ ⊢ₛᵃ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2))
        by (eapply ad_pat_consis__arrow; [ exact H | exact H0 | exact H1 ]).
      psia_leaf Hrec.
    + (* R' = arrow T1 T2 : recurse into the side with αs *)
      injection HeqSubj as HeqR1 HeqR2.
      assert (HmiQ1 : bskl_monoish Q1) by (inversion Hmi; assumption).
      assert (HmiQ2 : bskl_monoish Q2) by (inversion Hmi; assumption).
      simpl in Hα; apply union_1 in Hα; destruct Hα as [Hα | Hα].
      * eapply IHad_pat_consis1;
          [ exact HwfΘ | exact HmiQ1 | exact HeqR1 | exact Htsk | exact Hα ].
      * eapply IHad_pat_consis2;
          [ exact HwfΘ | exact HmiQ2 | exact HeqR2 | exact Htsk | exact Hα ].
  - (* forall_inh_tagged : Q = bskl_all_inh — not mono-ish *) inversion Hmi.
  - (* forall_inh_untagged : Q = bskl_all_inh *) inversion Hmi.
  - (* forall_syn_tagged : Q = bskl_all_syn *) inversion Hmi.
  - (* forall_syn : Q = bskl_all_syn *) inversion Hmi.
  - (* ghostg : Q = bskl_hole *) inversion Hmi.
  - (* topholeg : Q = bskl_tophole *) inversion Hmi.
  - (* hole : subject uskl_hole is not is_tskl *)
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    + destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa; inversion Htsk | discriminate HeqSubj ].
    + simpl in Hα; clear - Hα; exfalso; fsetdec.
  - (* tophole : Q = bskl_tophole *) inversion Hmi.
  - (* tophole_inh : Q = bskl_all_inh *) inversion Hmi.
  - (* tophole_drop : subject uskl_tophole R, Q arbitrary *)
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    + (* R' = var β : ψa = uskl_tophole R, not is_tskl *)
      destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa; inversion Htsk | discriminate HeqSubj ].
    + (* R' = tophole T0 : recurse on the body *)
      injection HeqSubj as HeqR.
      simpl in Hα.
      eapply IHad_pat_consis;
        [ exact HwfΘ | exact Hmi | exact HeqR | exact Htsk | exact Hα ].
  - (* flex_l : subject uskl_var_f α (rule's flex) *)
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj.
    2:{ simpl in Hα; exfalso; clear - Hα Hβ; fsetdec. }
    subst ψa.
    match goal with |- exists _, _ /\ uskl_var_f ?a = _ /\ _ =>
      exists (ptyp_var_f a) end.
    split; [ apply mono_ptyp__var | ].
    split; [ reflexivity | ].
    constructor; right; right; eexists; eassumption.
  - (* flex_r : Q = bskl_var α, unfold; premise faces a mono paint *)
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    eapply IHad_pat_consis;
      [ exact HwfΘ | apply bskl_monoish_paint; exact Hmd
      | exact HeqSubj | exact Htsk | exact Hα ].
Qed.

(* An ARROW-subject consistency whose counterpart [Q] is a DEFINED-FLEX var
   (rule [ad_pat_consis__flex_r]) is NOT an independent case: [Q]'s definition
   chain unfolds to a [bskl_arrow] endpoint, and the REFINEMENT side unfolds the
   very same chain ([ad_refine_flexdef_target_unfold]).  So both consistency-
   inversion branches (__arrow / __flex_r) share ONE continuation in which
   [Q = bskl_arrow Q1 Q2].  The chain is walked by the induction itself — no
   [destruct τ] / [a_def_chain] bookkeeping is needed, because each flex_r step
   simply re-invokes the IH on the sub-derivation with the unfolded target. *)
Lemma ad_pat_consis_arrow_refine_unify : forall Ψs Θ R Q,
  a_wf_aenv Θ ->
  Ψs ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  forall Ra Rb, R = uskl_arrow Ra Rb ->
  forall Δr Ql, Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ Q ->
  exists Ψ1 Ψ2 Q1 Q2,
    Ψs [=] Ψ1 `union` Ψ2 /\
    (Ψ1 ⨟ Θ ⊢ₛᵃ Ra ∼ Q1) /\
    (Ψ2 ⨟ Θ ⊢ₛᵃ Rb ∼ Q2) /\
    (Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ (bskl_arrow Q1 Q2)) /\
    (Ψs ⨟ Θ ⊢ₛᵃ (uskl_arrow Ra Rb) ∼ (bskl_arrow Q1 Q2)).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros Ra Rb Heq Δr Ql Href;
    try discriminate Heq.
  - (* __arrow: the structural case — read the split straight off *)
    injection Heq as Hea Heb; subst.
    do 4 eexists.
    split; [ eassumption | ].
    split; [ eassumption | ].
    split; [ eassumption | ].
    split; [ exact Href | ].
    eapply ad_pat_consis__arrow; eassumption.
  - (* __flex_r: unfold ONE definition step on BOTH sides, then recurse *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Href | reflexivity | eassumption ] ].
Qed.

Lemma guarded_pskl_to_bskl_inh : forall P,
  guarded_pskl P -> guarded_bskl (pskl_to_bskl_inh P).
Proof.
  intros P Hg; inversion Hg; subst; cbn [pskl_to_bskl_inh].
  - apply guarded_bskl__unit.
  - apply guarded_bskl__var.
  - apply guarded_bskl__arrow; apply lc_pskl_to_bskl_inh; assumption.
Qed.

(* ---- plain (non-hygienic) mirrors of the [_f] refinement inversions ---- *)

Lemma ad_refine_syn_guarded_r : forall Θ Δr Q Q',
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q ⊳ Q' ->
  guarded_bskl Q ->
  guarded_bskl Q'.
Proof.
  intros Θ Δr Q Q' HwfΘ Href Hg.
  eapply ad_refine_syn_f_guarded_r;
    [ exact HwfΘ | apply ad_refine_syn_f_of_plain; exact Href | exact Hg ].
Qed.

Lemma ad_refine_syn_tophole_keep_inv : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  guarded_bskl Q' ->
  Θ ⨟ Δr ⊢ᵣᵃ (bskl_tophole Q') ⊳ (bskl_tophole Q) ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q.
Proof.
  intros Θ Δr Q' Q HwfΘ Hg Href.
  apply ad_refine_syn_f_forget with (F := empty).
  eapply ad_refine_syn_f_tophole_keep_inv;
    [ exact HwfΘ | exact Hg | apply ad_refine_syn_f_of_plain; exact Href ].
Qed.

(* Only a ⊤◇-headed (or □) source can refine to a ⊤◇ target: the ∀/guarded
   sources are shape-excluded, and a defined-flex source unfolds to a MONOTYPE
   painting, which is guarded.  Kills every P0 but [⊤◇P0'] in the ⊤̇◇/⊤◇ cases. *)
Lemma ad_refine_syn_tophole_rhs_src : forall Θ Δr Q' Q,
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ Q' ⊳ Q ->
  forall Q0, Q = bskl_tophole Q0 ->
  (exists L0, Q' = bskl_tophole L0) \/ Q' = bskl_hole.
Proof.
  intros Θ Δr Q' Q HwfΘ Href; induction Href; intros Q0 Heq;
    try discriminate Heq.
  - (* __hole *)
    right; reflexivity.
  - (* __tophole_remove *) left; eexists; reflexivity.
  - (* __tophole_keep *) left; eexists; reflexivity.
  - (* __flex_l: the definition is a monotype, whose painting is guarded *)
    exfalso.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHref HwfΘ Q0 Heq) as [[L0 HL0] | HL0];
      destruct τ; simpl in HL0; try discriminate HL0; inversion Hmτ.
Qed.

Lemma ad_refine_syn_tophole_guarded_inv : forall Θ Δr Q Q',
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ (bskl_tophole Q) ⊳ Q' ->
  guarded_bskl Q' ->
  Θ ⨟ Δr ⊢ᵣᵃ Q ⊳ Q'.
Proof.
  intros Θ Δr Q Q' HwfΘ Href Hg.
  apply ad_refine_syn_f_forget with (F := empty).
  eapply ad_refine_syn_f_tophole_guarded_inv;
    [ exact HwfΘ | apply ad_refine_syn_f_of_plain; exact Href | exact Hg ].
Qed.

Lemma ad_refine_syn_all_inh_guarded_absurd : forall Θ Δr Q Q',
  a_wf_aenv Θ ->
  Θ ⨟ Δr ⊢ᵣᵃ (bskl_all_inh Q) ⊳ Q' ->
  guarded_bskl Q' ->
  False.
Proof.
  intros Θ Δr Q Q' HwfΘ Href Hg.
  eapply ad_refine_syn_f_all_inh_guarded_absurd;
    [ exact HwfΘ | apply ad_refine_syn_f_of_plain; exact Href | exact Hg ].
Qed.

(* [⊤◇]-subject consistency against a GUARDED target: the ghost must have been
   DROPPED (C-UnivGhost2) — [__tophole]/[__tophole_inh] have non-guarded targets,
   and a defined-flex target unfolds (on both sides) to a guarded monotype
   painting.  The paper's "by well-formedness of P ... Q is guarded" step. *)
Lemma ad_pat_consis_tophole_guarded_unify : forall Ψs Θ R Q,
  a_wf_aenv Θ ->
  Ψs ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  forall R0, R = uskl_tophole R0 ->
  forall Δr Ql, Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ Q ->
  guarded_bskl Q ->
  exists Q0,
    (Ψs ⨟ Θ ⊢ₛᵃ R0 ∼ Q0) /\
    (Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ Q0) /\
    guarded_bskl Q0.
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros R0 Heq Δr Ql Href Hg;
    try discriminate Heq.
  - (* __tophole : target ⊤◇Q — not guarded *) inversion Hg.
  - (* __tophole_inh : target ∀ — not guarded *) inversion Hg.
  - (* __tophole_drop : the ghost is dropped *)
    injection Heq as He; subst.
    eexists; split; [ eassumption | split; [ exact Href | exact Hg ] ].
  - (* __flex_r: unfold ONE definition step on BOTH sides, then recurse *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_guarded, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* [⊤̇◇]-subject consistency (rule C-UnivGhostG) up to the target's defined-flex
   chain — the [ad_pat_consis_arrow_refine_unify] pattern for [uskl_topholeg]. *)
Lemma ad_pat_consis_topholeg_refine_unify : forall Ψs Θ R Q,
  a_wf_aenv Θ ->
  Ψs ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  forall R0, R = uskl_topholeg R0 ->
  forall Δr Ql, Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ Q ->
  exists Q0,
    (Ψs ⨟ Θ ⊢ₛᵃ R0 ∼ Q0) /\
    (Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ (bskl_tophole Q0)).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros R0 Heq Δr Ql Href;
    try discriminate Heq.
  - (* __topholeg *)
    injection Heq as He; subst.
    eexists; split; [ eassumption | exact Href ].
  - (* __flex_r: unfold ONE definition step on BOTH sides, then recurse *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Href | reflexivity | eassumption ] ].
Qed.

(* ===================================================================== *)
(*  §2  ∀-BINDER KIT.  The ∀ / ⊤◇-vs-∀ rows run the IH under a FRESH rigid    *)
(*  binder β, added to BOTH Θ (the consistency/refinement context) and Θ0 *)
(*  (the algorithmic input context); every output must then lose β again  *)
(*  — the paper's "these judgements hold without β".                      *)
(* ===================================================================== *)

Lemma all_flex_mono_a_decls : forall Ξ, all_flex_mono Ξ -> a_decls Ξ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros H.
  - apply a_decls__nil.
  - inversion H as [ | ph pt Hb H' ]; subst; simpl in Hb; subst b.
    change ((x, abind_flex_mono) :: Ξ') with ((x ~ abind_flex_mono) ++ Ξ').
    apply a_decls__cons; apply IH; exact H'.
Qed.

(* (i) a MONOTYPE well-formed under a rigid binder it does not mention is
   well-formed without it. *)
Lemma a_wf_ptyp_mono_strip_tvar : forall β Θ τ,
  mono_ptyp τ ->
  a_wf_ptyp ((β ~ abind_tvar) ++ Θ) τ ->
  β `notin` ftvar_in_ptyp τ ->
  a_wf_ptyp Θ τ.
Proof.
  intros β Θ τ Hm; induction Hm; intros Hwf Hfr; simpl in Hfr.
  - apply a_wf_ptyp__unit.
  - inversion Hwf; subst.
    apply a_wf_ptyp__var.
    apply (@a_binds_tvar_strip_mid α β abind_tvar nil Θ);
      [ assumption | intro Hc; inversion Hc; subst; clear - Hfr; fsetdec
      | intro Hc; inversion Hc | intros τ0 Hc; inversion Hc ].
  - inversion Hwf; subst.
    apply a_wf_ptyp__arrow;
      [ apply IHHm1; [ assumption | clear - Hfr; fsetdec ]
      | apply IHHm2; [ assumption | clear - Hfr; fsetdec ] ].
Qed.

(* (ii) information increase: strip the binder from the middle of the source
   and from the front of the target (the collected prefix Ξ is all-flex_mono,
   and its images do not mention β). *)
Lemma a_inc_strip_tvar_mid : forall Ξ κa κb Θ0 β Θ,
  all_flex_mono Ξ ->
  keys κa = keys Ξ ->
  Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κa ->
  β `notin` dom Θ ->
  (κa ++ κb) ∷ (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ) ->
  (κa ++ κb) ∷ (Ξ ++ Θ0) ⊑ Θ.
Proof.
  intros Ξ κa κb Θ0 β Θ Hfm Hmap Hfr Hβ Hinc.
  destruct (@a_inc_flex_prefix_split Ξ κa ((β ~ abind_tvar) ++ Θ0) κb
              ((β ~ abind_tvar) ++ Θ) Hfm Hmap Hinc) as [Hwm Hrest].
  destruct (a_inc_tvar_inv Hrest) as (Ξs & Θ2 & Heq & Hsuf & Hinc').
  assert (HΘ2 : Θ2 = Θ).
  { destruct Ξs as [ | [x b] Ξs' ]; simpl in Heq.
    - inversion Heq; subst; reflexivity.
    - inversion Heq; subst.
      exfalso. apply Hβ.
      repeat rewrite dom_app; simpl; clear; fsetdec. }
  subst Θ2.
  apply a_inc_flex_prefix_build; [ exact Hfm | exact Hmap | | exact Hinc' ].
  rewrite Forall_forall in Hwm, Hfr |- *.
  intros p Hp. destruct (Hwm p Hp) as [Hwfp Hmp].
  split; [ | exact Hmp ].
  eapply a_wf_ptyp_mono_strip_tvar;
    [ exact Hmp | exact Hwfp | apply Hfr; exact Hp ].
Qed.

(* (iii) constraint solving only ever inspects Θ for FLEXIBILITY, so a rigid
   binder in the middle is pure ballast (no ftv side condition needed). *)
Lemma a_solve_cstr_strip_tvar_mid : forall Ξ β Θ0 𝒞 P P',
  (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ P' ->
  (Ξ ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ P'.
Proof.
  intros Ξ β Θ0 𝒞 P P' H.
  eapply a_solve_cstr_ctx_change; [ exact H | | ].
  - intros α Hft; destruct Hft as [Hb | [τ Hb]];
      [ left | right; exists τ ]; analyze_binds Hb.
  - intros P0 Hf; inversion Hf; subst;
      [ eapply a_flex__var | eapply a_flex__var_def ];
      apply binds_weaken_mid; eassumption.
Qed.

(* (iv) partial precision: strip a rigid binder that neither side mentions
   (the [α2 ∈ Δ] form [ad_partial_precise_strengthen_tvar] does not apply —
   here β never enters Δ). *)
Lemma ad_partial_precise_strip_tvar_mid : forall Θf Δ Ψ P ψ,
  Θf ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall β Θ1 Θ2, Θf = Θ1 ++ (β ~ abind_tvar) ++ Θ2 ->
  (forall α τ, binds α (abind_flex_mono_def τ) Θf -> β `notin` ftvar_in_ptyp τ) ->
  β `notin` ftvar_in_pskl P ->
  β `notin` ftvar_in_uskl ψ ->
  (Θ1 ++ Θ2) ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θf Δ Ψ P ψ H; induction H;
    intros β Θ1 Θ2 Heq Hdefs HfrP Hfrψ; subst; simpl in HfrP, Hfrψ.
  - apply ad_ppre__unit; assumption.
  - apply ad_ppre__var; [ assumption | ].
    match goal with Hor : _ \/ a_binds_tvar _ _ |- _ =>
      destruct Hor as [HΔ | Hb]; [ left; exact HΔ | right ] end.
    eapply a_binds_tvar_strip_mid;
      [ eassumption | intro Hc; inversion Hc; subst; clear - HfrP; fsetdec
      | intro Hc; inversion Hc | intros τ0 Hc; inversion Hc ].
  - eapply ad_ppre__arrow;
      [ eapply IHad_partial_precise1;
          [ reflexivity | exact Hdefs | clear - HfrP; fsetdec
          | clear - Hfrψ; fsetdec ]
      | eapply IHad_partial_precise2;
          [ reflexivity | exact Hdefs | clear - HfrP; fsetdec
          | clear - Hfrψ; fsetdec ]
      | assumption ].
  - eapply ad_ppre__forall with (L := L `union` singleton β); [ | eassumption ].
    intros α0 Hα0.
    eapply H0;
      [ clear - Hα0; fsetdec | reflexivity | exact Hdefs | | ].
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α0)) as Hup.
      simpl in Hup. clear - HfrP Hα0 Hup; fsetdec.
    + pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0)) as Hup.
      simpl in Hup. clear - Hfrψ Hα0 Hup; fsetdec.
  - apply ad_ppre__hole; assumption.
  - apply ad_ppre__tophole_remove.
    eapply IHad_partial_precise; [ reflexivity | exact Hdefs | exact HfrP | exact Hfrψ ].
  - eapply ad_ppre__tophole_fill with (L := L `union` singleton β).
    intros α0 Hα0.
    eapply (H0 α0 ltac:(clear - Hα0; fsetdec) β ((α0 ~ abind_tvar) ++ Θ1) Θ2);
      [ reflexivity
      | intros αd τ Hb; eapply Hdefs;
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
          [ discriminate Habs | exact Hb' ]
      | exact HfrP
      | pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α0)) as Hup;
        simpl in Hup; clear - Hfrψ Hα0 Hup; fsetdec ].
  - apply ad_ppre__tophole_keep.
    eapply IHad_partial_precise; [ reflexivity | exact Hdefs | exact HfrP | exact Hfrψ ].
  - (* flex_l: the subject IS the defined variable *)
    assert (Hαβ : α <> β) by (clear - HfrP; fsetdec).
    eapply ad_ppre__flex_l;
      [ eapply binds_strengthen_mid;
          [ eassumption | simpl; clear - Hαβ; fsetdec ]
      | ].
    eapply IHad_partial_precise;
      [ reflexivity | exact Hdefs
      | pose proof (ptyp_to_pskl_ftv τ) as Hft;
        pose proof (Hdefs α τ ltac:(eassumption)) as Hfrτ;
        clear - Hft Hfrτ; fsetdec
      | exact Hfrψ ].
  - (* flex_r: the target IS the defined variable *)
    assert (Hαβ : α <> β) by (clear - Hfrψ; fsetdec).
    eapply ad_ppre__flex_r;
      [ eapply binds_strengthen_mid;
          [ eassumption | simpl; clear - Hαβ; fsetdec ]
      | ].
    eapply IHad_partial_precise;
      [ reflexivity | exact Hdefs | exact HfrP
      | rewrite ftvar_in_uskl_ptyp_to_uskl_syn;
        pose proof (Hdefs α τ ltac:(eassumption)) as Hfrτ;
        clear - Hfrτ; fsetdec ].
Qed.

(* (v) refinement: a Δ-binder may be moved into the aenv as a rigid tvar.
   Needed because the CONSISTENCY's ∀-binder enters Θ while the REFINEMENT's
   (rule [ad_refine_syn__all]) enters Δ; the IH wants both in Θ.  Mirrors
   [a_wf_pskl_delta_to_tvar_mid] (mid-insertion, so the [tophole_fill] rule's
   own Θ-binder can be absorbed into Θ1). *)
Lemma ad_refine_syn_delta_to_tvar_mid : forall Θfull Δ Q Q',
  Θfull ⨟ Δ ⊢ᵣᵃ Q ⊳ Q' ->
  forall α1 Θ1 Θ2 Δ', Θfull = Θ1 ++ Θ2 ->
  Δ [<=] add α1 Δ' ->
  (Θ1 ++ (α1 ~ abind_tvar) ++ Θ2) ⨟ Δ' ⊢ᵣᵃ Q ⊳ Q'.
Proof.
  intros Θfull Δ Q Q' H; induction H; intros α1 Θ1 Θ2 Δ' HeqΘ Hsub; subst.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
    match goal with Hor : _ \/ a_binds_tvar ?α0 _ |- _ =>
      destruct Hor as [HΔ | Hbt];
      [ destruct (α0 == α1) as [-> | Hne];
        [ right; left; unfold binds;
          apply in_or_app; right; left; reflexivity
        | left; clear - HΔ Hsub Hne; fsetdec ]
      | right;
        destruct Hbt as [Hb | [Hb | [τ0 Hb]]];
        [ left | right; left | right; right; exists τ0 ];
        apply binds_weaken; exact Hb ]
    end.
  - apply ad_refine_syn__arrow; eauto.
  - apply ad_refine_syn__all with (L := L).
    intros α Hα.
    apply (H0 α Hα α1 Θ1 Θ2 (add α Δ') eq_refl).
    clear - Hsub; fsetdec.
  - apply ad_refine_syn__hole.
    eapply a_wf_pskl_weaken; [ | eassumption ].
    intros x b Hb; apply binds_weaken; exact Hb.
  - apply ad_refine_syn__tophole_remove; eauto.
  - apply ad_refine_syn__tophole_fill with (L := L).
    intros α Hα.
    apply (H0 α Hα α1 ((α ~ abind_tvar) ++ Θ1) Θ2 Δ' eq_refl Hsub).
  - apply ad_refine_syn__tophole_keep; [ assumption | eauto ].
  - eapply ad_refine_syn__flex_l; [ apply binds_weaken; eassumption | eauto ].
  - eapply ad_refine_syn__flex_r; [ apply binds_weaken; eassumption | eauto ].
Qed.

(* (vi) [msubst_uskl_syn] commutes with opening (mirror of [msubst_pskl_open]):
   every image is a MONOTYPE painting, hence locally closed. *)
Lemma msubst_uskl_syn_open_rec : forall Θ1 ζ Θ R' R0 k,
  ζ ∷ Θ1 ⊑ Θ ->
  msubst_uskl_syn ζ (open_uskl_wrt_uskl_rec k R0 R')
  = open_uskl_wrt_uskl_rec k (msubst_uskl_syn ζ R0) (msubst_uskl_syn ζ R').
Proof.
  intros Θ1 ζ Θ R'; induction R'; intros R0 k Hinc; simpl; f_equal; eauto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - symmetry.
    apply open_uskl_wrt_uskl_rec_degree_uskl_wrt_uskl.
    apply degree_uskl_wrt_uskl_O.
    apply degree_uskl_wrt_uskl_of_lc_uskl.
    apply mono_ptyp_to_uskl_syn_lc.
    eapply a_inc_lookup_mono; exact Hinc.
Qed.

Lemma msubst_uskl_syn_open : forall Θ1 ζ Θ R α,
  ζ ∷ Θ1 ⊑ Θ ->
  α `notin` dom ζ ->
  msubst_uskl_syn ζ (open_uskl_wrt_uskl R (uskl_var_f α))
  = open_uskl_wrt_uskl (msubst_uskl_syn ζ R) (uskl_var_f α).
Proof.
  intros Θ1 ζ Θ R α Hinc Hα.
  unfold open_uskl_wrt_uskl.
  rewrite (msubst_uskl_syn_open_rec R (uskl_var_f α) 0 Hinc).
  simpl. rewrite msubst_lookup_notin by exact Hα.
  reflexivity.
Qed.

(* the ∀-subject's body under κ and [ψa/α], as the consistency rules see it *)
Lemma p6cs_subject_open : forall Θ1 κ Θ ψa α R0 β,
  κ ∷ Θ1 ⊑ Θ ->
  α `notin` dom κ ->
  β `notin` dom κ ->
  β <> α ->
  lc_uskl ψa ->
  subst_bskl_in_uskl ψa α (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))
  = open_uskl_wrt_uskl
      (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R0)) (uskl_var_f β).
Proof.
  intros Θ1 κ Θ ψa α R0 β Hinc Hα Hβ Hne Hlc.
  rewrite (@msubst_uskl_syn_open Θ1 κ Θ R0 β Hinc Hβ).
  rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
    [ reflexivity | auto | exact Hlc ].
Qed.

(* ∀-subject consistency (C-ForallInh / C-ForallSyn), up to the target's
   defined-flex chain.  The two rows are told apart by the TARGET's colour:
   [bskl_all_inh] (inherited ∀ — LE-ForallInh) vs [bskl_all_syn] (synthesised
   ∀, which the refinement can only produce by FILLING a ⊤◇ — LE-ForallSyn). *)
Lemma ad_pat_consis_all_syn_refine_unify : forall Ψs Θ R Q,
  a_wf_aenv Θ ->
  Ψs ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  forall R0, R = uskl_all_syn R0 ->
  forall Δr Ql, Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ Q ->
  exists L Q0,
    (forall α, α `notin` L ->
       Ψs ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ₛᵃ (open_uskl_wrt_uskl R0 (uskl_var_f α))
            ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f α))) /\
    ((Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ (bskl_all_inh Q0)) \/
     (Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ (bskl_all_syn Q0))).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros R0 Heq Δr Ql Href;
    try discriminate Heq.
  - (* __forall_inh_untagged *)
    injection Heq as He; subst.
    exists L, Q; split; [ assumption | left; exact Href ].
  - (* __forall_syn *)
    injection Heq as He; subst.
    exists L, Q; split; [ assumption | right; exact Href ].
  - (* __flex_r *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Href | reflexivity | eassumption ] ].
Qed.

(* the ε-tagged mirror: [uskl_all_etag] subjects (C-ForallInh's tagged row
   splits the index as [Ψ = Ψ0, ε]; the ForallSyn row keeps it). *)
Lemma ad_pat_consis_all_etag_refine_unify : forall Ψs Θ R Q,
  a_wf_aenv Θ ->
  Ψs ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  forall εr R0, R = uskl_all_etag εr R0 ->
  forall Δr Ql, Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ Q ->
  exists L Q0 Ψ0,
    (forall α, α `notin` L ->
       Ψ0 ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ₛᵃ (open_uskl_wrt_uskl R0 (uskl_var_f α))
            ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f α))) /\
    (((Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ (bskl_all_inh Q0)) /\ Ψs [=] add εr Ψ0) \/
     ((Θ ⨟ Δr ⊢ᵣᵃ Ql ⊳ (bskl_all_syn Q0)) /\ Ψs [=] Ψ0)).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros εr R0 Heq Δr Ql Href;
    try discriminate Heq.
  - (* __forall_inh_tagged *)
    injection Heq as He1 He2; subst.
    exists L, Q, Ψ0; split; [ assumption | left; split; assumption ].
  - (* __forall_syn_tagged *)
    injection Heq as He1 He2; subst.
    exists L, Q, Ψ; split;
      [ assumption | right; split; [ exact Href | clear; fsetdec ] ].
  - (* __flex_r *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Href | reflexivity | eassumption ] ].
Qed.

(* ===================================================================== *)
(*  (vii) β-FRESHNESS OF THE COLLECTED CONSTRAINTS.                       *)
(*  LE-ForallInh / LE-UnivGhost1 open the TARGET under the binder, so the *)
(*  rule's single constraint set C must be β-FREE (the paper: we know     *)
(*  β ∉ ftv(Pa) because Pi and C cannot contain β).  That is NOT           *)
(*  syntactic — C's constraints are [eq P0sub] at the α-positions — but it *)
(*  follows semantically: at an α-position the target is what ψa faces,    *)
(*  and ψa is β-free.  The two transports below are the two halves.       *)
(* ===================================================================== *)

(* the variables an aenv's DEFINITIONS can contribute (keys + images) *)
Fixpoint def_ftv (Θ : aenv) : atoms :=
  match Θ with
  | nil => empty
  | (α, abind_flex_mono_def τ) :: Θ' => add α (ftvar_in_ptyp τ `union` def_ftv Θ')
  | _ :: Θ' => def_ftv Θ'
  end.

Lemma def_ftv_binds : forall Θ α τ,
  binds α (abind_flex_mono_def τ) Θ ->
  add α (ftvar_in_ptyp τ) [<=] def_ftv Θ.
Proof.
  induction Θ as [ | [x b] Θ' IH ]; intros α τ Hb; [ inversion Hb | ].
  destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[Heq Heqb] | Hb'].
  - subst. simpl. clear; fsetdec.
  - specialize (IH _ _ Hb'). destruct b; simpl; clear - IH; fsetdec.
Qed.

Lemma def_ftv_dom : forall Θ, a_wf_aenv Θ -> def_ftv Θ [<=] dom Θ.
Proof.
  intros Θ H; induction H; simpl; try (clear - IHa_wf_aenv; fsetdec).
  - clear; fsetdec.
  - pose proof (a_wf_ptyp_ftv_dom H0) as Hf.
    clear - Hf IHa_wf_aenv; fsetdec.
Qed.

Lemma mono_ptyp_to_uskl_syn_tskl : forall τ,
  mono_ptyp τ -> is_tskl (ptyp_to_uskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply is_tskl__unit | apply is_tskl__var
    | apply is_tskl__arrow; assumption ].
Qed.

(* (a) a DECORATED subject's counterpart only mentions the subject's own
   variables and the context's definitions (the [__hole] rule, which invents
   an arbitrary target, needs a PLAIN hole — [is_tskl] has only ⊙̇). *)
Lemma ad_pat_consis_target_ftv : forall Ψ Θ ψ Q,
  Ψ ⨟ Θ ⊢ₛᵃ ψ ∼ Q ->
  a_wf_aenv Θ ->
  is_tskl ψ ->
  ftvar_in_bskl Q [<=] ftvar_in_uskl ψ `union` def_ftv Θ.
Proof.
  intros Ψ Θ ψ Q H; induction H; intros HwfΘ Htsk; simpl in *;
    try solve [ inversion Htsk | clear; fsetdec ].
  - (* arrow *)
    inversion Htsk; subst.
    specialize (IHad_pat_consis1 HwfΘ ltac:(assumption)).
    specialize (IHad_pat_consis2 HwfΘ ltac:(assumption)).
    clear - IHad_pat_consis1 IHad_pat_consis2; fsetdec.
  - (* forall_inh_tagged *)
    inversion Htsk; subst.
    match goal with Ht : forall α, α `notin` ?Lt -> is_tskl _ |- _ =>
      rename Ht into Htb; remember Lt as Lt0 eqn:HeqLt; clear HeqLt end.
    pick fresh α for (L `union` Lt0 `union` dom Θ `union` ftvar_in_bskl Q
                        `union` ftvar_in_uskl R `union` def_ftv Θ).
    specialize (H0 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)
                  (Htb α ltac:(auto))).
    simpl in H0.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    simpl in Hup. clear - H0 Hlo Hup Fr; fsetdec.
  - (* forall_syn_tagged *)
    inversion Htsk; subst.
    match goal with Ht : forall α, α `notin` ?Lt -> is_tskl _ |- _ =>
      rename Ht into Htb; remember Lt as Lt0 eqn:HeqLt; clear HeqLt end.
    pick fresh α for (L `union` Lt0 `union` dom Θ `union` ftvar_in_bskl Q
                        `union` ftvar_in_uskl R `union` def_ftv Θ).
    specialize (H0 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)
                  (Htb α ltac:(auto))).
    simpl in H0.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    simpl in Hup. clear - H0 Hlo Hup Fr; fsetdec.
  - (* topholeg *)
    inversion Htsk; subst.
    specialize (IHad_pat_consis HwfΘ ltac:(assumption)).
    clear - IHad_pat_consis; fsetdec.
  - (* flex_l : the subject is a defined variable — recurse on its monotype *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    specialize (IHad_pat_consis HwfΘ (mono_ptyp_to_uskl_syn_tskl Hmτ)).
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn in IHad_pat_consis.
    pose proof (@def_ftv_binds _ _ _ H) as Hdb.
    clear - IHad_pat_consis Hdb; fsetdec.
  - (* flex_r : the target IS a defined variable *)
    pose proof (@def_ftv_binds _ _ _ H) as Hdb.
    clear - Hdb; fsetdec.
Qed.

(* (b) refinement never invents source variables: a source variable is either
   in the target or a definition variable of the context. *)
Lemma ad_refine_syn_src_ftv : forall Θ Δ Q' Q0,
  Θ ⨟ Δ ⊢ᵣᵃ Q' ⊳ Q0 ->
  a_wf_aenv Θ ->
  ftvar_in_bskl Q' [<=] ftvar_in_bskl Q0 `union` def_ftv Θ.
Proof.
  intros Θ Δ Q' Q0 H; induction H; intros HwfΘ; simpl in *;
    try solve [ clear; fsetdec ].
  - (* arrow *)
    specialize (IHad_refine_syn1 HwfΘ); specialize (IHad_refine_syn2 HwfΘ).
    clear - IHad_refine_syn1 IHad_refine_syn2; fsetdec.
  - (* all *)
    pick fresh α for (L `union` ftvar_in_bskl Q `union` ftvar_in_bskl P
                        `union` def_ftv Θ).
    specialize (H0 α ltac:(auto) HwfΘ).
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f α)) as Hlo.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f α)) as Hup.
    simpl in Hup. clear - H0 Hlo Hup Fr; fsetdec.
  - (* tophole_remove *)
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  - (* tophole_fill *)
    pick fresh α for (L `union` ftvar_in_bskl Q `union` ftvar_in_bskl P
                        `union` dom Θ `union` def_ftv Θ).
    specialize (H0 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)).
    simpl in H0.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper P (bskl_var_f α)) as Hup.
    simpl in Hup. clear - H0 Hup Fr; fsetdec.
  - (* tophole_keep *)
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  - (* flex_l : the source IS a defined variable *)
    pose proof (@def_ftv_binds _ _ _ H) as Hdb. clear - Hdb; fsetdec.
  - (* flex_r : recurse through the definition *)
    specialize (IHad_refine_syn HwfΘ).
    rewrite ftvar_in_bskl_ptyp_syn in IHad_refine_syn.
    pose proof (@def_ftv_binds _ _ _ H) as Hdb.
    clear - IHad_refine_syn Hdb; fsetdec.
Qed.

Lemma msubst_pskl_ftv_dom_lower : forall κ P,
  ftvar_in_pskl P [<=] ftvar_in_pskl (msubst_pskl κ P) `union` dom κ.
Proof.
  intros κ P α Hα.
  destruct (AtomSetProperties.In_dec α (dom κ)) as [Hd | Hd];
    [ clear - Hd; fsetdec | ].
  pose proof (@msubst_pskl_ftv_lower κ P α Hα) as Hlow.
  rewrite msubst_lookup_notin in Hlow by exact Hd.
  simpl in Hlow. clear - Hlow; fsetdec.
Qed.

Lemma ftv_subst_var_keep : forall P β α1 α,
  α `in` ftvar_in_pskl P -> β <> α ->
  α `in` ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f α1) β P).
Proof.
  intros P β α1 α Hin Hne.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower P (pskl_var_f α1) β) as Hlo.
  clear - Hlo Hin Hne; fsetdec.
Qed.

Lemma subst_var_pskl_neq_var : forall P β α1 α,
  P <> pskl_var_f α -> α1 <> α -> β <> α ->
  subst_pskl_in_pskl (pskl_var_f α1) β P <> pskl_var_f α.
Proof.
  intros P β α1 α Hne Hα1 Hβ Hc.
  destruct P; simpl in Hc; try discriminate Hc.
  destruct (α0 == β) as [-> | Hne2];
    [ inversion Hc; congruence | inversion Hc; subst; congruence ].
Qed.

(* (viii) SIMULTANEOUS renaming of a rigid variable on BOTH sides, keeping the
   collected flexibles and constraints — the constraint set is preserved
   exactly because β does not occur in it (see (vii)).  This turns the ONE
   fresh-β instance the IH produces into LE-ForallInh's cofinite family. *)
Lemma a_looksub_lookeq_rename_tvar :
  (forall α m P P' Ξ 𝒞, P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β α1, β <> α -> α1 <> α ->
     β `notin` ftvar_in_cstrs 𝒞 ->
     (subst_pskl_in_pskl (pskl_var_f α1) β P) ≼[ α , m ]
       (subst_pskl_in_pskl (pskl_var_f α1) β P') ⤳ Ξ ⨾ 𝒞) /\
  (forall α P P' Ξ 𝒞, P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β α1, β <> α -> α1 <> α ->
     β `notin` ftvar_in_cstrs 𝒞 ->
     (subst_pskl_in_pskl (pskl_var_f α1) β P) ∼[ α ]
       (subst_pskl_in_pskl (pskl_var_f α1) β P') ⤳ Ξ ⨾ 𝒞).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun α m P P' Ξ 𝒞 _ =>
              forall β α1, β <> α -> α1 <> α ->
              β `notin` ftvar_in_cstrs 𝒞 ->
              (subst_pskl_in_pskl (pskl_var_f α1) β P) ≼[ α , m ]
                (subst_pskl_in_pskl (pskl_var_f α1) β P') ⤳ Ξ ⨾ 𝒞)
           (fun α P P' Ξ 𝒞 _ =>
              forall β α1, β <> α -> α1 <> α ->
              β `notin` ftvar_in_cstrs 𝒞 ->
              (subst_pskl_in_pskl (pskl_var_f α1) β P) ∼[ α ]
                (subst_pskl_in_pskl (pskl_var_f α1) β P') ⤳ Ξ ⨾ 𝒞));
    intros; simpl in *.
  - (* LS-Var *)
    destruct_if; [ exfalso; congruence | ].
    rewrite subst_pskl_in_pskl_fresh_eq;
      [ apply a_looksub__var | clear - H1; simpl in H1; fsetdec ].
  - (* LS-Absent *)
    apply a_looksub__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f α1) β) as Hup.
    simpl in Hup.
    match goal with Hnf : _ `notin` ftvar_in_pskl _ |- _ =>
      clear - Hup Hnf H0; fsetdec end.
  - (* LS-Vacuous *) apply a_looksub__vacuous.
  - (* LS-Check *)
    apply a_looksub__check;
      [ apply subst_var_pskl_neq_var; auto
      | apply guarded_pskl_subst_var; assumption
      | apply guarded_pskl_subst_var; assumption
      | auto ].
  - (* LS-ForallR *)
    apply a_looksub__forall_r with (L := L `union` singleton β).
    intros β1 Hβ1.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ1; fsetdec | apply lc_pskl_var_f ].
    apply H; auto.
  - (* LS-Arrow *)
    match goal with Hc : _ `notin` ftvar_in_cstrs (?Ca ++ ?Cb) |- _ =>
      pose proof (ftvar_in_cstrs_app Ca Cb) as Happ; rename Hc into Hcs end.
    apply a_looksub__arrow;
      [ apply H; auto; clear - Hcs Happ; fsetdec
      | apply H0; auto; clear - Hcs Happ; fsetdec ].
  - (* LS-ForallL *)
    apply a_looksub__forall_l with (L := L `union` singleton β).
    intros β1 Hβ1.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ1; fsetdec | apply lc_pskl_var_f ].
    apply H; auto.
  - (* LS-UnivGhostL *) apply a_looksub__univ_ghost_l; apply H; auto.
  - (* LE-Var *)
    destruct_if; [ exfalso; congruence | ].
    rewrite subst_pskl_in_pskl_fresh_eq;
      [ apply a_lookeq__var | clear - H1; simpl in H1; fsetdec ].
  - (* LE-Absent *)
    apply a_lookeq__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f α1) β) as Hup.
    simpl in Hup.
    match goal with Hnf : _ `notin` ftvar_in_pskl _ |- _ =>
      clear - Hup Hnf H0; fsetdec end.
  - (* LE-Vacuous *) apply a_lookeq__vacuous.
  - (* LE-FlexR *)
    destruct_if.
    + apply a_lookeq__flex_r;
        [ apply subst_var_pskl_neq_var; auto
        | apply ftv_subst_var_keep; auto ].
    + apply a_lookeq__flex_r;
        [ apply subst_var_pskl_neq_var; auto
        | apply ftv_subst_var_keep; auto ].
  - (* LE-Arrow *)
    match goal with Hc : _ `notin` ftvar_in_cstrs (?Ca ++ ?Cb) |- _ =>
      pose proof (ftvar_in_cstrs_app Ca Cb) as Happ; rename Hc into Hcs end.
    apply a_lookeq__arrow;
      [ apply H; auto; clear - Hcs Happ; fsetdec
      | apply H0; auto; clear - Hcs Happ; fsetdec ].
  - (* LE-ForallInh *)
    apply a_lookeq__forall_inh with (L := L `union` singleton β).
    intros β1 Hβ1.
    repeat rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ apply H; auto | clear - Hβ1; fsetdec | apply lc_pskl_var_f
      | clear - Hβ1; fsetdec | apply lc_pskl_var_f ].
  - (* LE-ForallSyn *)
    apply a_lookeq__forall_syn with (L := L `union` singleton β).
    intros β1 Hβ1.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ1; fsetdec | apply lc_pskl_var_f ].
    apply H; auto.
  - (* LE-UnivGhost *) apply a_lookeq__univ_ghost; apply H; auto.
  - (* LE-UnivGhost1 *)
    apply a_lookeq__univ_ghost1 with (L := L `union` singleton β).
    intros β1 Hβ1.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hβ1; fsetdec | apply lc_pskl_var_f ].
    apply H; auto.
  - (* LE-UnivGhost2 *)
    apply a_lookeq__univ_ghost2;
      [ apply guarded_pskl_subst_var; assumption | apply H; auto ].
  - (* LE-UnivGhostR *)
    apply a_lookeq__univ_ghost_r;
      [ apply subst_var_pskl_neq_var; auto
      | apply guarded_pskl_subst_var; assumption
      | apply H; auto ].
Qed.

(* (ix) a GUARDED-HEADED subject forces a guarded counterpart.  Well-formedness
   of P makes every ⊤◇-body guarded, so this refutes the C-UnivGhost2 rows in
   which the ⊤◇ is dropped against a ∀ / ⊤◇ target.  (Mirror of
   [ad_pat_consis_guarded_r], which only covers plain-skeleton subjects.) *)
Definition uskl_guarded_head (R : uskl) : Prop :=
  R = uskl_unit \/ (exists α, R = uskl_var_f α) \/
  (exists R1 R2, R = uskl_arrow R1 R2).

Definition bskl_guarded_head (Q : bskl) : Prop :=
  Q = bskl_unit \/ (exists α, Q = bskl_var_f α) \/
  (exists Q1 Q2, Q = bskl_arrow Q1 Q2).

Lemma ad_pat_consis_guarded_head_target : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q ->
  a_wf_aenv Θ ->
  uskl_guarded_head R ->
  bskl_guarded_head Q.
Proof.
  intros Ψ Θ R Q H; induction H; intros HwfΘ Hgh;
    try solve [ destruct Hgh as [Habs | [[α Habs] | [R1 [R2 Habs]]]];
                discriminate Habs ].
  - left; reflexivity.
  - right; left; eexists; reflexivity.
  - right; right; do 2 eexists; reflexivity.
  - (* flex_l : recurse through the definition (a monotype painting) *)
    apply IHad_pat_consis; [ exact HwfΘ | ].
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct Hmτ; simpl;
      [ left; reflexivity
      | right; left; eexists; reflexivity
      | right; right; do 2 eexists; reflexivity ].
  - (* flex_r : the target IS a variable *)
    right; left; eexists; reflexivity.
Qed.

Lemma guarded_uskl_head : forall R, guarded_uskl R -> uskl_guarded_head R.
Proof.
  intros R H; inversion H;
    [ left | right; left; eexists | right; right; do 2 eexists ]; reflexivity.
Qed.

(* the ⊤◇-body's subject really is guarded-headed, PROVIDED the body is not the
   looked-up variable itself (there the subject is ψa, which may be a ∀ or ⊤̇◇) *)
Lemma p6cs_subject_guarded_head : forall Θ0 κ Θ ψa α R0,
  κ ∷ Θ0 ⊑ Θ ->
  guarded_pskl (uskl_to_pskl R0) ->
  R0 <> uskl_var_f α ->
  α `notin` dom κ ->
  (forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)) ->
  uskl_guarded_head (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R0)).
Proof.
  intros Θ0 κ Θ ψa α R0 Hκ Hg Hne Hακ Hκav.
  destruct R0; simpl in Hg; try solve [ inversion Hg ].
  - left; reflexivity.
  - (* var_f *)
    assert (Hαne : α0 <> α) by (intro Hc; subst; contradiction).
    cbn [msubst_uskl_syn].
    remember (msubst_lookup κ α0) as τ0 eqn:Heqτ0.
    assert (Hmτ : mono_ptyp τ0)
      by (subst τ0; eapply a_inc_lookup_mono; eauto).
    assert (Hαimg : α `notin` ftvar_in_ptyp τ0).
    { subst τ0. intro Hc.
      pose proof (@msubst_lookup_ftv_avoid κ α α0 Hκav Hc) as Heq; congruence. }
    clear Heqτ0.
    destruct Hmτ; simpl in Hαimg |- *;
      [ left; reflexivity
      | match goal with |- context [if ?c then _ else _] => destruct c end;
          [ exfalso; subst; simpl in Hαimg; clear - Hαimg; fsetdec
          | right; left; eexists; reflexivity ]
      | right; right; do 2 eexists; reflexivity ].
  - (* arrow *) right; right; do 2 eexists; cbn; reflexivity.
Qed.

(* ===================================================================== *)
(*  P6-Cs  —  a_lookeq_solve_complete                                      *)
(*                                                                         *)
(*  STATE: every paper case is proved.  The ONLY remaining gap is a single  *)
(*  configuration, hit by three rows of the ⊤◇ case:                        *)
(*                                                                         *)
(*      R = ⊤◇α   (the universal ghost wrapping the LOOKED-UP variable)     *)
(*                                                                         *)
(*  There the consistency subject is [⊤◇ψa] rather than [ψa], so the α-leaf *)
(*  cannot be handed to P6-Cv ([a_solve_eq_complete_var] expects the        *)
(*  subject ψa), and the guarded-headedness argument that refutes the       *)
(*  ghost-dropping rows for every other R0 does not apply (ψa may itself be *)
(*  a ∀ or a ⊤̇◇).  Closing it needs either a ⊤◇-wrapped variant of P6-Cv or *)
(*  a reachability argument for [P = ⊤◇α].                                  *)
(* ===================================================================== *)

Theorem a_lookeq_solve_complete :
  forall n NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α,
  size_uskl R' + size_pskl P0 <= n ->       (* measure: R' recursion + P0 ⊤◇-stripping *)
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->                            (* erase R' = P (R' is κ-FREE, paper-faithful) *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->   (* R' scoped at Θ0 + the lookup var α (wf) *)
  lc_uskl R' ->                             (* R' is a well-formed (locally-closed) skeleton *)
  a_tags_sort NM Ψ' ψa ->                  (* Θ ⊢^N Ψ'{syn ψa} *)
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->  (* S's tags ⊥ ψa's tags Ψ' *)
  Ψi `union` Ψa [<=] Ψ' ->                 (* Ψi, Ψa ⊆ Ψ' *)
  delta_def_fresh Δ Θ ->                   (* paper's implicit Δ-wf (feeds P6-Cv) *)
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->      (* Δ|Θ ⊢ κPi ⊑ᵖ[Ψi] ψa *)
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->   (* consistency index ⊆ R'-tags ∪ Ψa *)
  Ψa [<=] Ψsub ->                          (* ψa's subtree tags ⊆ index *)
  (* subject = (κR)[ψa/α], EXACTLY the paper's form *)
  Ψsub ⨟ Θ ⊢ₛᵃ (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R')) ∼ Q ->
  (* … and that subject is WELL-FORMED (the paper's prose "all inputs are
     well-formed"; erased to a pskl so the existing [a_wf_pskl] can state it —
     ⌊·⌋ˢ maps the dotted ghosts onto the plain ones, and the only content
     used is [a_wf_pskl__tophole]'s GUARDED ghost body).
     ⚠️ WITHOUT this premise the lemma is FALSE.  Counterexample: Θ=Θ0=·,
     κ=·, R' = ⊤◇α (so P = ⊤◇α), ψa = ⊤̇◇⟨⟩, P0 = Pi = ⊤◇⟨⟩, Q = ⊤◇⟨⟩.
     Every other premise holds (consistency by C-UnivGhost2 then C-UnivGhostG;
     refinement by R-UnivGhostKeep; precision by P-UnivGhostKeep), but the
     algorithm is FORCED: LE-UnivGhost ⇒ 𝒞 = [α ≐ ⟨⟩], and SE-GhostGuarded ⇒
     Pa = ⟨⟩, whose precision goal ⟨⟩ ⊑ᵖ ⊤̇◇⟨⟩ has no rule.  The subject there
     is ⊤◇(⊤̇◇⟨⟩) — a ghost over a ghost — which [a_wf_pskl__tophole] (and the
     declarative [d_wf_uskl__tophole]) forbid.
     [paper-external wf side condition — docs/WF-SIDE-CONDITIONS.md] *)
  Θ ⨟ empty ⊢ₚₛᵃ (uskl_to_pskl (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R'))) ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->   (* Θ ⊢ inh(κP0) ⊳ Q *)
  (* κa := ρc ++ κ is a SYNTACTIC extension of κ over the fresh Ξc — a
     provable STRENGTHENING of the paper's [κ ≡ κa] (cf. P6-Cv's κa:=κ).
     It mechanizes the paper's "equivalence of metasubstitutions" step
     (subtyping-proofs.tex refn[16]): msubst (ρc++κ) agrees with msubst κ
     on Θ0-scoped skeletons, so the erase-tie threads under recursion. *)
  exists 𝒞 Ξc Pa κc,
    (P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞) /\                   (* lookeq α P P0 𝒞 Ξc *)
    (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Pa /\                 (* solve 𝒞 Pi Pa *)
    (Ξc ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa /\               (* Θ0,Ξc ⊢ Pa *)
    a_wf_aenv (Ξc ++ Θ0) /\                      (* Ξc collected ⇒ context wf *)
    α `notin` dom Ξc /\                          (* α not among collected flexibles *)
    keys κc = keys Ξc /\  (* ρc's keys align with Ξc *)
    (* every image ρc assigns is built from ψa (the only source of witnesses
       is the flexible-P0 row, whose witness τψ satisfies ψa = syn τψ), so a
       binder FRESH for ψa is fresh for the images — this is what lets the
       ∀ rows strip their binder out of the [a_inc] conclusion. *)
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (* the collected CONSTRAINTS mention only ψa's variables, the collected
       flexibles, κ's domain and the context's definitions — never a fresh
       ∀-binder.  This is what makes LE-ForallInh / LE-UnivGhost1 (which open
       the TARGET under the binder) applicable with a single 𝒞. *)
    ftvar_in_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc `union` dom κ
                          `union` def_ftv Θ /\
    (κc ++ κ) ∷ (Ξc ++ Θ0) ⊑ Θ /\               (* κa : Θ0,Ξc ⊑ Θ *)
    a_inc_equiv Θ0 κ κ Θ /\                      (* κ ≡ κa on Θ0: κa|Θ0 = κ (ρc fresh) *)
    (forall α0, α0 `in` dom κc -> α0 `notin` add α (dom Θ0 `union` dom Θ)) /\   (* ρc fresh w.r.t. Θ0, α *)
    Θ ⨟ Δ ⊢ (msubst_pskl (κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
Proof.
  induction n as [ | n IHn ];
    intros NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α Hn.
  { exfalso. pose proof (size_uskl_min R'). pose proof (size_pskl_min P0). lia. }
  intros HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 HeraseR HscopeS HlcS Htags Hdisj Hsub
         Hdfresh Hpre HΨs1 HΨs2 Hconsis HwfSub Hrefine.
  (* ---------------------------------------------------------------- *)
  (* Special case P0 = □ (LE-Vacuous): refinement inversion gives Q   *)
  (* synthesised ⇒ Ψsub = ∅ ⇒ Ψa = ∅; take 𝒞=·, Ξc=·, Pa=Pi, κa=κ.    *)
  (* ---------------------------------------------------------------- *)
  destruct (pskl_hole_dec P0) as [-> | HP0nh].
  { (* P0 = □ *)
    simpl in Hrefine.  (* msubst κ □ = □ ; inh □ = bskl_hole *)
    assert (Hsk : is_sskl Q)
      by (eapply ad_refine_syn_hole_sskl; [ exact Hrefine | reflexivity ]).
    assert (HΨe : Ψsub [=] empty)
      by (eapply ad_pat_consis_sskl_tags; [ exact Hconsis | exact HwfΘ | exact Hsk ]).
    assert (HΨa0 : Ψa [=] empty) by (clear - HΨs2 HΨe; fsetdec).
    exists nil, nil, Pi, (@nil (atom * ptyp)).
    repeat split.
    - apply a_lookeq__vacuous.
    - simpl. apply a_solve_cstr__empty.
    - simpl. exact HwfPi.
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    - (* ftv 𝒞 : no constraints *) simpl; clear; fsetdec.
    - simpl. exact Hκ.
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - simpl. eapply ad_partial_precise_psi_cong; [ exact Hpre | clear - HΨa0; fsetdec ]. }
  (* ---------------------------------------------------------------- *)
  (* Special case P = α (LE-Var): R = var α ⇒ subject = ψa; delegate   *)
  (* to P6-Cv (a_solve_eq_complete_var) with the identity ρ.           *)
  (* ---------------------------------------------------------------- *)
  destruct (pskl_var_dec P α) as [-> | HPnα].
  { (* P = α *)
    assert (Hlk : msubst_lookup κ α = ptyp_var_f α).
    { apply msubst_lookup_notin_dom.
      intro Hc. apply (a_inc_dom_sub Hκ) in Hc. contradiction. }
    (* ⌊R'⌋ = P = var α ⇒ R' = uskl_var α *)
    assert (HR : R' = uskl_var_f α).
    { destruct R'; simpl in HeraseR; try discriminate HeraseR.
      injection HeraseR as ->. reflexivity. }
    subst R'.
    (* subject = (κ (var α))[ψa/α] = ψa *)
    assert (Hms : msubst_uskl_syn κ (uskl_var_f α) = uskl_var_f α)
      by (cbn; rewrite Hlk; apply ptyp_to_uskl_syn_var).
    rewrite Hms in Hconsis.
    assert (Hsubj : subst_bskl_in_uskl ψa α (uskl_var_f α) = ψa).
    { cbn. match goal with |- context [if ?c then _ else _] => destruct c end;
        [ reflexivity | contradiction ]. }
    rewrite Hsubj in Hconsis.
    cbn in HΨs1.        (* ftag_in_uskl (uskl_var_f α) = empty *)
    assert (Hlcψa : lc_uskl ψa) by (apply is_tskl_lc; inversion Htags; assumption).
    assert (Hcv : exists Pa, Θ0 ⊢ₑ Pi ∼ P0 ⤳ Pa /\
                    Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa).
    { eapply a_solve_eq_complete_var
        with (Δρ := empty) (Ψρ := empty) (ψsub := ψa) (Ψsub := Ψsub);
      [ exact HwfΘ | exact HwfΘ0 | exact HwfPi | exact HwfP0 | exact Hκ
      | apply urho__refl; [ exact Hlcψa | clear; fsetdec ]
      | exact Htags | exact Hsub | clear; fsetdec
      | unfold rho_fresh; intros α0 Hα0; clear - Hα0; exfalso; fsetdec
      | clear; fsetdec
      | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
      | exact Hdfresh
      | apply fa_clean; clear; fsetdec
      | exact Hpre
      | clear - HΨs1; fsetdec
      | exact HΨs2 | exact Hconsis | exact Hrefine ]. }
    destruct Hcv as (Pa & Hsolve & Hprec).
    exists (a_cstr_eq P0 :: nil), nil, Pa, (@nil (atom * ptyp)).
    repeat split.
    - apply a_lookeq__var.
    - simpl. eapply a_solve_cstr__eq; [ exact Hsolve | apply a_solve_cstr__empty ].
    - simpl. eapply a_solve_eq_wf; [ exact Hsolve | exact HwfPi | exact HwfP0 ].
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    - (* ftv 𝒞 : the ONE constraint is [eq P0]; κP0 refines to Q, and Q is what
         the (β-free) instantiation ψa faces *)
      simpl.
      pose proof (ad_refine_syn_src_ftv Hrefine HwfΘ) as Hrf.
      rewrite ftvar_in_bskl_inh in Hrf.
      pose proof (ad_pat_consis_target_ftv Hconsis HwfΘ
                    ltac:(inversion Htags; assumption)) as Hcf.
      pose proof (msubst_pskl_ftv_dom_lower κ P0) as Hlow.
      clear - Hrf Hcf Hlow; fsetdec.
    - simpl. exact Hκ.
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - simpl. exact Hprec. }
  (* ---------------------------------------------------------------- *)
  (* Special case α ∉ ftv P (LE-Absent): subject = κR (ψa absent) ⇒    *)
  (* Ψsub ⊆ ftag(κR) = ftag R', and Ψa ⊆ Ψsub while Ψa ⊆ Ψ' ⊥ ftag R' ⇒ *)
  (* Ψa = ∅.                                                           *)
  (* ---------------------------------------------------------------- *)
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P)) as [Hin | Hnin].
  2:{ (* α ∉ ftv P *)
    assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
    { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
      clear - HαΘ Hb; fsetdec. }
    assert (HαMS : α `notin` ftvar_in_uskl (msubst_uskl_syn κ R')).
    { rewrite <- ftvar_in_pskl_uskl_to_pskl. rewrite uskl_to_pskl_msubst_uskl_syn.
      rewrite HeraseR. apply msubst_pskl_ftv_avoid; [ exact Hκav | exact Hnin ]. }
    rewrite (subst_bskl_in_uskl_fresh_eq (msubst_uskl_syn κ R') ψa α HαMS) in Hconsis.
    assert (HΨsR : Ψsub [<=] ftag_in_uskl (msubst_uskl_syn κ R'))
      by (apply (ad_pat_consis_ftag_sub Hconsis)).
    rewrite ftag_in_uskl_msubst_uskl_syn in HΨsR.
    assert (HΨa0 : Ψa [=] empty) by (clear - HΨs2 HΨsR Hdisj Hsub; fsetdec).
    exists nil, nil, Pi, (@nil (atom * ptyp)).
    repeat split.
    - apply a_lookeq__absent; exact Hnin.
    - simpl. apply a_solve_cstr__empty.
    - simpl. exact HwfPi.
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    - (* ftv 𝒞 : no constraints *) simpl; clear; fsetdec.
    - simpl. exact Hκ.
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - simpl. eapply ad_partial_precise_psi_cong; [ exact Hpre | clear - HΨa0; fsetdec ]. }
  (* ---------------------------------------------------------------- *)
  (* Main induction: P0≠□, P≠α, α∈ftv P.  Case on S's shape (κ and     *)
  (* [ψa/α] distribute); α∈ftv R' rules out the leaf shapes, R'=var α    *)
  (* forces P=α (contra HPnα), leaving the 5 compound congruence cases.*)
  (* ---------------------------------------------------------------- *)
  assert (Hακdom : α `notin` dom κ)
    by (intro Hc; apply (a_inc_dom_sub Hκ) in Hc; contradiction).
  assert (Hκav : forall p, In p κ -> α `notin` ftvar_in_ptyp (snd p)).
  { intros p Hp. pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb.
    clear - HαΘ Hb; fsetdec. }
  assert (HαR : α `in` ftvar_in_uskl R').
  { rewrite <- HeraseR in Hin. rewrite ftvar_in_pskl_uskl_to_pskl in Hin. exact Hin. }
  destruct R' as [ | rn | β | Ra Rb | R0 | εr R0 | | R0 | | R0 ];
    simpl in HαR.
  - (* R' = unit : α ∈ ∅ absurd *) clear - HαR; fsetdec.
  - (* R' = var_b : α ∈ ∅ absurd *) clear - HαR; fsetdec.
  - (* R' = var_f β : α = β ⇒ R' = var α ⇒ P = α, contra HPnα *)
    assert (β = α) by (clear - HαR; fsetdec); subst β.
    simpl in HeraseR. contradiction (HPnα (eq_sym HeraseR)).
  - (* R' = arrow Ra Rb : LE-Arrow (P0-grid + sequential solve) *)
    pose proof Hconsis as Hcons0.  (* keep a FOLDED copy for the ⊤◇-P0 recursion *)
    cbn [msubst_uskl_syn subst_bskl_in_uskl] in Hconsis.
    assert (Hsza : size_uskl Ra <= n) by (cbn in Hn; lia).
    assert (Hszb : size_uskl Rb <= n) by (cbn in Hn; lia).
    destruct (lc_uskl_arrow_inv HlcS) as [HlcSa HlcSb].
    (* P is FORCED to the arrow shape by the erase-tie *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    cbn [msubst_uskl_syn subst_bskl_in_uskl uskl_to_pskl] in HwfSub.
    destruct (a_wf_pskl_arrow_inv HwfSub) as [HwfSubA HwfSubB].
    (* Consistency inversion would give TWO branches — __arrow (Q = Q1→Q2) and
       __flex_r (Q a DEFINED flex var, whose definition chain ends at an arrow).
       [ad_pat_consis_arrow_refine_unify] walks that chain on both the
       consistency and the refinement side, so we get ONE continuation with
       [Q := bskl_arrow Q1 Q2]. *)
    destruct (ad_pat_consis_arrow_refine_unify HwfΘ Hconsis eq_refl Hrefine)
      as (Ψ1 & Ψ2 & Q1 & Q2 & H6 & H1 & H4 & Href0 & Hcons0').
    clear Hconsis Hrefine Hcons0.
    rename Href0 into Hrefine.
    assert (Hcons0 : Ψsub ⨟ Θ ⊢ₛᵃ
              (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ (uskl_arrow Ra Rb)))
              ∼ (bskl_arrow Q1 Q2))
      by (cbn [msubst_uskl_syn subst_bskl_in_uskl]; exact Hcons0').
    clear Hcons0'.
    + (* Q = bskl_arrow Q1 Q2.  Dispatch the P0-grid. *)
      destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
      * (* P0 = unit : refinement bskl_unit ⊳ arrow — absurd *)
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine; inversion Hrefine.
      * (* P0 = var_b : refinement bskl_var_b ⊳ arrow — absurd *)
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine; inversion Hrefine.
      * (* P0 = var_f β0 : FLEX-P0 → LE-FlexR *)
        (* β0 is a_binds_tvar in Θ0.  Rigid ⇒ refinement bskl_var β0 ⊳ arrow
           is absurd; flexible ⇒ κβ0 is a monotype, so the counterpart Q is
           mono-ish, which (via the ψa-mono extraction) forces ψa itself to be
           a mono paint [ptyp_to_uskl_syn τψ].  Then LE-FlexR emits a fresh α1,
           the solve returns α1 (or Pi if Pi is a variable), and κa(α1) := τψ
           makes the precision hold by reflexivity of mono-paint precision. *)
        assert (Hbt0 : a_binds_tvar β0 Θ0).
        { inversion HwfP0; subst.
          match goal with H : _ \/ a_binds_tvar β0 _ |- _ =>
            destruct H as [Hemp | Hbt]; [ clear - Hemp; fsetdec | exact Hbt ] end. }
        destruct Hbt0 as [Hrig | Hflx].
        { (* rigid β0 : refinement-absurd *)
          exfalso.
          assert (Hmid : msubst_pskl κ (pskl_var_f β0) = pskl_var_f β0)
            by (eapply msubst_pskl_tvar_id; eauto).
          rewrite Hmid in Hrefine; cbn [pskl_to_bskl_inh] in Hrefine.
          eapply ad_refine_syn_rigid_var_arrow_absurd;
            [ exact HwfΘ | eapply a_inc_binds_tvar; eauto | exact Hrefine ]. }
        (* flexible β0 : κβ0 = τ0 mono, wf in Θ *)
        set (τ0 := msubst_lookup κ β0) in *.
        assert (Hτ0mono : mono_ptyp τ0) by (eapply a_inc_lookup_mono; eauto).
        assert (Hτ0wf : a_wf_ptyp Θ τ0)
          by (eapply a_inc_lookup_wf;
                [ exact Hκ | exact HwfΘ0 | right; exact Hflx ]).
        assert (Hmsβ : msubst_pskl κ (pskl_var_f β0) = ptyp_to_pskl τ0)
          by reflexivity.
        rewrite Hmsβ in Hrefine.
        rewrite (ptyp_to_bskl_inh_syn_eq Hτ0mono) in Hrefine.
        (* Q = arrow Q1 Q2 is mono-ish *)
        assert (Hmi : bskl_monoish (bskl_arrow Q1 Q2))
          by (eapply ad_refine_mono_paint_rhs_monoish;
                [ exact HwfΘ | exact Hrefine | reflexivity | exact Hτ0mono ]).
        (* ψa is a mono paint *)
        assert (Htskψa : is_tskl ψa) by (inversion Htags; subst; assumption).
        assert (HαT : α `in` ftvar_in_uskl (msubst_uskl_syn κ (uskl_arrow Ra Rb)))
          by (apply ftvar_in_uskl_msubst_uskl_syn_notin_dom;
                [ exact Hακdom | simpl; exact HαR ]).
        destruct (@ad_pat_consis_subst_psia_mono Ψsub Θ
                    (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ (uskl_arrow Ra Rb)))
                    (bskl_arrow Q1 Q2) Hcons0 HwfΘ Hmi
                    (msubst_uskl_syn κ (uskl_arrow Ra Rb)) ψa α eq_refl Htskψa HαT)
          as (τψ & Hτψmono & Heqψ & Hτψwf).
        (* ψa mono ⇒ Ψ' = ∅ ⇒ Ψi = Ψa = ∅ *)
        assert (HΨ'e : Ψ' [=] empty).
        { pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as HΨ't.
          rewrite Heqψ in HΨ't. rewrite ftag_in_uskl_ptyp_syn in HΨ't.
          exact HΨ't. }
        assert (HΨie : Ψi [=] empty) by (clear - Hsub HΨ'e; fsetdec).
        assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
        (* fresh α1 for the LE-FlexR payload *)
        pick fresh α1 for
          (add α (dom Θ0 `union` dom Θ) `union` dom Θ `union` dom κ `union` ftvar_in_pskl Pi).
        assert (Hγdom0 : α1 `notin` dom Θ0) by auto.
        (* Pa and the three Pa-dependent facts (solve / wf / precision) *)
        assert (Hbγ : binds α1 abind_flex_mono (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0))
          by (simpl_env; auto).
        assert (HPa : exists Pa,
          (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0) ⊢ₑ Pi ∼ (pskl_var_f α1) ⤳ Pa /\
          (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa /\
          Θ ⨟ Δ ⊢ msubst_pskl ((α1, τψ) :: κ) Pa ⊑ᵖ[ Ψi `union` Ψa ] ψa).
        { (* the SE-FlexR (Pa := α1) proof, shared by the non-variable Pi shapes *)
          assert (Hflexpa :
            (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0) ⨟ empty ⊢ₚₛᵃ (pskl_var_f α1) /\
            Θ ⨟ Δ ⊢ msubst_pskl ((α1, τψ) :: κ) (pskl_var_f α1)
                 ⊑ᵖ[ Ψi `union` Ψa ] ψa).
          { split.
            - apply a_wf_pskl__var; right; right; left; exact Hbγ.
            - replace (msubst_pskl ((α1, τψ) :: κ) (pskl_var_f α1))
                with (ptyp_to_pskl τψ)
                by (cbn [msubst_pskl msubst_lookup];
                    match goal with |- context [if ?c then _ else _] => destruct c end;
                    [ reflexivity | contradiction ]).
              rewrite Heqψ.
              eapply ad_partial_precise_psi_cong;
                [ apply ad_ppre_mono_paint_refl; [ exact Hτψwf | exact Hτψmono ]
                | clear - HΨie HΨae; fsetdec ]. }
          assert (Hlcpi : lc_pskl Pi) by (eapply a_wf_pskl_lc; exact HwfPi).
          destruct Pi as [ | nbi | α0 | Pi1 Pi2 | Pib | | Pit ].
          - (* unit *) exists (pskl_var_f α1); split;
              [ apply a_solve_eq__flex_r;
                  [ left; exact Hbγ | split; [ exact Hlcpi | intros Hf; inversion Hf ] ]
              | exact Hflexpa ].
          - (* var_b : not wf *) inversion HwfPi.
          - (* var_f α0 : SE-Var, Pa := α0 *)
            exists (pskl_var_f α0); split; [ apply a_solve_eq__var | ].
            assert (HXbt : a_binds_tvar α0 Θ0).
            { inversion HwfPi; subst.
              match goal with H : _ \/ a_binds_tvar α0 _ |- _ =>
                destruct H as [Hemp | Hbt]; [ clear - Hemp; fsetdec | exact Hbt ] end. }
            assert (HXdom : α0 `in` dom Θ0)
              by (destruct HXbt as [Hb | [Hb | [τx Hb]]];
                    apply binds_In in Hb; exact Hb).
            assert (Hα0γ : α0 <> α1) by (intro Hc; subst; auto).
            split.
            + apply a_wf_pskl_weaken with (Θ := Θ0);
                [ intros x b Hb; apply binds_app_3; exact Hb | exact HwfPi ].
            + replace (msubst_pskl ((α1, τψ) :: κ) (pskl_var_f α0))
                with (msubst_pskl κ (pskl_var_f α0))
                by (cbn [msubst_pskl msubst_lookup];
                    match goal with |- context [if ?c then _ else _] => destruct c end;
                    [ contradiction | reflexivity ]).
              eapply ad_partial_precise_psi_cong;
                [ exact Hpre | clear - HΨae; fsetdec ].
          - (* arrow : SE-FlexR *)
            exists (pskl_var_f α1); split;
              [ apply a_solve_eq__flex_r;
                  [ left; exact Hbγ | split; [ exact Hlcpi | intros Hf; inversion Hf ] ]
              | exact Hflexpa ].
          - (* all_syn : SE-FlexR *)
            exists (pskl_var_f α1); split;
              [ apply a_solve_eq__flex_r;
                  [ left; exact Hbγ | split; [ exact Hlcpi | intros Hf; inversion Hf ] ]
              | exact Hflexpa ].
          - (* hole : SE-FlexR *)
            exists (pskl_var_f α1); split;
              [ apply a_solve_eq__flex_r;
                  [ left; exact Hbγ | split; [ exact Hlcpi | intros Hf; inversion Hf ] ]
              | exact Hflexpa ].
          - (* tophole : SE-FlexR *)
            exists (pskl_var_f α1); split;
              [ apply a_solve_eq__flex_r;
                  [ left; exact Hbγ | split; [ exact Hlcpi | intros Hf; inversion Hf ] ]
              | exact Hflexpa ]. }
        destruct HPa as (Pa & Hsolve_eq & HwfPa & Hprec).
        exists (a_cstr_eq (pskl_var_f α1) :: nil),
               ((α1 ~ abind_flex_mono) ++ nil), Pa, ((α1, τψ) :: nil).
        repeat split.
        -- (* a_lookeq : LE-FlexR *)
           apply a_lookeq__flex_r; [ exact HPnα | exact Hin ].
        -- (* solve *)
           eapply a_solve_cstr__eq; [ exact Hsolve_eq | apply a_solve_cstr__empty ].
        -- (* wf Pa *) exact HwfPa.
        -- (* a_wf_aenv (Ξc ++ Θ0) *)
           simpl_env. apply a_wf_aenv__flex; [ exact Hγdom0 | exact HwfΘ0 ].
        -- (* α ∉ dom Ξc *) simpl; clear - Fr; fsetdec.
        (* keys ρc = keys Ξc : auto-closed by [repeat split] (eq_refl) *)
        -- (* ρc images come from ψa : here ψa IS the paint of τψ *)
           apply Forall_cons; [ | apply Forall_nil ].
           simpl. rewrite Heqψ. rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
           clear; fsetdec.
        -- (* ftv 𝒞 : the only constraint is [eq α1], and α1 ∈ dom Ξc *)
           simpl; clear; fsetdec.
        -- (* a_inc *)
           simpl_env. apply a_inc__flex; [ exact Hκ | exact Hτψwf | exact Hτψmono ].
        -- (* a_inc_equiv Θ0 κ κ Θ *) apply a_inc_equiv_refl; exact Hκ.
        -- (* ρc fresh *)
           intros α0 Hα0; simpl in Hα0.
           assert (α0 = α1) by (clear - Hα0; fsetdec); subst α0.
           clear - Fr; fsetdec.
        -- (* precision *) exact Hprec.
      * (* P0 = arrow P01 P02 : MAIN → LE-Arrow + sequential solve *)
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        destruct (ad_refine_arrow_arrow_inv Hrefine) as [Href1 Href2].
        destruct (a_wf_pskl_arrow_inv HwfP0) as [HwfP01 HwfP02].
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
        (* --- tag algebra: Ψa = (Ψ1∩Ψ') ∪ (Ψ2∩Ψ') --- *)
        assert (HΨa : Ψa [=] union (Ψ1 ∩ Ψ') (Ψ2 ∩ Ψ'))
          by (clear - HΨs1 HΨs2 Hsub H6 Hdisj; fsetdec).
        assert (HΨ1sub : Ψ1 [<=] union (ftag_in_uskl Ra) Ψ').
        { pose proof (ad_pat_consis_ftag_sub H1) as Hf1.
          pose proof (ftag_in_uskl_subst_bskl_in_uskl ψa α (msubst_uskl_syn κ Ra)) as Hb1.
          pose proof (ftag_in_uskl_msubst_uskl_syn κ Ra) as Hm1.
          clear - Hf1 Hb1 Hm1 Hψatag; fsetdec. }
        assert (HΨ2sub : Ψ2 [<=] union (ftag_in_uskl Rb) Ψ').
        { pose proof (ad_pat_consis_ftag_sub H4) as Hf2.
          pose proof (ftag_in_uskl_subst_bskl_in_uskl ψa α (msubst_uskl_syn κ Rb)) as Hb2.
          pose proof (ftag_in_uskl_msubst_uskl_syn κ Rb) as Hm2.
          clear - Hf2 Hb2 Hm2 Hψatag; fsetdec. }
        assert (HscopeSa : ftvar_in_uskl Ra [<=] add α (dom Θ0 `union` dom Θ))
          by (clear - HscopeS; simpl in HscopeS; fsetdec).
        assert (HscopeSb : ftvar_in_uskl Rb [<=] add α (dom Θ0 `union` dom Θ))
          by (clear - HscopeS; simpl in HscopeS; fsetdec).
        assert (HdisjSa : (ftag_in_uskl Ra) ∩ Ψ' [=] empty)
          by (clear - Hdisj; simpl in Hdisj; fsetdec).
        assert (HdisjSb : (ftag_in_uskl Rb) ∩ Ψ' [=] empty)
          by (clear - Hdisj; simpl in Hdisj; fsetdec).
        assert (Hml : size_uskl Ra + size_pskl P01 <= n) by (cbn in Hn; lia).
        assert (Hmr : size_uskl Rb + size_pskl P02 <= n) by (cbn in Hn; lia).
        assert (HsubL : union Ψi (Ψ1 ∩ Ψ') [<=] Ψ')
          by (clear - Hsub; fsetdec).
        assert (HΨs1L : Ψ1 [<=] union (ftag_in_uskl Ra) (Ψ1 ∩ Ψ'))
          by (clear - HΨ1sub; fsetdec).
        assert (HΨs2L : Ψ1 ∩ Ψ' [<=] Ψ1) by (clear; fsetdec).
        (* --- LEFT IH on Ra / P01 --- *)
        edestruct (IHn NM Θ0 Θ κ Δ Ψ' Ψi (Ψ1 ∩ Ψ') Ψ1 ψa Q1
                     (uskl_to_pskl Ra) P01 Pi Ra α
                     Hml HwfΘ HwfΘ0 HwfP01 HwfPi Hκ HαΘ HαΘ0 eq_refl
                     HscopeSa HlcSa Htags HdisjSa HsubL Hdfresh Hpre HΨs1L HΨs2L H1 HwfSubA Href1)
          as (C1 & Ξc1 & Pa1 & κc1 & HLK1 & HSolve1 & HwfPa1 & HwfΞ1 & HαΞ1
                & Hmap1 & Himg1 & HftvC1 & Hinc1 & Hinceq1 & Hκf1 & Hpre1).
        (* --- transports for the RIGHT IH (κ → ρc1 ++ κ) --- *)
        assert (Htr_c : msubst_uskl_syn (κc1 ++ κ) Rb = msubst_uskl_syn κ Rb).
        { apply msubst_uskl_syn_prepend_fresh. intros α0 Hα0.
          specialize (Hκf1 α0 Hα0). clear - Hκf1 HscopeSb; fsetdec. }
        assert (Htr_r : msubst_pskl (κc1 ++ κ) P02 = msubst_pskl κ P02).
        { apply msubst_pskl_prepend_fresh. intros α0 Hα0.
          specialize (Hκf1 α0 Hα0).
          pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
          clear - Hκf1 Hfd; fsetdec. }
        assert (HwfSubB' : Θ ⨟ empty ⊢ₚₛᵃ
                  (uskl_to_pskl (subst_bskl_in_uskl ψa α
                                   (msubst_uskl_syn (κc1 ++ κ) Rb))))
          by (rewrite Htr_c; exact HwfSubB).
        rewrite <- Htr_c in H4.
        rewrite <- Htr_r in Href2.
        assert (Hαr : α `notin` dom (Ξc1 ++ Θ0))
          by (rewrite dom_app; clear - HαΞ1 HαΘ0; fsetdec).
        assert (HscopeSbR : ftvar_in_uskl Rb [<=] add α (dom (Ξc1 ++ Θ0) `union` dom Θ))
          by (rewrite dom_app; clear - HscopeSb; fsetdec).
        assert (HsubR : union (union Ψi (Ψ1 ∩ Ψ'))
                              (Ψ2 ∩ Ψ') [<=] Ψ')
          by (clear - Hsub; fsetdec).
        assert (HΨs1R : Ψ2 [<=] union (ftag_in_uskl Rb) (Ψ2 ∩ Ψ'))
          by (clear - HΨ2sub; fsetdec).
        assert (HΨs2R : Ψ2 ∩ Ψ' [<=] Ψ2) by (clear; fsetdec).
        assert (HwfP02R : (Ξc1 ++ Θ0) ⨟ empty ⊢ₚₛᵃ P02)
          by (eapply a_wf_pskl_weaken; [ intros x b Hb; apply binds_app_3; exact Hb
                                       | exact HwfP02 ]).
        (* --- RIGHT IH on Rb / P02, at [Ξc1 ++ Θ0] with [ρc1 ++ κ] --- *)
        edestruct (IHn NM (Ξc1 ++ Θ0) Θ (κc1 ++ κ) Δ Ψ'
                     (union Ψi (Ψ1 ∩ Ψ')) (Ψ2 ∩ Ψ')
                     Ψ2 ψa Q2 (uskl_to_pskl Rb) P02 Pa1 Rb α
                     Hmr HwfΘ HwfΞ1 HwfP02R HwfPa1 Hinc1 HαΘ Hαr eq_refl
                     HscopeSbR HlcSb Htags HdisjSb HsubR Hdfresh Hpre1 HΨs1R HΨs2R H4 HwfSubB' Href2)
          as (C2 & Ξc2 & Pa2 & κc2 & HLK2 & HSolve2 & HwfPa2 & HwfΞ2 & HαΞ2
                & Hmap2 & Himg2 & HftvC2 & Hinc2 & Hinceq2 & Hκf2 & Hpre2).
        (* --- ASSEMBLY --- witnesses: 𝒞 := C1++C2, Ξc := Ξc1++Ξc2 (forced by
           LE-Arrow, which pairs Ξc1++Ξc2 with C1++C2), Pa := Pa2,
           ρc := ρc1++ρc2.  All the pieces are in scope:
             HLK1/HLK2, HSolve1 (@ Ξc1++Θ0), HSolve2 (@ Ξc2++Ξc1++Θ0),
             HwfPa2/HwfΞ2 (@ Ξc2++Ξc1++Θ0), Hinc2 (@ Ξc2++Ξc1++Θ0),
             Hinceq1/Hinceq2, Hρf1/Hρf2, Hpre2 (@ (Ψi∪Ψa1)∪Ψa2), HΨa.
           DIRECT conjuncts (no reorder): a_lookeq (a_lookeq__arrow HLK1 HLK2),
             α∉dom (dom_app+HαΞ1/HαΞ2), ρc-fresh (dom_app+Hρf1/Hρf2).
           REORDER conjuncts (need a homogeneous-flex_mono kit, since Ξc1/Ξc2
           are all abind_flex_mono and pairwise+Θ0-disjoint — TODO next session):
             - solve  : a_solve_cstr_app (C1 eq-only via a_lookeq_cstr_eq HLK1);
                        HSolve1 weakened (insert Ξc2 mid) + HSolve2 reordered
                        (Ξc2++Ξc1 → Ξc1++Ξc2), both via a NEW a_solve_cstr
                        ctx-move (binds-preserving; a_solve_sub_eq_ctx_change
                        does NOT cover the insertion direction, so a direct
                        fresh-flex-prefix weakening lemma is needed for the
                        SE-FlexR a_non_flex leg).
             - wf Pa2 / a_wf_aenv : reorder (Ξc2++Ξc1 → Ξc1++Ξc2), binds-based.
             - a_inc  : reorder Hinc2 (extract Ξc2 then Ξc1 as wf-mono images,
                        re-prepend in Ξc1,Ξc2 order onto Hκ) — a_inc flex-prefix
                        extract/prepend lemmas.
             - a_inc_equiv : a_inc_equiv Θ0 κ (ρc1++ρc2++κ) Θ from Hinceq1 by a
                        "prepend-fresh (ρc2 ∉ Θ0) preserves inc_equiv on Θ0"
                        step (ρc2's keys are invisible to a_inc_equiv over Θ0).
             - precision : Hpre2 + msubst reorder (ρc1++ρc2 ≡ ρc2++ρc1 on
                        disjoint domains, as msubst FUNCTIONS) + psi_cong via HΨa
                        ((Ψi∪Ψa1)∪Ψa2 [=] Ψi∪Ψa). *)
        pose proof (a_lookeq_all_flex_mono HLK1) as HfmΞ1.
        pose proof (a_lookeq_all_flex_mono HLK2) as HfmΞ2.
        destruct (@a_inc_flex_prefix_split Ξc1 κc1 Θ0 κ Θ HfmΞ1 Hmap1 Hinc1)
          as [Hwm1 _].
        destruct (@a_inc_flex_prefix_split Ξc2 κc2 (Ξc1 ++ Θ0) (κc1 ++ κ) Θ
                    HfmΞ2 Hmap2 Hinc2) as [Hwm2 _].
        pose proof (@keys_eq_dom _ _ κc1 Ξc1 Hmap1) as Hd1.  (* dom ρc1 [=] dom Ξc1 *)
        pose proof (@keys_eq_dom _ _ κc2 Ξc2 Hmap2) as Hd2.  (* dom ρc2 [=] dom Ξc2 *)
        assert (Hmapc : keys (κc1 ++ κc2) = keys (Ξc1 ++ Ξc2)).
        { rewrite !keys_app; rewrite Hmap1, Hmap2; reflexivity. }
        assert (Hdisj12 : forall β0, β0 `in` dom κc1 -> β0 `notin` dom κc2).
        { intros β0 Hβ0 Hin2. pose proof (Hκf2 β0 Hin2) as Hf2.
          rewrite dom_app in Hf2. rewrite Hd1 in Hβ0. clear - Hf2 Hβ0; fsetdec. }
        assert (HΞ2disj : forall x, x `in` dom Ξc2 -> x `notin` dom (Ξc1 ++ Θ0)).
        { intros x Hx. rewrite <- Hd2 in Hx. pose proof (Hκf2 x Hx) as Hf.
          clear - Hf; fsetdec. }
        exists (C1 ++ C2), (Ξc1 ++ Ξc2), Pa2, (κc1 ++ κc2).
        repeat split.
        -- (* a_lookeq *) apply a_lookeq__arrow; [ exact HLK1 | exact HLK2 ].
        -- (* solve *)
           rewrite (@app_assoc _ Ξc1 Ξc2 Θ0).
           eapply a_solve_cstr_app;
             [ exact (a_lookeq_cstr_eq HLK1)
             | apply a_solve_cstr_weaken_mid_flex;
                 [ exact HfmΞ2 | exact HΞ2disj
                 | intros x Hx; pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfd;
                     specialize (HΞ2disj x Hx); rewrite dom_app in HΞ2disj;
                     simpl in Hfd; clear - Hfd HΞ2disj; fsetdec
                 | intros x Hx;
                     pose proof ((proj2 a_looksub_lookeq_ftv) _ _ _ _ _ HLK1) as Hcf;
                     pose proof (a_wf_pskl_ftv_dom HwfP01) as Hpf;
                     specialize (HΞ2disj x Hx); rewrite dom_app in HΞ2disj;
                     simpl in Hpf; clear - Hcf Hpf HΞ2disj; fsetdec
                 | exact HSolve1 ]
             | eapply a_solve_cstr_ctx_change;
                 [ exact HSolve2
                 | intros α1 Hg; destruct Hg as [Hb | [τ Hb]];
                     [ left | right; exists τ ]; apply binds_swap_app; exact Hb
                 | intros P0 Hf; inversion Hf; subst;
                     [ apply a_flex__var with (α := α0)
                     | apply a_flex__var_def with (α := α0) (τ := τ) ];
                     apply binds_swap_app; assumption ] ].
        -- (* wf Pa2 *)
           rewrite (@app_assoc _ Ξc1 Ξc2 Θ0).
           apply a_wf_pskl_swap_app; exact HwfPa2.
        -- (* a_wf_aenv *)
           apply a_wf_aenv_flex_prefix;
             [ apply all_flex_mono_app; assumption
             | pose proof (a_wf_aenv_uniq_local HwfΞ2) as Huq;
               clear - Huq; solve_uniq
             | exact HwfΘ0 ].
        -- (* α ∉ dom (Ξc1++Ξc2) *)
           rewrite dom_app; clear - HαΞ1 HαΞ2; fsetdec.
        -- (* keys ρc = keys Ξc *) exact Hmapc.
        -- (* ρc images ⊆ ftv ψa *) apply Forall_app; split; assumption.
        -- (* ftv (C1++C2) : the right branch's κ is [ρc1++κ], whose domain is
              [dom Ξc1 ∪ dom κ] *)
           rewrite ftvar_in_cstrs_app. rewrite dom_app.
           rewrite dom_app in HftvC2.
           rewrite Hd1 in HftvC2.
           clear - HftvC1 HftvC2; fsetdec.
        -- (* a_inc *)
           apply a_inc_flex_prefix_build;
             [ apply all_flex_mono_app; assumption
             | exact Hmapc
             | apply Forall_app; split; assumption
             | exact Hκ ].
        -- (* a_inc_equiv Θ0 κ κ Θ *) apply a_inc_equiv_refl; exact Hκ.
        -- (* ρc fresh *)
           intros α0 Hα0. rewrite dom_app in Hα0.
           apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0].
           ++ apply Hκf1; exact Hα0.
           ++ pose proof (Hκf2 α0 Hα0) as Hf. rewrite dom_app in Hf.
              clear - Hf; fsetdec.
        -- (* precision *)
           rewrite (@app_assoc _ κc1 κc2 κ).
           rewrite (@msubst_pskl_app_swap κc1 κc2 κ Pa2 Hdisj12).
           eapply ad_partial_precise_psi_cong; [ exact Hpre2 | clear - HΨa; fsetdec ].
      * (* P0 = all_syn : refinement bskl_all_inh ⊳ arrow — absurd *)
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine; inversion Hrefine.
      * (* P0 = hole : excluded by HP0nh *)
        exfalso; apply HP0nh; reflexivity.
      * (* P0 = tophole P0s : ⊤◇ → LE-UnivGhostR + IHn (P0 shrinks, R' fixed) *)
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        inversion Hrefine; subst.
        match goal with
          H : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh _ ⊳ bskl_arrow _ _ |- _ =>
            rename H into Href' end.
        assert (Hmeas : size_uskl (uskl_arrow Ra Rb) + size_pskl P0s <= n)
          by (cbn in Hn |- *; lia).
        pose proof (proj2 (a_wf_pskl_tophole_inv HwfP0)) as HwfP0s.
        edestruct (IHn NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa (bskl_arrow Q1 Q2)
                     (pskl_arrow (uskl_to_pskl Ra) (uskl_to_pskl Rb)) P0s Pi
                     (uskl_arrow Ra Rb) α
                     Hmeas HwfΘ HwfΘ0 HwfP0s HwfPi Hκ HαΘ HαΘ0
                     (eq_refl : ⌊ uskl_arrow Ra Rb ⌋ˢ
                                = pskl_arrow (uskl_to_pskl Ra) (uskl_to_pskl Rb))
                     HscopeS HlcS Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hcons0 HwfSub Href')
          as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
        exists 𝒞, Ξc, Pa, κc.
        repeat split; try assumption.
        apply a_lookeq__univ_ghost_r;
          [ exact HPnα
          | apply guarded_pskl__arrow; apply lc_uskl_to_pskl_local; assumption
          | exact HLK ].
  (* ---------------------------------------------------------------- *)
  (* The two ∀ cases (paper Cases C-ForallInh / C-ForallSyn) need the   *)
  (* ∀-BINDER KIT, which neither is available yet nor is case-specific: *)
  (*  - C-ForallSyn  (Q = bskl_all_syn Q0): the refinement inverts to   *)
  (*    [__tophole_fill] (so P0 = ⊤◇P0', as the paper says), whose      *)
  (*    binder ALSO enters Θ — the contexts MATCH, so only the          *)
  (*    output-strengthening below is missing.                          *)
  (*  - C-ForallInh  (Q = bskl_all_inh Q0): the refinement inverts to   *)
  (*    [__all], whose binder enters Δ while the consistency's enters   *)
  (*    Θ — needs a [Δ→Θ] transport (true: Δ and Θ meet only in         *)
  (*    __var's [α0 ∈ Δ ∨ a_binds_tvar α0 Θ], __hole's wf, and the flex   *)
  (*    binds — all weakenable) or P6-Cv's [aenv_split Θ Θtv Θr].       *)
  (* KIT (shared by both, and by the ⊤◇ rows above): run the IH at      *)
  (* Θ := β,Θ and Θ0 := β,Θ0, then REMOVE β from every output — the     *)
  (* paper's "reff, refg, refh, refi hold without β".  Needed:          *)
  (* a_inc tvar-extension; and β-strengthening for a_solve_cstr,        *)
  (* a_wf_pskl, a_wf_aenv, a_inc, a_inc_equiv and precision.            *)
  (* ---------------------------------------------------------------- *)
  - (* R' = all_syn R0 : C-ForallInh (→ LE-ForallInh) / C-ForallSyn (→ LE-ForallSyn) *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    cbn [msubst_uskl_syn subst_bskl_in_uskl] in Hconsis.
    assert (Hlcψa : lc_uskl ψa) by (apply is_tskl_lc; inversion Htags; assumption).
    cbn [msubst_uskl_syn subst_bskl_in_uskl uskl_to_pskl] in HwfSub.
    inversion HwfSub; subst.
    match goal with H : forall α0, α0 `notin` ?Ls -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
      rename H into Hsbody; remember Ls as Ls0 eqn:HeqLs; clear HeqLs end.
    inversion HlcS; subst.
    match goal with H : forall α0, lc_uskl _ |- _ => rename H into Hlcbody end.
    destruct (ad_pat_consis_all_syn_refine_unify HwfΘ Hconsis eq_refl Hrefine)
      as (Lcof & Q0 & Hcof & [HrefInh | HrefSyn]).
    + (* C-ForallInh: Q = ∀ᴵ.Q0.  Refinement inversion gives P0 = ∀.P0' and the
         binder in Δ, which [ad_refine_syn_delta_to_tvar_mid] moves into Θ so
         that it matches the consistency's; LE-ForallInh then needs a β-FREE
         constraint set, which the conclusion's ftv-bound supplies. *)
      destruct P0 as [ | n0 | β0 | P01 P02 | P0' | | P0s ].
      * (* unit *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefInh | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__unit ]. }
        inversion Hbad.
      * (* var_b *) inversion HwfP0.
      * (* var_f *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefInh | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__var ]. }
        inversion Hbad.
      * (* arrow *)
        exfalso.
        assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
        { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption. }
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefInh | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
        inversion Hbad.
      * (* P0 = ∀.P0' : LE-ForallInh *)
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
        inversion HrefInh; subst.
        match goal with H : forall α0, α0 `notin` ?Lr -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
          rename H into Hrbody; remember Lr as Lr0 eqn:HeqLr; clear HeqLr end.
        inversion HwfP0; subst.
        match goal with H : forall α0, α0 `notin` ?L0 -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
          rename H into Hw0body; remember L0 as Lw0 eqn:HeqLw0; clear HeqLw0 end.
        pick fresh β for
          (Lcof `union` Lr0 `union` Lw0 `union` dom Θ `union` dom Θ0
             `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
             `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
             `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0'
             `union` def_ftv Θ
                `union` Ls0).
        assert (HβΘ : β `notin` dom Θ) by auto.
        assert (HβΘ0 : β `notin` dom Θ0) by auto.
        assert (Hβα : β <> α) by auto.
        assert (Hβκ : β `notin` dom κ) by auto.
        assert (Hwfβ : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hwfβ0 : a_wf_aenv ((β ~ abind_tvar) ++ Θ0))
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hweak : forall (x : atom) (b : abind),
                  binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
          by (intros x b Hb; apply binds_app_3; exact Hb).
        assert (HwfP0β : ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                  ⊢ₚₛᵃ (open_pskl_wrt_pskl P0' (pskl_var_f β))).
        { eapply a_wf_pskl_delta_to_tvar_mid
            with (α1 := β) (Θ1 := nil) (Θ2 := Θ0) (Δ' := empty);
            [ apply (Hw0body β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
        assert (HwfPiβ : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi)
          by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfPi ]).
        assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
          by (apply a_inc_cons_tvar; exact Hκ).
        assert (HαΘβ : α `notin` dom ((β ~ abind_tvar) ++ Θ))
          by (simpl; clear - HαΘ Hβα; fsetdec).
        assert (HαΘ0β : α `notin` dom ((β ~ abind_tvar) ++ Θ0))
          by (simpl; clear - HαΘ0 Hβα; fsetdec).
        assert (HscopeSβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                  [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
        { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β)) as Hup.
          simpl in Hup, HscopeS |- *. clear - Hup HscopeS; fsetdec. }
        assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) ∩ Ψ' [=] empty).
        { rewrite ftag_in_uskl_open_var. simpl in Hdisj. exact Hdisj. }
        assert (HΨs1β : Ψsub [<=] union
                  (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) Ψa).
        { rewrite ftag_in_uskl_open_var. simpl in HΨs1. exact HΨs1. }
        assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ)).
        { intros β0 α0 τ0 Hβ0 Hb. eapply Hdfresh; [ exact Hβ0 | ].
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
            [ discriminate Habs | exact Hb' ]. }
        assert (Hpreβ : ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                  ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa)
          by (eapply ad_partial_precise_weaken;
                [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
        assert (Hconsβ : Ψsub ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ₛᵃ
                  (subst_bskl_in_uskl ψa α
                     (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β))))
                  ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f β))).
        { rewrite (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
          apply Hcof; auto. }
        assert (HwfSubβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛᵃ
                  (uskl_to_pskl (subst_bskl_in_uskl ψa α
                     (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))))).
        { rewrite (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
          rewrite uskl_to_pskl_open.
          eapply a_wf_pskl_delta_to_tvar_mid
            with (α1 := β) (Θ1 := nil) (Θ2 := Θ) (Δ' := empty);
            [ apply (Hsbody β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
        assert (Hrefβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                  (pskl_to_bskl_inh (msubst_pskl κ (open_pskl_wrt_pskl P0'
                                                      (pskl_var_f β))))
                  ⊳ (open_bskl_wrt_bskl Q0 (bskl_var_f β))).
        { rewrite (@msubst_pskl_open Θ0 κ Θ P0' β Hκ Hβκ).
          rewrite pskl_to_bskl_inh_open.
          eapply ad_refine_syn_delta_to_tvar_mid
            with (α1 := β) (Θ1 := nil) (Θ2 := Θ) (Δ' := empty);
            [ apply (Hrbody β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
        assert (Hmeas : size_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                          + size_pskl (open_pskl_wrt_pskl P0' (pskl_var_f β)) <= n).
        { rewrite size_uskl_open_uskl_wrt_uskl_var.
          rewrite size_pskl_open_pskl_wrt_pskl_var. cbn in Hn |- *; lia. }
        edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) κ Δ Ψ'
                     Ψi Ψa Ψsub ψa (open_bskl_wrt_bskl Q0 (bskl_var_f β))
                     (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                     (open_pskl_wrt_pskl P0' (pskl_var_f β)) Pi
                     (open_uskl_wrt_uskl R0 (uskl_var_f β)) α
                     Hmeas Hwfβ Hwfβ0 HwfP0β HwfPiβ Hκβ HαΘβ HαΘ0β eq_refl
                     HscopeSβ (Hlcbody β) Htags Hdisjβ Hsub Hdfreshβ Hpreβ
                     HΨs1β HΨs2 Hconsβ HwfSubβ Hrefβ)
          as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
        (* --- β-freeness of every output (this time 𝒞 comes from the bound) --- *)
        pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
        assert (HβΞc : β `notin` dom Ξc).
        { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
          apply Hκfresh. simpl; clear; fsetdec. }
        assert (Hβψa : β `notin` ftvar_in_uskl ψa) by auto.
        assert (Hβdef : β `notin` def_ftv Θ) by auto.
        assert (HβC : β `notin` ftvar_in_cstrs 𝒞).
        { cbn [def_ftv] in HftvC.
          clear - HftvC HβΞc Hβκ Hβψa Hβdef; fsetdec. }
        assert (HβPa : β `notin` ftvar_in_pskl Pa).
        { pose proof (a_solve_cstr_ftv HSolve) as Hpf.
          pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
          clear - Hpf Hfi HβC HβΘ0; fsetdec. }
        assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
        { rewrite Forall_forall in Himg |- *. intros p Hp.
          specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
        assert (Hfmc : all_flex_mono Ξc) by (eapply a_lookeq_all_flex_mono; exact HLK).
        exists 𝒞, Ξc, Pa, κc.
        repeat split.
        -- (* a_lookeq : LE-ForallInh (BOTH sides renamed) *)
           apply a_lookeq__forall_inh
             with (L := singleton α `union` singleton β
                          `union` ftvar_in_pskl (uskl_to_pskl R0)
                          `union` ftvar_in_pskl P0').
           intros α1 Hα1.
           rewrite uskl_to_pskl_open in HLK.
           rewrite (subst_pskl_in_pskl_intro β (uskl_to_pskl R0) (pskl_var_f α1));
             [ | auto ].
           rewrite (subst_pskl_in_pskl_intro β P0' (pskl_var_f α1));
             [ | auto ].
           eapply (proj2 a_looksub_lookeq_rename_tvar);
             [ exact HLK | auto | clear - Hα1; fsetdec | exact HβC ].
        -- (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
        -- (* wf Pa *) eapply a_wf_pskl_strip_tvar; [ exact HwfPa | exact HβPa ].
        -- (* a_wf_aenv *)
           eapply a_wf_aenv_strip_mid;
             [ apply all_flex_mono_a_decls; exact Hfmc | exact HwfΞ ].
        -- (* α ∉ dom Ξc *) exact HαΞ.
        -- (* keys *) exact Hmapfst.
        -- (* ρc images *) exact Himg.
        -- (* ftv 𝒞 *) cbn [def_ftv] in HftvC. exact HftvC.
        -- (* a_inc *)
           eapply a_inc_strip_tvar_mid;
             [ exact Hfmc | exact Hmapfst | exact Hβκc | exact HβΘ | exact Hinc ].
        -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
        -- (* ρc fresh *)
           intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
           clear - Hκfresh; fsetdec.
        -- (* precision *)
           eapply ad_partial_precise_strip_tvar_mid
             with (β := β) (Θ1 := nil) (Θ2 := Θ);
             [ exact Hprec | reflexivity
             | intros α0 τ0 Hb;
               assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
                 by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                       [ discriminate Habs | exact Hb' ]);
               pose proof (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb') as Hwfτ;
               pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hftd;
               clear - Hftd HβΘ; fsetdec
             | apply msubst_pskl_ftv_avoid;
                 [ intros p Hp; apply in_app_or in Hp; destruct Hp as [Hp | Hp];
                     [ rewrite Forall_forall in Hβκc; apply Hβκc; exact Hp
                     | pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb;
                       clear - Hb HβΘ; fsetdec ]
                 | exact HβPa ]
             | exact Hβψa ].
      * (* hole : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
      * (* ⊤◇P0s : a ⊤◇ source refines to ∀ᴵ only by [__tophole_remove], whose
           (guarded) body cannot reach an inherited quantifier *)
        exfalso.
        destruct (a_wf_pskl_tophole_inv HwfP0) as [HgP0s HwfP0s].
        assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
          by (apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
        inversion HrefInh; subst.
        match goal with
          H : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_inh _ |- _ =>
            pose proof (ad_refine_syn_guarded_r HwfΘ H HgL) as Hbad end.
        inversion Hbad.
    + (* C-ForallSyn: Q = ∀ˢ.Q0.  The refinement can only reach a SYNTHESISED
         ∀ by FILLING a universal ghost, so P0 = ⊤◇P0s (paper: "since P0 ≠ □,
         inversion on the refinement premise gives P0 = ⊤◇.P0'"), and the
         fill rule's binder enters Θ — matching the consistency's. *)
      destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
      * (* unit : guarded source ⇒ guarded target, but ∀ˢ is not guarded *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefSyn | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__unit ]. }
        inversion Hbad.
      * (* var_b : not well-formed *) inversion HwfP0.
      * (* var_f : guarded *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefSyn | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__var ]. }
        inversion Hbad.
      * (* arrow : guarded *)
        exfalso.
        assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
        { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption. }
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefSyn | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
        inversion Hbad.
      * (* all_syn : an INHERITED ∀ source never refines to a SYNTHESISED ∀ *)
        exfalso. cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
        inversion HrefSyn.
      * (* hole : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
      * (* P0 = ⊤◇P0s : LE-ForallSyn *)
        destruct (a_wf_pskl_tophole_inv HwfP0) as [HgP0s HwfP0s].
        assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
          by (apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
        inversion HrefSyn; subst.
        -- (* __tophole_remove : guarded source ⇒ guarded target — absurd *)
           exfalso.
           match goal with
             H : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_syn _ |- _ =>
               pose proof (ad_refine_syn_guarded_r HwfΘ H HgL) as Hbad end.
           inversion Hbad.
        -- (* __tophole_fill : the ghost is filled — run the IH under β *)
           match goal with H : forall α0, α0 `notin` ?Lf -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
             rename H into Hfill end.
           match goal with H : forall α0, α0 `notin` ?Lf -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
             let Lf' := fresh "Lf" in
             remember Lf as Lf' eqn:HeqLf; clear HeqLf end.
           pick fresh β for
             (Lcof `union` Lf `union` dom Θ `union` dom Θ0
                `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
                `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
                `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0s
                `union` Ls0).
           assert (HβΘ : β `notin` dom Θ) by auto.
           assert (HβΘ0 : β `notin` dom Θ0) by auto.
           assert (Hβα : β <> α) by auto.
           assert (Hβκ : β `notin` dom κ) by auto.
           assert (Hwfβ : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
             by (apply a_wf_aenv__tvar; assumption).
           assert (Hwfβ0 : a_wf_aenv ((β ~ abind_tvar) ++ Θ0))
             by (apply a_wf_aenv__tvar; assumption).
           assert (Hweak : forall (x : atom) (b : abind),
                     binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
             by (intros x b Hb; apply binds_app_3; exact Hb).
           assert (HwfP0β : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ (pskl_tophole P0s))
             by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfP0 ]).
           assert (HwfPiβ : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi)
             by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfPi ]).
           assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
             by (apply a_inc_cons_tvar; exact Hκ).
           assert (HαΘβ : α `notin` dom ((β ~ abind_tvar) ++ Θ))
             by (simpl; clear - HαΘ Hβα; fsetdec).
           assert (HαΘ0β : α `notin` dom ((β ~ abind_tvar) ++ Θ0))
             by (simpl; clear - HαΘ0 Hβα; fsetdec).
           assert (HscopeSβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                     [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
           { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β)) as Hup.
             simpl in Hup, HscopeS |- *. clear - Hup HscopeS; fsetdec. }
           assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) ∩ Ψ' [=] empty).
           { rewrite ftag_in_uskl_open_var. simpl in Hdisj. exact Hdisj. }
           assert (HΨs1β : Ψsub [<=] union
                     (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) Ψa).
           { rewrite ftag_in_uskl_open_var. simpl in HΨs1. exact HΨs1. }
           assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ)).
           { intros β0 α0 τ0 Hβ0 Hb. eapply Hdfresh; [ exact Hβ0 | ].
             destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
               [ discriminate Habs | exact Hb' ]. }
           assert (Hpreβ : ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                     ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa)
             by (eapply ad_partial_precise_weaken;
                   [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
           assert (Hconsβ : Ψsub ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ₛᵃ
                     (subst_bskl_in_uskl ψa α
                        (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β))))
                     ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f β))).
           { rewrite (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
             apply Hcof; auto. }
           assert (HwfSubβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛᵃ
                     (uskl_to_pskl (subst_bskl_in_uskl ψa α
                        (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))))).
           { rewrite (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
             rewrite uskl_to_pskl_open.
             eapply a_wf_pskl_delta_to_tvar_mid
               with (α1 := β) (Θ1 := nil) (Θ2 := Θ) (Δ' := empty);
               [ apply (Hsbody β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
           assert (Hrefβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                     (pskl_to_bskl_inh (msubst_pskl κ (pskl_tophole P0s)))
                     ⊳ (open_bskl_wrt_bskl Q0 (bskl_var_f β)))
             by (cbn [msubst_pskl pskl_to_bskl_inh]; apply Hfill; auto).
           assert (Hmeas : size_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                             + size_pskl (pskl_tophole P0s) <= n).
           { rewrite size_uskl_open_uskl_wrt_uskl_var. cbn in Hn |- *; lia. }
           edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) κ Δ Ψ'
                        Ψi Ψa Ψsub ψa (open_bskl_wrt_bskl Q0 (bskl_var_f β))
                        (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                        (pskl_tophole P0s) Pi
                        (open_uskl_wrt_uskl R0 (uskl_var_f β)) α
                        Hmeas Hwfβ Hwfβ0 HwfP0β HwfPiβ Hκβ HαΘβ HαΘ0β eq_refl
                        HscopeSβ (Hlcbody β) Htags Hdisjβ Hsub Hdfreshβ Hpreβ
                        HΨs1β HΨs2 Hconsβ HwfSubβ Hrefβ)
             as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
                   & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
           (* --- β-freeness of every output --- *)
           pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
           assert (HβΞc : β `notin` dom Ξc).
           { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
             apply Hκfresh. simpl; clear; fsetdec. }
           assert (HβC : β `notin` ftvar_in_cstrs 𝒞).
           { pose proof ((proj2 a_looksub_lookeq_ftv) _ _ _ _ _ HLK) as Hcf.
             pose proof (a_wf_pskl_ftv_dom HwfP0) as Hfd.
             simpl in Hfd. clear - Hcf Hfd HβΞc HβΘ0; fsetdec. }
           assert (HβPa : β `notin` ftvar_in_pskl Pa).
           { pose proof (a_solve_cstr_ftv HSolve) as Hpf.
             pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
             clear - Hpf Hfi HβC HβΘ0; fsetdec. }
           assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
           { rewrite Forall_forall in Himg |- *. intros p Hp.
             specialize (Himg p Hp). clear - Himg Fr; fsetdec. }
           assert (Hfmc : all_flex_mono Ξc) by (eapply a_lookeq_all_flex_mono; exact HLK).
           exists 𝒞, Ξc, Pa, κc.
           repeat split.
           ++ (* a_lookeq : LE-ForallSyn (the source binder is renamed) *)
              apply a_lookeq__forall_syn
                with (L := singleton α `union` singleton β
                             `union` ftvar_in_pskl (uskl_to_pskl R0)).
              intros α1 Hα1.
              rewrite uskl_to_pskl_open in HLK.
              rewrite (subst_pskl_in_pskl_intro β (uskl_to_pskl R0) (pskl_var_f α1));
                [ | clear - Fr; fsetdec ].
              eapply (proj2 a_looksub_lookeq_subst_stable);
                [ exact HLK | auto | simpl; clear - Hα1; fsetdec
                | apply lc_pskl_var_f ].
           ++ (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
           ++ (* wf Pa *)
              eapply a_wf_pskl_strip_tvar; [ exact HwfPa | exact HβPa ].
           ++ (* a_wf_aenv *)
              eapply a_wf_aenv_strip_mid;
                [ apply all_flex_mono_a_decls; exact Hfmc | exact HwfΞ ].
           ++ (* α ∉ dom Ξc *) exact HαΞ.
           ++ (* keys *) exact Hmapfst.
           ++ (* ρc images *) exact Himg.
           ++ (* ftv 𝒞 : [def_ftv] ignores the rigid binder β *)
              cbn [def_ftv] in HftvC. exact HftvC.
           ++ (* a_inc *)
              eapply a_inc_strip_tvar_mid;
                [ exact Hfmc | exact Hmapfst | exact Hβκc | exact HβΘ | exact Hinc ].
           ++ (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
           ++ (* ρc fresh *)
              intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
              clear - Hκfresh; fsetdec.
           ++ (* precision *)
              eapply ad_partial_precise_strip_tvar_mid
                with (β := β) (Θ1 := nil) (Θ2 := Θ);
                [ exact Hprec | reflexivity
                | intros α0 τ0 Hb;
                  assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
                    by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                          [ discriminate Habs | exact Hb' ]);
                  pose proof (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb') as Hwfτ;
                  pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hftd;
                  clear - Hftd HβΘ; fsetdec
                | apply msubst_pskl_ftv_avoid;
                    [ intros p Hp; apply in_app_or in Hp; destruct Hp as [Hp | Hp];
                        [ rewrite Forall_forall in Hβκc; apply Hβκc; exact Hp
                        | pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb;
                          clear - Hb HβΘ; fsetdec ]
                    | exact HβPa ]
                | clear - Fr; fsetdec ].
  - (* R' = all_etag εr R0 : the ε-TAGGED mirror of the previous case
       (C-ForallInh's tagged row splits the index [Ψ = Ψ0, ε]). *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    cbn [msubst_uskl_syn subst_bskl_in_uskl] in Hconsis.
    assert (Hlcψa : lc_uskl ψa) by (apply is_tskl_lc; inversion Htags; assumption).
    cbn [msubst_uskl_syn subst_bskl_in_uskl uskl_to_pskl] in HwfSub.
    inversion HwfSub; subst.
    match goal with H : forall α0, α0 `notin` ?Ls -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
      rename H into Hsbody; remember Ls as Ls0 eqn:HeqLs; clear HeqLs end.
    inversion HlcS; subst.
    match goal with H : forall α0, lc_uskl _ |- _ => rename H into Hlcbody end.
    destruct (ad_pat_consis_all_etag_refine_unify HwfΘ Hconsis eq_refl Hrefine)
      as (Lcof & Q0 & Ψ0 & Hcof & [[HrefInh HΨeq] | [HrefSyn HΨeq]]).
    + (* C-ForallInh: Q = ∀ᴵ.Q0.  Refinement inversion gives P0 = ∀.P0' and the
         binder in Δ, which [ad_refine_syn_delta_to_tvar_mid] moves into Θ so
         that it matches the consistency's; LE-ForallInh then needs a β-FREE
         constraint set, which the conclusion's ftv-bound supplies. *)
      destruct P0 as [ | n0 | β0 | P01 P02 | P0' | | P0s ].
      * (* unit *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefInh | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__unit ]. }
        inversion Hbad.
      * (* var_b *) inversion HwfP0.
      * (* var_f *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefInh | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__var ]. }
        inversion Hbad.
      * (* arrow *)
        exfalso.
        assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
        { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption. }
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefInh | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
        inversion Hbad.
      * (* P0 = ∀.P0' : LE-ForallInh *)
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
        inversion HrefInh; subst.
        match goal with H : forall α0, α0 `notin` ?Lr -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
          rename H into Hrbody; remember Lr as Lr0 eqn:HeqLr; clear HeqLr end.
        inversion HwfP0; subst.
        match goal with H : forall α0, α0 `notin` ?L0 -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
          rename H into Hw0body; remember L0 as Lw0 eqn:HeqLw0; clear HeqLw0 end.
        pick fresh β for
          (Lcof `union` Lr0 `union` Lw0 `union` dom Θ `union` dom Θ0
             `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
             `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
             `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0'
             `union` def_ftv Θ
                `union` Ls0).
        assert (HβΘ : β `notin` dom Θ) by auto.
        assert (HβΘ0 : β `notin` dom Θ0) by auto.
        assert (Hβα : β <> α) by auto.
        assert (Hβκ : β `notin` dom κ) by auto.
        assert (Hwfβ : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hwfβ0 : a_wf_aenv ((β ~ abind_tvar) ++ Θ0))
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hweak : forall (x : atom) (b : abind),
                  binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
          by (intros x b Hb; apply binds_app_3; exact Hb).
        assert (HwfP0β : ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                  ⊢ₚₛᵃ (open_pskl_wrt_pskl P0' (pskl_var_f β))).
        { eapply a_wf_pskl_delta_to_tvar_mid
            with (α1 := β) (Θ1 := nil) (Θ2 := Θ0) (Δ' := empty);
            [ apply (Hw0body β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
        assert (HwfPiβ : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi)
          by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfPi ]).
        assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
          by (apply a_inc_cons_tvar; exact Hκ).
        assert (HαΘβ : α `notin` dom ((β ~ abind_tvar) ++ Θ))
          by (simpl; clear - HαΘ Hβα; fsetdec).
        assert (HαΘ0β : α `notin` dom ((β ~ abind_tvar) ++ Θ0))
          by (simpl; clear - HαΘ0 Hβα; fsetdec).
        assert (HscopeSβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                  [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
        { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β)) as Hup.
          simpl in Hup, HscopeS |- *. clear - Hup HscopeS; fsetdec. }
        assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) ∩ Ψ' [=] empty).
        { rewrite ftag_in_uskl_open_var. simpl in Hdisj.
          clear - Hdisj; fsetdec. }
        assert (HΨs1β : Ψ0 [<=] union
                  (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) Ψa).
        { rewrite ftag_in_uskl_open_var.
          pose proof (ad_pat_consis_ftag_sub (Hcof β ltac:(auto))) as Hfb.
          rewrite ftag_in_uskl_open_var in Hfb.
          pose proof (ftag_in_uskl_subst_bskl_in_uskl ψa α
                        (msubst_uskl_syn κ R0)) as Hsb.
          rewrite ftag_in_uskl_msubst_uskl_syn in Hsb.
          pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
          simpl in HΨs1, Hdisj.
          rewrite <- Hψatag in Hsb.
          intros x Hx.
          pose proof (Hsb x (Hfb x Hx)) as Hx2.
          apply union_1 in Hx2; destruct Hx2 as [Hx2 | Hx2];
            [ clear - Hx2; fsetdec | ].
          assert (Hxs : x `in` Ψsub) by (clear - Hx HΨeq; fsetdec).
          pose proof (HΨs1 x Hxs) as Hx3.
          apply union_1 in Hx3; destruct Hx3 as [Hx3 | Hx3];
            [ exfalso;
              assert (Hinx : x `in` (add εr (ftag_in_uskl R0)) ∩ Ψ')
                by (apply inter_3; assumption);
              rewrite Hdisj in Hinx; clear - Hinx; fsetdec
            | clear - Hx3; fsetdec ]. }
        assert (HΨs2β : Ψa [<=] Ψ0).
        { pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
          simpl in Hdisj.
          intros x Hx.
          assert (Hxs : x `in` Ψsub) by (clear - Hx HΨs2; fsetdec).
          rewrite HΨeq in Hxs.
          destruct (x == εr) as [-> | Hne]; [ | clear - Hxs Hne; fsetdec ].
          exfalso.
          assert (Hinx : εr `in` (add εr (ftag_in_uskl R0)) ∩ Ψ').
          { apply inter_3; [ clear; fsetdec | ].
            clear - Hx Hsub HΨs2; fsetdec. }
          rewrite Hdisj in Hinx; clear - Hinx; fsetdec. }
        assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ)).
        { intros β0 α0 τ0 Hβ0 Hb. eapply Hdfresh; [ exact Hβ0 | ].
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
            [ discriminate Habs | exact Hb' ]. }
        assert (Hpreβ : ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                  ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa)
          by (eapply ad_partial_precise_weaken;
                [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
        assert (Hconsβ : Ψ0 ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ₛᵃ
                  (subst_bskl_in_uskl ψa α
                     (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β))))
                  ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f β))).
        { rewrite (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
          apply Hcof; auto. }
        assert (HwfSubβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛᵃ
                  (uskl_to_pskl (subst_bskl_in_uskl ψa α
                     (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))))).
        { rewrite (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
          rewrite uskl_to_pskl_open.
          eapply a_wf_pskl_delta_to_tvar_mid
            with (α1 := β) (Θ1 := nil) (Θ2 := Θ) (Δ' := empty);
            [ apply (Hsbody β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
        assert (Hrefβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                  (pskl_to_bskl_inh (msubst_pskl κ (open_pskl_wrt_pskl P0'
                                                      (pskl_var_f β))))
                  ⊳ (open_bskl_wrt_bskl Q0 (bskl_var_f β))).
        { rewrite (@msubst_pskl_open Θ0 κ Θ P0' β Hκ Hβκ).
          rewrite pskl_to_bskl_inh_open.
          eapply ad_refine_syn_delta_to_tvar_mid
            with (α1 := β) (Θ1 := nil) (Θ2 := Θ) (Δ' := empty);
            [ apply (Hrbody β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
        assert (Hmeas : size_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                          + size_pskl (open_pskl_wrt_pskl P0' (pskl_var_f β)) <= n).
        { rewrite size_uskl_open_uskl_wrt_uskl_var.
          rewrite size_pskl_open_pskl_wrt_pskl_var. cbn in Hn |- *; lia. }
        edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) κ Δ Ψ'
                     Ψi Ψa Ψ0 ψa (open_bskl_wrt_bskl Q0 (bskl_var_f β))
                     (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                     (open_pskl_wrt_pskl P0' (pskl_var_f β)) Pi
                     (open_uskl_wrt_uskl R0 (uskl_var_f β)) α
                     Hmeas Hwfβ Hwfβ0 HwfP0β HwfPiβ Hκβ HαΘβ HαΘ0β eq_refl
                     HscopeSβ (Hlcbody β) Htags Hdisjβ Hsub Hdfreshβ Hpreβ
                     HΨs1β HΨs2β Hconsβ HwfSubβ Hrefβ)
          as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
        (* --- β-freeness of every output (this time 𝒞 comes from the bound) --- *)
        pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
        assert (HβΞc : β `notin` dom Ξc).
        { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
          apply Hκfresh. simpl; clear; fsetdec. }
        assert (Hβψa : β `notin` ftvar_in_uskl ψa) by auto.
        assert (Hβdef : β `notin` def_ftv Θ) by auto.
        assert (HβC : β `notin` ftvar_in_cstrs 𝒞).
        { cbn [def_ftv] in HftvC.
          clear - HftvC HβΞc Hβκ Hβψa Hβdef; fsetdec. }
        assert (HβPa : β `notin` ftvar_in_pskl Pa).
        { pose proof (a_solve_cstr_ftv HSolve) as Hpf.
          pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
          clear - Hpf Hfi HβC HβΘ0; fsetdec. }
        assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
        { rewrite Forall_forall in Himg |- *. intros p Hp.
          specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
        assert (Hfmc : all_flex_mono Ξc) by (eapply a_lookeq_all_flex_mono; exact HLK).
        exists 𝒞, Ξc, Pa, κc.
        repeat split.
        -- (* a_lookeq : LE-ForallInh (BOTH sides renamed) *)
           apply a_lookeq__forall_inh
             with (L := singleton α `union` singleton β
                          `union` ftvar_in_pskl (uskl_to_pskl R0)
                          `union` ftvar_in_pskl P0').
           intros α1 Hα1.
           rewrite uskl_to_pskl_open in HLK.
           rewrite (subst_pskl_in_pskl_intro β (uskl_to_pskl R0) (pskl_var_f α1));
             [ | auto ].
           rewrite (subst_pskl_in_pskl_intro β P0' (pskl_var_f α1));
             [ | auto ].
           eapply (proj2 a_looksub_lookeq_rename_tvar);
             [ exact HLK | auto | clear - Hα1; fsetdec | exact HβC ].
        -- (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
        -- (* wf Pa *) eapply a_wf_pskl_strip_tvar; [ exact HwfPa | exact HβPa ].
        -- (* a_wf_aenv *)
           eapply a_wf_aenv_strip_mid;
             [ apply all_flex_mono_a_decls; exact Hfmc | exact HwfΞ ].
        -- (* α ∉ dom Ξc *) exact HαΞ.
        -- (* keys *) exact Hmapfst.
        -- (* ρc images *) exact Himg.
        -- (* ftv 𝒞 *) cbn [def_ftv] in HftvC. exact HftvC.
        -- (* a_inc *)
           eapply a_inc_strip_tvar_mid;
             [ exact Hfmc | exact Hmapfst | exact Hβκc | exact HβΘ | exact Hinc ].
        -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
        -- (* ρc fresh *)
           intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
           clear - Hκfresh; fsetdec.
        -- (* precision *)
           eapply ad_partial_precise_strip_tvar_mid
             with (β := β) (Θ1 := nil) (Θ2 := Θ);
             [ exact Hprec | reflexivity
             | intros α0 τ0 Hb;
               assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
                 by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                       [ discriminate Habs | exact Hb' ]);
               pose proof (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb') as Hwfτ;
               pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hftd;
               clear - Hftd HβΘ; fsetdec
             | apply msubst_pskl_ftv_avoid;
                 [ intros p Hp; apply in_app_or in Hp; destruct Hp as [Hp | Hp];
                     [ rewrite Forall_forall in Hβκc; apply Hβκc; exact Hp
                     | pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb;
                       clear - Hb HβΘ; fsetdec ]
                 | exact HβPa ]
             | exact Hβψa ].
      * (* hole : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
      * (* ⊤◇P0s : a ⊤◇ source refines to ∀ᴵ only by [__tophole_remove], whose
           (guarded) body cannot reach an inherited quantifier *)
        exfalso.
        destruct (a_wf_pskl_tophole_inv HwfP0) as [HgP0s HwfP0s].
        assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
          by (apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
        inversion HrefInh; subst.
        match goal with
          H : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_inh _ |- _ =>
            pose proof (ad_refine_syn_guarded_r HwfΘ H HgL) as Hbad end.
        inversion Hbad.
    + (* C-ForallSyn: Q = ∀ˢ.Q0.  The refinement can only reach a SYNTHESISED
         ∀ by FILLING a universal ghost, so P0 = ⊤◇P0s (paper: "since P0 ≠ □,
         inversion on the refinement premise gives P0 = ⊤◇.P0'"), and the
         fill rule's binder enters Θ — matching the consistency's. *)
      destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
      * (* unit : guarded source ⇒ guarded target, but ∀ˢ is not guarded *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefSyn | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__unit ]. }
        inversion Hbad.
      * (* var_b : not well-formed *) inversion HwfP0.
      * (* var_f : guarded *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefSyn | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__var ]. }
        inversion Hbad.
      * (* arrow : guarded *)
        exfalso.
        assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
        { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption. }
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact HrefSyn | ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
        inversion Hbad.
      * (* all_syn : an INHERITED ∀ source never refines to a SYNTHESISED ∀ *)
        exfalso. cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
        inversion HrefSyn.
      * (* hole : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
      * (* P0 = ⊤◇P0s : LE-ForallSyn *)
        destruct (a_wf_pskl_tophole_inv HwfP0) as [HgP0s HwfP0s].
        assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
          by (apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
        inversion HrefSyn; subst.
        -- (* __tophole_remove : guarded source ⇒ guarded target — absurd *)
           exfalso.
           match goal with
             H : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_syn _ |- _ =>
               pose proof (ad_refine_syn_guarded_r HwfΘ H HgL) as Hbad end.
           inversion Hbad.
        -- (* __tophole_fill : the ghost is filled — run the IH under β *)
           match goal with H : forall α0, α0 `notin` ?Lf -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
             rename H into Hfill end.
           match goal with H : forall α0, α0 `notin` ?Lf -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
             let Lf' := fresh "Lf" in
             remember Lf as Lf' eqn:HeqLf; clear HeqLf end.
           pick fresh β for
             (Lcof `union` Lf `union` dom Θ `union` dom Θ0
                `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
                `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
                `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0s
                `union` Ls0).
           assert (HβΘ : β `notin` dom Θ) by auto.
           assert (HβΘ0 : β `notin` dom Θ0) by auto.
           assert (Hβα : β <> α) by auto.
           assert (Hβκ : β `notin` dom κ) by auto.
           assert (Hwfβ : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
             by (apply a_wf_aenv__tvar; assumption).
           assert (Hwfβ0 : a_wf_aenv ((β ~ abind_tvar) ++ Θ0))
             by (apply a_wf_aenv__tvar; assumption).
           assert (Hweak : forall (x : atom) (b : abind),
                     binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
             by (intros x b Hb; apply binds_app_3; exact Hb).
           assert (HwfP0β : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ (pskl_tophole P0s))
             by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfP0 ]).
           assert (HwfPiβ : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi)
             by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfPi ]).
           assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
             by (apply a_inc_cons_tvar; exact Hκ).
           assert (HαΘβ : α `notin` dom ((β ~ abind_tvar) ++ Θ))
             by (simpl; clear - HαΘ Hβα; fsetdec).
           assert (HαΘ0β : α `notin` dom ((β ~ abind_tvar) ++ Θ0))
             by (simpl; clear - HαΘ0 Hβα; fsetdec).
           assert (HscopeSβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                     [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
           { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β)) as Hup.
             simpl in Hup, HscopeS |- *. clear - Hup HscopeS; fsetdec. }
           assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) ∩ Ψ' [=] empty).
           { rewrite ftag_in_uskl_open_var. simpl in Hdisj.
             clear - Hdisj; fsetdec. }
           assert (HΨs1β : Ψ0 [<=] union
                     (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) Ψa).
           { rewrite ftag_in_uskl_open_var.
             (* the tagged row's index is [Ψsub = Ψ0]; the extra tag ε sits in
                [ftag R'] but is disjoint from Ψ', while the body's own bound
                comes from the sub-consistency *)
             pose proof (ad_pat_consis_ftag_sub (Hcof β ltac:(auto))) as Hfb.
             rewrite ftag_in_uskl_open_var in Hfb.
             pose proof (ftag_in_uskl_subst_bskl_in_uskl ψa α
                           (msubst_uskl_syn κ R0)) as Hsb.
             rewrite ftag_in_uskl_msubst_uskl_syn in Hsb.
             pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
             simpl in HΨs1, Hdisj.
             rewrite HΨeq in HΨs1.
             rewrite <- Hψatag in Hsb.
             intros x Hx.
             pose proof (Hsb x (Hfb x Hx)) as Hx2.
             apply union_1 in Hx2; destruct Hx2 as [Hx2 | Hx2];
               [ clear - Hx2; fsetdec | ].
             pose proof (HΨs1 x Hx) as Hx3.
             apply union_1 in Hx3; destruct Hx3 as [Hx3 | Hx3];
               [ exfalso;
                 assert (Hinx : x `in` (add εr (ftag_in_uskl R0)) ∩ Ψ')
                   by (apply inter_3; assumption);
                 rewrite Hdisj in Hinx; clear - Hinx; fsetdec
               | clear - Hx3; fsetdec ]. }
           assert (HΨs2β : Ψa [<=] Ψ0) by (clear - HΨs2 HΨeq; fsetdec).
           assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ)).
           { intros β0 α0 τ0 Hβ0 Hb. eapply Hdfresh; [ exact Hβ0 | ].
             destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
               [ discriminate Habs | exact Hb' ]. }
           assert (Hpreβ : ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                     ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa)
             by (eapply ad_partial_precise_weaken;
                   [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
           assert (Hconsβ : Ψ0 ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ₛᵃ
                     (subst_bskl_in_uskl ψa α
                        (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β))))
                     ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f β))).
           { rewrite (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
             apply Hcof; auto. }
           assert (HwfSubβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛᵃ
                     (uskl_to_pskl (subst_bskl_in_uskl ψa α
                        (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))))).
           { rewrite (@p6cs_subject_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
             rewrite uskl_to_pskl_open.
             eapply a_wf_pskl_delta_to_tvar_mid
               with (α1 := β) (Θ1 := nil) (Θ2 := Θ) (Δ' := empty);
               [ apply (Hsbody β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
           assert (Hrefβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                     (pskl_to_bskl_inh (msubst_pskl κ (pskl_tophole P0s)))
                     ⊳ (open_bskl_wrt_bskl Q0 (bskl_var_f β)))
             by (cbn [msubst_pskl pskl_to_bskl_inh]; apply Hfill; auto).
           assert (Hmeas : size_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                             + size_pskl (pskl_tophole P0s) <= n).
           { rewrite size_uskl_open_uskl_wrt_uskl_var. cbn in Hn |- *; lia. }
           edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) κ Δ Ψ'
                        Ψi Ψa Ψ0 ψa (open_bskl_wrt_bskl Q0 (bskl_var_f β))
                        (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                        (pskl_tophole P0s) Pi
                        (open_uskl_wrt_uskl R0 (uskl_var_f β)) α
                        Hmeas Hwfβ Hwfβ0 HwfP0β HwfPiβ Hκβ HαΘβ HαΘ0β eq_refl
                        HscopeSβ (Hlcbody β) Htags Hdisjβ Hsub Hdfreshβ Hpreβ
                        HΨs1β HΨs2β Hconsβ HwfSubβ Hrefβ)
             as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
                   & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
           (* --- β-freeness of every output --- *)
           pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
           assert (HβΞc : β `notin` dom Ξc).
           { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
             apply Hκfresh. simpl; clear; fsetdec. }
           assert (HβC : β `notin` ftvar_in_cstrs 𝒞).
           { pose proof ((proj2 a_looksub_lookeq_ftv) _ _ _ _ _ HLK) as Hcf.
             pose proof (a_wf_pskl_ftv_dom HwfP0) as Hfd.
             simpl in Hfd. clear - Hcf Hfd HβΞc HβΘ0; fsetdec. }
           assert (HβPa : β `notin` ftvar_in_pskl Pa).
           { pose proof (a_solve_cstr_ftv HSolve) as Hpf.
             pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
             clear - Hpf Hfi HβC HβΘ0; fsetdec. }
           assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
           { rewrite Forall_forall in Himg |- *. intros p Hp.
             specialize (Himg p Hp). clear - Himg Fr; fsetdec. }
           assert (Hfmc : all_flex_mono Ξc) by (eapply a_lookeq_all_flex_mono; exact HLK).
           exists 𝒞, Ξc, Pa, κc.
           repeat split.
           ++ (* a_lookeq : LE-ForallSyn (the source binder is renamed) *)
              apply a_lookeq__forall_syn
                with (L := singleton α `union` singleton β
                             `union` ftvar_in_pskl (uskl_to_pskl R0)).
              intros α1 Hα1.
              rewrite uskl_to_pskl_open in HLK.
              rewrite (subst_pskl_in_pskl_intro β (uskl_to_pskl R0) (pskl_var_f α1));
                [ | clear - Fr; fsetdec ].
              eapply (proj2 a_looksub_lookeq_subst_stable);
                [ exact HLK | auto | simpl; clear - Hα1; fsetdec
                | apply lc_pskl_var_f ].
           ++ (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
           ++ (* wf Pa *)
              eapply a_wf_pskl_strip_tvar; [ exact HwfPa | exact HβPa ].
           ++ (* a_wf_aenv *)
              eapply a_wf_aenv_strip_mid;
                [ apply all_flex_mono_a_decls; exact Hfmc | exact HwfΞ ].
           ++ (* α ∉ dom Ξc *) exact HαΞ.
           ++ (* keys *) exact Hmapfst.
           ++ (* ρc images *) exact Himg.
           ++ (* ftv 𝒞 : [def_ftv] ignores the rigid binder β *)
              cbn [def_ftv] in HftvC. exact HftvC.
           ++ (* a_inc *)
              eapply a_inc_strip_tvar_mid;
                [ exact Hfmc | exact Hmapfst | exact Hβκc | exact HβΘ | exact Hinc ].
           ++ (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
           ++ (* ρc fresh *)
              intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
              clear - Hκfresh; fsetdec.
           ++ (* precision *)
              eapply ad_partial_precise_strip_tvar_mid
                with (β := β) (Θ1 := nil) (Θ2 := Θ);
                [ exact Hprec | reflexivity
                | intros α0 τ0 Hb;
                  assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
                    by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                          [ discriminate Habs | exact Hb' ]);
                  pose proof (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb') as Hwfτ;
                  pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hftd;
                  clear - Hftd HβΘ; fsetdec
                | apply msubst_pskl_ftv_avoid;
                    [ intros p Hp; apply in_app_or in Hp; destruct Hp as [Hp | Hp];
                        [ rewrite Forall_forall in Hβκc; apply Hβκc; exact Hp
                        | pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb;
                          clear - Hb HβΘ; fsetdec ]
                    | exact HβPa ]
                | clear - Fr; fsetdec ].
  - (* R' = hole : α ∈ ∅ absurd *) clear - HαR; fsetdec.
  - (* R' = tophole R0 : C-UnivGhost / C-UnivGhost1 / C-UnivGhost2.
       [⌊⊤◇R0⌋ = ⊤◇⌊R0⌋]; well-formedness of P makes ⌊R0⌋ GUARDED, which is
       the paper's handle on this case.  The P0-grid follows the paper's
       "case analysis on P0" in Case C-UnivGhost2. *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    pose proof (lc_uskl_tophole_inv HlcS) as HlcS0.
    cbn [msubst_uskl_syn subst_bskl_in_uskl uskl_to_pskl] in HwfSub.
    destruct (a_wf_pskl_tophole_inv HwfSub) as [HgSub0 HwfSub0].
    cbn [msubst_uskl_syn subst_bskl_in_uskl] in Hconsis.
    assert (Hmeas0 : forall P0', size_pskl P0' <= size_pskl P0 ->
                     size_uskl R0 + size_pskl P0' <= n)
      by (intros P0' HP0'; cbn in Hn; lia).
    destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
    + (* P0 = unit : GUARDED ⇒ the ghost is dropped ⇒ LE-UnivGhost2 *)
      assert (HgP0 : guarded_pskl pskl_unit) by apply guarded_pskl__unit.
      assert (HgQ : guarded_bskl Q).
      { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact Hrefine | ].
        apply guarded_pskl_to_bskl_inh;
          eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
      destruct (ad_pat_consis_tophole_guarded_unify HwfΘ Hconsis eq_refl Hrefine HgQ)
        as (Q0 & Hc0 & Href0 & HgQ0).
      edestruct (IHn NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                   (uskl_to_pskl R0) pskl_unit Pi R0 α
                   (Hmeas0 pskl_unit ltac:(cbn; lia))
                   HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 eq_refl
                   HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 HwfSub0 Href0)
        as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
              & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
      exists 𝒞, Ξc, Pa, κc.
      repeat split; try assumption.
      apply a_lookeq__univ_ghost2; [ exact HgP0 | exact HLK ].
    + (* P0 = var_b : not well-formed *) inversion HwfP0.
    + (* P0 = var_f β0 : GUARDED ⇒ LE-UnivGhost2 *)
      assert (HgP0 : guarded_pskl (pskl_var_f β0)) by apply guarded_pskl__var.
      assert (HgQ : guarded_bskl Q).
      { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact Hrefine | ].
        apply guarded_pskl_to_bskl_inh;
          eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
      destruct (ad_pat_consis_tophole_guarded_unify HwfΘ Hconsis eq_refl Hrefine HgQ)
        as (Q0 & Hc0 & Href0 & HgQ0).
      edestruct (IHn NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                   (uskl_to_pskl R0) (pskl_var_f β0) Pi R0 α
                   (Hmeas0 (pskl_var_f β0) ltac:(cbn; lia))
                   HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 eq_refl
                   HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 HwfSub0 Href0)
        as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
              & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
      exists 𝒞, Ξc, Pa, κc.
      repeat split; try assumption.
      apply a_lookeq__univ_ghost2; [ exact HgP0 | exact HLK ].
    + (* P0 = arrow P01 P02 : GUARDED ⇒ LE-UnivGhost2 *)
      assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
      { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
        apply guarded_pskl__arrow; assumption. }
      assert (HgQ : guarded_bskl Q).
      { eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact Hrefine | ].
        apply guarded_pskl_to_bskl_inh;
          eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
      destruct (ad_pat_consis_tophole_guarded_unify HwfΘ Hconsis eq_refl Hrefine HgQ)
        as (Q0 & Hc0 & Href0 & HgQ0).
      edestruct (IHn NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                   (uskl_to_pskl R0) (pskl_arrow P01 P02) Pi R0 α
                   (Hmeas0 (pskl_arrow P01 P02) ltac:(cbn; lia))
                   HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 eq_refl
                   HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 HwfSub0 Href0)
        as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
              & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
      exists 𝒞, Ξc, Pa, κc.
      repeat split; try assumption.
      apply a_lookeq__univ_ghost2; [ exact HgP0 | exact HLK ].
    + (* P0 = ∀.P0' : C-UnivGhost1 → LE-UnivGhost1.  The ∀-binder kit applies:
         the refinement's Δ-binder is moved into Θ by
         [ad_refine_syn_delta_to_tvar_mid], the IH runs at β,Θ / β,Θ0 with R'
         UNCHANGED (only P0 shrinks), and β is stripped from every output. *)
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      * (* refinement __all *)
        match goal with
          H : forall α0, α0 `notin` ?Lr -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ open_bskl_wrt_bskl ?Qb _ |- _ =>
            rename H into Hrbody;
            remember Lr as Lr0 eqn:HeqLr; clear HeqLr;
            remember Qb as Qb0 eqn:HeqQb; clear HeqQb
        end.
        inversion HwfP0; subst.
        match goal with H : forall α0, α0 `notin` ?L0 -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
          rename H into Hw0body; remember L0 as Lw0 eqn:HeqLw0; clear HeqLw0 end.
        (* consistency: C-UnivGhost1 (the ghost is kept under the ∀) or
           C-UnivGhost2 (dropped) *)
        inversion Hconsis; subst.
        -- (* C-UnivGhost1 *)
           match goal with H : forall α0, α0 `notin` ?Lc -> _ ⨟ _ ⊢ₛᵃ _ ∼ _ |- _ =>
             rename H into Hcbody; remember Lc as Lc0 eqn:HeqLc; clear HeqLc end.
           pick fresh β for
             (Lr0 `union` Lw0 `union` Lc0 `union` dom Θ `union` dom Θ0
                `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
                `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
                `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0s
                `union` def_ftv Θ).
           assert (HβΘ : β `notin` dom Θ) by auto.
           assert (HβΘ0 : β `notin` dom Θ0) by auto.
           assert (Hβα : β <> α) by auto.
           assert (Hβκ : β `notin` dom κ) by auto.
           assert (Hβψa : β `notin` ftvar_in_uskl ψa) by auto.
           assert (Hβdef : β `notin` def_ftv Θ) by auto.
           assert (Hwfβ : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
             by (apply a_wf_aenv__tvar; assumption).
           assert (Hwfβ0 : a_wf_aenv ((β ~ abind_tvar) ++ Θ0))
             by (apply a_wf_aenv__tvar; assumption).
           assert (Hweak : forall (x : atom) (b : abind),
                     binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
             by (intros x b Hb; apply binds_app_3; exact Hb).
           assert (HwfP0β : ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                     ⊢ₚₛᵃ (open_pskl_wrt_pskl P0s (pskl_var_f β))).
           { eapply a_wf_pskl_delta_to_tvar_mid
               with (α1 := β) (Θ1 := nil) (Θ2 := Θ0) (Δ' := empty);
               [ apply (Hw0body β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
           assert (HwfPiβ : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi)
             by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfPi ]).
           assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
             by (apply a_inc_cons_tvar; exact Hκ).
           assert (HαΘβ : α `notin` dom ((β ~ abind_tvar) ++ Θ))
             by (simpl; clear - HαΘ Hβα; fsetdec).
           assert (HαΘ0β : α `notin` dom ((β ~ abind_tvar) ++ Θ0))
             by (simpl; clear - HαΘ0 Hβα; fsetdec).
           assert (HscopeSβ : ftvar_in_uskl (uskl_tophole R0)
                     [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
           { simpl in HscopeS |- *. clear - HscopeS; fsetdec. }
           assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ)).
           { intros β0 α0 τ0 Hβ0 Hb. eapply Hdfresh; [ exact Hβ0 | ].
             destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
               [ discriminate Habs | exact Hb' ]. }
           assert (Hpreβ : ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                     ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa)
             by (eapply ad_partial_precise_weaken;
                   [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
           assert (HwfSubβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛᵃ
                     (uskl_to_pskl (subst_bskl_in_uskl ψa α
                        (msubst_uskl_syn κ (uskl_tophole R0)))))
             by (eapply a_wf_pskl_weaken;
                   [ intros x b Hb; apply binds_app_3; exact Hb | exact HwfSub ]).
           assert (Hrefβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                     (pskl_to_bskl_inh (msubst_pskl κ (open_pskl_wrt_pskl P0s
                                                         (pskl_var_f β))))
                     ⊳ (open_bskl_wrt_bskl Qb0 (bskl_var_f β))).
           { rewrite (@msubst_pskl_open Θ0 κ Θ P0s β Hκ Hβκ).
             rewrite pskl_to_bskl_inh_open.
             eapply ad_refine_syn_delta_to_tvar_mid
               with (α1 := β) (Θ1 := nil) (Θ2 := Θ) (Δ' := empty);
               [ apply (Hrbody β ltac:(auto)) | reflexivity | clear; fsetdec ]. }
           assert (Hmeas : size_uskl (uskl_tophole R0)
                             + size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β))
                             <= n).
           { rewrite size_pskl_open_pskl_wrt_pskl_var. cbn in Hn |- *; lia. }
           edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) κ Δ
                        Ψ' Ψi Ψa Ψsub ψa (open_bskl_wrt_bskl Qb0 (bskl_var_f β))
                        (pskl_tophole (uskl_to_pskl R0))
                        (open_pskl_wrt_pskl P0s (pskl_var_f β)) Pi
                        (uskl_tophole R0) α
                        Hmeas Hwfβ Hwfβ0 HwfP0β HwfPiβ Hκβ HαΘβ HαΘ0β eq_refl
                        HscopeSβ HlcS Htags Hdisj Hsub Hdfreshβ Hpreβ
                        HΨs1 HΨs2 (Hcbody β ltac:(auto)) HwfSubβ Hrefβ)
             as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
                   & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
           pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
           assert (HβΞc : β `notin` dom Ξc).
           { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
             apply Hκfresh. simpl; clear; fsetdec. }
           assert (HβC : β `notin` ftvar_in_cstrs 𝒞).
           { cbn [def_ftv] in HftvC.
             clear - HftvC HβΞc Hβκ Hβψa Hβdef; fsetdec. }
           assert (HβPa : β `notin` ftvar_in_pskl Pa).
           { pose proof (a_solve_cstr_ftv HSolve) as Hpf.
             pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
             clear - Hpf Hfi HβC HβΘ0; fsetdec. }
           assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
           { rewrite Forall_forall in Himg |- *. intros p Hp.
             specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
           assert (Hfmc : all_flex_mono Ξc)
             by (eapply a_lookeq_all_flex_mono; exact HLK).
           exists 𝒞, Ξc, Pa, κc.
           repeat split.
           ++ (* a_lookeq : LE-UnivGhost1 (only the TARGET is renamed) *)
              apply a_lookeq__univ_ghost1
                with (L := singleton α `union` singleton β
                             `union` ftvar_in_pskl (uskl_to_pskl R0)
                             `union` ftvar_in_pskl P0s).
              intros α1 Hα1.
              rewrite (subst_pskl_in_pskl_intro β P0s (pskl_var_f α1)); [ | auto ].
              rewrite <- (subst_pskl_in_pskl_fresh_eq
                            (pskl_tophole (uskl_to_pskl R0)) (pskl_var_f α1) β)
                by (simpl; auto).
              eapply (proj2 a_looksub_lookeq_rename_tvar);
                [ exact HLK | auto | clear - Hα1; fsetdec | exact HβC ].
           ++ (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
           ++ (* wf Pa *) eapply a_wf_pskl_strip_tvar; [ exact HwfPa | exact HβPa ].
           ++ (* a_wf_aenv *)
              eapply a_wf_aenv_strip_mid;
                [ apply all_flex_mono_a_decls; exact Hfmc | exact HwfΞ ].
           ++ (* α ∉ dom Ξc *) exact HαΞ.
           ++ (* keys *) exact Hmapfst.
           ++ (* ρc images *) exact Himg.
           ++ (* ftv 𝒞 *) cbn [def_ftv] in HftvC. exact HftvC.
           ++ (* a_inc *)
              eapply a_inc_strip_tvar_mid;
                [ exact Hfmc | exact Hmapfst | exact Hβκc | exact HβΘ | exact Hinc ].
           ++ (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
           ++ (* ρc fresh *)
              intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
              clear - Hκfresh; fsetdec.
           ++ (* precision *)
              eapply ad_partial_precise_strip_tvar_mid
                with (β := β) (Θ1 := nil) (Θ2 := Θ);
                [ exact Hprec | reflexivity
                | intros α0 τ0 Hb;
                  assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
                    by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                          [ discriminate Habs | exact Hb' ]);
                  pose proof (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb') as Hwfτ;
                  pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hftd;
                  clear - Hftd HβΘ; fsetdec
                | apply msubst_pskl_ftv_avoid;
                    [ intros p Hp; apply in_app_or in Hp; destruct Hp as [Hp | Hp];
                        [ rewrite Forall_forall in Hβκc; apply Hβκc; exact Hp
                        | pose proof (a_inc_image_ftv_dom Hκ p Hp) as Hb;
                          clear - Hb HβΘ; fsetdec ]
                    | exact HβPa ]
                | exact Hβψa ].
        -- (* C-UnivGhost2: the ghost is DROPPED against an inherited ∀.  The
              residual subject is the ⊤◇-BODY, which well-formedness of the
              SUBJECT makes guarded (ghost bodies are guarded) — and a guarded
              subject never faces a quantifier.  [This is the row that is FALSE
              without the subject-wf premise: with R0 = α the body's subject is
              ψa itself, which may be a ∀ or a ⊤̇◇.] *)
           exfalso.
           pose proof (guarded_uskl_head
                         (@guarded_uskl_of_pskl
                            (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R0)) HgSub0))
             as Hghsub.
           match goal with
             H : _ ⨟ _ ⊢ₛᵃ subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R0)
                   ∼ bskl_all_inh _ |- _ =>
               pose proof (ad_pat_consis_guarded_head_target H HwfΘ Hghsub) as Hgh
           end.
           destruct Hgh as [Habs | [[α0 Habs] | [Q1 [Q2 Habs]]]];
             discriminate Habs.
      * (* refinement __flex_r : the target is a defined flex VAR, hence
           guarded — and an inherited ∀ never refines to a guarded skeleton *)
        exfalso.
        eapply ad_refine_syn_all_inh_guarded_absurd;
          [ exact HwfΘ | exact Hrefine | apply guarded_bskl__var ].
    + (* P0 = hole : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
    + (* P0 = ⊤◇P0s : LE-UnivGhost (ghost kept on both sides) *)
      destruct (a_wf_pskl_tophole_inv HwfP0) as [HgP0s HwfP0s].
      assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
        by (apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      * (* refinement __tophole_remove: the target is guarded, so the
           consistency drops its ghost too — LE-UnivGhost *)
        match goal with
          H : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ Q |- _ =>
            rename H into Href1 end.
        assert (HgQ : guarded_bskl Q)
          by (eapply ad_refine_syn_guarded_r; [ exact HwfΘ | exact Href1 | exact HgL ]).
        destruct (ad_pat_consis_tophole_guarded_unify HwfΘ Hconsis eq_refl Hrefine HgQ)
          as (Q0 & Hc0 & Href0 & HgQ0).
        assert (Href2 : Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0s)) ⊳ Q0)
          by (eapply ad_refine_syn_tophole_guarded_inv;
                [ exact HwfΘ | exact Href0 | exact HgQ0 ]).
        edestruct (IHn NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                     (uskl_to_pskl R0) P0s Pi R0 α
                     (Hmeas0 P0s ltac:(cbn; lia))
                     HwfΘ HwfΘ0 HwfP0s HwfPi Hκ HαΘ HαΘ0 eq_refl
                     HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 HwfSub0 Href2)
          as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
        exists 𝒞, Ξc, Pa, κc.
        repeat split; try assumption.
        apply a_lookeq__univ_ghost; exact HLK.
      * (* refinement __tophole_fill: Q = ∀ˢ.Q0.  A ⊤◇ subject can only meet a
           SYNTHESISED ∀ by dropping its ghost (C-UnivGhost2), and the residual
           subject is guarded (subject wf) — impossible against a ∀. *)
        exfalso.
        inversion Hconsis; subst.
        pose proof (guarded_uskl_head
                      (@guarded_uskl_of_pskl
                         (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R0)) HgSub0))
          as Hghsub.
        match goal with
          H : _ ⨟ _ ⊢ₛᵃ subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R0)
                ∼ bskl_all_syn _ |- _ =>
            pose proof (ad_pat_consis_guarded_head_target H HwfΘ Hghsub) as Hgh
        end.
        destruct Hgh as [Habs | [[α0 Habs] | [Q1 [Q2 Habs]]]]; discriminate Habs.
      * (* refinement __tophole_keep: Q = ⊤◇Q0 with [inh κP0s ⊳ Q0].  The
           consistency keeps its ghost too (C-UnivGhost); the dropping
           alternative is refuted because the residual subject is guarded. *)
        match goal with
          H : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ ?Q0' |- _ =>
            rename H into Href1 end.
        inversion Hconsis; subst.
        -- (* C-UnivGhost : the ghost is kept on both sides *)
           match goal with
             H : _ ⨟ _ ⊢ₛᵃ subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R0) ∼ _ |- _ =>
               rename H into Hc0 end.
           edestruct (IHn NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa _
                        (uskl_to_pskl R0) P0s Pi R0 α
                        (Hmeas0 P0s ltac:(cbn; lia))
                        HwfΘ HwfΘ0 HwfP0s HwfPi Hκ HαΘ HαΘ0 eq_refl
                        HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2
                        Hc0 HwfSub0 Href1)
             as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
                   & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
           exists 𝒞, Ξc, Pa, κc.
           repeat split; try assumption.
           apply a_lookeq__univ_ghost; exact HLK.
        -- (* C-UnivGhost2 : impossible against a ⊤◇ target *)
           exfalso.
           pose proof (guarded_uskl_head
                         (@guarded_uskl_of_pskl
                            (subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R0)) HgSub0))
             as Hghsub.
           match goal with
             H : _ ⨟ _ ⊢ₛᵃ subst_bskl_in_uskl ψa α (msubst_uskl_syn κ R0)
                   ∼ bskl_tophole _ |- _ =>
               pose proof (ad_pat_consis_guarded_head_target H HwfΘ Hghsub) as Hgh
           end.
           destruct Hgh as [Habs | [[α0 Habs] | [Q1 [Q2 Habs]]]];
             discriminate Habs.
      * (* refinement __flex_r: the target is a defined flex VAR — guarded,
           so this is the ghost-dropping path again *)
        match goal with H : binds ?αf (abind_flex_mono_def ?τ) Θ |- _ =>
          rename H into Hbf end.
        assert (HgQ : guarded_bskl (bskl_var_f α0)) by apply guarded_bskl__var.
        destruct (ad_pat_consis_tophole_guarded_unify HwfΘ Hconsis eq_refl Hrefine HgQ)
          as (Q0 & Hc0 & Href0 & HgQ0).
        assert (Href2 : Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0s)) ⊳ Q0)
          by (eapply ad_refine_syn_tophole_guarded_inv;
                [ exact HwfΘ | exact Href0 | exact HgQ0 ]).
        edestruct (IHn NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                     (uskl_to_pskl R0) P0s Pi R0 α
                     (Hmeas0 P0s ltac:(cbn; lia))
                     HwfΘ HwfΘ0 HwfP0s HwfPi Hκ HαΘ HαΘ0 eq_refl
                     HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 HwfSub0 Href2)
          as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
        exists 𝒞, Ξc, Pa, κc.
        repeat split; try assumption.
        apply a_lookeq__univ_ghost; exact HLK.
  - (* R' = holeg : α ∈ ∅ absurd *) clear - HαR; fsetdec.
  - (* R' = topholeg R0 : C-UnivGhostG → LE-UnivGhost.
       [⌊⊤̇◇R0⌋ = ⊤◇⌊R0⌋], the consistency target is [⊤◇Q0] (up to the
       defined-flex chain), and only [P0 = ⊤◇P0s] can refine to a [⊤◇]. *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    pose proof (lc_uskl_topholeg_inv HlcS) as HlcS0.
    cbn [msubst_uskl_syn subst_bskl_in_uskl uskl_to_pskl] in HwfSub.
    destruct (a_wf_pskl_tophole_inv HwfSub) as [HgSub0 HwfSub0].
    cbn [msubst_uskl_syn subst_bskl_in_uskl] in Hconsis.
    destruct (ad_pat_consis_topholeg_refine_unify HwfΘ Hconsis eq_refl Hrefine)
      as (Q0 & Hc0 & Href0).
    clear Hconsis Hrefine.
    assert (Hsrc : (exists L0, pskl_to_bskl_inh (msubst_pskl κ P0) = bskl_tophole L0)
                   \/ pskl_to_bskl_inh (msubst_pskl κ P0) = bskl_hole)
      by (eapply ad_refine_syn_tophole_rhs_src;
            [ exact HwfΘ | exact Href0 | reflexivity ]).
    destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
    + (* unit *)
      exfalso; destruct Hsrc as [[L0 HL0] | HL0]; cbn in HL0; discriminate.
    + (* var_b : not well-formed *) inversion HwfP0.
    + (* var_f β0 : κβ0 is a ptyp painting — never a ⊤◇ or □ *)
      exfalso; destruct Hsrc as [[L0 HL0] | HL0];
        cbn [msubst_pskl] in HL0; destruct (msubst_lookup κ β0);
        cbn in HL0; discriminate.
    + (* arrow *)
      exfalso; destruct Hsrc as [[L0 HL0] | HL0]; cbn in HL0; discriminate.
    + (* all_syn *)
      exfalso; destruct Hsrc as [[L0 HL0] | HL0]; cbn in HL0; discriminate.
    + (* hole : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
    + (* P0 = ⊤◇P0s : the surviving shape — LE-UnivGhost *)
      clear Hsrc.
      destruct (a_wf_pskl_tophole_inv HwfP0) as [HgP0s HwfP0s].
      cbn [msubst_pskl pskl_to_bskl_inh] in Href0.
      (* the source's ⊤◇ must be KEPT: its body is guarded, so it cannot
         itself refine to the ⊤◇ target *)
      assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
        by (apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
      pose proof (ad_refine_syn_tophole_keep_inv HwfΘ HgL Href0) as Href1.
      assert (Hmeas : size_uskl R0 + size_pskl P0s <= n) by (cbn in Hn; lia).
      edestruct (IHn NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                   (uskl_to_pskl R0) P0s Pi R0 α
                   Hmeas HwfΘ HwfΘ0 HwfP0s HwfPi Hκ HαΘ HαΘ0 eq_refl
                   HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0
                   HwfSub0 Href1)
        as (𝒞 & Ξc & Pa & κc & HLK & HSolve & HwfPa & HwfΞ & HαΞ
              & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec).
      exists 𝒞, Ξc, Pa, κc.
      repeat split; try assumption.
      apply a_lookeq__univ_ghost; exact HLK.
Qed.

Print Assumptions a_lookeq_solve_complete.
