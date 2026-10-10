(** P6-Cs — completeness of consistency CONSTRAINT COLLECTION AND SOLVING
    ([lemma:complete-consistency-constraint-collection-solving],
    consistency-proofs.tex:920).

    Companion of [a_solve_eq_complete_var] (P6-Cv,
    sub/look/prop_eq_var.v), which this file's α-leaf case
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
    FALSE, as machine-checked in [fresco/algo/cex/cex_p6cs_subject_wf.v].
    See docs/WF-SIDE-CONDITIONS.md. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.prop_tag.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_skeleton.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.algo.prop_inc.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.prop_stability.
Require Import src.fresco.algo.prop_refine.
Require Import src.fresco.algo.consis.prop_soundness_consis.
Require Import src.fresco.algo.consis.prop_completeness_consis.
Require Import src.fresco.algo.prop_mono_bridge.
Require Import src.fresco.algo.prop_precise.
Require Import src.fresco.algo.prop_pat_sub.
Require Import src.fresco.algo.consis.prop_consis_precise.
Require Import src.fresco.algo.sub.prop_looksub.
Require Import src.fresco.algo.sub.prop_solve_sub.
Require Import src.fresco.algo.sub.prop_completeness_sub_precise.
Require Import src.fresco.algo.prop_normal.
Require Import src.fresco.algo.prop_inc_strengthen.
Require Import src.fresco.algo.prop_compose.
Require Import src.fresco.algo.prop_metasubst.
Require Import src.fresco.algo.sub.look.prop_rsubst.
Require Import src.fresco.algo.sub.look.prop_solve_ext.
Require Import src.fresco.algo.sub.look.prop_eq_var.

Set Implicit Arguments.

(* Reusable: retag the tag index of a partial-precision derivation.
   (mirror of [ad_partial_precise_delta_cong]; migrate to prop_precise.v). *)

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
Lemma ftag_in_uskl_subst_uskl_in_uskl : forall R0 α R',
  ftag_in_uskl (subst_uskl_in_uskl R0 α R')
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
  pose proof (ftag_ptyp_to_uskl_syn (msubst_lookup κ α)) as Hgf.
  fsetdec.
Qed.

(* Compose two constraint solves over an appended EQ-only list.  ⭐ It THREADS
   now (the SolE-FlexR repair): the second half runs at the first half's block,
   and the outputs concatenate in the same right-to-left order the rules use. *)
Lemma a_solve_cstr_app : forall Θ C1 𝒞2 Pi Pmid Pa Ξ1 Ξ2,
  Forall (fun c => exists Q, c = a_cstr_eq Q) C1 ->
  {{ Θ ⊩ C1 ⨾ Pi ⤳ Ξ1 ⨾ Pmid }}a ->
  {{ (Ξ1 ++ Θ) ⊩ 𝒞2 ⨾ Pmid ⤳ Ξ2 ⨾ Pa }}a ->
  {{ Θ ⊩ (C1 ++ 𝒞2) ⨾ Pi ⤳ (Ξ2 ++ Ξ1) ⨾ Pa }}a.
Proof.
  intros Θ C1; revert Θ; induction C1 as [ | c C1' IH ];
    intros Θ 𝒞2 Pi Pmid Pa Ξ1 Ξ2 Hall H1 H2.
  - inversion H1; subst. cbn [app] in *. rewrite app_nil_r. exact H2.
  - inversion Hall as [ | ? ? [Q ->] Hall' ]; subst.
    inversion H1 as [ | | ? ? ? ? Ξ1a Ξ1b ? P'' Heq Htail ]; subst.
    cbn [app]. rewrite <- (aenv_app_assoc Ξ2 Ξ1b Ξ1a).
    eapply a_solve_cstr__eq;
      [ exact Heq
      | eapply IH;
          [ exact Hall' | exact Htail
          | rewrite (aenv_app_assoc Ξ1b Ξ1a Θ) in H2; exact H2 ] ].
Qed.

(* Case-split helpers for the paper's three special cases. *)
Lemma pskl_ghost_dec : forall (P : pskl), P = pskl_ghost \/ P <> pskl_ghost.
Proof. destruct P; solve [ left; reflexivity | right; discriminate ]. Qed.

(* ⚙ RENAMED from [pskl_var_dec] 2026-08-09 (cleanup audit §8.1c): it collided with a
   DIFFERENT lemma of that name, and this one decides P = var a for a GIVEN a; prop_completeness_consis.v's decides 'is a var at all'. *)
Lemma pskl_eq_var_dec : forall (P : pskl) (a : atom),
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

(** ⚙ The [∩ … [=] empty] form of an avoid-set conclusion, from its ∀-form
    input — which is how P6-Cs / P6-Ss report the fact. *)
Lemma inter_dom_empty_of_forall : forall (S : atoms) (Ξ : aenv),
  (forall α0, α0 `in` dom Ξ -> α0 `notin` S) ->
  S ∩ dom Ξ [=] empty.
Proof.
  intros S Ξ Hfr.
  apply AtomSetProperties.empty_is_empty_1.
  intros x Hx. apply AtomSetFacts.inter_iff in Hx. destruct Hx as [H1 H2].
  exact (Hfr x H2 H1).
Qed.

Lemma a_lookeq_all_flex_mono : forall Θ α P P0 Ξ 𝒞,
  {{ Θ ⊢ P ∼[ α ] P0 ⤳ Ξ ⨾ 𝒞 }}a -> all_flex_mono Ξ.
Proof.
  intros Θ α P P0 Ξ 𝒞 H; unfold all_flex_mono; induction H.
  - constructor.                                          (* var *)
  - constructor.                                          (* absent *)
  - constructor.                                          (* vacuous *)
  - constructor; [ reflexivity | constructor ].          (* flex_r *)
  - apply Forall_app; split; assumption.                 (* arrow *)
  - assumption.                                           (* forall_inh *)
  - assumption.                                           (* forall_syn *)
  - assumption.                                           (* univ_ghost *)
  - assumption.                                           (* univ_ghost1 *)
  - assumption.                                           (* univ_ghost2 *)
  - assumption.                                           (* univ_ghost_r *)
Qed.

(* ⚙️ MOVED UP to sub/look/prop_rsubst.v (2026-08-04, the SolE-FlexR repair).
   The whole mid-block weakening kit — Metalib's [binds_weaken],
   [binds_strengthen_mid], [a_flex_tvar_weaken_mid], [a_non_flex_weaken_mid],
   [a_solve_sub_eq_weaken_mid_flex_size] and its two corollaries
   [a_solve_sub_weaken_mid_flex] / [a_solve_eq_weaken_mid_flex], plus
   [a_inc_flex_prefix_split] / [a_inc_flex_prefix_build] — is needed at EVERY
   level of the P6 tower now, not only here, because every arrow row merges two
   generated blocks.  The moved statements THREAD the block and carry the new
   [dom Ξm ∩ dom Ξ = ∅] premise; see also [a_solve_eq_weaken_flex_block], which
   is the packaged form the arrow rows actually call. *)

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

(* ⚙ Peeling a COMMON PREFIX off both sides of a lookup equation is
   [msubst_lookup_app_agree] (prop_metasubst.v).  With
   [msubst_lookup_app_swap] this is all the block algebra the arrow row's
   κ-reordering needs — a swap moves the top two blocks, that one gets at the
   ones below.  (Its pointwise-everywhere twin [msubst_lookup_app_congr] was
   deleted 2026-10-10.) *)



(* [binds] over an append is plain MEMBERSHIP, so any reordering of the blocks
   preserves it — no disjointness side condition anywhere.  The arrow row moves
   between the order its right IH produced ([Ξs2, Ξc2, Ξs1, Ξc1, Θ0]) and the
   conclusion's ([Ξs2, Ξs1, Ξc1, Ξc2, Θ0]), and back. *)
Lemma binds_rot_app : forall (x : atom) (b : abind) A B C D,
  binds x b (A ++ B ++ C ++ D) -> binds x b (B ++ C ++ A ++ D).
Proof. intros x b A B C D H. analyze_binds H. Qed.

Lemma binds_rot_app_rev : forall (x : atom) (b : abind) A B C D,
  binds x b (B ++ C ++ A ++ D) -> binds x b (A ++ B ++ C ++ D).
Proof. intros x b A B C D H. analyze_binds H. Qed.

Lemma binds_app_perm5 : forall (x : atom) (b : abind) A B C D E,
  binds x b (A ++ B ++ C ++ D ++ E) -> binds x b (A ++ C ++ D ++ B ++ E).
Proof. intros x b A B C D E H. analyze_binds H. Qed.

(* Build [a_wf_aenv] of an all-flex_mono prefix over a wf tail. *)
Lemma a_wf_aenv_flex_prefix : forall Ξ Θ0,
  all_flex_mono Ξ -> uniq (Ξ ++ Θ0) -> {{ ⊢ Θ0 }}a -> {{ ⊢ (Ξ ++ Θ0) }}a.
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
(* The [dom Θ' ⊆ dom Θ] premise is inherited from
   [a_solve_sub_eq_ctx_change], which became SHRINK-only in the freshness
   campaign: the exists-fresh binder rules carry [∉ dom Θ] side conditions,
   so growth can capture a recorded witness.  Both call sites are context
   SWAPS, where the domains are equal. *)
(* Both flex conditions ride under an appended prefix — the shape the eq row's
   THREADED tail needs (it runs at [Ξ1 ++ Θ], not at [Θ]). *)

Lemma a_solve_cstr_ctx_change : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  forall Θ',
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  (forall α, a_flex_tvar Θ α -> a_flex_tvar Θ' α) ->
  (forall P0, a_flex Θ' P0 -> a_flex Θ P0) ->
  {{ Θ' ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H; intros Θ' Hdom Hft Hfl.
  - apply a_solve_cstr__empty.
  - apply a_solve_cstr__sub. eapply (proj1 a_solve_sub_eq_ctx_change); eauto.
  - eapply a_solve_cstr__eq;
      [ eapply (proj2 a_solve_sub_eq_ctx_change);
          [ eassumption | eauto | eauto | eauto ]
      | apply IHa_solve_cstr;
          [ repeat rewrite ftvar_in_aenv_app; clear - Hdom; fsetdec
          | intros α0 Hf0; eapply a_flex_tvar_app_mono; [ exact Hft | exact Hf0 ]
          | intros P1 Hf1; eapply a_flex_app_anti; [ exact Hfl | exact Hf1 ] ] ].
Qed.

(* The OUTPUT premise is inherited from the mutual lemma (a leaked SS-ForallR
   witness cannot be moved, so the inserted block must avoid it by
   hypothesis).  Its two call sites read it off [a_solve_cstr_ftv_eq]: their
   constraint lists are all-eq, and the eq half never leaks. *)
Lemma a_solve_cstr_weaken_mid_flex : forall Ξl Ξm Θ0 𝒞 P Ξ P',
  all_flex_mono Ξm ->
  (forall x, x `in` dom Ξm -> x `notin` dom (Ξl ++ Θ0)) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_a_cstrs 𝒞) ->
  (forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P') ->
  (* ⭐ NEW (2026-08-04): the inserted block must also dodge the block the
     SOLVE ITSELF generates — SolE-FlexR invents names, and an inserted key
     that collided with one would conflate two independently-invented
     flexibles. *)
  (forall x, x `in` dom Ξm -> x `notin` dom Ξ) ->
  {{ (Ξl ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  {{ (Ξl ++ Ξm ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a.
Proof.
  intros Ξl Ξm Θ0 𝒞 P Ξ P' Hfm Hdisj HP HC Hfin Hblk Hsolve.
  remember (Ξl ++ Θ0) as Θ eqn:HeqΘ.
  revert Ξl Θ0 HeqΘ Hdisj HP HC Hfin Hblk.
  induction Hsolve; intros Ξl Θ0 HeqΘ Hdisj HP HC Hfin Hblk; subst.
  - apply a_solve_cstr__empty.
  - (* sub *)
    apply a_solve_cstr__sub.
    eapply a_solve_sub_weaken_mid_flex;
      [ eassumption | reflexivity | exact Hfm | exact Hdisj | exact HP
      | exact Hfin | exact Hblk ].
  - (* eq — the intermediate output is bounded EXACTLY (the eq half), and the
       tail now runs UNDER the first premise's block *)
    assert (Hb1 : forall x, x `in` dom Ξm -> x `notin` dom Ξ1)
      by (intros x Hx; specialize (Hblk x Hx);
          rewrite dom_app in Hblk; clear - Hblk; fsetdec).
    assert (Hb2 : forall x, x `in` dom Ξm -> x `notin` dom Ξ2)
      by (intros x Hx; specialize (Hblk x Hx);
          rewrite dom_app in Hblk; clear - Hblk; fsetdec).
    assert (Hmid : forall x, x `in` dom Ξm -> x `notin` ftvar_in_pskl P'').
    { intros x Hx.
      pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ _ H) as Hf.
      specialize (HP x Hx). specialize (HC x Hx). specialize (Hb1 x Hx).
      simpl in HC. clear - Hf HP HC Hb1; fsetdec. }
    eapply a_solve_cstr__eq.
    + eapply a_solve_eq_weaken_mid_flex;
        [ eassumption | reflexivity | exact Hfm | exact Hdisj | exact HP
        | exact Hmid | exact Hb1 ].
    + rewrite <- (aenv_app_assoc Ξ1 Ξl (Ξm ++ Θ0)).
      apply IHHsolve;
        [ rewrite (aenv_app_assoc Ξ1 Ξl Θ0); reflexivity
        | intros x Hx; rewrite dom_app; rewrite dom_app;
          specialize (Hdisj x Hx); specialize (Hb1 x Hx);
          rewrite dom_app in Hdisj; clear - Hdisj Hb1; fsetdec
        | exact Hmid
        | (* ftv 𝒞 avoids Ξm : 𝒞 ⊆ (eq Q :: 𝒞) *)
          intros x Hx; specialize (HC x Hx); simpl in HC;
          clear - HC; fsetdec
        | exact Hfin
        | exact Hb2 ].
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
  apply msubst_pskl_ftv_keep; [ exact Hdom | ].
  rewrite ftvar_in_pskl_uskl_to_pskl; exact Hin.
Qed.

(* A mono-paint consistency subject is well-formed as a monotype: every
   variable leaf is [a_binds_tvar] (from [__var] / [__flex_l]). *)

(* closes an α-leaf: the whole subject IS ψa, faced with mono-ish Q. *)
Ltac psia_leaf Hrec :=
  match goal with
  | HwfΘ : {{ ⊢ ?Θ }}a, Htsk : is_dskl ?ψa, Hmi : bskl_monoish ?Q |- _ =>
      let τψ := fresh "τψ" in let Hmn := fresh "Hmn" in let Heqψ := fresh "Heqψ" in
      destruct (ad_pat_consis_monoish_counterpart Hrec HwfΘ Htsk Hmi)
        as (_ & τψ & Hmn & Heqψ);
      exists τψ; repeat split;
        [ exact Hmn | exact Heqψ
        | eapply ad_pat_consis_mono_subject_wf;
            [ exact Hrec | exact Heqψ | exact Hmn ] ]
  end.

(* THE ψa-MONO EXTRACTION (the flex-P0 crux).  When the whole consistency
   subject [(κR)[ψa/αs]] faces a MONO-ISH [Q] (the case of a flexible P0,
   whose κ-image is a monotype pinning Q mono-ish), the instantiation
   [ψa] sitting at the αs-positions is itself a mono paint.  Induction on the
   consistency: at an αs-leaf ([T = var αs], subject = ψa) it is
   [ad_pat_consis_monoish_counterpart]; at an arrow it recurses into the side
   carrying αs; flex_r/univ_ghost_drop recurse on the sub-derivation; ghost/∀
   counterparts are excluded by [bskl_monoish Q]. *)
Lemma ad_pat_consis_subst_psia_mono : forall Ψs Θ Rsubj Q,
  {{ Ψs ⨟ Θ ⊢ˢ Rsubj ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  bskl_monoish Q ->
  forall R' ψa αs,
    Rsubj = subst_uskl_in_uskl ψa αs R' ->
    is_dskl ψa ->
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
      assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ uskl_unit ∼ bskl_unit }}ad)
        by (apply ad_pat_consis__unit; assumption).
      psia_leaf Hrec.
  - (* var α : Q = bskl_var α *)
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj.
    + subst ψa.
      assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_var_f α) ∼ (bskl_var_f α) }}ad)
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
      assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2) }}ad)
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
  - (* ghostg : Q = bskl_ghost *) inversion Hmi.
  - (* dot_univ_ghost : Q = bskl_univ_ghost *) inversion Hmi.
  - (* ghost : subject uskl_ghost is not is_dskl *)
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    + destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa; inversion Htsk | discriminate HeqSubj ].
    + simpl in Hα; clear - Hα; exfalso; fsetdec.
  - (* univ_ghost : Q = bskl_univ_ghost *) inversion Hmi.
  - (* univ_ghost_inh : Q = bskl_all_inh *) inversion Hmi.
  - (* univ_ghost_drop : subject uskl_univ_ghost R, Q arbitrary *)
    destruct R' as [ | nb | β | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
      simpl in HeqSubj; try discriminate HeqSubj.
    + (* R' = var β : ψa = uskl_univ_ghost R, not is_dskl *)
      destruct (eq_var β αs) as [ -> | Hβ ]; simpl in HeqSubj;
        [ subst ψa; inversion Htsk | discriminate HeqSubj ].
    + (* R' = univ_ghost T0 : recurse on the body *)
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

(* ===================================================================== *)
(*  The ρ-GENERALIZED ψa-mono extraction (P6-Cs's flexible-P0 row under ρ). *)
(*                                                                         *)
(*  Under the ρ-generalization the consistency subject is no longer         *)
(*  [(κR)[ψa/α]] but its ρ-IMAGE, so [ad_pat_consis_subst_psia_mono] does   *)
(*  not apply syntactically.  ⚠️ It does NOT apply after a "commutation"     *)
(*  either: [uskl_rsubst] is a RELATION, not a substitution — [ursubst__leaf]     *)
(*  may send two occurrences of the SAME Δρ-variable to DIFFERENT images —  *)
(*  so [ρ((κR)[ψa/α]) = (ρψa)[ρ(κR)/α]] is FALSE in general (take           *)
(*  R = α→α, ψa = β ∈ Δρ, and give the two βs different images).            *)
(*                                                                         *)
(*  What IS available at the call site is that the guess is Δρ-CLEAN       *)
(*  (P6-Cs's premise [ftvar_in_uskl ψa ∩ Δρ = ∅]).  Cleanliness makes ρ the *)
(*  identity ON THE GUESS ([uskl_rsubst_clean_eq]), which is exactly what   *)
(*  the αs-leaf needs;                                                     *)
(*  everywhere else ρ is threaded structurally, and the [ursubst__leaf]        *)
(*  disjunct is impossible because the ideal there is a Δρ-variable while   *)
(*  the ideal here is either ψa (clean) or an αs-carrying ρ-free position.  *)
(* ===================================================================== *)

(** The αs-LEAF step: [R' = αs], so the ideal IS the guess, ρ collapses to
    equality, and the ρ-free [psia_leaf] argument applies verbatim. *)
Lemma psia_rsubst_leaf_step : forall Ψs Θ Rsubj Q NM Δρ Ψρ ψa αs R',
  {{ Ψs ⨟ Θ ⊢ˢ Rsubj ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  bskl_monoish Q ->
  uskl_rsubst NM Θ Δρ Ψρ Rsubj (subst_uskl_in_uskl ψa αs R') ->
  R' = uskl_var_f αs ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  is_dskl ψa ->
  exists τψ, mono_ptyp τψ /\ ψa = ptyp_to_uskl_syn τψ /\ a_wf_ptyp Θ τψ.
Proof.
  intros Ψs Θ Rsubj Q NM Δρ Ψρ ψa αs R' Hcons HwfΘ Hmi Hrho HeqR Hclean Htsk.
  subst R'.
  assert (Hid : subst_uskl_in_uskl ψa αs (uskl_var_f αs) = ψa)
    by (simpl; match goal with |- context [if ?c then _ else _] => destruct c end;
        [ reflexivity | congruence ]).
  rewrite Hid in Hrho.
  destruct (uskl_rsubst_clean_eq Hrho Hclean) as [-> _].
  destruct (ad_pat_consis_monoish_counterpart Hcons HwfΘ Htsk Hmi)
    as (_ & τψ & Hmn & Heqψ).
  exists τψ; repeat split;
    [ exact Hmn | exact Heqψ
    | eapply ad_pat_consis_mono_subject_wf;
        [ exact Hcons | exact Heqψ | exact Hmn ] ].
Qed.

(** The [ursubst__leaf] disjunct never fires on an αs-carrying ideal. *)
Lemma psia_rsubst_leaf_impossible : forall ψa αs R' βρ Δρ,
  subst_uskl_in_uskl ψa αs R' = uskl_var_f βρ ->
  βρ `in` Δρ ->
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  αs `notin` Δρ ->
  αs `in` ftvar_in_uskl R' ->
  False.
Proof.
  intros ψa αs R' βρ Δρ Heq Hβ Hclean Hαρ Hα.
  destruct R' as [ | nb | γ | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
    simpl in Heq; try discriminate Heq.
  destruct (eq_var γ αs) as [ -> | Hγ ]; simpl in Heq.
  - (* the guess IS the Δρ-variable — contradicts cleanliness *)
    subst ψa. simpl in Hclean. clear - Hclean Hβ; fsetdec.
  - (* otherwise αs = γ = βρ ∈ Δρ, contradicting αs ∉ Δρ *)
    injection Heq as Heq; subst γ.
    simpl in Hα. clear - Hα Hαρ Hβ; fsetdec.
Qed.

Lemma ad_pat_consis_rsubst_psia_mono : forall Ψs Θ Rsubj Q,
  {{ Ψs ⨟ Θ ⊢ˢ Rsubj ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  bskl_monoish Q ->
  forall NM Δρ Ψρ R' ψa αs,
    uskl_rsubst NM Θ Δρ Ψρ Rsubj (subst_uskl_in_uskl ψa αs R') ->
    (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
    αs `notin` Δρ ->
    is_dskl ψa ->
    αs `in` ftvar_in_uskl R' ->
    exists τψ, mono_ptyp τψ /\ ψa = ptyp_to_uskl_syn τψ /\ a_wf_ptyp Θ τψ.
Proof.
  intros Ψs Θ Rsubj Q H. induction H;
    intros HwfΘ Hmi NM Δρ Ψρ R' ψa αs Hrho Hclean Hαρ Htsk Hα.
  - (* unit *)
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ uskl_unit ∼ bskl_unit }}ad)
      by (apply ad_pat_consis__unit; assumption).
    destruct (uskl_rsubst_unit_l_inv Hrho) as [ [Heq _] | Hleaf ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
  - (* var α *)
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_var_f α) ∼ (bskl_var_f α) }}ad)
      by (apply ad_pat_consis__var; assumption).
    destruct (uskl_rsubst_var_l_inv Hrho) as [ [Heq _] | Hleaf ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
  - (* arrow *)
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2) }}ad)
      by (eapply ad_pat_consis__arrow; [ exact H | exact H0 | exact H1 ]).
    destruct (uskl_rsubst_arrow_l_inv Hrho) as [ [Heq _] | [ Hleaf | Hcong ] ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
    + destruct Hcong as (Ia & Ib & Ψr1 & Ψr2 & Heq & Hra & Hrb & _).
      destruct R' as [ | nb | γ | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
        simpl in Heq; try discriminate Heq.
      * (* R' = var γ : either the αs-leaf, or shape-absurd *)
        destruct (eq_var γ αs) as [ -> | Hγ ]; simpl in Heq;
          [ | discriminate Heq ].
        eapply psia_rsubst_leaf_step;
          [ exact Hrec | exact HwfΘ | exact Hmi | exact Hrho | reflexivity
          | exact Hclean | exact Htsk ].
      * (* R' = arrow T1 T2 : recurse into the side carrying αs *)
        injection Heq as HeqA HeqB; subst Ia Ib.
        assert (HmiQ1 : bskl_monoish Q1) by (inversion Hmi; assumption).
        assert (HmiQ2 : bskl_monoish Q2) by (inversion Hmi; assumption).
        simpl in Hα; apply union_1 in Hα; destruct Hα as [Hα | Hα].
        -- eapply IHad_pat_consis1;
             [ exact HwfΘ | exact HmiQ1 | exact Hra | exact Hclean
             | exact Hαρ | exact Htsk | exact Hα ].
        -- eapply IHad_pat_consis2;
             [ exact HwfΘ | exact HmiQ2 | exact Hrb | exact Hclean
             | exact Hαρ | exact Htsk | exact Hα ].
  - (* forall_inh_tagged *) inversion Hmi.
  - (* forall_inh_untagged *) inversion Hmi.
  - (* forall_syn_tagged *) inversion Hmi.
  - (* forall_syn *) inversion Hmi.
  - (* ghostg *) inversion Hmi.
  - (* dot_univ_ghost *) inversion Hmi.
  - (* ghost *)
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ uskl_ghost ∼ (pskl_to_bskl_inh P) }}ad)
      by (apply ad_pat_consis__ghost; assumption).
    destruct (uskl_rsubst_ghost_l_inv Hrho) as [ [Heq _] | Hleaf ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
  - (* univ_ghost *) inversion Hmi.
  - (* univ_ghost_inh *) inversion Hmi.
  - (* univ_ghost_drop *)
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_univ_ghost R) ∼ Q }}ad)
      by (apply ad_pat_consis__univ_ghost_drop; exact H).
    destruct (uskl_rsubst_univ_ghost_l_inv Hrho) as [ [Heq _] | [ Hleaf | Hcong ] ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
    + destruct Hcong as (I0 & Heq & Hr0).
      destruct R' as [ | nb | γ | T1 T2 | T0 | εt T0 | | T0 | | T0 ];
        simpl in Heq; try discriminate Heq.
      * destruct (eq_var γ αs) as [ -> | Hγ ]; simpl in Heq;
          [ | discriminate Heq ].
        eapply psia_rsubst_leaf_step;
          [ exact Hrec | exact HwfΘ | exact Hmi | exact Hrho | reflexivity
          | exact Hclean | exact Htsk ].
      * injection Heq as Heq; subst I0.
        simpl in Hα.
        eapply IHad_pat_consis;
          [ exact HwfΘ | exact Hmi | exact Hr0 | exact Hclean
          | exact Hαρ | exact Htsk | exact Hα ].
  - (* flex_l *)
    assert (Hrec : {{ Ψ ⨟ Θ ⊢ˢ (uskl_var_f α) ∼ Q }}ad)
      by (eapply ad_pat_consis__flex_l; [ exact H | exact H0 ]).
    destruct (uskl_rsubst_var_l_inv Hrho) as [ [Heq _] | Hleaf ].
    + eapply ad_pat_consis_subst_psia_mono;
        [ exact Hrec | exact HwfΘ | exact Hmi | symmetry; exact Heq
        | exact Htsk | exact Hα ].
    + exfalso. destruct Hleaf as (βρ & Ψρ0 & Heqv & Hβρ & _ & _ & _).
      eapply psia_rsubst_leaf_impossible; eassumption.
  - (* flex_r : unfold the definition; the premise faces a mono paint *)
    assert (Hmd : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ]).
    eapply IHad_pat_consis;
      [ exact HwfΘ | apply bskl_monoish_paint; exact Hmd
      | exact Hrho | exact Hclean | exact Hαρ | exact Htsk | exact Hα ].
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
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Ra Rb, R = uskl_arrow Ra Rb ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  lc_bskl Q ->
  exists Ψ1 Ψ2 Q1 Q2,
    Ψs [=] Ψ1 `union` Ψ2 /\
    ({{ Ψ1 ⨟ Θ ⊢ˢ Ra ∼ Q1 }}ad) /\
    ({{ Ψ2 ⨟ Θ ⊢ˢ Rb ∼ Q2 }}ad) /\
    ({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_arrow Q1 Q2) }}ad) /\
    ({{ Ψs ⨟ Θ ⊢ˢ (uskl_arrow Ra Rb) ∼ (bskl_arrow Q1 Q2) }}ad) /\
    lc_bskl (bskl_arrow Q1 Q2).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros Ra Rb Heq Δr Ql Hdf Href Hlc;
    try discriminate Heq.
  - (* __arrow: the structural case — read the split straight off *)
    injection Heq as Hea Heb; subst.
    do 4 eexists.
    split; [ eassumption | ].
    split; [ eassumption | ].
    split; [ eassumption | ].
    split; [ exact Href | ].
    split; [ eapply ad_pat_consis__arrow; eassumption | exact Hlc ].
  - (* __flex_r: unfold ONE definition step on BOTH sides, then recurse *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* ---- guarded-source inversions of refinement ---- *)

(* A guarded source never refines to a ∀ target (no lc side condition). *)
Lemma ad_refine_syn_guarded_r_not_all : forall Θ Δr Q Q',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q ⊳ Q' }}ad ->
  guarded_bskl Q ->
  forall Q0, Q' <> bskl_all_inh Q0 /\ Q' <> bskl_all_syn Q0.
Proof.
  intros Θ Δr Q Q' HwfΘ Href; induction Href; intros Hg Q0;
    try solve [ inversion Hg | split; discriminate ].
  assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
  apply IHHref; [ exact HwfΘ | ].
  apply mono_bskl_guarded, mono_ptyp_to_bskl_syn; exact Hmτ.
Qed.

(* The ∀-target form of [ad_refine_syn_guarded_r]: there the conclusion is
   absurd, so no lc side condition is needed. *)
Lemma ad_refine_syn_guarded_r_all : forall Θ Δr Q Q',
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q ⊳ Q' }}ad ->
  guarded_bskl Q ->
  (exists Q0, Q' = bskl_all_inh Q0 \/ Q' = bskl_all_syn Q0) ->
  guarded_bskl Q'.
Proof.
  intros Θ Δr Q Q' HwfΘ Href Hg (Q0 & HQ0).
  exfalso. destruct (ad_refine_syn_guarded_r_not_all HwfΘ Href Hg Q0).
  destruct HQ0; contradiction.
Qed.

(* Only a ∀◇-headed (or □) source can refine to a ∀◇ target: the ∀/guarded
   sources are shape-excluded, and a defined-flex source unfolds to a MONOTYPE
   painting, which is guarded.  Kills every P0 but [∀◇P0'] in the ∀◈/∀◇ cases. *)
Lemma ad_refine_syn_univ_ghost_rhs_src : forall Θ Δr Q' Q,
  {{ ⊢ Θ }}a ->
  {{ Θ ⨟ Δr ⊢ᵣ Q' ⊳ Q }}ad ->
  forall Q0, Q = bskl_univ_ghost Q0 ->
  (exists L0, Q' = bskl_univ_ghost L0) \/ Q' = bskl_ghost.
Proof.
  intros Θ Δr Q' Q HwfΘ Href; induction Href; intros Q0 Heq;
    try discriminate Heq.
  - (* __ghost *)
    right; reflexivity.
  - (* __univ_ghost_remove *) left; eexists; reflexivity.
  - (* __univ_ghost_keep *) left; eexists; reflexivity.
  - (* __flex_l: the definition is a monotype, whose painting is guarded *)
    exfalso.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    destruct (IHHref HwfΘ Q0 Heq) as [[L0 HL0] | HL0];
      destruct τ; simpl in HL0; try discriminate HL0; inversion Hmτ.
Qed.

(* [∀◇]-subject consistency against a GUARDED target: the ghost must have been
   DROPPED (C-UnivGhost2) — [__univ_ghost]/[__univ_ghost_inh] have non-guarded targets,
   and a defined-flex target unfolds (on both sides) to a guarded monotype
   painting.  The paper's "by well-formedness of P ... Q is guarded" step. *)
Lemma ad_pat_consis_univ_ghost_guarded_unify : forall Ψs Θ R Q,
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall R0, R = uskl_univ_ghost R0 ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  guarded_bskl Q ->
  lc_bskl Q ->
  exists Q0,
    ({{ Ψs ⨟ Θ ⊢ˢ R0 ∼ Q0 }}ad) /\
    ({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q0 }}ad) /\
    guarded_bskl Q0 /\ lc_bskl Q0.
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros R0 Heq Δr Ql Hdf Href Hg Hlc;
    try discriminate Heq.
  - (* __univ_ghost : target ∀◇Q — not guarded *) inversion Hg.
  - (* __univ_ghost_inh : target ∀ — not guarded *) inversion Hg.
  - (* __univ_ghost_drop : the ghost is dropped *)
    injection Heq as He; subst.
    eexists; split; [ eassumption | split; [ exact Href | split; [ exact Hg | exact Hlc ] ] ].
  - (* __flex_r: unfold ONE definition step on BOTH sides, then recurse *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_guarded, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* [∀◈]-subject consistency (rule C-UnivGhostG) up to the target's defined-flex
   chain — the [ad_pat_consis_arrow_refine_unify] pattern for [uskl_dot_univ_ghost]. *)
Lemma ad_pat_consis_dot_univ_ghost_refine_unify : forall Ψs Θ R Q,
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall R0, R = uskl_dot_univ_ghost R0 ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  lc_bskl Q ->
  exists Q0,
    ({{ Ψs ⨟ Θ ⊢ˢ R0 ∼ Q0 }}ad) /\
    ({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_univ_ghost Q0) }}ad) /\
    lc_bskl Q0.
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros R0 Heq Δr Ql Hdf Href Hlc;
    try discriminate Heq.
  - (* __dot_univ_ghost *)
    injection Heq as He; subst.
    eexists; split; [ eassumption | split; [ exact Href | inversion Hlc; assumption ] ].
  - (* __flex_r: unfold ONE definition step on BOTH sides, then recurse *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* ===================================================================== *)
(*  §2  ∀-BINDER KIT.  The ∀ / ∀◇-vs-∀ rows run the IH under a FRESH rigid    *)
(*  binder β, added to BOTH Θ (the consistency/refinement context) and Θ0 *)
(*  (the algorithmic input context); every output must then lose β again  *)
(*  — the paper's "these judgements hold without β".                      *)
(* ===================================================================== *)

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
Lemma a_solve_cstr_strip_tvar_mid : forall Ξ β Θ0 𝒞 P Ξo P',
  {{ (Ξ ++ (β ~ abind_tvar) ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ Ξo ⨾ P' }}a ->
  {{ (Ξ ++ Θ0) ⊩ 𝒞 ⨾ P ⤳ Ξo ⨾ P' }}a.
Proof.
  intros Ξ β Θ0 𝒞 P Ξo P' H.
  eapply a_solve_cstr_ctx_change; [ exact H | | | ].
  - (* the ftv SHRINKS — the exists-fresh side conditions transport *)
    repeat rewrite ftvar_in_aenv_app; simpl; clear; fsetdec.
  - intros α Hft; destruct Hft as [Hb | [τ Hb]];
      [ left | right; exists τ ]; analyze_binds Hb.
  - intros P0 Hf; inversion Hf; subst;
      [ eapply a_flex__var | eapply a_flex__var_def ];
      apply binds_weaken; eassumption.
Qed.

(* ===================================================================== *)
(*  ⭐⭐ THE ForallR-PRIORITY REORDER (2026-08-18)                          *)
(*                                                                        *)
(*  Under the ForallR-PRIORITY GUARD [forall_r_off] an LS-ForallL step is  *)
(*  BLOCKED at a ghost-free ∀ counterpart in check mode, because there the *)
(*  runner commits to LS-ForallR.  P6-Ss builds exactly such steps, so it  *)
(*  needs the reordered derivation: peel the COUNTERPART first, and only   *)
(*  then the subject.                                                      *)
(*                                                                        *)
(*  The collection side of one peel is [a_looksub_open_target]             *)
(*  (algo/sub/prop_looksub.v §2c) — an INVERSION, since under the guard    *)
(*  only Var / Absent / ForallR can be the root there.  What follows is    *)
(*  the SOLVE side of the same peel, and then the two together, iterated   *)
(*  on the counterpart's size.                                             *)
(* ===================================================================== *)

(** The solve reads its context only for FLEXIBILITY and for freshness, and
    two rigid entries commute in both. *)

(** ⭐⭐ SS-ForallR, GENERALIZED PAST THE SOLVE-DISPATCH GUARD (2026-08-18).

    Under guard 5 the row no longer fires at a VARIABLE, a [∀] or a [⫯]
    subject — the implementation dispatches on the subject first
    (type.ml:494) — but the completeness chain builds it at an ARBITRARY
    accumulated pattern.  ⭐ The peeled routes give the SAME answer, and
    that is what this block proves: the old rule survives as a DERIVED one.

    ⚙ Three inversions and a size induction.  The [∀] case is the
    COMMUTATION §8c.16 §D budgeted, and it is paid exactly once, here,
    instead of at every consumer: peel the subject's binder, EXCHANGE the
    two rigid openers, recurse, and re-close. *)

Lemma a_solve_sub_forall_r_gen_n : forall n Θ P B Ξ P' β,
  size_pskl P <= n ->
  pskl_ghost_free (pskl_all_syn B) ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
     (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
  {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a.
Proof.
  induction n as [ | n IH ]; intros Θ P B Ξ P' β Hsz Hgf Hβ HD;
    [ exfalso; destruct P; simpl in Hsz; lia | ].
  destruct P as [ | k | α | P1 P2 | P0 | | P0 ].
  - apply a_solve_sub__forall_r with (β := β);
      [ exact Hgf | apply solve_l_off_unit | exact Hβ | exact HD ].
  - apply a_solve_sub__forall_r with (β := β);
      [ exact Hgf | apply solve_l_off_var_b | exact Hβ | exact HD ].
  - (* a VARIABLE subject: [SS-Var] answers it, and so did the premise *)
    destruct (a_solve_sub_var_subject HD) as [-> ->].
    apply a_solve_sub__var.
  - apply a_solve_sub__forall_r with (β := β);
      [ exact Hgf | apply solve_l_off_arrow | exact Hβ | exact HD ].
  - (* ⭐ a ∀ subject: THE COMMUTATION.  Peel, exchange the two rigid
       openers, recurse, re-close. *)
    destruct (a_solve_sub_inv_forall_l HD) as (β' & P'' & Hβ' & -> & Hp).
    apply a_solve_sub_ctx_exchange in Hp.
    simpl in Hsz, Hβ.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f β'))
      as Hup.
    rewrite ftvar_in_aenv_cons_tvar in Hβ'.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower B (pskl_var_f β))
      as Hlow.
    apply a_solve_sub__forall_l with (β := β').
    + clear - Hβ' Hlow. simpl in *. fsetdec.
    + apply (IH _ _ _ _ _ β).
      * rewrite size_pskl_open_pskl_wrt_pskl_var. lia.
      * exact Hgf.
      * rewrite ftvar_in_aenv_cons_tvar.
        assert (Hne : β <> β') by (clear - Hβ'; fsetdec).
        clear - Hβ Hup Hne. simpl in *. fsetdec.
      * exact Hp.
  - apply a_solve_sub__forall_r with (β := β);
      [ exact Hgf | apply solve_l_off_ghost | exact Hβ | exact HD ].
  - (* a ⫯ subject: strip, recurse, re-wrap *)
    destruct (a_solve_sub_inv_univ_ghost_l HD) as (P'' & -> & Hp).
    simpl in Hsz, Hβ.
    apply a_solve_sub__univ_ghost_l.
    apply (IH _ _ _ _ _ β); [ lia | exact Hgf | exact Hβ | exact Hp ].
Qed.

Lemma a_solve_sub_forall_r_gen : forall Θ P B Ξ P' β,
  pskl_ghost_free (pskl_all_syn B) ->
  β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
     (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
  {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a.
Proof.
  intros. eapply a_solve_sub_forall_r_gen_n;
    [ apply le_n | eassumption | eassumption | eassumption ].
Qed.


(** ⭐ ONE PEEL OF THE COUNTERPART, SOLVE SIDE.  At a ghost-free ∀ target in
    check mode only four rows can end an [a_solve_sub] derivation — SS-Var,
    SS-ForallL, SS-UnivGhostL and SS-ForallR (SS-Check and SS-GhostL want a
    [guarded] target, SS-Vacuous a ghost one, SS-Arrow / SS-GhostLF an arrow
    and a function mode).  ⚠️ The opener is EXISTENTIAL for the same reason as
    on the collection side: SS-ForallR LEAKS its binder into the OUTPUT, so
    re-picking it would move [P']. *)
Lemma a_solve_sub_open_target : forall Θ m0 Pi T Ξ Pa,
  {{ Θ ⊢ₛ Pi ≼[ m0 ] T ⤳ Ξ ⨾ Pa }}a ->
  forall B, T = pskl_all_syn B -> m0 = mode_tc ->
  exists γ,
    γ `notin` (ftvar_in_aenv Θ `union` ftvar_in_pskl Pi `union` ftvar_in_pskl B
                 `union` dom Ξ)
    /\ {{ ((γ ~ abind_tvar) ++ Θ) ⊢ₛ Pi ≼[ mode_tc ]
          (open_pskl_wrt_pskl B (pskl_var_f γ)) ⤳ Ξ ⨾ Pa }}a.
Proof.
  intros Θ m0 Pi T Ξ Pa H.
  induction H; intros B0 HT Hm0;
    try discriminate HT; try discriminate Hm0; subst.
  - (* SS-Var — the row answers at ANY target *)
    pick fresh γ for
      (ftvar_in_aenv Θ `union` ftvar_in_pskl (pskl_var_f α)
         `union` ftvar_in_pskl B0).
    exists γ. split; [ simpl in Fr |- *; clear - Fr; fsetdec
                     | apply a_solve_sub__var ].
  - (* SS-ForallL — recurse, then EXCHANGE the two rigid entries back *)
    destruct (IHa_solve_sub B0 eq_refl eq_refl) as [γ [Hγ Hp]].
    rewrite ftvar_in_aenv_cons_tvar in Hγ.
    exists γ. split.
    + pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f β))
        as Hlo.
      simpl. clear - Hγ Hlo. fsetdec.
    + apply a_solve_sub_ctx_exchange in Hp.
      apply a_solve_sub__forall_l with (β := β); [ | exact Hp ].
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B0 (pskl_var_f γ))
        as Hup.
      rewrite ftvar_in_aenv_cons_tvar.
      (* ⚙ [H] is the rule's own freshness side condition; [Hγ] gives
         [γ ≠ β] and [Hup] bounds the opened counterpart. *)
      simpl in H, Hup |- *. clear - H Hγ Hup. fsetdec.
  - (* SS-UnivGhostL *)
    destruct (IHa_solve_sub B0 eq_refl eq_refl) as [γ [Hγ Hp]].
    exists γ. split; [ simpl in Hγ |- *; clear - Hγ; fsetdec | ].
    apply a_solve_sub__univ_ghost_l; exact Hp.
  - (* SS-Check — a ∀ target is never [guarded] *)
    exfalso. match goal with Hg : guarded_pskl _ |- _ => inversion Hg end.
  - (* SS-ForallR — THE ROW: hand its own binder back *)
    injection HT as HTB; subst B0.
    match goal with
    | Hfr : ?b `notin` _ ,
      Hp : {{ ((?b ~ abind_tvar) ++ _) ⊢ₛ _ ≼[ _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
        exists b;
        (* ⭐ [b ∉ dom Ξ] is the run's OWN junk-freeness: the premise ran at
           [(b ~ tvar) ++ Θ], so its block dodges b
           ([a_solve_sub_eq_generated_fresh_set], prop_solve_sub.v) *)
        pose proof ((proj1 a_solve_sub_eq_generated_fresh_set)
                      _ _ _ _ _ _ Hp) as Hjf;
        rewrite ftvar_in_aenv_cons_tvar in Hjf;
        split; [ simpl in Hfr; clear - Hfr Hjf; fsetdec | exact Hp ]
    end.
  - (* SS-GhostL — a ∀ target is never [guarded] *)
    exfalso. match goal with Hg : guarded_pskl _ |- _ => inversion Hg end.
Qed.

(** ⭐⭐ THE PEEL AT A CHOSEN OPENER — and this is what unblocks the reorder.

    The collected constraint NAMES the peeled counterpart, so the collection's
    opener and the solve's opener must be THE SAME atom; but the solve's is
    FORCED (SS-ForallR hands its own binder back) while the collection's is
    sometimes free.  The way out is that the forced opener can be SWAPPED to
    any other, and the two side conditions the swap needs are BOTH consequences
    of the run itself:

      γ0 ∉ dom Ξ    — the run's junk-freeness, since its premise ran at
                      [(γ0 ~ tvar) ++ Θ] ([a_solve_sub_open_target]);
      γ0 ∉ ftv Pa   — because the OUTPUT is bounded by the block and the
                      context ([a_wf_pskl_ftv_dom] at the use site), and γ0
                      dodges both.

    So the caller supplies the output's own scope bound and gets an opener
    avoiding whatever it likes. *)
Lemma a_solve_sub_open_target_avoid : forall (L : atoms) Θ Pi B Ξ Pa,
  {{ Θ ⊢ₛ Pi ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ Pa }}a ->
  all_flex_mono Ξ ->
  ftvar_in_pskl Pa [<=] dom Ξ `union` ftvar_in_aenv Θ ->
  exists γ,
    γ `notin` (L `union` ftvar_in_aenv Θ `union` ftvar_in_pskl Pi
                 `union` ftvar_in_pskl B `union` dom Ξ
                 `union` ftvar_in_pskl Pa)
    /\ {{ ((γ ~ abind_tvar) ++ Θ) ⊢ₛ Pi ≼[ mode_tc ]
          (open_pskl_wrt_pskl B (pskl_var_f γ)) ⤳ Ξ ⨾ Pa }}a.
Proof.
  intros L Θ Pi B Ξ Pa H Hfm Hbound.
  destruct (a_solve_sub_open_target H eq_refl eq_refl) as [γ0 [Hγ0 Hd]].
  pose proof (all_flex_mono_ftvar_in_aenv Hfm) as HΞftv.
  assert (Hγ0Pa : γ0 `notin` ftvar_in_pskl Pa)
    by (clear - Hγ0 Hbound; fsetdec).
  pick fresh γ for
    (L `union` ftvar_in_aenv Θ `union` ftvar_in_pskl Pi `union` ftvar_in_pskl B
       `union` dom Ξ `union` ftvar_in_pskl Pa `union` singleton γ0).
  exists γ. split; [ clear - Fr; fsetdec | ].
  destruct (γ == γ0) as [-> | Hne]; [ exact Hd | ].
  pose proof ((proj1 (a_solve_sub_eq_swap γ0 γ)) _ _ _ _ _ _ Hd) as Hs.
  assert (Hctx : swap_aenv γ0 γ ((γ0 ~ abind_tvar) ++ Θ)
                 = (γ ~ abind_tvar) ++ Θ).
  { simpl. rewrite swap_atom_l.
    rewrite (swap_aenv_fresh_id γ0 γ Θ) by (clear - Hγ0 Fr; fsetdec).
    reflexivity. }
  rewrite Hctx in Hs.
  rewrite swap_pskl_open_var in Hs. rewrite swap_atom_l in Hs.
  rewrite (swap_pskl_fresh_id γ0 γ Pi) in Hs
    by (clear - Hγ0 Fr; fsetdec).
  rewrite (swap_pskl_fresh_id γ0 γ B) in Hs
    by (clear - Hγ0 Fr; fsetdec).
  rewrite (swap_pskl_fresh_id γ0 γ Pa) in Hs
    by (clear - Hγ0Pa Fr; fsetdec).
  rewrite (swap_aenv_fresh_id γ0 γ Ξ) in Hs
    by (clear - Hγ0 Fr HΞftv; fsetdec).
  exact Hs.
Qed.

(** The single-constraint solve inverts. *)
Lemma a_solve_cstr_sub_single_inv : forall Θ m T Pi Ξ Pa,
  {{ Θ ⊩ (a_cstr_sub m T :: nil) ⨾ Pi ⤳ Ξ ⨾ Pa }}a ->
  {{ Θ ⊢ₛ Pi ≼[ m ] T ⤳ Ξ ⨾ Pa }}a.
Proof.
  intros Θ m T Pi Ξ Pa H. inversion H; subst. assumption.
Qed.

(** ⭐⭐⭐ THE REORDER.  P6-Ss caps a collection derivation with LS-ForallL;
    under the ForallR-PRIORITY GUARD that row is BLOCKED whenever the
    counterpart is a ghost-free ∀ at check mode, and there the run must peel
    the COUNTERPART first — repeatedly, since the peeled counterpart can be a
    ghost-free ∀ again.  Hence the induction on the counterpart's SIZE.

    ⭐ The collected constraints come through UNCHANGED except at the α-STACK
    leaf, where LS-Var deposits the counterpart itself.  That is the only cell
    where the SOLVE has to follow the peel, and it is the cell where the two
    sides must agree on ONE opener: the collection's is free there and the
    solve's is forced, so [a_solve_sub_open_target_avoid] moves the forced one.

    ⚙ The last two premises are that lemma's price, and P6-Ss has both on hand:
    the solve's block is all-flex_mono, and its output is scoped by the block
    and the context ([a_wf_pskl_ftv_dom] on the IH's [a_wf_pskl] conjunct). *)
Lemma a_looksub_solve_forall_l : forall n Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β,
  size_pskl P' <= n ->
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl Q (pskl_var_f β))
     ≼[ α , mode_tc ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ Θ2 ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  P' <> pskl_ghost ->
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
                     `union` ftvar_in_pskl P') ->
  all_flex_mono Ξs ->
  ftvar_in_pskl Pa [<=] dom Ξs `union` ftvar_in_aenv Θ2 ->
  (* ⭐ THE BLOCK-vs-CONSTRAINTS INVARIANT rides through the reorder
     (2026-08-20): the α-stack leaf re-derives the solve at a FRESH opener γ
     and puts γ into the new constraint, so the conjunct has to be carried
     rather than re-derived — but γ misses [dom Ξs] by the solve's own
     freshness at the extended context. *)
  (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞) ->
  exists 𝒞',
    {{ Θ ⊢ (pskl_all_syn Q) ≼[ α , mode_tc ] P' ⤳ Ξ ⨾ 𝒞' }}a
    /\ {{ Θ2 ⊩ 𝒞' ⨾ Pi ⤳ Ξs ⨾ Pa }}a
    /\ (𝒞' = 𝒞
        \/ (Q = pskl_var_f α /\ Ξ = nil
            /\ exists T T', 𝒞 = a_cstr_sub mode_tc T :: nil
                          /\ 𝒞' = a_cstr_sub mode_tc T' :: nil))
    /\ (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞').
Proof.
  induction n as [ | n IHn ].
  { intros Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β Hsz.
    exfalso. pose proof (size_pskl_min P'). lia. }
  intros Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β Hsz Hlk Hsol Hnh Hβ Hfm Hbound Hap.
  (* the counterpart's shape decides whether LS-ForallR has priority here *)
  destruct P' as [ | nq | γq | Pd1 Pd2 | B | | Pt ];
    try solve
      [ exists 𝒞;
        split; [ apply a_looksub_forall_l_adm with (β := β);
                   [ exact Hnh
                   | apply forall_r_off_nonall; intros ?; discriminate
                   | exact Hβ | exact Hlk ]
               | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ] ].
  (* ⚙ the [◇] shape is closed by the same arm — [P' ≠ ◇] is a hypothesis, so
     the branch discharges its own [exact Hnh]. *)
  (* --- a ∀ counterpart at CHECK mode --- *)
  destruct (pskl_ghost_free_dec (pskl_all_syn B)) as [Hgf | Hngf].
  2: { exists 𝒞.
       split; [ apply a_looksub_forall_l_adm with (β := β);
                  [ exact Hnh | apply forall_r_off_ghosty; exact Hngf
                  | exact Hβ | exact Hlk ]
              | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ]. }
  (* GHOST-FREE: LS-ForallR has priority, so the counterpart must peel *)
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_all_syn Q)))
    as [Hin | Hni].
  2: { (* the subject is α-free — LS-Absent answers on both sides *)
       assert (Hno : α `notin` ftvar_in_pskl
                       (open_pskl_wrt_pskl Q (pskl_var_f β)))
         by (apply ftv_open_absent; [ clear - Hβ; fsetdec | exact Hni ]).
       destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ Hlk Hno)
         as [-> ->].
       exists nil.
       split; [ apply a_looksub__absent; exact Hni | ].
       split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ]. }
  assert (Hβα : β <> α) by (clear - Hβ; fsetdec).
  destruct (a_looksub_open_target Hlk Hgf)
    as [ (Hvar & HΞ & H𝒞) | [b [Hb Hpeel]] ].
  - (* ⭐ THE α-STACK LEAF.  [Q] IS the looked-for variable, so the collection
       is LS-ForallR* then LS-ForallL then LS-Var, and the deposited
       constraint moves with the counterpart — which is why the SOLVE has to
       be peeled at THE SAME opener. *)
    assert (HQ : Q = pskl_var_f α)
      by (eapply open_var_eq_var_inv; [ exact Hvar | exact Hβα ]). subst Q. subst Ξ. subst 𝒞.
    pose proof (a_solve_cstr_sub_single_inv Hsol) as Hsolsub.
    destruct (a_solve_sub_open_target_avoid
                (add α (ftvar_in_aenv Θ)) Hsolsub Hfm Hbound)
      as [γ [Hγ Hsol']].
    assert (Hsolγ : {{ ((γ ~ abind_tvar) ++ Θ2)
                       ⊩ (a_cstr_sub mode_tc
                            (open_pskl_wrt_pskl B (pskl_var_f γ)) :: nil)
                       ⨾ Pi ⤳ Ξs ⨾ Pa }}a)
      by (apply a_solve_cstr__sub; exact Hsol').
    assert (Hsol2 : {{ Θ2 ⊩ (a_cstr_sub mode_tc
                               (open_pskl_wrt_pskl B (pskl_var_f γ)) :: nil)
                       ⨾ Pi ⤳ Ξs ⨾ Pa }}a)
      by (exact (@a_solve_cstr_strip_tvar_mid nil γ Θ2 _ _ _ _ Hsolγ)).
    pick fresh β1 for
      (add α (ftvar_in_aenv ((γ ~ abind_tvar) ++ Θ)
                `union` ftvar_in_pskl (pskl_var_f α)
                `union` ftvar_in_pskl
                          (open_pskl_wrt_pskl B (pskl_var_f γ)))).
    assert (Hleaf : {{ ((β1 ~ abind_tvar) ++ (γ ~ abind_tvar) ++ Θ)
                       ⊢ (open_pskl_wrt_pskl (pskl_var_f α) (pskl_var_f β1))
                       ≼[ α , mode_tc ]
                       (open_pskl_wrt_pskl B (pskl_var_f γ))
                       ⤳ nil ⨾ (a_cstr_sub mode_tc
                                  (open_pskl_wrt_pskl B (pskl_var_f γ))
                                :: nil) }}a).
    { unfold open_pskl_wrt_pskl; simpl. apply a_looksub__var. }
    (* ⭐ the invariant survives the OPENER MOVE: [Hap] bounds [dom Ξs] away
       from [B] (the constraint here is the UNDESCENDED ∀), and the re-derived
       solve runs at [γ,Θ2], so γ misses the block too. *)
    assert (HapG : forall α0, α0 `in` dom Ξs ->
              α0 `notin` ftvar_in_a_cstrs
                           (a_cstr_sub mode_tc
                              (open_pskl_wrt_pskl B (pskl_var_f γ)) :: nil)).
    { intros α0 Hα0.
      pose proof (Hap α0 Hα0) as Hf.
      pose proof (a_solve_sub_generated_fresh Hsol' Hα0) as Hg.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f γ))
        as Hup.
      cbn [ftvar_in_a_cstrs ftvar_in_a_cstr] in Hf |- *.
      simpl in Hf, Hg, Hup.
      clear - Hf Hg Hup. fsetdec. }
    destruct (IHn ((γ ~ abind_tvar) ++ Θ) α (pskl_var_f α)
                (open_pskl_wrt_pskl B (pskl_var_f γ)) nil
                (a_cstr_sub mode_tc (open_pskl_wrt_pskl B (pskl_var_f γ))
                 :: nil)
                Θ2 Pi Ξs Pa β1
                ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                      cbn [size_pskl] in Hsz; lia)
                Hleaf Hsol2
                ltac:(apply ghost_free_open_var_neq_ghost; exact Hgf)
                ltac:(clear - Fr; fsetdec) Hfm Hbound HapG)
      as [𝒞'' [Hlk'' [Hsol'' [Hdisj Hap'']]]].
    exists 𝒞''. split.
    + apply a_looksub__forall_r with (β := γ);
        [ exact Hgf
        | simpl; clear - Hγ; fsetdec
        | simpl; clear; fsetdec
        | discriminate
        | exact Hlk'' ].
    + split; [ exact Hsol'' | ].
      split; [ | exact Hap'' ].
      right. split; [ reflexivity | ]. split; [ reflexivity | ].
      exists (pskl_all_syn B).
      destruct Hdisj as [ -> | (_ & _ & T & T' & HT & HT') ];
        [ exists (open_pskl_wrt_pskl B (pskl_var_f γ))
        | exists T' ]; split; solve [ reflexivity | exact HT' ].
  - (* the counterpart peels at the derivation's OWN binder, and 𝒞 is
       untouched — so the solve rides through unchanged *)
    assert (Hbβ : b <> β)
      by (rewrite ftvar_in_aenv_cons_tvar in Hb; clear - Hb; fsetdec).
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
      as HupB.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower Q (pskl_var_f β))
      as HloQ.
    rewrite ftvar_in_aenv_cons_tvar in Hb.
    destruct (IHn ((b ~ abind_tvar) ++ Θ) α Q
                (open_pskl_wrt_pskl B (pskl_var_f b)) Ξ 𝒞 Θ2 Pi Ξs Pa β
                ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                      cbn [size_pskl] in Hsz; lia)
                ltac:(apply a_looksub_ctx_exchange; exact Hpeel)
                Hsol
                ltac:(apply ghost_free_open_var_neq_ghost; exact Hgf)
                ltac:(rewrite ftvar_in_aenv_cons_tvar;
                      simpl in Hβ, HupB |- *;
                      clear - Hβ Hbβ HupB; fsetdec)
                Hfm Hbound Hap)
      as [𝒞'' [Hlk'' [Hsol'' [Hdisj Hap'']]]].
    exists 𝒞''. split.
    + apply a_looksub__forall_r with (β := b);
        [ exact Hgf
        | simpl; simpl in Hb; clear - Hb HloQ; fsetdec
        | exact Hin
        | discriminate
        | exact Hlk'' ].
    + split; [ exact Hsol'' | split; [ exact Hdisj | exact Hap'' ] ].
Qed.

(** The [⫯] twin.  [LS-UnivGhostL] has no binder of its own, so the statement
    loses the opener — everything else is [a_looksub_solve_forall_l] verbatim,
    including the α-stack leaf and its opener move. *)
Lemma a_looksub_solve_univ_ghost_l : forall n Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa,
  size_pskl P' <= n ->
  {{ Θ ⊢ Q ≼[ α , mode_tc ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ Θ2 ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  P' <> pskl_ghost ->
  all_flex_mono Ξs ->
  ftvar_in_pskl Pa [<=] dom Ξs `union` ftvar_in_aenv Θ2 ->
  (* ⭐ THE BLOCK-vs-CONSTRAINTS INVARIANT rides through the reorder
     (2026-08-20): the α-stack leaf re-derives the solve at a FRESH opener γ
     and puts γ into the new constraint, so the conjunct has to be carried
     rather than re-derived — but γ misses [dom Ξs] by the solve's own
     freshness at the extended context. *)
  (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞) ->
  exists 𝒞',
    {{ Θ ⊢ (pskl_univ_ghost Q) ≼[ α , mode_tc ] P' ⤳ Ξ ⨾ 𝒞' }}a
    /\ {{ Θ2 ⊩ 𝒞' ⨾ Pi ⤳ Ξs ⨾ Pa }}a
    /\ (𝒞' = 𝒞
        \/ (Q = pskl_var_f α /\ Ξ = nil
            /\ exists T T', 𝒞 = a_cstr_sub mode_tc T :: nil
                          /\ 𝒞' = a_cstr_sub mode_tc T' :: nil))
    /\ (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞').
Proof.
  induction n as [ | n IHn ].
  { intros Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa Hsz.
    exfalso. pose proof (size_pskl_min P'). lia. }
  intros Θ α Q P' Ξ 𝒞 Θ2 Pi Ξs Pa Hsz Hlk Hsol Hnh Hfm Hbound Hap.
  destruct P' as [ | nq | γq | Pd1 Pd2 | B | | Pt ];
    try solve
      [ exists 𝒞;
        split; [ apply a_looksub__univ_ghost_l;
                   [ exact Hnh
                   | apply forall_r_off_nonall; intros ?; discriminate
                   | exact Hlk ]
               | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ] ].
  destruct (pskl_ghost_free_dec (pskl_all_syn B)) as [Hgf | Hngf].
  2: { exists 𝒞.
       split; [ apply a_looksub__univ_ghost_l;
                  [ exact Hnh | apply forall_r_off_ghosty; exact Hngf
                  | exact Hlk ]
              | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ]. }
  destruct (AtomSetProperties.In_dec α (ftvar_in_pskl (pskl_univ_ghost Q)))
    as [Hin | Hni].
  2: { simpl in Hni.
       destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ Hlk Hni)
         as [-> ->].
       exists nil.
       split; [ apply a_looksub__absent; simpl; exact Hni | ].
       split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ]. }
  destruct (a_looksub_open_target Hlk Hgf)
    as [ (Hvar & HΞ & H𝒞) | [b [Hb Hpeel]] ].
  - (* ⭐ THE α-STACK LEAF, under a [⫯] this time *)
    subst Q. subst Ξ. subst 𝒞.
    pose proof (a_solve_cstr_sub_single_inv Hsol) as Hsolsub.
    destruct (a_solve_sub_open_target_avoid
                (add α (ftvar_in_aenv Θ)) Hsolsub Hfm Hbound)
      as [γ [Hγ Hsol']].
    assert (Hsolγ : {{ ((γ ~ abind_tvar) ++ Θ2)
                       ⊩ (a_cstr_sub mode_tc
                            (open_pskl_wrt_pskl B (pskl_var_f γ)) :: nil)
                       ⨾ Pi ⤳ Ξs ⨾ Pa }}a)
      by (apply a_solve_cstr__sub; exact Hsol').
    assert (Hsol2 : {{ Θ2 ⊩ (a_cstr_sub mode_tc
                               (open_pskl_wrt_pskl B (pskl_var_f γ)) :: nil)
                       ⨾ Pi ⤳ Ξs ⨾ Pa }}a)
      by (exact (@a_solve_cstr_strip_tvar_mid nil γ Θ2 _ _ _ _ Hsolγ)).
    (* ⭐ the invariant survives the OPENER MOVE: [Hap] bounds [dom Ξs] away
       from [B] (the constraint here is the UNDESCENDED ∀), and the re-derived
       solve runs at [γ,Θ2], so γ misses the block too. *)
    assert (HapG : forall α0, α0 `in` dom Ξs ->
              α0 `notin` ftvar_in_a_cstrs
                           (a_cstr_sub mode_tc
                              (open_pskl_wrt_pskl B (pskl_var_f γ)) :: nil)).
    { intros α0 Hα0.
      pose proof (Hap α0 Hα0) as Hf.
      pose proof (a_solve_sub_generated_fresh Hsol' Hα0) as Hg.
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f γ))
        as Hup.
      cbn [ftvar_in_a_cstrs ftvar_in_a_cstr] in Hf |- *.
      simpl in Hf, Hg, Hup.
      clear - Hf Hg Hup. fsetdec. }
    destruct (IHn ((γ ~ abind_tvar) ++ Θ) α (pskl_var_f α)
                (open_pskl_wrt_pskl B (pskl_var_f γ)) nil
                (a_cstr_sub mode_tc (open_pskl_wrt_pskl B (pskl_var_f γ))
                 :: nil)
                Θ2 Pi Ξs Pa
                ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                      cbn [size_pskl] in Hsz; lia)
                (a_looksub__var ((γ ~ abind_tvar) ++ Θ) α mode_tc
                   (open_pskl_wrt_pskl B (pskl_var_f γ)))
                Hsol2
                ltac:(apply ghost_free_open_var_neq_ghost; exact Hgf)
                Hfm Hbound HapG)
      as [𝒞'' [Hlk'' [Hsol'' [Hdisj Hap'']]]].
    exists 𝒞''. split.
    + apply a_looksub__forall_r with (β := γ);
        [ exact Hgf
        | simpl; clear - Hγ; fsetdec
        | simpl; clear; fsetdec
        | discriminate
        | exact Hlk'' ].
    + split; [ exact Hsol'' | ].
      split; [ | exact Hap'' ].
      right. split; [ reflexivity | ]. split; [ reflexivity | ].
      exists (pskl_all_syn B).
      destruct Hdisj as [ -> | (_ & _ & T & T' & HT & HT') ];
        [ exists (open_pskl_wrt_pskl B (pskl_var_f γ))
        | exists T' ]; split; solve [ reflexivity | exact HT' ].
  - (* the counterpart peels at the derivation's own binder *)
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
      as HupB.
    destruct (IHn ((b ~ abind_tvar) ++ Θ) α Q
                (open_pskl_wrt_pskl B (pskl_var_f b)) Ξ 𝒞 Θ2 Pi Ξs Pa
                ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                      cbn [size_pskl] in Hsz; lia)
                Hpeel Hsol
                ltac:(apply ghost_free_open_var_neq_ghost; exact Hgf)
                Hfm Hbound Hap)
      as [𝒞'' [Hlk'' [Hsol'' [Hdisj Hap'']]]].
    exists 𝒞''. split.
    + apply a_looksub__forall_r with (β := b);
        [ exact Hgf
        | simpl; simpl in Hb; clear - Hb; fsetdec
        | exact Hin
        | discriminate
        | exact Hlk'' ].
    + split; [ exact Hsol'' | split; [ exact Hdisj | exact Hap'' ] ].
Qed.

(** ⭐ The two shapes P6-Ss actually applies, at an ARBITRARY mode: outside
    CHECK mode the guard is vacuous and the rule fires as before. *)
Lemma a_looksub_solve_forall_l_mode : forall Θ α m Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β,
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ (open_pskl_wrt_pskl Q (pskl_var_f β))
     ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ Θ2 ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  P' <> pskl_ghost ->
  β `notin` add α (ftvar_in_aenv Θ `union` ftvar_in_pskl Q
                     `union` ftvar_in_pskl P') ->
  all_flex_mono Ξs ->
  ftvar_in_pskl Pa [<=] dom Ξs `union` ftvar_in_aenv Θ2 ->
  (* ⭐ THE BLOCK-vs-CONSTRAINTS INVARIANT rides through the reorder
     (2026-08-20): the α-stack leaf re-derives the solve at a FRESH opener γ
     and puts γ into the new constraint, so the conjunct has to be carried
     rather than re-derived — but γ misses [dom Ξs] by the solve's own
     freshness at the extended context. *)
  (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞) ->
  exists 𝒞',
    {{ Θ ⊢ (pskl_all_syn Q) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞' }}a
    /\ {{ Θ2 ⊩ 𝒞' ⨾ Pi ⤳ Ξs ⨾ Pa }}a
    /\ (𝒞' = 𝒞
        \/ (Q = pskl_var_f α /\ Ξ = nil
            /\ exists T T', 𝒞 = a_cstr_sub m T :: nil
                          /\ 𝒞' = a_cstr_sub m T' :: nil))
    /\ (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞').
Proof.
  intros Θ α m Q P' Ξ 𝒞 Θ2 Pi Ξs Pa β Hlk Hsol Hnh Hβ Hfm Hbound Hap.
  destruct m as [ | | m' ];
    try solve
      [ exists 𝒞;
        split; [ apply a_looksub_forall_l_adm with (β := β);
                   [ exact Hnh | apply forall_r_off_nontc; discriminate
                   | exact Hβ | exact Hlk ]
               | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ] ].
  eapply a_looksub_solve_forall_l;
    [ apply le_n | exact Hlk | exact Hsol | exact Hnh | exact Hβ
    | exact Hfm | exact Hbound | exact Hap ].
Qed.

Lemma a_looksub_solve_univ_ghost_l_mode : forall Θ α m Q P' Ξ 𝒞 Θ2 Pi Ξs Pa,
  {{ Θ ⊢ Q ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 }}a ->
  {{ Θ2 ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a ->
  P' <> pskl_ghost ->
  all_flex_mono Ξs ->
  ftvar_in_pskl Pa [<=] dom Ξs `union` ftvar_in_aenv Θ2 ->
  (* ⭐ THE BLOCK-vs-CONSTRAINTS INVARIANT rides through the reorder
     (2026-08-20): the α-stack leaf re-derives the solve at a FRESH opener γ
     and puts γ into the new constraint, so the conjunct has to be carried
     rather than re-derived — but γ misses [dom Ξs] by the solve's own
     freshness at the extended context. *)
  (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞) ->
  exists 𝒞',
    {{ Θ ⊢ (pskl_univ_ghost Q) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞' }}a
    /\ {{ Θ2 ⊩ 𝒞' ⨾ Pi ⤳ Ξs ⨾ Pa }}a
    /\ (𝒞' = 𝒞
        \/ (Q = pskl_var_f α /\ Ξ = nil
            /\ exists T T', 𝒞 = a_cstr_sub m T :: nil
                          /\ 𝒞' = a_cstr_sub m T' :: nil))
    /\ (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞').
Proof.
  intros Θ α m Q P' Ξ 𝒞 Θ2 Pi Ξs Pa Hlk Hsol Hnh Hfm Hbound Hap.
  destruct m as [ | | m' ];
    try solve
      [ exists 𝒞;
        split; [ apply a_looksub__univ_ghost_l;
                   [ exact Hnh | apply forall_r_off_nontc; discriminate
                   | exact Hlk ]
               | split; [ exact Hsol | split; [ left; reflexivity | exact Hap ] ] ] ].
  eapply a_looksub_solve_univ_ghost_l;
    [ apply le_n | exact Hlk | exact Hsol | exact Hnh
    | exact Hfm | exact Hbound | exact Hap ].
Qed.

(* (iv) refinement: the REFINEMENT's ∀-binder (rule [ad_refine_syn__all])
   enters BOTH Θ and Δ, the CONSISTENCY's only Θ; the IH runs at Δ = empty,
   so the binder is dropped from Δ with [ad_refine_syn_delta_mono]. *)

(* (v) [msubst_uskl_syn] commutes with opening (mirror of [msubst_pskl_open]):
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
Lemma subst_msubst_uskl_syn_open : forall Θ1 κ Θ ψa α R0 β,
  κ ∷ Θ1 ⊑ Θ ->
  α `notin` dom κ ->
  β `notin` dom κ ->
  β <> α ->
  lc_uskl ψa ->
  subst_uskl_in_uskl ψa α (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β)))
  = open_uskl_wrt_uskl
      (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R0)) (uskl_var_f β).
Proof.
  intros Θ1 κ Θ ψa α R0 β Hinc Hα Hβ Hne Hlc.
  rewrite (@msubst_uskl_syn_open Θ1 κ Θ R0 β Hinc Hβ).
  rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
    [ reflexivity | auto | exact Hlc ].
Qed.

(* ∀-subject consistency (C-ForallInh / C-ForallSyn), up to the target's
   defined-flex chain.  The two rows are told apart by the TARGET's colour:
   [bskl_all_inh] (inherited ∀ — LE-ForallInh) vs [bskl_all_syn] (synthesised
   ∀, which the refinement can only produce by FILLING a ∀◇ — LE-ForallSyn). *)
Lemma ad_pat_consis_all_syn_refine_unify : forall Ψs Θ R Q,
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall R0, R = uskl_all_syn R0 ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  lc_bskl Q ->
  exists L Q0,
    (forall α, α `notin` L ->
       {{ Ψs ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ (open_uskl_wrt_uskl R0 (uskl_var_f α))
            ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f α)) }}ad) /\
    (forall α, lc_bskl (open_bskl_wrt_bskl Q0 (bskl_var_f α))) /\
    (({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_all_inh Q0) }}ad) \/
     ({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_all_syn Q0) }}ad)).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros R0 Heq Δr Ql Hdf Href Hlc;
    try discriminate Heq.
  - (* __forall_inh_untagged *)
    injection Heq as He; subst.
    exists L, Q; split; [ assumption | split; [ inversion Hlc; auto | left; exact Href ] ].
  - (* __forall_syn *)
    injection Heq as He; subst.
    exists L, Q; split; [ assumption | split; [ inversion Hlc; auto | right; exact Href ] ].
  - (* __flex_r *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* the ε-tagged mirror: [uskl_all_tag] subjects (C-ForallInh's tagged row
   splits the index as [Ψ = Ψ0, ε]; the ForallSyn row keeps it). *)
Lemma ad_pat_consis_all_tag_refine_unify : forall Ψs Θ R Q,
  {{ ⊢ Θ }}a ->
  {{ Ψs ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall εr R0, R = uskl_all_tag εr R0 ->
  forall Δr Ql, delta_def_fresh Δr Θ -> {{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ Q }}ad ->
  lc_bskl Q ->
  exists L Q0 Ψ0,
    (forall α, α `notin` L ->
       {{ Ψ0 ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ (open_uskl_wrt_uskl R0 (uskl_var_f α))
            ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f α)) }}ad) /\
    (forall α, lc_bskl (open_bskl_wrt_bskl Q0 (bskl_var_f α))) /\
    ((({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_all_inh Q0) }}ad) /\ Ψs [=] add εr Ψ0) \/
     (({{ Θ ⨟ Δr ⊢ᵣ Ql ⊳ (bskl_all_syn Q0) }}ad) /\ Ψs [=] Ψ0)).
Proof.
  intros Ψs Θ R Q HwfΘ H; induction H; intros εr R0 Heq Δr Ql Hdf Href Hlc;
    try discriminate Heq.
  - (* __forall_inh_tagged *)
    injection Heq as He1 He2; subst.
    exists L, Q, Ψ0; split;
      [ assumption | split; [ inversion Hlc; auto | left; split; assumption ] ].
  - (* __forall_syn_tagged *)
    injection Heq as He1 He2; subst.
    exists L, Q, Ψ; split;
      [ assumption
      | split; [ inversion Hlc; auto | right; split; [ exact Href | clear; fsetdec ] ] ].
  - (* __flex_r *)
    subst.
    eapply IHad_pat_consis;
      [ exact HwfΘ | reflexivity | exact Hdf
      | eapply ad_refine_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdf | exact Href | reflexivity | eassumption ]
      | apply mono_bskl_lc, mono_ptyp_to_bskl_syn;
        eapply a_wf_aenv_binds_def_mono; eauto ].
Qed.

(* ===================================================================== *)
(*  (vi) β-FRESHNESS OF THE COLLECTED CONSTRAINTS.                        *)
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

Lemma def_ftv_dom : forall Θ, {{ ⊢ Θ }}a -> def_ftv Θ [<=] dom Θ.
Proof.
  intros Θ H; induction H; simpl; try (clear - IHa_wf_aenv; fsetdec).
  - clear; fsetdec.
  - pose proof (a_wf_ptyp_ftv_dom H0) as Hf.
    clear - Hf IHa_wf_aenv; fsetdec.
Qed.

(* (a) a DECORATED subject's counterpart only mentions the subject's own
   variables and the context's definitions (the [__ghost] rule, which invents
   an arbitrary target, needs a PLAIN ghost — [is_dskl] has only ◈). *)
Lemma ad_pat_consis_target_ftv : forall Ψ Θ ψ Q,
  {{ Ψ ⨟ Θ ⊢ˢ ψ ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
  is_dskl ψ ->
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
    match goal with Ht : forall α, α `notin` ?Lt -> is_dskl _ |- _ =>
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
    match goal with Ht : forall α, α `notin` ?Lt -> is_dskl _ |- _ =>
      rename Ht into Htb; remember Lt as Lt0 eqn:HeqLt; clear HeqLt end.
    pick fresh α for (L `union` Lt0 `union` dom Θ `union` ftvar_in_bskl Q
                        `union` ftvar_in_uskl R `union` def_ftv Θ).
    specialize (H0 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)
                  (Htb α ltac:(auto))).
    simpl in H0.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f α)) as Hlo.
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R (uskl_var_f α)) as Hup.
    simpl in Hup. clear - H0 Hlo Hup Fr; fsetdec.
  - (* dot_univ_ghost *)
    inversion Htsk; subst.
    specialize (IHad_pat_consis HwfΘ ltac:(assumption)).
    clear - IHad_pat_consis; fsetdec.
  - (* flex_l : the subject is a defined variable — recurse on its monotype *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    specialize (IHad_pat_consis HwfΘ (mono_ptyp_to_uskl_syn_is_dskl Hmτ)).
    rewrite ftvar_ptyp_to_uskl_syn in IHad_pat_consis.
    pose proof (@def_ftv_binds _ _ _ H) as Hdb.
    clear - IHad_pat_consis Hdb; fsetdec.
  - (* flex_r : the target IS a defined variable *)
    pose proof (@def_ftv_binds _ _ _ H) as Hdb.
    clear - Hdb; fsetdec.
Qed.

(* (b) refinement never invents source variables: a source variable is either
   in the target or a definition variable of the context. *)
Lemma ad_refine_syn_src_ftv : forall Θ Δ Q' Q0,
  {{ Θ ⨟ Δ ⊢ᵣ Q' ⊳ Q0 }}ad ->
  {{ ⊢ Θ }}a ->
  ftvar_in_bskl Q' [<=] ftvar_in_bskl Q0 `union` def_ftv Θ.
Proof.
  intros Θ Δ Q' Q0 H; induction H; intros HwfΘ; simpl in *;
    try solve [ clear; fsetdec ].
  - (* arrow *)
    specialize (IHad_refine_syn1 HwfΘ); specialize (IHad_refine_syn2 HwfΘ).
    clear - IHad_refine_syn1 IHad_refine_syn2; fsetdec.
  - (* all *)
    pick fresh α for (L `union` ftvar_in_bskl Q `union` ftvar_in_bskl Q'
                        `union` dom Θ `union` def_ftv Θ).
    specialize (H1 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)).
    simpl in H1.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_lower Q (bskl_var_f α)) as Hlo.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f α)) as Hup.
    simpl in Hup. clear - H1 Hlo Hup Fr; fsetdec.
  - (* univ_ghost_remove *)
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  - (* univ_ghost_fill *)
    pick fresh α for (L `union` ftvar_in_bskl Q `union` ftvar_in_bskl Q'
                        `union` dom Θ `union` def_ftv Θ).
    specialize (H1 α ltac:(auto) ltac:(apply a_wf_aenv__tvar; auto)).
    simpl in H1.
    pose proof (ftvar_in_bskl_open_bskl_wrt_bskl_upper Q' (bskl_var_f α)) as Hup.
    simpl in Hup. clear - H1 Hup Fr; fsetdec.
  - (* univ_ghost_keep *)
    specialize (IHad_refine_syn HwfΘ). clear - IHad_refine_syn; fsetdec.
  - (* flex_l : the source IS a defined variable *)
    pose proof (@def_ftv_binds _ _ _ H) as Hdb. clear - Hdb; fsetdec.
  - (* flex_r : recurse through the definition *)
    specialize (IHad_refine_syn HwfΘ).
    rewrite ftvar_ptyp_to_bskl_syn in IHad_refine_syn.
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

(* (vii) a GUARDED-HEADED subject forces a guarded counterpart.  Well-formedness
   of P makes every ∀◇-body guarded, so this refutes the C-UnivGhost2 rows in
   which the ∀◇ is dropped against a ∀ / ∀◇ target.  (Mirror of
   [ad_pat_consis_guarded_r], which only covers plain-skeleton subjects.) *)
Definition uskl_guarded_head (R : uskl) : Prop :=
  R = uskl_unit \/ (exists α, R = uskl_var_f α) \/
  (exists R1 R2, R = uskl_arrow R1 R2).

Definition bskl_guarded_head (Q : bskl) : Prop :=
  Q = bskl_unit \/ (exists α, Q = bskl_var_f α) \/
  (exists Q1 Q2, Q = bskl_arrow Q1 Q2).

Lemma ad_pat_consis_guarded_head_target : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ ⊢ Θ }}a ->
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

(* ===================================================================== *)
(*  P6-Cs  —  a_lookeq_solve_complete                                      *)
(*                                                                         *)
(*  STATE: every paper case is proved.  The ONLY remaining gap is a single  *)
(*  configuration, hit by three rows of the ∀◇ case:                        *)
(*                                                                         *)
(*      R = ∀◇α   (the universal ghost wrapping the LOOKED-UP variable)     *)
(*                                                                         *)
(*  There the consistency subject is [∀◇ψa] rather than [ψa], so the α-leaf *)
(*  cannot be handed to P6-Cv ([a_solve_eq_complete_var] expects the        *)
(*  subject ψa), and the guarded-headedness argument that refutes the       *)
(*  ghost-dropping rows for every other R0 does not apply (ψa may itself be *)
(*  a ∀ or a ∀◈).  Closing it needs either a ∀◇-wrapped variant of P6-Cv or *)
(*  a reachability argument for [P = ∀◇α].                                  *)
(* ===================================================================== *)

(** The ρ-binders' ftv side condition is ANTITONE in both skeletons, so every
    descent that shrinks P0 (arrow components, ∀◇-strip) and keeps Pi gets it
    for free.  Only two rows need an argument: the Arrow row's RIGHT recursion
    (its Pi becomes the left branch's output Pa1) and the ∀ rows (whose P0
    gains the fresh binder β — free, since Δρ ⊆ dom Θ and β ∉ dom Θ). *)
Lemma rsubst_ftv_apart_mono : forall Δρ P0 Pi P0' Pi',
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi) ->
  ftvar_in_pskl P0' [<=] ftvar_in_pskl P0 ->
  ftvar_in_pskl Pi' [<=] ftvar_in_pskl Pi ->
  forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0' `union` ftvar_in_pskl Pi'.
Proof.
  intros Δρ P0 Pi P0' Pi' H HP HPi α0 Hα0.
  specialize (H α0 Hα0). clear - H HP HPi; fsetdec.
Qed.

(* ρ-GENERALIZED (2026-07-29).  P6-Ss's Sub-ForallL absorbs its guess into an
   accumulated RIGID substitution ρ, and a ForallL can sit above a Check whose
   whole subject is handed to P6-Cs — so P6-Cs must accept a subject that is
   the ρ-IMAGE [Rsub] of the paper's ideal [(κR)[ψa/α]] rather than the ideal
   itself.  Three facts keep this to threading rather than a rewrite:
     1. ρ NEVER GROWS inside P6-Cs (consistency has no ForallL), so Δρ is
        constant and the measure — on the ρ-free ideal [R'] — is untouched;
     2. every row dispatches on [R'], so the [uskl_rsubst_*_r_inv] family reads
        [Rsub]'s shape off the ideal's, and for a non-variable ideal that
        returns a SINGLE congruence (no disjunct to case on);
     3. ψa never moves, so ρ's action on the guess is fixed throughout.
   The ρ premise is stated at a FIXED context [Θs] with a binds-monotonicity
   into [Θ] (P6-Sv's device).  It must NOT be stated at [Θ]: the ∀ rows run the
   IH at [Θ,β] and then strip β from 𝒞, and the ftv-𝒞 conclusion below names
   the ρ-images' scope — at [Θ] that bound would readmit the very binder being
   stripped. *)

(* ⛔⛔ RESUME HERE (2026-08-04) — P6-Cs UNDER THE SolE-FlexR REPAIR.

   The STATEMENT below is converted and final; what is left is the PROOF.
   [coqc] stops in the flexible-P0 row's CLEAN arm (the [HPa] block, ≈ line
   2175), which is the first row where [SE-FlexR] actually fires.

   ── what the statement gained ────────────────────────────────────────────
   1. The SOLVE now generates a block, so the conclusion carries [Ξs] beside
      [Ξc], at [Ξs ++ Ξc ++ Θ0], with the extensions stacked the same way:
      [(κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ].  The order is FORCED by
      [a_extract__solve] (algo/def_rules.v:764), P6-L's consumer, which runs the
      solve at [Ξ ++ Θ0] and the final guess at [Ξs ++ Ξ ++ Θ0].
   2. An avoid-set PARAMETER [L] with [ftvar_in_aenv Θ0 [<=] L], and the
      output freshness [dom Ξs ∩ L = ∅].  [L] must be an input: at a binder
      row the witness is fixed before the block is picked.
   3. ⭐ THE Θw PACK — [{{ ⊢ Θw }}a], the two binds conditions, and the
      κ-image bound.  This was NOT in the first design and it is forced: the
      ∀ rows call the IH at [(β ~ tvar) ++ Θ] and then STRIP β out of the
      [a_inc] conclusion ([a_inc_strip_tvar_mid]), whose premise is
      [Forall (fun p => β ∉ ftv (snd p))] on the PREFIX.  For [κc] that came
      from the [ftv ⊆ ftv ψa] conjunct; [κs] has no such bound, so its
      payloads must be wf in a context that does not have β — i.e. a FIXED
      [Θw], exactly as in P6-Cv.  This is why [a_solve_eq_complete_var_at]
      (sub/look/prop_eq_var.v, after the paper statement) exists: the
      paper-facing [a_solve_eq_complete_var] pins [Θw := Θ] and is unusable
      under a binder.

   ── rows already converted ───────────────────────────────────────────────
   [P0 = □] · [α ∉ ftv P] · [LE-Var] (delegates to
   [a_solve_eq_complete_var_at]) · the flexible-P0 ρ-VARIABLE leaf ·
   ⭐ THE FLEXIBLE-P0 CLEAN ARM, which is the only row where [SE-FlexR] itself
   fires.  Its shape is worth copying downstream:
     * [WIT] wraps [a_guess_ty_witness_mono] at [κ := (α1, τψ) :: κ] — the
       node is EXACTLY P6-Cv's SE-FlexR node, since [ψa] is the mono paint
       [syn τψ] and the precision premise is [msubst κ Pi ⊑ᵖ syn τψ].
       [msubst_pskl_prepend_fresh] is what lets the fresh [α1] be prefixed
       without moving [msubst κ Pi].
     * the Pi grid is now SIX ways, not two: unit / arrow / ∀ take SE-FlexR at
       the guess; a VARIABLE takes SE-Var (nothing generated); ◇ takes
       SE-GhostL and returns the TARGET [α1] — the sharing [nonghost_pskl]
       protects; and ∀◇P peels by SE-GhostGuarded (the target [α1] is
       guarded) onto a body that wf forces GUARDED, hence nonghost, so one
       peel always lands on a SE-FlexR/SE-Var node.
     * the ∀◇ peel needs the precision unfolded and re-folded along a
       DEFINITION CHAIN: [ad_ppre_univ_ghost_subject_chain_inv] one way,
       [ad_ppre_chain_fold] (new, just above this comment) the other.

   ── rows left, hardest first ─────────────────────────────────────────────
   (a) ⛔ THE ARROW ROW.  Its LEFT IH is converted; [coqc] stops on the RIGHT
       one, and there is a ⛔ RESUME block at that exact line with the six
       steps worked out — read it, not this summary.  The headline: the right
       IH runs at [Ξs1 ++ Ξc1 ++ Θ0] under [κs1 ++ κc1 ++ κ], NOT at
       [Ξc1 ++ Θ0], because [Pa1] mentions the flexibles the LEFT SOLVE
       invented; everything it returns is then permuted into the conclusion's
       [Ξs2 ++ Ξs1] / [Ξc1 ++ Ξc2] order, which is cheap because [binds] over
       an append is plain membership.
   (b) THE FIVE ∀ / ∀◇ ROWS: pass [Θw] and [Hψaw] down unchanged, run the IH
       at [add β L], and strip β from the [a_inc] with [a_inc_strip_tvar_mid]
       — whose [Forall (β ∉ ftv)] premise on the [κs] prefix now comes from
       [a_wf_ptyp Θw] plus [β ∉ dom Θw].
   (c) The corollary [a_lookeq_solve_complete] at the bottom of the file
       (instantiate [Θw := Θ]; [Hψaw] from the subject's own wf).

   ⚙️ [HFw] (asserted at the top of the proof) turns the package's [Θw]
   payloads into the [Θ] ones [a_inc_flex_prefix_build] wants. *)
(* ===================================================================== *)
(*  ⭐⭐ THE FLEX-P0 CASE, FACTORED (2026-08-18).                            *)
(*                                                                        *)
(*  It was inline in the ARROW grid, and the FlexR-PRIORITY GUARD gave it  *)
(*  a SECOND consumer: under that guard the ⫯-subject grid can no longer   *)
(*  answer a FLEXIBLE counterpart with LE-UnivGhost2 either, so its        *)
(*  var-P0 row has to build the FlexR answer itself.                       *)
(*                                                                        *)
(*  ⭐ THE BLOCK NEVER LOOKED AT THE SUBJECT'S SHAPE — it reads it only    *)
(*  through [≠ α], [α ∈ ftv] and its freshness unions — so factoring is a  *)
(*  RENAMING of six spots, not a re-proof.  And it uses NO induction       *)
(*  hypothesis, which is why it can leave the induction at all.           *)
(* ===================================================================== *)

Lemma a_lookeq_flex_p0_complete :
  forall NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q Pi R' α Θs Δρ Ψρ Rsub β0 L,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a -> {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ (pskl_var_f β0) }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  ftvar_in_uskl ψa [<=] dom Θw ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  a_tags_sort NM Ψ' ψa ->
  Ψi `union` Ψa [<=] Ψ' ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  {{ Ψsub ⨟ Θ ⊢ˢ Rsub ∼ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ (pskl_var_f β0))) ⊳ Q }}ad ->
  uskl_rsubst NM Θs Δρ Ψρ Rsub
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->
  (forall x b, binds x b Θs -> binds x b Θ) ->
  rsubst_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  Δρ ∩ dom Θw [=] empty ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl (pskl_var_f β0) `union` ftvar_in_pskl Pi) ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  ftvar_in_uskl ψa ∩ Δρ [=] empty ->
  ftvar_in_aenv Θ0 [<=] L ->
  Δρ [<=] dom Θ -> Δρ [<=] dom Θ0 ->
  (forall κ0 : list (atom * ptyp),
     Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 ->
     Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ0) ->
  (forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
     binds α0 (abind_flex_mono_def τ0) Θw) ->
  ⌊ R' ⌋ˢ <> pskl_var_f α ->
  α `in` ftvar_in_pskl ⌊ R' ⌋ˢ ->
  α `notin` dom κ ->
  (forall p : atom * ptyp, In p κ -> α `notin` ftvar_in_ptyp (snd p)) ->
  α `in` ftvar_in_uskl R' ->
  a_binds_tvar β0 Θ0 ->
  a_flex_tvar Θ0 β0 ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    {{ Θ0 ⊢ ⌊ R' ⌋ˢ ∼[ α ] (pskl_var_f β0) ⤳ Ξc ⨾ 𝒞 }}a /\
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
    all_flex_mono Ξs /\ uniq Ξs /\ keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p : atom * ptyp =>
              a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p : atom * ptyp =>
              ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    ftvar_in_a_cstrs 𝒞
      [<=] ftvar_in_uskl ψa `union` dom Ξc `union` dom κ `union` def_ftv Θ /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa)
        ⊑ᵖ[ (Ψi `union` Ψa) ] ψa }}ad /\
    (* ⭐⭐ the SOLVE's block is apart from the collected constraints — see
       [a_lookeq_solve_complete_gen]'s last conjunct. *)
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).
Proof.
  intros NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q Pi R' α Θs Δρ Ψρ Rsub β0 L
    HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw HαΘ HαΘ0
    Htags Hsub Hdfresh Hpre Hcons0 Hrefine Hrho0 HΘs Hrfr HΔρΔ HΔρw
    HΔρftv HΔρPi Hψaap HL HΔρΘ HΔρΘ0 HFw Hdefs HPnα Hin Hακdom Hκav
    HαR Hbt0 Hflx.
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
(* the counterpart is mono-ish *)
assert (Hmi : bskl_monoish (Q))
  by (eapply ad_refine_mono_paint_rhs_monoish;
        [ exact HwfΘ | exact Hrefine | reflexivity | exact Hτ0mono ]).
(* ψa is a mono paint *)
assert (Htskψa : is_dskl ψa) by (inversion Htags; subst; assumption).
assert (HαT : α `in` ftvar_in_uskl (msubst_uskl_syn κ (R')))
  by (apply ftvar_in_uskl_msubst_uskl_syn_notin_dom;
        [ exact Hακdom | simpl; exact HαR ]).
(* ρ makes the subject the IMAGE of [(κR)[ψa/α]], so the ρ-free
   extraction no longer applies syntactically — and no commutation
   repairs that ([uskl_rsubst] is a relation; see the header of
   [ad_pat_consis_rsubst_psia_mono]).  What DOES apply is that the guess
   is Δρ-clean ([Hψaap]), and the ρ-generalized extraction only needs that. *)
assert (Hαρ : α `notin` Δρ).
{ intro Hc. destruct (Hrfr α Hc) as (Hb & _ & _).
  apply binds_In in Hb. contradiction. }
destruct (@ad_pat_consis_rsubst_psia_mono Ψsub Θ
            (Rsub) (Q) Hcons0 HwfΘ Hmi
            NM Δρ Ψρ (msubst_uskl_syn κ (R')) ψa α
            ltac:(eapply uskl_rsubst_weaken; [ exact Hrho0 | exact HΘs ])
            Hψaap Hαρ Htskψa HαT)
  as (τψ & Hτψmono & Heqψ & Hτψwf).
(* ψa mono ⇒ Ψ' = ∅ ⇒ Ψi = Ψa = ∅ *)
assert (HΨ'e : Ψ' [=] empty).
{ pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as HΨ't.
  rewrite Heqψ in HΨ't. rewrite ftag_ptyp_to_uskl_syn in HΨ't.
  exact HΨ't. }
assert (HΨie : Ψi [=] empty) by (clear - Hsub HΨ'e; fsetdec).
assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
(* fresh α1 for the LE-FlexR payload.  The last four unions are
   LE-FlexR's own [fresh γ̂] (cluster 3): the generated flexible avoids
   the ambient context, the flexible on the right, and the subject. *)
pick fresh α1 for
  (add α (dom Θ0 `union` dom Θ) `union` dom Θ `union` dom κ `union` ftvar_in_pskl Pi
     `union` ftvar_in_uskl ψa
     `union` ftvar_in_aenv Θ0 `union` singleton β0
     `union` ftvar_in_pskl ⌊ R' ⌋ˢ).
assert (Hγdom0 : α1 `notin` dom Θ0) by auto.
(* Pa and the three Pa-dependent facts (solve / wf / precision) *)
assert (Hbγ : binds α1 abind_flex_mono (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0))
  by (simpl_env; auto).
(* ⭐ the ideal guess's counterpart is wf at the FIXED [Θw] — the
   κ-extension's payloads must be, and [ψa]'s Θw-scoping is one of the
   theorem's premises. *)
assert (Hτψwfw : a_wf_ptyp Θw τψ).
{ eapply a_wf_ptyp_mono_strengthen_dom;
    [ exact HwfΘ | exact Hmon | exact Hτψmono | exact Hτψwf | ].
  rewrite Heqψ in Hψaw.
  rewrite ftvar_ptyp_to_uskl_syn in Hψaw. exact Hψaw. }
(* ⭐⭐ THE WITNESS, shared by every NONGHOST subject shape.  Under the
   repair SE-FlexR returns [guess^TY(Pi)], not the flexible, so this
   node is EXACTLY P6-Cv's SE-FlexR node: the target is the mono paint
   [syn τψ] and the precision premise is [msubst κ Pi ⊑ᵖ syn τψ].  The
   avoid-set is fixed BEFORE the block is picked, as always. *)
assert (WIT : forall Pi0 τw,
  {{ Θ0 ⨟ empty ⊢ₚₛ Pi0 }}a ->
  α1 `notin` ftvar_in_pskl Pi0 ->
  mono_ptyp τw -> a_wf_ptyp Θw τw ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi0) ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τw) }}ad ->
  exists Ξg A κg,
    (forall Θg, ftvar_in_aenv Θg
                [<=] add α1 (L `union` ftvar_in_aenv Θ0) ->
       a_guess_mono Θg Pi0 Ξg A) /\
    all_flex_mono Ξg /\ uniq Ξg /\ keys κg = keys Ξg /\
    (forall α2, α2 `in` dom Ξg -> α2 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κg /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κg ++ ((α1, τψ) :: κ)) (ptyp_to_pskl A))
        ⊑ᵖ[ Ψi ] (ptyp_to_uskl_syn τw) }}ad).
{ intros Pi0 τw HwfPi0 Hα1Pi0 Hm0 Hwf0 Hpre0.
  assert (Hprefix : msubst_pskl ((α1, τψ) :: κ) Pi0
                    = msubst_pskl κ Pi0).
  { change ((α1, τψ) :: κ) with (((α1, τψ) :: nil) ++ κ).
    apply msubst_pskl_prepend_fresh.
    intros α2 Hα2; cbn in Hα2.
    assert (α2 = α1) by (clear - Hα2; fsetdec); subst α2.
    exact Hα1Pi0. }
  destruct (@a_guess_ty_witness_mono (size_pskl Pi0) Θ0 Θ Θw
              ((α1, τψ) :: κ) Δ Ψi τw Pi0
              ltac:(reflexivity) HwfΘ HwfΘw Hmon Hdefs HwfPi0
              Hm0 Hwf0
              ltac:(rewrite Hprefix; exact Hpre0)
              (add α1 (L `union` ftvar_in_aenv Θ0)))
    as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
  exists Ξg, Ag, κg.
  split; [ exact Hgu | ].
  split; [ exact Hfmg | ].
  split; [ exact Hug | ].
  split; [ exact Hkg | ].
  split; [ intros α2 Hα2; pose proof (Hfrg α2 Hα2) as Hnf2;
           clear - Hnf2; fsetdec | ].
  split; [ exact HFg | ].
  exact Hqg. }
(* the guess's context bound, discharged once *)
assert (HgΘ : ftvar_in_aenv (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0)
                [<=] add α1 (L `union` ftvar_in_aenv Θ0))
  by (simpl_env; simpl; clear; fsetdec).
assert (HPa : exists Ξs Pa κs,
  {{ (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0) ⊢ₑ Pi ∼ (pskl_var_f α1)
     ⤳ Ξs ⨾ Pa }}a /\
  all_flex_mono Ξs /\ uniq Ξs /\ keys κs = keys Ξs /\
  (forall α2, α2 `in` dom Ξs -> α2 `notin` L) /\
  Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
  {{ Θ ⨟ Δ ⊢ˢ msubst_pskl (κs ++ ((α1, τψ) :: κ)) Pa
      ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
{ assert (Hlcpi : lc_pskl Pi) by (eapply a_wf_pskl_lc; exact HwfPi).
  assert (Hα1Pi : α1 `notin` ftvar_in_pskl Pi) by (clear - Fr; solve_notin).
  (* the two GHOST shapes keep the old answer — [nonghost_pskl] excludes
     them from SE-FlexR (PAPER-GAPS finding 2), and SE-GhostL returns
     the target [α1] whose image IS [τψ]. *)
  assert (Hflexpa : {{ Θ ⨟ Δ ⊢ˢ msubst_pskl (nil ++ ((α1, τψ) :: κ))
                              (pskl_var_f α1)
                      ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
  { cbn [app].
    replace (msubst_pskl ((α1, τψ) :: κ) (pskl_var_f α1))
      with (ptyp_to_pskl τψ)
      by (cbn [msubst_pskl msubst_lookup];
          match goal with |- context [if ?c then _ else _] => destruct c end;
          [ reflexivity | contradiction ]).
    rewrite Heqψ.
    eapply ad_partial_precise_psi_cong;
      [ apply ad_ppre_mono_refl; exact Hτψmono
      | clear - HΨie HΨae; fsetdec ]. }
  assert (Hnf : a_non_flex (((α1 ~ abind_flex_mono) ++ nil) ++ Θ0) Pi ->
            True) by (intros; exact I).
  clear Hnf.
  destruct Pi as [ | nbi | α0 | Pi1 Pi2 | Pib | | Pit ].
  - (* unit : SE-FlexR at the guess *)
    destruct (WIT pskl_unit τψ HwfPi Hα1Pi Hτψmono Hτψwfw
                ltac:(rewrite <- Heqψ; exact Hpre))
      as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
    exists Ξg, (ptyp_to_pskl Ag), κg.
    split; [ apply a_solve_eq__flex_r;
               [ left; exact Hbγ
               | split; [ exact Hlcpi | intros Hf; inversion Hf ]
               | apply nonghost_pskl__unit
               | apply Hgu; exact HgΘ ] | ].
    split; [ exact Hfmg | ]. split; [ exact Hug | ].
    split; [ exact Hkg | ]. split; [ exact Hfrg | ].
    split; [ exact HFg | ].
    rewrite Heqψ.
    eapply ad_partial_precise_psi_cong;
      [ exact Hqg | clear - HΨae; fsetdec ].
  - (* var_b : not wf *) inversion HwfPi.
  - (* var_f α0 : SE-Var keeps it, so nothing is generated *)
    exists nil, (pskl_var_f α0), (@nil (atom * ptyp)).
    split; [ apply a_solve_eq__var | ].
    split; [ apply Forall_nil | ]. split; [ apply uniq_nil | ].
    split; [ reflexivity | ].
    split; [ intros α2 Hα2; cbn in Hα2; exfalso; clear - Hα2; fsetdec | ].
    split; [ apply Forall_nil | ].
    assert (Hα0γ : α0 <> α1)
      by (intro Hc; subst α1; clear - Hα1Pi; cbn in Hα1Pi; fsetdec).
    cbn [app].
    replace (msubst_pskl ((α1, τψ) :: κ) (pskl_var_f α0))
      with (msubst_pskl κ (pskl_var_f α0))
      by (cbn [msubst_pskl msubst_lookup];
          match goal with |- context [if ?c then _ else _] => destruct c end;
          [ contradiction | reflexivity ]).
    eapply ad_partial_precise_psi_cong;
      [ exact Hpre | clear - HΨae; fsetdec ].
  - (* arrow : SE-FlexR at the guess *)
    destruct (WIT (pskl_arrow Pi1 Pi2) τψ HwfPi Hα1Pi Hτψmono Hτψwfw
                ltac:(rewrite <- Heqψ; exact Hpre))
      as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
    exists Ξg, (ptyp_to_pskl Ag), κg.
    split; [ apply a_solve_eq__flex_r;
               [ left; exact Hbγ
               | split; [ exact Hlcpi | intros Hf; inversion Hf ]
               | apply nonghost_pskl__arrow
               | apply Hgu; exact HgΘ ] | ].
    split; [ exact Hfmg | ]. split; [ exact Hug | ].
    split; [ exact Hkg | ]. split; [ exact Hfrg | ].
    split; [ exact HFg | ].
    rewrite Heqψ.
    eapply ad_partial_precise_psi_cong;
      [ exact Hqg | clear - HΨae; fsetdec ].
  - (* all_syn : SE-FlexR at the guess *)
    destruct (WIT (pskl_all_syn Pib) τψ HwfPi Hα1Pi Hτψmono Hτψwfw
                ltac:(rewrite <- Heqψ; exact Hpre))
      as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
    exists Ξg, (ptyp_to_pskl Ag), κg.
    split; [ apply a_solve_eq__flex_r;
               [ left; exact Hbγ
               | split; [ exact Hlcpi | intros Hf; inversion Hf ]
               | apply nonghost_pskl__all
               | apply Hgu; exact HgΘ ] | ].
    split; [ exact Hfmg | ]. split; [ exact Hug | ].
    split; [ exact Hkg | ]. split; [ exact Hfrg | ].
    split; [ exact HFg | ].
    rewrite Heqψ.
    eapply ad_partial_precise_psi_cong;
      [ exact Hqg | clear - HΨae; fsetdec ].
  - (* ghost : SE-GhostL returns the TARGET — that sharing is exactly
       what [nonghost_pskl] protects *)
    exists nil, (pskl_var_f α1), (@nil (atom * ptyp)).
    split; [ apply a_solve_eq__ghost_l | ].
    split; [ apply Forall_nil | ]. split; [ apply uniq_nil | ].
    split; [ reflexivity | ].
    split; [ intros α2 Hα2; cbn in Hα2; exfalso; clear - Hα2; fsetdec | ].
    split; [ apply Forall_nil | ].
    exact Hflexpa.
  - (* ∀◇Pit : SE-GhostGuarded peels (the target [α1] is guarded), and
       the body is GUARDED by wf, hence NONGHOST — so one peel lands on
       a SE-FlexR / SE-Var node.  The precision unfolds along a
       definition chain and folds back. *)
    assert (Hg : guarded_pskl Pit /\ ({{ Θ0 ⨟ empty ⊢ₚₛ Pit }}a))
      by (exact (a_wf_pskl_univ_ghost_inv HwfPi)).
    destruct Hg as [HgPit HwfPit].
    assert (Hα1Pit : α1 `notin` ftvar_in_pskl Pit)
      by (clear - Hα1Pi; cbn in Hα1Pi; exact Hα1Pi).
    destruct (@ad_ppre_univ_ghost_subject_chain_inv Θ Δ Ψi
                (msubst_pskl κ (pskl_univ_ghost Pit)) ψa HwfΘ Hpre
                (msubst_pskl κ Pit) eq_refl τψ Heqψ Hτψmono)
      as (τe & Hchain & Hmτe & Hpree).
    assert (Hτewfw : a_wf_ptyp Θw τe)
      by (eapply a_def_chain_wf_at;
            [ exact Hchain | exact HwfΘw | exact Hdefs | exact Hτψwfw ]).
    destruct HgPit as [ | α0 | Pit1 Pit2 ].
    + (* unit *)
      destruct (WIT pskl_unit τe HwfPit Hα1Pit Hmτe Hτewfw Hpree)
        as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
      exists Ξg, (ptyp_to_pskl Ag), κg.
      split; [ apply a_solve_eq__univ_ghost_l_guarded;
                 [ apply guarded_pskl__var
                 | apply a_solve_eq__flex_r;
                     [ left; exact Hbγ
                     | split; [ apply lc_pskl_unit
                              | intros Hf; inversion Hf ]
                     | apply nonghost_pskl__unit
                     | apply Hgu; exact HgΘ ] ] | ].
      split; [ exact Hfmg | ]. split; [ exact Hug | ].
      split; [ exact Hkg | ]. split; [ exact Hfrg | ].
      split; [ exact HFg | ].
      rewrite Heqψ.
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_ppre_chain_fold; [ exact Hchain | exact Hqg ]
        | clear - HΨae; fsetdec ].
    + (* var α0 : SE-Var *)
      exists nil, (pskl_var_f α0), (@nil (atom * ptyp)).
      split; [ apply a_solve_eq__univ_ghost_l_guarded;
                 [ apply guarded_pskl__var | apply a_solve_eq__var ] | ].
      split; [ apply Forall_nil | ]. split; [ apply uniq_nil | ].
      split; [ reflexivity | ].
      split; [ intros α2 Hα2; cbn in Hα2; exfalso; clear - Hα2; fsetdec | ].
      split; [ apply Forall_nil | ].
      assert (Hα0γ : α0 <> α1)
        by (intro Hc; subst α1; clear - Hα1Pit; cbn in Hα1Pit; fsetdec).
      cbn [app].
      replace (msubst_pskl ((α1, τψ) :: κ) (pskl_var_f α0))
        with (msubst_pskl κ (pskl_var_f α0))
        by (cbn [msubst_pskl msubst_lookup];
            match goal with |- context [if ?c then _ else _] => destruct c end;
            [ contradiction | reflexivity ]).
      rewrite Heqψ.
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_ppre_chain_fold; [ exact Hchain | exact Hpree ]
        | clear - HΨae; fsetdec ].
    + (* arrow *)
      destruct (WIT (pskl_arrow Pit1 Pit2) τe HwfPit Hα1Pit Hmτe
                  Hτewfw Hpree)
        as (Ξg & Ag & κg & Hgu & Hfmg & Hug & Hkg & Hfrg & HFg & Hqg).
      exists Ξg, (ptyp_to_pskl Ag), κg.
      split; [ apply a_solve_eq__univ_ghost_l_guarded;
                 [ apply guarded_pskl__var
                 | apply a_solve_eq__flex_r;
                     [ left; exact Hbγ
                     | split; [ apply lc_pskl_arrow; assumption
                              | intros Hf; inversion Hf ]
                     | apply nonghost_pskl__arrow
                     | apply Hgu; exact HgΘ ] ] | ].
      split; [ exact Hfmg | ]. split; [ exact Hug | ].
      split; [ exact Hkg | ]. split; [ exact Hfrg | ].
      split; [ exact HFg | ].
      rewrite Heqψ.
      eapply ad_partial_precise_psi_cong;
        [ eapply ad_ppre_chain_fold; [ exact Hchain | exact Hqg ]
        | clear - HΨae; fsetdec ]. }
destruct HPa as (Ξs & Pa & κs & Hsolve_eq & Hfms & Hus & Hks & Hfrs
                 & HFs & Hprec).
exists (a_cstr_eq (pskl_var_f α1) :: nil),
       ((α1 ~ abind_flex_mono) ++ nil), Ξs, Pa,
       ((α1, τψ) :: nil), κs.
repeat split.
-- (* a_lookeq : LE-FlexR *)
   apply a_lookeq__flex_r;
     solve [ cbn; clear - Fr; solve_notin
           | exact Hflx | exact HPnα | exact Hin ].
-- (* solve *)
   apply a_solve_cstr__eq with (Ξ1 := Ξs)
        (Ξ2 := (@nil (atom * abind))) (P'' := Pa);
     [ exact Hsolve_eq | apply a_solve_cstr__empty ].
-- (* all_flex_mono Ξs *) exact Hfms.
-- (* uniq Ξs *) exact Hus.
-- (* keys κs = keys Ξs *) exact Hks.
-- (* dom Ξs ∩ L = ∅ *) exact Hfrs.
-- (* the SOLVE block's payloads *) exact HFs.
-- (* wf Pa, at [Ξs ++ Ξc ++ Θ0] *)
   eapply a_solve_eq_wf;
     [ exact Hsolve_eq
     | apply a_wf_pskl_weaken with (Θ := Θ0);
         [ intros x b Hb; apply binds_app_3; exact Hb | exact HwfPi ]
     | apply a_wf_pskl__var; right; left; exact Hbγ ].
-- (* {{ ⊢ (Ξc ++ Θ0) }}a *)
   simpl_env. apply a_wf_aenv__flex; [ exact Hγdom0 | exact HwfΘ0 ].
-- (* α ∉ dom Ξc *) simpl; clear - Fr; fsetdec.
(* keys ρc = keys Ξc : auto-closed by [repeat split] (eq_refl) *)
-- (* ρc images come from ψa : here ψa IS the paint of τψ *)
   apply Forall_cons; [ | apply Forall_nil ].
   simpl. rewrite Heqψ. rewrite ftvar_ptyp_to_uskl_syn.
   clear; fsetdec.
-- (* ftv 𝒞 : the only constraint is [eq α1], and α1 ∈ dom Ξc *)
   simpl; clear; fsetdec.
-- (* a_inc : the two blocks are prefixed one after the other *)
   apply a_inc_flex_prefix_build;
     [ exact Hfms | exact Hks | apply HFw; exact HFs | ].
   cbn [app]. simpl_env.
   apply a_inc__flex; [ exact Hκ | exact Hτψwf | exact Hτψmono ].
-- (* a_inc_equiv Θ0 κ κ Θ *) apply a_inc_equiv_refl; exact Hκ.
-- (* ρc fresh *)
   intros α0 Hα0; simpl in Hα0.
   assert (α0 = α1) by (clear - Hα0; fsetdec); subst α0.
   clear - Fr; fsetdec.
-- (* precision *) cbn [app]. exact Hprec.
-- (* ⭐ the SOLVE's block vs the ONE constraint [eq α1]: the eq-solve ran at
      a context that BINDS α1, so its block cannot contain it *)
   intros α2 Hα2. simpl.
   pose proof (a_solve_eq_generated_fresh Hsolve_eq Hα2) as Hf.
   simpl in Hf. clear - Hf. fsetdec.
Qed.


(** The counterpart's local closure, at a SUB-counterpart: read off the
    statement's [lc_bskl Q] through the inversions the rows performed. *)
Ltac lc_tgt :=
  match goal with
  | |- lc_bskl _ =>
      first
        [ assumption
        | solve [ eauto ]
        | match goal with
          | H : lc_bskl _ |- _ => solve [ inversion H; subst; eauto ]
          end ]
  end.

Theorem a_lookeq_solve_complete_gen :
  forall n NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α Θs Δρ Ψρ Rsub,
  size_uskl R' + size_pskl P0 <= n ->       (* measure: R' recursion + P0 ∀◇-stripping *)
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  (* ⭐ THE Θw PACK (2026-08-04), identical to P6-Cv's and needed for the same
     reason ONE LEVEL UP: the ∀ rows call the IH at [(β ~ tvar) ++ Θ] and then
     STRIP β out of the [a_inc] conclusion ([a_inc_strip_tvar_mid]), which
     needs the SOLVE block's payloads wf in a context that does not have β.
     The κc side already had this, spelled as [ftv ⊆ ftv ψa]; the κs side gets
     it from a FIXED [Θw].  Vacuous at the top-level call ([Θw := Θ]). *)
  {{ ⊢ Θw }}a ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (forall α0, a_flex_tvar Θ0 α0 ->
     ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw) ->
  (* ⭐ and the IDEAL GUESS is Θw-scoped.  Forced by the flexible-P0 row: there
     [ψa] is a mono paint [syn τψ] and [τψ] is the κs payload, so [τψ] must be
     wf at [Θw] — while [ad_pat_consis_rsubst_psia_mono] only reports it at
     [Θ].  INVARIANT for free: [ψa] never moves inside P6-Cs (the header says
     so) and [Θw] is fixed.  At the ρ = identity corollary it follows from the
     subject's own well-formedness. *)
  ftvar_in_uskl ψa [<=] dom Θw ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->                            (* erase R' = P (R' is κ-FREE, paper-faithful) *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->   (* R' scoped at Θ0 + the lookup var α (wf) *)
  lc_uskl R' ->                             (* R' is a well-formed (locally-closed) skeleton *)
  a_tags_sort NM Ψ' ψa ->                  (* Θ ⊢^N Ψ'{syn ψa} *)
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->  (* S's tags ⊥ ψa's tags Ψ' *)
  Ψi `union` Ψa [<=] Ψ' ->                 (* Ψi, Ψa ⊆ Ψ' *)
  delta_def_fresh Δ Θ ->                   (* paper's implicit Δ-wf (feeds P6-Cv) *)
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->      (* {{ Θ ⨟ Δ ⊢ˢ κPi ⊑ᵖ[Ψi] ψa }}ad *)
  Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa ->  (* index ⊆ R'-tags ∪ ρ's ∪ Ψa *)
  Ψa [<=] Ψsub ->                          (* ψa's subtree tags ⊆ index *)
  (* subject = the ρ-IMAGE of the paper's (κR)[ψa/α] (ρ = id ⇒ the paper's) *)
  {{ Ψsub ⨟ Θ ⊢ˢ Rsub ∼ Q }}ad ->
  (* the counterpart is locally closed — the part of its well-formedness (the
     paper's presupposition, declarative.tex:2074) this induction reads: a
     plain-◇ subject's Ghost row fills an ARBITRARY counterpart.  The
     corollary below takes the disciplined form; docs/WF-SIDE-CONDITIONS.md
     §2a. *)
  lc_bskl Q ->
  (* … and that subject is WELL-FORMED (the paper's prose "all inputs are
     well-formed"; erased to a pskl so the existing [a_wf_pskl] can state it —
     ⌊·⌋ˢ maps the dotted ghosts onto the plain ones, and the only content
     used is [a_wf_pskl__univ_ghost]'s GUARDED ghost body).
     ⚠️ WITHOUT this premise the lemma is FALSE.  Counterexample: Θ=Θ0=·,
     κ=·, R' = ∀◇α (so P = ∀◇α), ψa = ∀◈⟨⟩, P0 = Pi = ∀◇⟨⟩, Q = ∀◇⟨⟩.
     Every other premise holds (consistency by C-UnivGhost2 then C-UnivGhostG;
     refinement by R-UnivGhostKeep; precision by P-UnivGhostKeep), but the
     algorithm is FORCED: LE-UnivGhost ⇒ 𝒞 = [α ≐ ⟨⟩], and SE-GhostGuarded ⇒
     Pa = ⟨⟩, whose precision goal ⟨⟩ ⊑ᵖ ∀◈⟨⟩ has no rule.  The subject there
     is ∀◇(∀◈⟨⟩) — a ghost over a ghost — which [a_wf_pskl__univ_ghost] (and the
     declarative [d_wf_uskl__univ_ghost]) forbid.
     [paper-external wf side condition — docs/WF-SIDE-CONDITIONS.md] *)
  {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl Rsub) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->   (* Θ ⊢ inh(κP0) ⊳ Q *)
  (* --- the ρ-generalization pack (all VACUOUS at ρ = identity) --- *)
  uskl_rsubst NM Θs Δρ Ψρ Rsub
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ->   (* Rsub = ρ((κR)[ψa/α]) *)
  (forall x b, binds x b Θs -> binds x b Θ) ->  (* Θs ⊆ Θ: ρ's images predate Θ's growth *)
  Ψρ ∩ Ψ' [=] empty ->                     (* ρ's tags ⊥ ψa's *)
  rsubst_fresh Δρ Θ κ ->                      (* P6-Cv's ρ-freshness pack *)
  Δρ [<=] Δ ->
  (* ⭐ THE ρ-VARIABLES MISS [Θw] (2026-08-04) — forced by the ARROW row, and
     by nothing else.  That row's right IH runs under [κs1 ++ κc1 ++ κ] and has
     to re-establish the shielded-ftv premise below for the BIGGER
     metasubstitution, i.e. that a ρ-replaced variable misses every image.  For
     the collection block [κc1] that is the [Forall … ∩ Δρ = ∅] CONCLUSION; the
     SOLVE's own block has no such conjunct — the only handle on its payloads is
     their well-formedness at the FIXED [Θw] (and it cannot get one: the LE-Var
     row reads [κs] off P6-Cv, whose package carries no ftv bound at all) — so
     Δρ must miss [Θw]'s domain.
     INVARIANT for free: Δρ and Θw are both CONSTANT inside P6-Cs.  Vacuous at
     the ρ = identity corollary (Δρ = ∅), and P6-Ss's Sub-ForallL maintains it
     because the fresh rigid it adds to Δρ is picked fresh for Θ ⊇ Θw.
     ⚙️ A proof-construction fact about the mech's own ρ-generalization, not a
     paper finding — nothing goes to docs/PAPER-GAPS.md for it. *)
  Δρ ∩ dom Θw [=] empty ->
  (* ρ's binders avoid the SOURCE and the TARGET skeleton.
     ⚠️ NOT the stronger [Δρ ∩ dom Θ0 = ∅] this premise used to be: together
     with [κ ∷ Θ0 ⊑ Θ] and [rsubst_fresh Δρ Θ κ] that forces [Δρ = ∅] — an
     increase never INVENTS a rigid, so every Δρ-variable is already a rigid
     of Θ0 (machine-checked, cex/cex_p6cs_rsubst_delta_vacuous.v) — and the
     generalization would be the ρ = identity statement again.  P6-Ss's
     Sub-ForallL needs Δρ ≠ ∅: its fresh rigid β enters Θ0 AND Θ (forced by
     [a_inc_cons_tvar]) and joins Δρ.  The ftv form is all the old premise
     was ever used for (via [a_wf_pskl_ftv_dom]), and every descent
     preserves it. *)
  (forall α0, α0 `in` Δρ ->
     α0 `notin` ftvar_in_pskl P0 `union` ftvar_in_pskl Pi) ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  (* THE IDEAL GUESS-SKELETON IS ρ-APART.  ψa never moves inside P6-Cs and Δρ
     never grows here (consistency has no ForallL), so this is threaded
     unchanged by every row; P6-Ss maintains it because its own ψa is fixed
     across the main induction and every Sub-ForallL binder is picked fresh
     for it, and the ρ = identity corollary gets it from Δρ = ∅.
     It is what lets the ftv-𝒞 conclusion below name NO CONTEXT: without it
     the bound needs [dom Θs], the ρ-images' scope, and P6-Ss's Sub-ForallR
     then readmits the very binder it is stripping — a nested Sub-ForallL's
     guess drags β into that scope.  See docs/DESIGN-completeness-subtyping.md
     §8 (h) and [uskl_rsubst_ftv_apart]. *)
  (ftvar_in_uskl ψa) ∩ Δρ [=] empty ->
  (* κa := ρc ++ κ is a SYNTACTIC extension of κ over the fresh Ξc — a
     provable STRENGTHENING of the paper's [κ ≡ κa] (cf. P6-Cv's κa:=κ).
     It mechanizes the paper's "equivalence of metasubstitutions" step
     (subtyping-proofs.tex refn[16]): msubst (ρc++κ) agrees with msubst κ
     on Θ0-scoped skeletons, so the erase-tie threads under recursion. *)
  (* ⭐ THE AVOID-SET PARAMETER (2026-08-04, the SolE-FlexR repair).  The SOLVE
     now generates its own block, and at a binder row the witness must be fixed
     BEFORE that block is picked — so [L] is an INPUT, exactly as in P6-Cv's
     [solve_ext].  The premise is about [Θ0] alone; the run's own [Ξc] is
     absorbed inside (the P6-Cv calls go at [L ∪ ftvar_in_aenv Ξc]). *)
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\              (* lookeq α P P0 𝒞 Ξc *)
    (* ⭐ the SOLVE's own block [Ξs] and its aligned extension [κs].  The order
       [Ξs ++ Ξc ++ Θ0] is the one [a_extract__solve] (algo/def_rules.v:764) runs
       the final guess at, so P6-L consumes this verbatim. *)
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\            (* solve 𝒞 Pi Ξs Pa *)
    (* [all_flex_mono] is re-derivable ([a_solve_cstr_decls]) but [uniq Ξs] is
       NOT (hand-off §4c), and the ARROW row needs both to rebuild
       [{{ ⊢ (Ξs ++ Ξc ++ Θ0) }}a] for its right branch. *)
    all_flex_mono Ξs /\
    uniq Ξs /\
    keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\         (* Θ0,Ξc,Ξs ⊢ Pa *)
    {{ ⊢ (Ξc ++ Θ0) }}a /\                      (* Ξc collected ⇒ context wf *)
    α `notin` dom Ξc /\                          (* α not among collected flexibles *)
    keys κc = keys Ξc /\  (* ρc's keys align with Ξc *)
    (* every image ρc assigns is built from ψa (the only source of witnesses
       is the flexible-P0 row, whose witness τψ satisfies ψa = syn τψ), so a
       binder FRESH for ψa is fresh for the images — this is what lets the
       ∀ rows strip their binder out of the [a_inc] conclusion. *)
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    (* the collected CONSTRAINTS mention only ψa's variables, the ρ-images'
       (FIXED) scope Θs, the collected flexibles, κ's domain and the context's
       definitions — never a fresh ∀-binder.  This is what makes LE-ForallInh /
       LE-UnivGhost1 (which open the TARGET under the binder) applicable with a
       single 𝒞.  [dom Θs], NOT [dom Θ]: see the header. *)
    ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa
                          `union` dom Ξc `union` dom κ
                          `union` def_ftv Θ /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\   (* κa : Θ0,Ξc,Ξs ⊑ Θ *)
    a_inc_equiv Θ0 κ κ Θ /\                      (* κ ≡ κa on Θ0: κa|Θ0 = κ (ρc fresh) *)
    (* ρc / Ξc's names are the ones the RUN INVENTED, so they avoid everything
       that existed when it started: α, both contexts, and the ideal guess ψa.
       ⚙ The ψa disjunct is cluster 3's addition, and it is load-bearing: since
       [a_looksub_lookeq_ftv] became DISJUNCTIVE (the ∀ rules leak), the only
       bound on 𝒞 is the ψa-based one below, so the Arrow row can no longer
       show that the RIGHT branch's fresh flexibles miss the LEFT branch's
       constraints without knowing they miss ψa. *)
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad /\
    (* ⭐⭐ THE SOLVE'S BLOCK IS APART FROM THE COLLECTED CONSTRAINTS
       (2026-08-20).  What [a_extract__solve]'s CROSS-LAYER GUARD needs, and
       it cannot be got at the consumer: the escaping variables of [𝒞] are
       the ∀ rows' LEAKED OPENERS, which are bound nowhere, so no scoping
       fact and no instantiation of [L] can reach them — [L] is fixed before
       [𝒞] exists.  ⚙ Here it is nearly free: the ARROW row's two cross
       cases are [HC2s1] (already proved for the ftv-𝒞 bound above) and the
       recursive [L], which we own.  ⚙ The ∀ FORM, not [∩ … [=] empty]:
       [repeat split] dismantles an [Equal] through its [iff] and every row
       would then owe TWO goals. *)
    (forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞).
Proof.
  induction n as [ | n IHn ];
    intros NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α Θs Δρ Ψρ Rsub Hn.
  { exfalso. pose proof (size_uskl_min R'). pose proof (size_pskl_min P0). lia. }
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw
         HαΘ HαΘ0 HeraseR HscopeS HlcS Htags Hdisj Hsub
         Hdfresh Hpre HΨs1 HΨs2 Hconsis HlcQ HwfSub Hrefine
         Hrho HΘs HΨρ Hrfr HΔρΔ HΔρw HΔρftv HΔρPi Hψaap L HL.
  (* the two ρ-scope facts every row reuses: Θs is a sub-context of Θ, and the
     ρ-replaced variables are rigid tvars OF Θ *)
  assert (HΘsdom : dom Θs [<=] dom Θ).
  { intros α0 Hα0. apply binds_In_inv in Hα0. destruct Hα0 as [b Hb].
    apply HΘs in Hb. apply binds_In in Hb. exact Hb. }
  assert (HΔρΘ : Δρ [<=] dom Θ).
  { intros α0 Hα0. destruct (Hrfr α0 Hα0) as (Hb & _ & _).
    apply binds_In in Hb; exact Hb. }
  (* …and they are rigids of Θ0 too — an increase never INVENTS a rigid
     ([a_inc_binds_tvar_rev], prop_inc.v).  This is what discharges the
     "…or the run invented this name" arm of [a_lookeq_ftv_ctx] for a
     ρ-replaced variable. *)
  assert (HΔρΘ0 : Δρ [<=] dom Θ0).
  { intros α0 Hα0. destruct (Hrfr α0 Hα0) as (Hb & _ & _).
    apply binds_In with (a := abind_tvar).
    eapply a_inc_binds_tvar_rev; [ exact Hκ | exact Hb ]. }
  (* the package's payloads are reported at the FIXED [Θw]; [a_inc] wants them
     at [Θ], and [Θw ⊆ Θ] — this is the only place the direction is used *)
  assert (HFw : forall κ0,
            Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ0 ->
            Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ0)
    by (intros κ0 HF0; eapply forall_wf_mono_weaken; [ exact Hmon | exact HF0 ]).
  (* the definition-only form the guess/witness kit asks for *)
  assert (Hdefs : forall α0 τ0, binds α0 (abind_flex_mono_def τ0) Θ ->
                    binds α0 (abind_flex_mono_def τ0) Θw)
    by (intros α0 τ0 Hb; destruct (Hnr _ _ Hb) as [Hb' | Hc];
        [ exact Hb' | discriminate Hc ]).
  (* ---------------------------------------------------------------- *)
  (* Special case P = α (LE-Var): R = var α ⇒ subject = ψa; delegate   *)
  (* to P6-Cv (a_solve_eq_complete_var) with the identity ρ.           *)
  (* ---------------------------------------------------------------- *)
  destruct (pskl_eq_var_dec P α) as [-> | HPnα].
  { (* P = α *)
    assert (Hlk : msubst_lookup κ α = ptyp_var_f α).
    { apply msubst_lookup_notin.
      intro Hc. apply (a_inc_dom_sub Hκ) in Hc. contradiction. }
    (* ⌊R'⌋ = P = var α ⇒ R' = uskl_var α *)
    assert (HR : R' = uskl_var_f α).
    { destruct R'; simpl in HeraseR; try discriminate HeraseR.
      injection HeraseR as ->. reflexivity. }
    subst R'.
    (* subject = (κ (var α))[ψa/α] = ψa *)
    assert (Hms : msubst_uskl_syn κ (uskl_var_f α) = uskl_var_f α)
      by (cbn; rewrite Hlk; apply ptyp_to_uskl_syn_var).
    (* under ρ the SUBJECT is [Rsub], so it is the IDEAL side of [Hrho] that
       collapses to ψa — [Hconsis] is already in the shape P6-Cv wants. *)
    rewrite Hms in Hrho.
    assert (Hsubj : subst_uskl_in_uskl ψa α (uskl_var_f α) = ψa).
    { cbn. match goal with |- context [if ?c then _ else _] => destruct c end;
        [ reflexivity | contradiction ]. }
    rewrite Hsubj in Hrho.
    cbn in HΨs1.        (* ftag_in_uskl (uskl_var_f α) = empty *)
    assert (Htskψa : is_dskl ψa) by (inversion Htags; assumption).
    assert (HtskRs : is_dskl Rsub) by (eapply uskl_rsubst_is_dskl; eassumption).
    assert (Hcv : exists Ξ Pa κ',
                    {{ Θ0 ⊢ₑ Pi ∼ P0 ⤳ Ξ ⨾ Pa }}a /\
                    all_flex_mono Ξ /\ uniq Ξ /\
                    keys κ' = keys Ξ /\
                    (forall α0, α0 `in` dom Ξ -> α0 `notin` L) /\
                    Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) κ' /\
                    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κ' ++ κ) Pa)
                        ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
    { eapply a_solve_eq_complete_var_at
        with (Δρ := Δρ) (Ψρ := Ψρ) (ψsub := Rsub) (Ψsub := Ψsub);
      [ exact HwfΘ | exact HwfΘ0 | exact HwfΘw | exact Hmon | exact Hnr
      | exact HwfPi | exact HwfP0 | exact Hκ | exact Hκw
      | eapply uskl_rsubst_weaken; [ exact Hrho | exact HΘs ]
      | exact Htags | exact Hsub | exact HΨρ
      | exact Hrfr
      | exact HΔρΔ
      | exact HΔρPi
      | exact Hdfresh
      | exact Hpre
      | clear - HΨs1; fsetdec
      | exact HΨs2 | exact Hconsis | exact Hrefine | exact HL ]. }
    destruct Hcv as (Ξs & Pa & κs & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
                     & Hprec).
    exists (a_cstr_eq P0 :: nil), nil, Ξs, Pa, (@nil (atom * ptyp)), κs.
    repeat split.
    - apply a_lookeq__var.
    - simpl. apply a_solve_cstr__eq
        with (Ξ1 := Ξs) (Ξ2 := (@nil (atom * abind))) (P'' := Pa);
        [ exact Hsolve | apply a_solve_cstr__empty ].
    - exact Hfms.
    - exact Hus.
    - exact Hks.
    - exact Hfrs.
    - exact HFs.
    - cbn [app].
      eapply a_solve_eq_wf; [ exact Hsolve | exact HwfPi | exact HwfP0 ].
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    - (* ftv 𝒞 : the ONE constraint is [eq P0]; κP0 refines to Q, and Q is what
         the (β-free) instantiation ψa faces *)
      simpl.
      pose proof (ad_refine_syn_src_ftv Hrefine HwfΘ) as Hrf.
      rewrite ftvar_in_bskl_inh in Hrf.
      pose proof (ad_pat_consis_target_ftv Hconsis HwfΘ HtskRs) as Hcf.
      (* under ρ the consistency bounds ftv Q by the IMAGE [Rsub]; the ρ
         relation carries that back to ψa with NO context slack, because the
         ideal here IS ψa and ψa is Δρ-apart — ρ acts only at a Δρ-variable *)
      pose proof (uskl_rsubst_ftv_apart Hrho ltac:(clear - Hψaap; solve_notin_auto))
        as Hbnd.
      pose proof (msubst_pskl_ftv_dom_lower κ P0) as Hlow.
      clear - Hrf Hcf Hbnd Hlow; fsetdec.
    - cbn [app].
      apply a_inc_flex_prefix_build;
        [ exact Hfms | exact Hks | apply HFw; exact HFs | exact Hκ ].
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - cbn [app]. exact Hprec.
    - (* the SOLVE's block vs the ONE constraint [eq P0]: P0 is Θ0-scoped,
         and the block dodges [L ⊇ ftvar_in_aenv Θ0] *)
      intros α0 Hα0. simpl.
      pose proof (a_wf_pskl_ftv_dom HwfP0) as Hfd. simpl in Hfd.
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hds.
      pose proof (Hfrs α0 Hα0) as Hf.
      clear - Hfd Hds HL Hf. fsetdec. }
  (* ---------------------------------------------------------------- *)
  (* Special case P0 = □ (LE-Vacuous): refinement inversion gives Q   *)
  (* synthesised ⇒ Ψsub = ∅ ⇒ Ψa = ∅; take 𝒞=·, Ξc=·, Pa=Pi, κa=κ.    *)
  (* ---------------------------------------------------------------- *)
  destruct (pskl_ghost_dec P0) as [-> | HP0nh].
  { (* P0 = □ *)
    simpl in Hrefine.  (* msubst κ □ = □ ; inh □ = bskl_ghost *)
    assert (Hsk : is_sskl Q)
      by (eapply ad_refine_syn_ghost_sskl; [ exact Hrefine | reflexivity
                 | exact HlcQ ]).
    assert (HΨe : Ψsub [=] empty)
      by (eapply ad_pat_consis_sskl_tags; [ exact Hconsis | exact HwfΘ | exact Hsk ]).
    assert (HΨa0 : Ψa [=] empty) by (clear - HΨs2 HΨe; fsetdec).
    exists nil, nil, nil, Pi, (@nil (atom * ptyp)), (@nil (atom * ptyp)).
    repeat split.
    - (* ◇-dispatch guard: the SUBJECT check ran first, so [P ≠ α] *)
      apply a_lookeq__vacuous; exact HPnα.
    - simpl. apply a_solve_cstr__empty.
    - apply Forall_nil.
    - apply uniq_nil.
    - intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec.
    - apply Forall_nil.
    - simpl. exact HwfPi.
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    - (* ftv 𝒞 : no constraints *) simpl; clear; fsetdec.
    - simpl. exact Hκ.
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - simpl. eapply ad_partial_precise_psi_cong; [ exact Hpre | clear - HΨa0; fsetdec ].
    - (* the SOLVE's block is EMPTY *)
      intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec. }
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
    (* under ρ the tag bound reads off the IMAGE, so ρ's own tags Ψρ join it —
       and they are ⊥ Ψ' by [HΨρ], exactly as R'-tags are by [Hdisj] *)
    rewrite (subst_uskl_in_uskl_fresh_eq (msubst_uskl_syn κ R') ψa α HαMS) in Hrho.
    assert (HΨsR : Ψsub [<=] ftag_in_uskl Rsub)
      by (apply (ad_pat_consis_ftag_sub Hconsis)).
    pose proof (uskl_rsubst_ftag_sub Hrho) as Hftr.
    rewrite ftag_in_uskl_msubst_uskl_syn in Hftr.
    assert (HΨa0 : Ψa [=] empty)
      by (clear - HΨs2 HΨsR Hftr Hdisj Hsub HΨρ; fsetdec).
    exists nil, nil, nil, Pi, (@nil (atom * ptyp)), (@nil (atom * ptyp)).
    repeat split.
    - apply a_lookeq__absent; exact Hnin.
    - simpl. apply a_solve_cstr__empty.
    - apply Forall_nil.
    - apply uniq_nil.
    - intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec.
    - apply Forall_nil.
    - simpl. exact HwfPi.
    - simpl. exact HwfΘ0.
    - simpl; clear; fsetdec.
    - apply Forall_nil.
    - (* ftv 𝒞 : no constraints *) simpl; clear; fsetdec.
    - simpl. exact Hκ.
    - simpl. apply a_inc_equiv_refl; exact Hκ.
    - intros α0 Hα0; simpl in Hα0; clear - Hα0; fsetdec.
    - simpl. eapply ad_partial_precise_psi_cong; [ exact Hpre | clear - HΨa0; fsetdec ].
    - (* the SOLVE's block is EMPTY *)
      intros α0 Hα0; simpl in Hα0; exfalso; clear - Hα0; fsetdec. }
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
    (* ρ-INVERSION: the ideal is an arrow, and [uskl_rsubst_arrow_r_inv] returns a
       SINGLE congruence (the leaf disjunct needs a VARIABLE ideal), so [Rsub]
       is an arrow of ρ-images and the row's text survives with those in place
       of the ideal's components. *)
    pose proof Hrho as Hrho0.  (* FOLDED copy for the flexible-P0 row *)
    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_arrow_r_inv Hrho)
      as (Ra' & Rb' & Ψρ1 & Ψρ2 & HRs & Hrhoa & Hrhob & HΨρeq).
    subst Rsub.
    assert (Hsza : size_uskl Ra <= n) by (cbn in Hn; lia).
    assert (Hszb : size_uskl Rb <= n) by (cbn in Hn; lia).
    destruct (lc_uskl_arrow_inv HlcS) as [HlcSa HlcSb].
    (* P is FORCED to the arrow shape by the erase-tie *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    cbn [uskl_to_pskl] in HwfSub.
    destruct (a_wf_pskl_arrow_inv HwfSub) as [HwfSubA HwfSubB].
    (* Consistency inversion would give TWO branches — __arrow (Q = Q1→Q2) and
       __flex_r (Q a DEFINED flex var, whose definition chain ends at an arrow).
       [ad_pat_consis_arrow_refine_unify] walks that chain on both the
       consistency and the refinement side, so we get ONE continuation with
       [Q := bskl_arrow Q1 Q2]. *)
    destruct (ad_pat_consis_arrow_refine_unify HwfΘ Hconsis eq_refl
                (delta_def_fresh_empty Θ) Hrefine HlcQ)
      as (Ψ1 & Ψ2 & Q1 & Q2 & H6 & H1 & H4 & Href0 & Hcons0 & HlcQ12).
    clear Hconsis Hrefine.
    rename Href0 into Hrefine.
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
        { inversion HwfP0; subst; assumption. }
        destruct Hbt0 as [Hrig | Hflx].
        { (* rigid β0 : refinement-absurd *)
          exfalso.
          assert (Hmid : msubst_pskl κ (pskl_var_f β0) = pskl_var_f β0)
            by (eapply msubst_pskl_tvar_id;
                [ exact HwfΘ0 | exact Hκ | exact Hrig ]).
          rewrite Hmid in Hrefine; cbn [pskl_to_bskl_inh] in Hrefine.
          eapply (ad_refine_syn_rigid_var_nonvar_absurd Hrefine);
            [ intros x b Hb; exact Hb | apply a_wf_aenv_uniq; exact HwfΘ
            | eapply a_inc_binds_tvar; eauto | intros βx Hcc; discriminate Hcc ]. }
        (* ⭐ flexible β0 : THE FLEX-P0 CASE, now FACTORED (2026-08-18) —
           the block never looked at the subject's shape, and the
           FlexR-PRIORITY GUARD gave it a second consumer in the ⫯ grid. *)
        eapply (@a_lookeq_flex_p0_complete NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa
                  (bskl_arrow Q1 Q2) Pi (uskl_arrow Ra Rb) α Θs Δρ Ψρ
                  (uskl_arrow Ra' Rb') β0 L);
          solve [ eassumption | reflexivity | right; exact Hflx
                | assumption | cbn; assumption ].
      * (* P0 = arrow P01 P02 : MAIN → LE-Arrow + sequential solve *)
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        destruct (ad_refine_arrow_arrow_inv Hrefine) as [Href1 Href2].
        destruct (a_wf_pskl_arrow_inv HwfP0) as [HwfP01 HwfP02].
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
        (* --- tag algebra: Ψa = (Ψ1∩Ψ') ∪ (Ψ2∩Ψ') --- *)
        assert (HΨa : Ψa [=] union (Ψ1 ∩ Ψ') (Ψ2 ∩ Ψ'))
          by (clear - HΨs1 HΨs2 Hsub H6 Hdisj HΨρ; fsetdec).
        (* under ρ the per-component tag bounds read off the ρ-IMAGES, so each
           picks up its own slice of Ψρ ([uskl_rsubst_ftag_sub]) *)
        assert (HΨ1sub : Ψ1 [<=] union (ftag_in_uskl Ra) (union Ψρ1 Ψ')).
        { pose proof (ad_pat_consis_ftag_sub H1) as Hf1.
          pose proof (uskl_rsubst_ftag_sub Hrhoa) as Hr1.
          pose proof (ftag_in_uskl_subst_uskl_in_uskl ψa α (msubst_uskl_syn κ Ra)) as Hb1.
          pose proof (ftag_in_uskl_msubst_uskl_syn κ Ra) as Hm1.
          clear - Hf1 Hr1 Hb1 Hm1 Hψatag; fsetdec. }
        assert (HΨ2sub : Ψ2 [<=] union (ftag_in_uskl Rb) (union Ψρ2 Ψ')).
        { pose proof (ad_pat_consis_ftag_sub H4) as Hf2.
          pose proof (uskl_rsubst_ftag_sub Hrhob) as Hr2.
          pose proof (ftag_in_uskl_subst_uskl_in_uskl ψa α (msubst_uskl_syn κ Rb)) as Hb2.
          pose proof (ftag_in_uskl_msubst_uskl_syn κ Rb) as Hm2.
          clear - Hf2 Hr2 Hb2 Hm2 Hψatag; fsetdec. }
        assert (HΨρ1e : Ψρ1 ∩ Ψ' [=] empty) by (clear - HΨρ HΨρeq; fsetdec).
        assert (HΨρ2e : Ψρ2 ∩ Ψ' [=] empty) by (clear - HΨρ HΨρeq; fsetdec).
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
        assert (HΨs1L : Ψ1 [<=] union (ftag_in_uskl Ra) (union Ψρ1 (Ψ1 ∩ Ψ')))
          by (clear - HΨ1sub; fsetdec).
        assert (HΨs2L : Ψ1 ∩ Ψ' [<=] Ψ1) by (clear; fsetdec).
        (* ⭐ THE AVOID-SETS (2026-08-04, the SolE-FlexR repair).  BOTH IHs must
           dodge [α] — the row needs [α ∉ dom Ξs1] to rebuild
           [α ∉ dom (Ξs1 ++ Ξc1 ++ Θ0)] for the right IH — and [dom Θ], because
           the right IH's ρ- and refinement-transports carry [Rb] (scoped at α,
           Θ0 and Θ) across the LEFT solve's block.  Neither is in [L], and [L]
           is an INPUT, so we simply hand the IHs a bigger one; the conclusion's
           own [∉ L] follows a fortiori.  The RIGHT IH dodges the left run's two
           blocks on top of that — which is what makes [uniq (Ξs2 ++ Ξs1)] and
           the [Ξc2]-insertion into the left solve provable. *)
        assert (HL1 : ftvar_in_aenv Θ0 [<=] add α (union L (dom Θ)))
          by (clear - HL; fsetdec).
        (* --- LEFT IH on Ra / P01 --- *)
        edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi (Ψ1 ∩ Ψ') Ψ1 ψa Q1
                     (uskl_to_pskl Ra) P01 Pi Ra α Θs Δρ Ψρ1 Ra'
                     Hml HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP01 HwfPi Hκ Hκw Hψaw
                     HαΘ HαΘ0 eq_refl
                     HscopeSa HlcSa Htags HdisjSa HsubL Hdfresh Hpre HΨs1L HΨs2L H1 ltac:(lc_tgt) HwfSubA Href1
                     Hrhoa HΘs HΨρ1e Hrfr HΔρΔ HΔρw
                     ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap
                     (add α (union L (dom Θ))) HL1)
          as (C1 & Ξc1 & Ξs1 & Pa1 & κc1 & κs1
                & HLK1 & HSolve1 & Hfms1 & Hus1 & Hks1 & Hfrs1 & HFs1
                & HwfPa1 & HwfΞ1 & HαΞ1
                & Hmap1 & Himg1 & HftvC1 & Hinc1 & Hinceq1 & Hκf1
                & Hpre1 & Hapart1).
        (* --- the LEFT run's two blocks, read off [Hfrs1] and the solve kit --- *)
        pose proof (a_lookeq_all_flex_mono HLK1) as HfmΞ1.
        pose proof (@keys_eq_dom _ _ κc1 Ξc1 Hmap1) as Hd1'.
        assert (Hd_s1 : dom κs1 [=] dom Ξs1) by (apply keys_eq_dom; exact Hks1).
        assert (Hfrs1κ : forall α0, α0 `in` dom κs1 ->
                  α0 `notin` add α (union L (dom Θ)))
          by (intros α0 Hα0; apply Hfrs1; clear - Hα0 Hd_s1; fsetdec).
        assert (HαΞs1 : α `notin` dom Ξs1)
          by (intro Hc; pose proof (Hfrs1 α Hc) as Hf; clear - Hf; fsetdec).
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf0.
        assert (HΞs1Θ0 : forall x, x `in` dom Ξs1 -> x `notin` dom Θ0)
          by (intros x Hx; pose proof (Hfrs1 x Hx) as Hf;
              clear - Hf Hdf0 HL; fsetdec).
        (* the SOLVE's block dodges everything its own context MENTIONS — the
           master invariant of the Ξ scoping kit (prop_solve_sub.v §K2) *)
        assert (HΞs1fr : forall x, x `in` dom Ξs1 ->
                  x `notin` ftvar_in_aenv (Ξc1 ++ Θ0))
          by (intros x Hx; eapply a_solve_cstr_generated_fresh;
                [ exact HSolve1 | exact Hx ]).
        assert (HwfΞs1 : {{ ⊢ (Ξs1 ++ Ξc1 ++ Θ0) }}a).
        { apply a_wf_aenv_flex_prefix; [ exact Hfms1 | | exact HwfΞ1 ].
          pose proof (a_wf_aenv_uniq HwfΞ1) as Huq1.
          assert (Hdd : dom Ξs1 ∩ dom (Ξc1 ++ Θ0) [<=] empty).
          { intros x Hx.
            assert (Hx1 : x `in` dom Ξs1) by (clear - Hx; fsetdec).
            assert (Hx2 : x `in` dom (Ξc1 ++ Θ0)) by (clear - Hx; fsetdec).
            pose proof (HΞs1fr x Hx1) as Hf.
            pose proof (dom_subset_ftvar_in_aenv (Ξc1 ++ Θ0)) as Hd.
            exfalso; clear - Hf Hd Hx2; fsetdec. }
          apply uniq_app_4; [ exact Hus1 | exact Huq1 | exact Hdd ]. }
        (* the two [Forall]s in POINTWISE form (the originals are still needed
           for the conclusion's own conjuncts, so keep them intact) *)
        assert (Himg1F : forall p, In p κc1 ->
                  ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa)
          by (rewrite Forall_forall in Himg1; exact Himg1).
        assert (HimgΔ1F : forall p, In p κc1 ->
                  (ftvar_in_ptyp (snd p)) ∩ Δρ [=] empty)
          by (intros p Hp; pose proof (Himg1F p Hp) as Hi;
              clear - Hi Hψaap; fsetdec).
        pose proof (forall_wf_mono_images_dom HFs1) as HFs1d.
        (* ⭐ THE RIGHT IH's κ-IMAGE BOUND.  A flexible of [Ξs1 ++ Ξc1 ++ Θ0]
           looks up in [κs1] — bounded by [HFs1], wf at Θw — or in [κc1] —
           bounded by [Himg1] (⊆ ftv ψa) then [Hψaw] — or, being outside both
           domains, in [κ], where the incoming [Hκw] applies. *)
        assert (Hκc1w : forall p, In p κc1 ->
          ftvar_in_ptyp (snd p) [<=] dom Θw)
          by (intros p Hp; pose proof (Himg1F p Hp) as Hb;
              clear - Hb Hψaw; fsetdec).
        destruct (solve_scope_flex_prefix
                    (solve_scope_flex_prefix (conj Hmon (conj Hnr Hκw)) Hmap1 Hκc1w)
                    Hks1 HFs1d) as (_ & _ & HκwR).
        (* --- transports for the RIGHT IH (κ → κs1 ++ κc1 ++ κ).  BOTH blocks
           the left branch generated have to be peeled: the collection's [κc1]
           (fresh for α, Θ0, Θ and ψa by [Hκf1]) and the SOLVE's [κs1] (fresh
           for the avoid-set we handed the left IH, which holds α, [L] ⊇ ftv Θ0
           and [dom Θ]). *)
        assert (Htr_c1 : msubst_uskl_syn (κc1 ++ κ) Rb = msubst_uskl_syn κ Rb).
        { apply msubst_uskl_syn_prepend_fresh. intros α0 Hα0.
          specialize (Hκf1 α0 Hα0). clear - Hκf1 HscopeSb; fsetdec. }
        assert (Htr_c : msubst_uskl_syn (κs1 ++ κc1 ++ κ) Rb
                        = msubst_uskl_syn κ Rb).
        { rewrite <- Htr_c1. apply msubst_uskl_syn_prepend_fresh.
          intros α0 Hα0. pose proof (Hfrs1κ α0 Hα0) as Hf.
          clear - Hf HscopeSb Hdf0 HL; fsetdec. }
        assert (Htr_r1 : msubst_pskl (κc1 ++ κ) P02 = msubst_pskl κ P02).
        { apply msubst_pskl_prepend_fresh. intros α0 Hα0.
          specialize (Hκf1 α0 Hα0).
          pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
          clear - Hκf1 Hfd; fsetdec. }
        assert (Htr_r : msubst_pskl (κs1 ++ κc1 ++ κ) P02 = msubst_pskl κ P02).
        { rewrite <- Htr_r1. apply msubst_pskl_prepend_fresh.
          intros α0 Hα0. pose proof (Hfrs1κ α0 Hα0) as Hf.
          pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
          clear - Hf Hfd Hdf0 HL; fsetdec. }
        (* the consistency and wf premises are now stated on the ρ-IMAGE [Rb'],
           which is κ-free — only the ρ premise still mentions κ, so it is the
           only one that needs the κ-transport *)
        rewrite <- Htr_c in Hrhob.
        rewrite <- Htr_r in Href2.
        assert (Hαr : α `notin` dom (Ξs1 ++ Ξc1 ++ Θ0))
          by (repeat rewrite dom_app; clear - HαΞs1 HαΞ1 HαΘ0; fsetdec).
        assert (HscopeSbR : ftvar_in_uskl Rb
                  [<=] add α (dom (Ξs1 ++ Ξc1 ++ Θ0) `union` dom Θ))
          by (repeat rewrite dom_app; clear - HscopeSb; fsetdec).
        assert (HsubR : union (union Ψi (Ψ1 ∩ Ψ'))
                              (Ψ2 ∩ Ψ') [<=] Ψ')
          by (clear - Hsub; fsetdec).
        assert (HΨs1R : Ψ2 [<=] union (ftag_in_uskl Rb) (union Ψρ2 (Ψ2 ∩ Ψ')))
          by (clear - HΨ2sub; fsetdec).
        assert (HΨs2R : Ψ2 ∩ Ψ' [<=] Ψ2) by (clear; fsetdec).
        assert (HwfP02R : {{ (Ξs1 ++ Ξc1 ++ Θ0) ⨟ empty ⊢ₚₛ P02 }}a)
          by (eapply a_wf_pskl_weaken;
                [ intros x b Hb; apply binds_app_3; apply binds_app_3; exact Hb
                | exact HwfP02 ]).
        (* --- ρ-transports for the RIGHT IH.  Ξc1's flexibles are fresh for Θ
           and Δρ ⊆ dom Θ, so the ρ-binders stay outside the grown Θ0; the new
           Pi := Pa1 is (Ξc1,Θ0)-scoped and both κc1's images (Δρ-clean by the
           new [Forall] output) and κ's (by [rsubst_fresh]) avoid them. *)
        (* the new Pi is the LEFT branch's output, so its ftv-apartness is
           EARNED, not inherited: [a_solve_cstr_ftv] bounds it by the old Pi
           and the collected constraints, [a_lookeq_ftv] bounds those by P01
           and the collected flexibles, and Ξc1's names are fresh for Θ ⊇ Δρ *)
        assert (HΔρΞc1 : forall α0, α0 `in` Δρ -> α0 `notin` dom Ξc1).
        { intros α0 Hα0 Hc. rewrite <- Hd1' in Hc. specialize (Hκf1 α0 Hc).
          specialize (HΔρΘ α0 Hα0). clear - Hκf1 HΔρΘ; fsetdec. }
        assert (HΔρPa1ftv : forall α0, α0 `in` Δρ ->
                  α0 `notin` ftvar_in_pskl Pa1).
        { intros α0 Hα0.
          (* EXACT bound (the consistency collection is all-eq, and the eq
             half never leaks) — [a_solve_cstr_ftv] is disjunctive now.  The
             look's bound is disjunctive too, but α0 is a RIGID OF Θ0, so it
             is not a name the run can have invented ([a_lookeq_ftv_ctx]). *)
          pose proof (a_solve_cstr_ftv_eq HSolve1 (a_lookeq_cstr_eq HLK1))
            as Hs1.
          pose proof (HΔρftv α0 Hα0) as Hd0. cbn [ftvar_in_pskl] in Hd0.
          pose proof (HΔρΞc1 α0 Hα0) as HΞ.
          assert (Hc1 : α0 `notin` ftvar_in_a_cstrs C1).
          { eapply a_lookeq_ftv_ctx;
              [ exact HLK1 | clear - HΔρΘ0 Hα0; fsetdec
              | clear - Hd0; fsetdec | exact HΞ ]. }
          (* ⭐ the bound now has a [dom Ξs1] term — the SOLVE generates names
             too.  A ρ-replaced variable is a RIGID of Θ0, and the block dodges
             [L ⊇ ftvar_in_aenv Θ0], so it is not one of them. *)
          assert (HΞs : α0 `notin` dom Ξs1).
          { intro Hc. pose proof (Hfrs1 α0 Hc) as Hf.
            pose proof (HΔρΘ0 α0 Hα0) as Hd00.
            pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf.
            clear - Hf Hd00 Hdf HL; fsetdec. }
          clear - Hs1 Hc1 Hd0 HΞ HΞs; fsetdec. }
        assert (HΔρftvR : forall α0, α0 `in` Δρ ->
                  α0 `notin` ftvar_in_pskl P02 `union` ftvar_in_pskl Pa1).
        { intros α0 Hα0. pose proof (HΔρftv α0 Hα0) as Hd0.
          cbn [ftvar_in_pskl] in Hd0.
          pose proof (HΔρPa1ftv α0 Hα0) as Hp1. clear - Hd0 Hp1; fsetdec. }
        (* ⭐ THE THREE-BLOCK ρ-CLEANNESS.  [κc1]'s images are Δρ-clean by the
           conclusion's own [Forall]; [κ]'s by [rsubst_fresh]; and the SOLVE's
           [κs1] — which has no such conjunct, and cannot get one, since the
           LE-Var row reads it off P6-Cv — by its payloads being wf at the FIXED
           [Θw] together with the premise [HΔρw] that Δρ misses [dom Θw].  This
           is the only place [HΔρw] is used, and the only reason it exists. *)
        assert (Hκs1Δρ : forall p, In p κs1 ->
                  forall α0, α0 `in` Δρ -> α0 `notin` ftvar_in_ptyp (snd p)).
        { intros p Hp α0 Hα0. pose proof (HFs1d p Hp) as Hb.
          clear - Hb HΔρw Hα0; fsetdec. }
        assert (HΔρPa1 : forall α0, α0 `in` Δρ ->
                  α0 `notin` pskl_shielded_ftv
                               (msubst_pskl (κs1 ++ κc1 ++ κ) Pa1)).
        { intros α0 Hα0.
          pose proof (pskl_shielded_ftv_sub_ftv
                        (msubst_pskl (κs1 ++ κc1 ++ κ) Pa1)) as Hsh.
          enough (Hne : α0 `notin`
                    ftvar_in_pskl (msubst_pskl (κs1 ++ κc1 ++ κ) Pa1))
            by (clear - Hsh Hne; fsetdec).
          apply msubst_pskl_ftv_avoid.
          - intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp | Hp].
            + exact (Hκs1Δρ p Hp α0 Hα0).
            + apply in_app_or in Hp; destruct Hp as [Hp | Hp].
              * pose proof (HimgΔ1F p Hp) as Hi. clear - Hi Hα0; fsetdec.
              * destruct (Hrfr α0 Hα0) as (_ & Hκim & _). apply Hκim; exact Hp.
          - exact (HΔρPa1ftv α0 Hα0). }
        assert (HrfrR : rsubst_fresh Δρ Θ (κs1 ++ κc1 ++ κ)).
        { intros α0 Hα0. destruct (Hrfr α0 Hα0) as (Hb & Hκim & Hdef).
          repeat split; [ exact Hb | | exact Hdef ].
          intros p Hp. apply in_app_or in Hp; destruct Hp as [Hp | Hp].
          - exact (Hκs1Δρ p Hp α0 Hα0).
          - apply in_app_or in Hp; destruct Hp as [Hp | Hp].
            + pose proof (HimgΔ1F p Hp) as Hi. clear - Hi Hα0; fsetdec.
            + apply Hκim; exact Hp. }
        (* P02 is Θ0-scoped and Ξc1's names are fresh for Θ0, so the collected
           block misses it. *)
        assert (HfrP02Ξ : (ftvar_in_pskl P02) ∩ (dom Ξc1) [=] empty).
        { pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
          intros α0; split; intros Hmem; [ | clear - Hmem; fsetdec ].
          exfalso.
          assert (Hm1 : α0 `in` dom Ξc1) by (clear - Hmem; fsetdec).
          assert (Hmκ : α0 `in` dom κc1) by (clear - Hm1 Hd1'; fsetdec).
          specialize (Hκf1 α0 Hmκ).
          assert (Hm2 : α0 `in` ftvar_in_pskl P02) by (clear - Hmem; fsetdec).
          clear - Hfd Hκf1 Hm2; fsetdec. }
        assert (HfrP02Ξs : (ftvar_in_pskl P02) ∩ (dom Ξs1) [=] empty).
        { pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
          intros α0; split; intros Hmem; [ | clear - Hmem; fsetdec ].
          exfalso.
          assert (Hm1 : α0 `in` dom Ξs1) by (clear - Hmem; fsetdec).
          pose proof (Hfrs1 α0 Hm1) as Hf.
          assert (Hm2 : α0 `in` ftvar_in_pskl P02) by (clear - Hmem; fsetdec).
          clear - Hfd Hf Hm2 Hdf0 HL; fsetdec. }
        (* ⭐ THE ARROW MERGE (2026-08-04, the SolE-FlexR repair).

           ⚠️ THE RIGHT IH DOES NOT RUN AT [Ξc1 ++ Θ0].  [Pa1] is the LEFT
           SOLVE's output and mentions the flexibles [Ξs1] that solve invented,
           so the precision the right branch consumes ([Hpre1]) is stated under
           [κs1 ++ κc1 ++ κ] — and the only context at which THAT is an [a_inc]
           is [Ξs1 ++ Ξc1 ++ Θ0], which is [Hinc1] verbatim.  So the right IH
           runs at

               Θ0 := Ξs1 ++ Ξc1 ++ Θ0        κ := κs1 ++ κc1 ++ κ

           and everything it hands back is PERMUTED into the conclusion's
           [Ξs2 ++ Ξs1] / [Ξc1 ++ Ξc2] order.  The permutation is cheap because
           [binds] over an append is plain MEMBERSHIP: any reordering preserves
           it, with no disjointness side condition ([binds_rot_app] and
           friends).  The two places order really matters are [uniq (Ξs2 ++ Ξs1)]
           — paid for by handing the right IH [dom Ξs1] in its avoid-set — and
           the κ-reordering of the precision, which is a lookup-level identity
           on pairwise-disjoint blocks. *)
        (* ⭐ …AND THE LEFT RUN'S CONSTRAINTS JOIN THE RIGHT RUN'S AVOID-SET
           (2026-08-20).  That is one of the four cases of the new
           block-vs-constraints conjunct — [dom Ξs2 ∩ ftv 𝒞1] — and it is the
           one no invariant supplies, because 𝒞1's escapees are LEAKED
           OPENERS.  Here it is free: 𝒞1 is CONCRETE by the time the right IH
           runs. *)
        assert (HL2 : ftvar_in_aenv (Ξs1 ++ Ξc1 ++ Θ0)
                  [<=] add α (union (union (union L (dom Θ))
                                    (union (dom Ξs1) (dom Ξc1)))
                                    (ftvar_in_a_cstrs C1))).
        { repeat rewrite ftvar_in_aenv_app.
          pose proof (all_flex_mono_ftvar_in_aenv Hfms1) as Hfs.
          pose proof (all_flex_mono_ftvar_in_aenv HfmΞ1) as Hfc.
          clear - Hfs Hfc HL; fsetdec. }
        (* --- RIGHT IH on Rb / P02, at [Ξs1 ++ Ξc1 ++ Θ0] with
               [κs1 ++ κc1 ++ κ] --- *)
        edestruct (IHn NM (Ξs1 ++ Ξc1 ++ Θ0) Θ Θw (κs1 ++ κc1 ++ κ) Δ Ψ'
                     (union Ψi (Ψ1 ∩ Ψ')) (Ψ2 ∩ Ψ')
                     Ψ2 ψa Q2 (uskl_to_pskl Rb) P02 Pa1 Rb α Θs Δρ Ψρ2 Rb'
                     Hmr HwfΘ HwfΞs1 HwfΘw Hmon Hnr HwfP02R HwfPa1 Hinc1 HκwR Hψaw
                     HαΘ Hαr eq_refl
                     HscopeSbR HlcSb Htags HdisjSb HsubR Hdfresh Hpre1 HΨs1R HΨs2R H4 ltac:(lc_tgt) HwfSubB Href2
                     Hrhob HΘs HΨρ2e HrfrR HΔρΔ HΔρw HΔρftvR HΔρPa1 Hψaap
                     (add α (union (union (union L (dom Θ))
                                   (union (dom Ξs1) (dom Ξc1)))
                                   (ftvar_in_a_cstrs C1))) HL2)
          as (C2 & Ξc2 & Ξs2 & Pa2 & κc2 & κs2
                & HLK2 & HSolve2 & Hfms2 & Hus2 & Hks2 & Hfrs2 & HFs2
                & HwfPa2 & HwfΞ2 & HαΞ2
                & Hmap2 & Himg2 & HftvC2 & Hinc2 & Hinceq2 & Hκf2
                & Hpre2 & Hapart2).
        (* --- ASSEMBLY.  Witnesses: 𝒞 := C1++C2 and Ξc := Ξc1++Ξc2 (forced by
           LE-Arrow, which pairs them), Ξs := Ξs2++Ξs1 (forced by
           [a_solve_cstr_app], which stacks the THREADED blocks the other way
           round), Pa := Pa2, κc := κc1++κc2, κs := κs2++κs1. *)
        pose proof (a_lookeq_all_flex_mono HLK2) as HfmΞ2.
        (* the wf-mono [Forall]s for the four blocks: the two SOLVE ones come
           from the packages ([HFs1]/[HFs2], moved from Θw to Θ by [HFw]), the
           two COLLECTION ones by splitting the increases the IHs returned *)
        destruct (@a_inc_flex_prefix_split Ξs1 κs1 (Ξc1 ++ Θ0) (κc1 ++ κ) Θ
                    Hfms1 Hks1 Hinc1) as [_ HincC1].
        destruct (@a_inc_flex_prefix_split Ξc1 κc1 Θ0 κ Θ HfmΞ1 Hmap1 HincC1)
          as [Hwm1 _].
        destruct (@a_inc_flex_prefix_split Ξs2 κs2 (Ξc2 ++ Ξs1 ++ Ξc1 ++ Θ0)
                    (κc2 ++ κs1 ++ κc1 ++ κ) Θ Hfms2 Hks2 Hinc2) as [_ HincC2].
        destruct (@a_inc_flex_prefix_split Ξc2 κc2 (Ξs1 ++ Ξc1 ++ Θ0)
                    (κs1 ++ κc1 ++ κ) Θ HfmΞ2 Hmap2 HincC2) as [Hwm2 _].
        pose proof (@keys_eq_dom _ _ κc2 Ξc2 Hmap2) as Hd2.  (* dom κc2 [=] dom Ξc2 *)
        assert (Hmapc : keys (κc1 ++ κc2) = keys (Ξc1 ++ Ξc2))
          by (rewrite !keys_app; rewrite Hmap1, Hmap2; reflexivity).
        assert (Hmaps : keys (κs2 ++ κs1) = keys (Ξs2 ++ Ξs1))
          by (rewrite !keys_app; rewrite Hks1, Hks2; reflexivity).
        (* the RIGHT run's collection block dodges EVERYTHING that existed when
           it started — α, both of the left run's blocks, Θ0, Θ and ψa.  That
           single fact ([Hκf2] at the grown Θ0) discharges every disjointness
           the merge needs. *)
        assert (HΞ2disj : forall x, x `in` dom Ξc2 ->
                  x `notin` dom (Ξs1 ++ Ξc1 ++ Θ0)).
        { intros x Hx. rewrite <- Hd2 in Hx. pose proof (Hκf2 x Hx) as Hf.
          clear - Hf; fsetdec. }
        assert (HΞ2Ξs1 : forall x, x `in` dom Ξc2 -> x `notin` dom Ξs1).
        { intros x Hx. pose proof (HΞ2disj x Hx) as Hf.
          repeat rewrite dom_app in Hf. clear - Hf; fsetdec. }
        assert (HΞ2Ξc1Θ0 : forall x, x `in` dom Ξc2 -> x `notin` dom (Ξc1 ++ Θ0)).
        { intros x Hx. pose proof (HΞ2disj x Hx) as Hf.
          repeat rewrite dom_app in Hf. rewrite dom_app. clear - Hf; fsetdec. }
        assert (Hdisj12 : forall β0, β0 `in` dom κc1 -> β0 `notin` dom κc2).
        { intros β0 Hβ0 Hin2. pose proof (Hκf2 β0 Hin2) as Hf2.
          repeat rewrite dom_app in Hf2. rewrite Hd1' in Hβ0.
          clear - Hf2 Hβ0; fsetdec. }
        assert (Hdisj2s1 : forall β0, β0 `in` dom κc2 -> β0 `notin` dom κs1).
        { intros β0 Hβ0. pose proof (Hκf2 β0 Hβ0) as Hf2.
          repeat rewrite dom_app in Hf2. clear - Hf2 Hd_s1; fsetdec. }
        exists (C1 ++ C2), (Ξc1 ++ Ξc2), (Ξs2 ++ Ξs1), Pa2,
               (κc1 ++ κc2), (κs2 ++ κs1).
        repeat split.
        -- (* a_lookeq.  The RIGHT branch ran at the GROWN context
              [Ξs1 ++ Ξc1 ++ Θ0] (its own flexibles avoid both of the left
              run's blocks); the rule wants both halves at [Θ0], and dropping
              declarations only SHRINKS the avoid-set, which is the direction
              [a_lookeq_ctx_ftv_mono] goes. *)
           (* ⭐ THE CROSS-HALF FRESHNESS GUARD (2026-08-19).  Both conjuncts
              are already facts of this configuration, in the two shapes the
              proof has anyway: the RIGHT run's block dodges the LEFT run's
              constraints (its own ftv-𝒞 bound, as [HΞ2C1] below repeats),
              and the RIGHT run's constraints dodge the LEFT run's block
              (the look's DISJUNCTIVE ftv bound — the second disjunct is
              impossible because [Ξc1] is IN the right run's context, and
              the first lands in [P02] or [Ξc2], both apart from it). *)
           assert (Hgc1 : ftvar_in_a_cstrs C1 ∩ dom Ξc2 [=] empty).
           { intros x; split; intros Hx; [ | clear - Hx; fsetdec ].
             exfalso.
             assert (Hx1 : x `in` ftvar_in_a_cstrs C1) by (clear - Hx; fsetdec).
             assert (Hx2 : x `in` dom Ξc2) by (clear - Hx; fsetdec).
             rewrite <- Hd2 in Hx2.
             pose proof (Hκf2 x Hx2) as Hf. repeat rewrite dom_app in Hf.
             assert (Hxκ : x `notin` dom κ).
             { intro Hc. destruct (a_inc_dom_flex Hκ Hc) as [Hb | [τ0 Hb]];
                 apply binds_In in Hb; clear - Hf Hb; fsetdec. }
             pose proof (def_ftv_dom HwfΘ) as Hdf.
             clear - HftvC1 Hf Hxκ Hdf Hx1; fsetdec. }
           assert (Hgc2 : ftvar_in_a_cstrs C2 ∩ dom Ξc1 [=] empty).
           { intros x; split; intros Hx; [ | clear - Hx; fsetdec ].
             exfalso.
             assert (Hx1 : x `in` ftvar_in_a_cstrs C2) by (clear - Hx; fsetdec).
             assert (Hx2 : x `in` dom Ξc1) by (clear - Hx; fsetdec).
             assert (Hxin : x `in` ftvar_in_aenv (Ξs1 ++ Ξc1 ++ Θ0)).
             { pose proof (dom_subset_ftvar_in_aenv (Ξs1 ++ Ξc1 ++ Θ0)) as Hds.
               repeat rewrite dom_app in Hds. clear - Hds Hx2; fsetdec. }
             destruct ((proj2 a_looksub_lookeq_ftv) _ _ _ _ _ _ HLK2 x Hx1)
               as [Hlft | Hrgt]; [ | clear - Hrgt Hxin; contradiction ].
             assert (HxΞ2 : x `notin` dom Ξc2).
             { intro Hc. rewrite <- Hd2 in Hc. rewrite <- Hd1' in Hx2.
               exact (Hdisj12 x Hx2 Hc). }
             clear - Hlft HxΞ2 HfrP02Ξ Hx2; fsetdec. }
           apply a_lookeq__arrow;
             [ exact Hgc1 | exact Hgc2
             | exact HLK1
             | eapply a_lookeq_ctx_ftv_mono;
                 [ exact HLK2
                 | repeat rewrite ftvar_in_aenv_app; clear; fsetdec
                 | (* ⭐ AND THE FLEXIBLES SURVIVE THE DROP, because the guard's
                      condition is scoped to the COUNTERPART's variables and
                      [P02] is Θ0-scoped: it misses both blocks, which is
                      exactly [HfrP02Ξs] / [HfrP02Ξ] above. *)
                   intros β0 Hβ0;
                   (* ⚠️ [@]: [Set Implicit Arguments] makes all three binders
                      implicit here (each occurs in the conclusion) *)
                   assert (Hns : β0 `notin` dom Ξs1)
                     by (clear - HfrP02Ξs Hβ0; fsetdec);
                   assert (Hnc : β0 `notin` dom Ξc1)
                     by (clear - HfrP02Ξ Hβ0; fsetdec);
                   rewrite (@a_flex_tvar_app_notin Ξs1 (Ξc1 ++ Θ0) β0 Hns);
                   rewrite (@a_flex_tvar_app_notin Ξc1 Θ0 β0 Hnc);
                   reflexivity ] ].
        -- (* solve *)
           (* the Ξc2-apartness facts, each proved from a SMALL set of
              inclusions — [fsetdec] on all of them at once does not scale *)
           assert (HΞ2Pi : forall x, x `in` dom Ξc2 ->
                     x `notin` ftvar_in_pskl Pi).
           { intros x Hx; pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfd;
             pose proof (HΞ2Ξc1Θ0 x Hx) as Hf; rewrite dom_app in Hf;
             simpl in Hfd; clear - Hfd Hf; fsetdec. }
           assert (HΞ2C1 : forall x, x `in` dom Ξc2 ->
                     x `notin` ftvar_in_a_cstrs C1).
           { (* [a_looksub_lookeq_ftv]'s EXACT bound is gone (the ∀ rules
                leak), and x is a name the RIGHT run invented, so the ctx
                corollary does not apply either.  What does apply is the
                IH's OWN ftv-𝒞 bound: the left run's constraints live in
                ψa ∪ dom Ξc1 ∪ dom κ ∪ def_ftv Θ, and an invented name
                avoids all four. *)
             intros x Hx. rewrite <- Hd2 in Hx.
             pose proof (Hκf2 x Hx) as Hf. repeat rewrite dom_app in Hf.
             assert (Hxκ : x `notin` dom κ).
             { intro Hc. destruct (a_inc_dom_flex Hκ Hc) as [Hb | [τ0 Hb]];
                 apply binds_In in Hb; clear - Hf Hb; fsetdec. }
             pose proof (def_ftv_dom HwfΘ) as Hdf.
             clear - HftvC1 Hf Hxκ Hdf; fsetdec. }
           (* OUTPUT freshness (a premise of the weakening): C1 is all-eq, so
              [a_solve_cstr_ftv_eq] bounds Pa1 EXACTLY by the three sets Ξc2
              already avoids — including, now, the left SOLVE's own block *)
           assert (HΞ2Pa1 : forall x, x `in` dom Ξc2 ->
                     x `notin` ftvar_in_pskl Pa1).
           { intros x Hx;
             pose proof (a_solve_cstr_ftv_eq HSolve1
                           (a_lookeq_cstr_eq HLK1)) as Hfe;
             pose proof (HΞ2Pi x Hx) as HxPi;
             pose proof (HΞ2C1 x Hx) as HxC1;
             pose proof (HΞ2Ξs1 x Hx) as HxS1;
             clear - Hfe HxPi HxC1 HxS1; fsetdec. }
           rewrite (aenv_app_assoc Ξc1 Ξc2 Θ0).
           eapply a_solve_cstr_app;
             [ exact (a_lookeq_cstr_eq HLK1)
             | apply a_solve_cstr_weaken_mid_flex;
                 [ exact HfmΞ2 | exact HΞ2Ξc1Θ0 | exact HΞ2Pi | exact HΞ2C1
                 | exact HΞ2Pa1 | exact HΞ2Ξs1 | exact HSolve1 ]
             | (* [Ξc2 ++ Ξs1 ++ Ξc1 ++ Θ0] → [Ξs1 ++ Ξc1 ++ Ξc2 ++ Θ0]:
                  the same entries, so both flex directions are one rotation *)
               eapply a_solve_cstr_ctx_change;
                 [ exact HSolve2
                 | repeat rewrite ftvar_in_aenv_app; clear; fsetdec
                 | intros α1 Hg; destruct Hg as [Hb | [τ Hb]];
                     [ left | right; exists τ ]; apply binds_rot_app; exact Hb
                 | intros P0 Hf; inversion Hf; subst;
                     [ apply a_flex__var with (α := α0)
                     | apply a_flex__var_def with (α := α0) (τ := τ) ];
                     apply binds_rot_app_rev; assumption ] ].
        -- (* all_flex_mono (Ξs2 ++ Ξs1) *)
           apply all_flex_mono_app; assumption.
        -- (* uniq (Ξs2 ++ Ξs1) — this is what [dom Ξs1] in the right IH's
              avoid-set was for; [uniq Ξ] is not re-derivable (hand-off §4c) *)
           assert (Hdd : dom Ξs2 ∩ dom Ξs1 [<=] empty).
           { intros x Hx.
             assert (Hx2 : x `in` dom Ξs2) by (clear - Hx; fsetdec).
             assert (Hx1 : x `in` dom Ξs1) by (clear - Hx; fsetdec).
             pose proof (Hfrs2 x Hx2) as Hf. exfalso; clear - Hf Hx1; fsetdec. }
           apply uniq_app_4; [ exact Hus2 | exact Hus1 | exact Hdd ].
        -- (* keys κs = keys Ξs *) exact Hmaps.
        -- (* dom Ξs ∩ L = ∅ : both blocks dodged a SUPERSET of L *)
           intros α0 Hα0. rewrite dom_app in Hα0.
           apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0];
             [ pose proof (Hfrs2 α0 Hα0) as Hf | pose proof (Hfrs1 α0 Hα0) as Hf ];
             clear - Hf; fsetdec.
        -- (* the SOLVE blocks' payloads *) apply Forall_app; split; assumption.
        -- (* wf Pa2 : [Ξs2,Ξc2,Ξs1,Ξc1,Θ0] → [Ξs2,Ξs1,Ξc1,Ξc2,Θ0] *)
           eapply a_wf_pskl_weaken; [ | exact HwfPa2 ].
           intros x b Hb.
           rewrite (aenv_app_assoc Ξs2 Ξs1 ((Ξc1 ++ Ξc2) ++ Θ0)).
           rewrite (aenv_app_assoc Ξc1 Ξc2 Θ0).
           apply binds_app_perm5; exact Hb.
        -- (* {{ ⊢ ((Ξc1 ++ Ξc2) ++ Θ0) }}a *)
           apply a_wf_aenv_flex_prefix;
             [ apply all_flex_mono_app; assumption
             | pose proof (a_wf_aenv_uniq HwfΞ2) as Huq;
               clear - Huq; solve_uniq
             | exact HwfΘ0 ].
        -- (* α ∉ dom (Ξc1++Ξc2) *)
           rewrite dom_app; clear - HαΞ1 HαΞ2; fsetdec.
        -- (* keys κc = keys Ξc *) exact Hmapc.
        -- (* κc images ⊆ ftv ψa *) apply Forall_app; split; assumption.
        -- (* ftv (C1++C2).  The right branch's κ is [κs1 ++ κc1 ++ κ], so its
              bound carries a [dom Ξs1] term the conclusion does NOT have — and
              that term has to be ELIMINATED, not absorbed: a name of Ξs1 is a
              name of the context the right run started in, it misses P02 (which
              is Θ0-scoped) and it misses Ξc2, so [a_lookeq_ftv_ctx] says it is
              not in C2 at all. *)
           assert (HC2s1 : forall x, x `in` dom Ξs1 ->
                     x `notin` ftvar_in_a_cstrs C2).
           { intros x Hx. eapply a_lookeq_ftv_ctx;
               [ exact HLK2
               | repeat rewrite dom_app; clear - Hx; fsetdec
               | pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd;
                 pose proof (Hfrs1 x Hx) as Hf;
                 clear - Hfd Hf Hdf0 HL; fsetdec
               | intro Hc; rewrite <- Hd2 in Hc;
                 pose proof (Hκf2 x Hc) as Hf2;
                 repeat rewrite dom_app in Hf2; clear - Hf2 Hx; fsetdec ]. }
           assert (HC2s1' : ftvar_in_a_cstrs C2 ∩ dom Ξs1 [<=] empty).
           { intros x Hx.
             assert (Hx1 : x `in` dom Ξs1) by (clear - Hx; fsetdec).
             assert (Hx2 : x `in` ftvar_in_a_cstrs C2) by (clear - Hx; fsetdec).
             exfalso; apply (HC2s1 x Hx1); exact Hx2. }
           rewrite ftvar_in_a_cstrs_app. rewrite dom_app.
           repeat rewrite dom_app in HftvC2.
           rewrite Hd1' in HftvC2. rewrite Hd_s1 in HftvC2.
           clear - HftvC1 HftvC2 HC2s1'; fsetdec.
        -- (* a_inc.  Do NOT permute [Hinc2] — REBUILD from [Hκ], one block at a
              time, since [a_inc_flex_prefix_build] does not care WHERE a block
              was generated, only that its payloads are wf monotypes in Θ. *)
           assert (Hb1 : (κc2 ++ κ) ∷ (Ξc2 ++ Θ0) ⊑ Θ)
             by (apply a_inc_flex_prefix_build;
                   [ exact HfmΞ2 | exact Hmap2 | exact Hwm2 | exact Hκ ]).
           assert (Hb2 : (κc1 ++ κc2 ++ κ) ∷ (Ξc1 ++ Ξc2 ++ Θ0) ⊑ Θ)
             by (apply a_inc_flex_prefix_build;
                   [ exact HfmΞ1 | exact Hmap1 | exact Hwm1 | exact Hb1 ]).
           assert (Hb3 : (κs1 ++ κc1 ++ κc2 ++ κ)
                           ∷ (Ξs1 ++ Ξc1 ++ Ξc2 ++ Θ0) ⊑ Θ)
             by (apply a_inc_flex_prefix_build;
                   [ exact Hfms1 | exact Hks1 | apply HFw; exact HFs1
                   | exact Hb2 ]).
           assert (Hb4 : (κs2 ++ κs1 ++ κc1 ++ κc2 ++ κ)
                           ∷ (Ξs2 ++ Ξs1 ++ Ξc1 ++ Ξc2 ++ Θ0) ⊑ Θ)
             by (apply a_inc_flex_prefix_build;
                   [ exact Hfms2 | exact Hks2 | apply HFw; exact HFs2
                   | exact Hb3 ]).
           rewrite (list_app_assoc κs2 κs1 ((κc1 ++ κc2) ++ κ)).
           rewrite (list_app_assoc κc1 κc2 κ).
           rewrite (aenv_app_assoc Ξs2 Ξs1 ((Ξc1 ++ Ξc2) ++ Θ0)).
           rewrite (aenv_app_assoc Ξc1 Ξc2 Θ0).
           exact Hb4.
        -- (* a_inc_equiv Θ0 κ κ Θ *) apply a_inc_equiv_refl; exact Hκ.
        -- (* κc fresh *)
           intros α0 Hα0. rewrite dom_app in Hα0.
           apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0].
           ++ apply Hκf1; exact Hα0.
           ++ pose proof (Hκf2 α0 Hα0) as Hf. repeat rewrite dom_app in Hf.
              clear - Hf; fsetdec.
        -- (* precision.  [Hpre2] is under [κs2 ++ κc2 ++ κs1 ++ κc1 ++ κ] and
              the goal wants [(κs2 ++ κs1) ++ (κc1 ++ κc2) ++ κ] — the same
              bindings on pairwise-disjoint domains, so it is a lookup-level
              identity: peel [κs2], swap [κc2] past [κs1], peel [κs1], swap
              [κc2] past [κc1]. *)
           assert (Hperm : msubst_pskl ((κs2 ++ κs1) ++ (κc1 ++ κc2) ++ κ) Pa2
                         = msubst_pskl (κs2 ++ κc2 ++ κs1 ++ κc1 ++ κ) Pa2).
           { rewrite (list_app_assoc κs2 κs1 ((κc1 ++ κc2) ++ κ)).
             rewrite (list_app_assoc κc1 κc2 κ).
             apply msubst_pskl_lookup_congr. intro β.
             apply msubst_lookup_app_agree.
             rewrite (@msubst_lookup_app_swap κc2 κs1 (κc1 ++ κ) β Hdisj2s1).
             apply msubst_lookup_app_agree.
             apply (@msubst_lookup_app_swap κc1 κc2 κ β Hdisj12). }
           rewrite Hperm.
           eapply ad_partial_precise_psi_cong; [ exact Hpre2 | clear - HΨa; fsetdec ].
        -- (* ⭐⭐ THE SOLVE BLOCKS vs THE COLLECTED CONSTRAINTS — four cases.
              Two are the IHs'; [dom Ξs2 ∩ ftv 𝒞1] is bought by the RIGHT
              IH's enlarged avoid-set; and [dom Ξs1 ∩ ftv 𝒞2] is [HC2s1] —
              the RIGHT run's look ran at a context CONTAINING [Ξs1], so
              [a_lookeq_ftv_ctx] applies to it (this is the same derivation
              the ftv-𝒞 bullet above makes, repeated because bullets do not
              share). *)
           assert (HC2s1 : forall x, x `in` dom Ξs1 ->
                     x `notin` ftvar_in_a_cstrs C2).
           { intros x Hx. eapply a_lookeq_ftv_ctx;
               [ exact HLK2
               | repeat rewrite dom_app; clear - Hx; fsetdec
               | pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd;
                 pose proof (Hfrs1 x Hx) as Hf;
                 clear - Hfd Hf Hdf0 HL; fsetdec
               | intro Hc; rewrite <- Hd2 in Hc;
                 pose proof (Hκf2 x Hc) as Hf2;
                 repeat rewrite dom_app in Hf2; clear - Hf2 Hx; fsetdec ]. }
           intros α0 Hα0. rewrite dom_app in Hα0.
           rewrite ftvar_in_a_cstrs_app.
           destruct (AtomSetProperties.In_dec α0 (dom Ξs2)) as [Hin2 | Hnin2].
           { pose proof (Hapart2 α0 Hin2) as Ha2.
             pose proof (Hfrs2 α0 Hin2) as Hf2.
             clear - Ha2 Hf2. fsetdec. }
           assert (Hin1 : α0 `in` dom Ξs1) by (clear - Hα0 Hnin2; fsetdec).
           pose proof (Hapart1 α0 Hin1) as Ha1.
           pose proof (HC2s1 α0 Hin1) as Hc2.
           clear - Ha1 Hc2. fsetdec.
      * (* P0 = all_syn : refinement bskl_all_inh ⊳ arrow — absurd *)
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine; inversion Hrefine.
      * (* P0 = ghost : excluded by HP0nh *)
        exfalso; apply HP0nh; reflexivity.
      * (* P0 = univ_ghost P0s : ∀◇ → LE-UnivGhostR + IHn (P0 shrinks, R' fixed) *)
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        inversion Hrefine; subst.
        match goal with
          H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh _ ⊳ bskl_arrow _ _ }}ad |- _ =>
            rename H into Href' end.
        assert (Hmeas : size_uskl (uskl_arrow Ra Rb) + size_pskl P0s <= n)
          by (cbn in Hn |- *; lia).
        pose proof (proj2 (a_wf_pskl_univ_ghost_inv HwfP0)) as HwfP0s.
        (* a PASS-THROUGH row: Θ0, Θ, Θw, κ and the avoid-set [L] are all
           unchanged, so both blocks and both extensions come back verbatim *)
        edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa (bskl_arrow Q1 Q2)
                     (pskl_arrow (uskl_to_pskl Ra) (uskl_to_pskl Rb)) P0s Pi
                     (uskl_arrow Ra Rb) α Θs Δρ Ψρ (uskl_arrow Ra' Rb')
                     Hmeas HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0s HwfPi Hκ Hκw Hψaw
                     HαΘ HαΘ0
                     (eq_refl : ⌊ uskl_arrow Ra Rb ⌋ˢ
                                = pskl_arrow (uskl_to_pskl Ra) (uskl_to_pskl Rb))
                     HscopeS HlcS Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hcons0 ltac:(lc_tgt) HwfSub Href'
                     Hrho0 HΘs HΨρ Hrfr HΔρΔ HΔρw
                     ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
          as (𝒞 & Ξc & Ξs & Pa & κc & κs
                & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
                & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
        exists 𝒞, Ξc, Ξs, Pa, κc, κs.
        repeat split; try assumption.
        apply a_lookeq__univ_ghost_r;
          [ exact HPnα
          | apply guarded_pskl__arrow; apply lc_uskl_to_pskl; assumption
          | exact HLK ].
  (* ---------------------------------------------------------------- *)
  (* The two ∀ cases (paper Cases C-ForallInh / C-ForallSyn) need the   *)
  (* ∀-BINDER KIT, which neither is available yet nor is case-specific: *)
  (*  - C-ForallSyn  (Q = bskl_all_syn Q0): the refinement inverts to   *)
  (*    [__univ_ghost_fill] (so P0 = ∀◇P0', as the paper says), whose      *)
  (*    binder ALSO enters Θ — the contexts MATCH, so only the          *)
  (*    output-strengthening below is missing.                          *)
  (*  - C-ForallInh  (Q = bskl_all_inh Q0): the refinement inverts to   *)
  (*    [__all], whose binder enters Θ AND Δ while the consistency's    *)
  (*    enters Θ only — dropping it from Δ suffices                      *)
  (*    ([ad_refine_syn_delta_mono]).                                   *)
  (* KIT (shared by both, and by the ∀◇ rows above): run the IH at      *)
  (* Θ := β,Θ and Θ0 := β,Θ0, then REMOVE β from every output — the     *)
  (* paper's "reff, refg, refh, refi hold without β".  Needed:          *)
  (* a_inc tvar-extension; and β-strengthening for a_solve_cstr,        *)
  (* a_wf_pskl, a_wf_aenv, a_inc, a_inc_equiv and precision.            *)
  (* ---------------------------------------------------------------- *)
  - (* R' = all_syn R0 : C-ForallInh (→ LE-ForallInh) / C-ForallSyn (→ LE-ForallSyn) *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    (* ρ-INVERSION: a ∀ˢ ideal forces a ∀ˢ image with the SAME Ψρ, and the
       cofinite family is exactly what the IH at the opened body wants. *)
    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_all_syn_r_inv Hrho) as (Lρ & Rsub0 & HRs & Hrhobody).
    subst Rsub.
    assert (Hlcψa : lc_uskl ψa) by (apply is_dskl_lc; inversion Htags; assumption).
    cbn [uskl_to_pskl] in HwfSub.
    inversion HwfSub; subst.
    match goal with H : forall α0, α0 `notin` ?Ls -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
      rename H into Hsbody; remember Ls as Ls0 eqn:HeqLs; clear HeqLs end.
    inversion HlcS; subst.
    match goal with H : forall α0, lc_uskl _ |- _ => rename H into Hlcbody end.
    destruct (ad_pat_consis_all_syn_refine_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HlcQ)
      as (Lcof & Q0 & Hcof & HlcQ0 & [HrefInh | HrefSyn]).
    + (* C-ForallInh: Q = ∀ᴵ.Q0.  Refinement inversion gives P0 = ∀.P0' and the
         binder in Θ and Δ; dropping it from Δ ([ad_refine_syn_delta_mono])
         matches the consistency's; LE-ForallInh then needs a β-FREE
         constraint set, which the conclusion's ftv-bound supplies. *)
      destruct P0 as [ | n0 | β0 | P01 P02 | P0' | | P0s ].
      * (* unit *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefInh | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__unit ]. }
        inversion Hbad.
      * (* var_b *) inversion HwfP0.
      * (* var_f *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefInh | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__var ]. }
        inversion Hbad.
      * (* arrow *)
        exfalso.
        assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
        { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption. }
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefInh | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
        inversion Hbad.
      * (* P0 = ∀.P0' : LE-ForallInh *)
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
        inversion HrefInh; subst.
        match goal with H : forall α0, α0 `notin` ?Lr -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
          rename H into Hrbody; remember Lr as Lr0 eqn:HeqLr; clear HeqLr end.
        inversion HwfP0; subst.
        match goal with H : forall α0, α0 `notin` ?L0 -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
          rename H into Hw0body; remember L0 as Lw0 eqn:HeqLw0; clear HeqLw0 end.
        pick fresh β for
          (Lcof `union` Lρ `union` Lr0 `union` Lw0 `union` dom Θ `union` dom Θ0
             `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
             `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
             `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0'
             `union` def_ftv Θ
             (* the ∀ rule's own avoid-input (cluster 3) *)
             `union` ftvar_in_aenv Θ0
                `union` Ls0).
        assert (HβΘ : β `notin` dom Θ) by auto.
        assert (HβΘ0 : β `notin` dom Θ0) by auto.
        assert (Hβα : β <> α) by auto.
        assert (Hβκ : β `notin` dom κ) by auto.
        destruct (solve_context_open_tvar
                    HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0)
          as (Hweak & _ & Hwfβ & Hwfβ0 & HαΘβ & HαΘ0β & Hκβ & _ & HwfPiβ).
        assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                  ⊢ₚₛ (open_pskl_wrt_pskl P0' (pskl_var_f β)) }}a).
        { eapply a_wf_pskl_delta_mono;
            [ apply (Hw0body β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
        assert (HscopeSβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                  [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
        { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β)) as Hup.
          simpl in Hup, HscopeS |- *. clear - Hup HscopeS; fsetdec. }
        assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) ∩ Ψ' [=] empty).
        { rewrite ftag_in_uskl_open_var. simpl in Hdisj. exact Hdisj. }
        assert (HΨs1β : Ψsub [<=] union
                  (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) (union Ψρ Ψa)).
        { rewrite ftag_in_uskl_open_var. simpl in HΨs1. exact HΨs1. }
        assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ))
          by (eapply delta_def_fresh_weaken_tvar; eassumption).
        assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                  ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
          by (eapply ad_partial_precise_weaken;
                [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
        assert (Hconsβ : {{ Ψsub ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ˢ
                  (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                  ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad)
          by (apply Hcof; auto).
        (* the consistency/wf premises now speak of the IMAGE, which opens directly;
           [subst_msubst_uskl_syn_open] moves to the ρ premise, the only one still ideal-side *)
        assert (Hrhoβ : uskl_rsubst NM Θs Δρ Ψρ
                  (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                  (subst_uskl_in_uskl ψa α
                     (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β))))).
        { rewrite (@subst_msubst_uskl_syn_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
          apply Hrhobody; auto. }
        assert (HβΘs : β `notin` dom Θs) by (clear - HβΘ HΘsdom; fsetdec).
        assert (HΘsβ : forall x b, binds x b Θs -> binds x b ((β ~ abind_tvar) ++ Θ))
          by (intros x b Hb; apply binds_app_3; apply HΘs; exact Hb).
        assert (Hrfrβ : rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
          by (apply rsubst_fresh_weaken_tvar; exact Hrfr).
        assert (HΔρftvβ : forall α0, α0 `in` Δρ ->
                  α0 `notin` ftvar_in_pskl
                       (open_pskl_wrt_pskl P0' (pskl_var_f β))
                     `union` ftvar_in_pskl Pi).
        { intros α0 Hα0.
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0'
                        (pskl_var_f β)) as Hup.
          pose proof (HΔρftv α0 Hα0) as Hd0. pose proof (HΔρΘ α0 Hα0) as Hd1.
          cbn [ftvar_in_pskl] in Hup, Hd0.
          clear - Hup Hd0 Hd1 HβΘ; fsetdec. }
        assert (HwfSubβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                  (uskl_to_pskl (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))) }}a).
        { rewrite uskl_to_pskl_open.
          eapply a_wf_pskl_delta_mono;
            [ apply (Hsbody β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
        assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                  (pskl_to_bskl_inh (msubst_pskl κ (open_pskl_wrt_pskl P0'
                                                      (pskl_var_f β))))
                  ⊳ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad).
        { rewrite (@msubst_pskl_open Θ0 κ Θ P0' β Hκ Hβκ).
          rewrite pskl_to_bskl_inh_open.
          eapply ad_refine_syn_delta_mono;
            [ apply (Hrbody β ltac:(auto)) | clear; fsetdec ]. }
        assert (Hmeas : size_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                          + size_pskl (open_pskl_wrt_pskl P0' (pskl_var_f β)) <= n).
        { rewrite size_uskl_open_uskl_wrt_uskl_var.
          rewrite size_pskl_open_pskl_wrt_pskl_var. cbn in Hn |- *; lia. }
        (* ⭐ THE Θw PACK UNDER A BINDER (2026-08-04).  [Θw] does NOT move — it
           is the fixed context the SOLVE block's payloads are well-formed in,
           and keeping it fixed is exactly what lets β be stripped out of the
           [a_inc] below.  Only the two binds conditions and the κ-image bound
           have to be re-established at [(β ~ tvar) ++ Θ], and each is one
           line: the new entry is a RIGID, so it is on the [b = abind_tvar]
           side of [Hnr] and it is invisible to [a_flex_tvar]. *)
        destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
          as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
        (* ⚙️ THE IH's AVOID-SET IS [add β L], not [L].  The block is emitted
           OUTSIDE the ∀ and the fold renames the binder, so the row's own β
           must be dodged — otherwise [β ∉ dom Ξs] is unavailable, and both
           [HβPa] (the solve's ftv bound now carries a [dom Ξs] term) and the
           [a_inc] strip need it.  It costs nothing: the avoid-set premise is
           about [(β ~ tvar) ++ Θ0], which mentions β anyway. *)
        assert (HLβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β L)
          by (rewrite ftvar_in_aenv_cons_tvar; clear - HL; fsetdec).
        edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) Θw
                     κ Δ Ψ'
                     Ψi Ψa Ψsub ψa (open_bskl_wrt_bskl Q0 (bskl_var_f β))
                     (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                     (open_pskl_wrt_pskl P0' (pskl_var_f β)) Pi
                     (open_uskl_wrt_uskl R0 (uskl_var_f β)) α
                     Θs Δρ Ψρ (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                     Hmeas Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ HwfP0β HwfPiβ Hκβ Hκwβ
                     Hψaw HαΘβ HαΘ0β eq_refl
                     HscopeSβ (Hlcbody β) Htags Hdisjβ Hsub Hdfreshβ Hpreβ
                     HΨs1β HΨs2 Hconsβ ltac:(lc_tgt) HwfSubβ Hrefβ
                     Hrhoβ HΘsβ HΨρ Hrfrβ HΔρΔ HΔρw HΔρftvβ HΔρPi Hψaap
                     (add β L) HLβ)
          as (𝒞 & Ξc & Ξs & Pa & κc & κs
                & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
                & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
        (* --- β-freeness of every output (this time 𝒞 comes from the bound) --- *)
        pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
        assert (HβΞc : β `notin` dom Ξc).
        { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
          apply Hκfresh. simpl; clear; fsetdec. }
        assert (HβΞs : β `notin` dom Ξs)
          by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
        assert (Hβψa : β `notin` ftvar_in_uskl ψa) by auto.
        assert (Hβdef : β `notin` def_ftv Θ) by auto.
        assert (HβC : β `notin` ftvar_in_a_cstrs 𝒞).
        { cbn [def_ftv] in HftvC.
          clear - HftvC HβΞc Hβκ Hβψa Hβdef HβΘs; fsetdec. }
        assert (HβPa : β `notin` ftvar_in_pskl Pa).
        { pose proof (a_solve_cstr_ftv_eq HSolve (a_lookeq_cstr_eq HLK)) as Hpf.
          pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
          clear - Hpf Hfi HβC HβΘ0 HβΞs; fsetdec. }
        assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
        { rewrite Forall_forall in Himg |- *. intros p Hp.
          specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
        (* ⭐ and the SOLVE block's payloads dodge β for a DIFFERENT reason: they
           are well-formed in the FIXED [Θw], which predates the binder. *)

        assert (Hβκs : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κs).
        { rewrite Forall_forall. intros p Hp.
          pose proof (forall_wf_mono_images_dom HFs p Hp) as Hb.
          clear - Hb HβΘw; fsetdec. }
        assert (Hfmc : all_flex_mono Ξc) by (eapply a_lookeq_all_flex_mono; exact HLK).
        exists 𝒞, Ξc, Ξs, Pa, κc, κs.
        repeat split.
        -- (* a_lookeq : LE-ForallInh.  Exists-fresh: the rule fires at the very
              β this row already picked, so there is no representative to rename
              back — the payoff the campaign predicted. *)
           rewrite uskl_to_pskl_open in HLK.
           apply a_lookeq_forall_inh_adm with (β := β);
             [ clear - Fr; solve_notin | exact HLK ].
        -- (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
        -- (* all_flex_mono Ξs *) exact Hfms.
        -- (* uniq Ξs *) exact Hus.
        -- (* keys κs = keys Ξs *) exact Hks.
        -- (* dom Ξs ∩ L = ∅ *)
           intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
        -- (* the SOLVE block's payloads — at the FIXED Θw, so unchanged *)
           exact HFs.
        -- (* wf Pa *)
           rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
           apply (@a_wf_pskl_strip_tvar (Ξs ++ Ξc) β Θ0 empty Pa);
             [ rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
               exact HwfPa
             | exact HβPa ].
        -- (* a_wf_aenv *)
           eapply a_wf_aenv_strip_mid;
             [ apply all_flex_mono_decls; exact Hfmc | exact HwfΞ ].
        -- (* α ∉ dom Ξc *) exact HαΞ.
        -- (* keys *) exact Hmapfst.
        -- (* κc images *) exact Himg.
        -- (* ftv 𝒞 *) cbn [def_ftv] in HftvC. exact HftvC.
        -- (* a_inc — the strip now peels BOTH blocks at once *)
           rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
           rewrite <- (list_app_assoc κs κc κ).
           eapply a_inc_strip_tvar_mid;
             [ apply all_flex_mono_app; [ exact Hfms | exact Hfmc ]
             | rewrite !keys_app; rewrite Hks, Hmapfst; reflexivity
             | apply Forall_app; split; [ exact Hβκs | exact Hβκc ]
             | exact HβΘ
             | rewrite (list_app_assoc κs κc κ);
               rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
               exact Hinc ].
        -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
        -- (* κc fresh *)
           intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
           clear - Hκfresh; fsetdec.
        -- (* precision *)
           eapply ad_partial_precise_strengthen_tvar; exact Hprec.
        -- (* the SOLVE's block vs the constraints: both pass through the
              ∀ row unchanged *)
           exact Hapart.
      * (* ghost : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
      * (* ∀◇P0s : a ∀◇ source refines to ∀ᴵ only by [__univ_ghost_remove], whose
           (guarded) body cannot reach an inherited quantifier *)
        exfalso.
        destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
        assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
          by (apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
        inversion HrefInh; subst.
        match goal with
          H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_inh _ }}ad |- _ =>
            pose proof (ad_refine_syn_guarded_r_all HwfΘ H HgL
                          ltac:(eexists; (left + right); reflexivity)) as Hbad end.
        inversion Hbad.
    + (* C-ForallSyn: Q = ∀ˢ.Q0.  The refinement can only reach a SYNTHESISED
         ∀ by FILLING a universal ghost, so P0 = ∀◇P0s (paper: "since P0 ≠ □,
         inversion on the refinement premise gives P0 = ∀◇.P0'"), and the
         fill rule's binder enters Θ — matching the consistency's. *)
      destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
      * (* unit : guarded source ⇒ guarded target, but ∀ˢ is not guarded *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefSyn | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__unit ]. }
        inversion Hbad.
      * (* var_b : not well-formed *) inversion HwfP0.
      * (* var_f : guarded *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefSyn | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__var ]. }
        inversion Hbad.
      * (* arrow : guarded *)
        exfalso.
        assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
        { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption. }
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefSyn | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
        inversion Hbad.
      * (* all_syn : an INHERITED ∀ source never refines to a SYNTHESISED ∀ *)
        exfalso. cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
        inversion HrefSyn.
      * (* ghost : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
      * (* P0 = ∀◇P0s : LE-ForallSyn *)
        destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
        assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
          by (apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
        inversion HrefSyn; subst.
        -- (* __univ_ghost_remove : guarded source ⇒ guarded target — absurd *)
           exfalso.
           match goal with
             H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_syn _ }}ad |- _ =>
               pose proof (ad_refine_syn_guarded_r_all HwfΘ H HgL
                          ltac:(eexists; (left + right); reflexivity)) as Hbad end.
           inversion Hbad.
        -- (* __univ_ghost_fill : the ghost is filled — run the IH under β *)
           match goal with H : forall α0, α0 `notin` ?Lf -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
             rename H into Hfill end.
           match goal with H : forall α0, α0 `notin` ?Lf -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
             let Lf' := fresh "Lf" in
             remember Lf as Lf' eqn:HeqLf; clear HeqLf end.
           pick fresh β for
             (Lcof `union` Lρ `union` Lf `union` dom Θ `union` dom Θ0
                `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
                `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
                `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0s
                (* the ∀ rule's own avoid-input (cluster 3) *)
                `union` ftvar_in_aenv Θ0
                `union` Ls0).
           assert (HβΘ : β `notin` dom Θ) by auto.
           assert (HβΘ0 : β `notin` dom Θ0) by auto.
           assert (Hβα : β <> α) by auto.
           assert (Hβκ : β `notin` dom κ) by auto.
           destruct (solve_context_open_tvar
                       HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0)
             as (Hweak & _ & Hwfβ & Hwfβ0 & HαΘβ & HαΘ0β & Hκβ & HwfP0β & HwfPiβ).
           assert (HscopeSβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                     [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
           { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β)) as Hup.
             simpl in Hup, HscopeS |- *. clear - Hup HscopeS; fsetdec. }
           assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) ∩ Ψ' [=] empty).
           { rewrite ftag_in_uskl_open_var. simpl in Hdisj. exact Hdisj. }
           assert (HΨs1β : Ψsub [<=] union
                     (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) (union Ψρ Ψa)).
           { rewrite ftag_in_uskl_open_var. simpl in HΨs1. exact HΨs1. }
           assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ))
             by (eapply delta_def_fresh_weaken_tvar; eassumption).
           assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                     ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
             by (eapply ad_partial_precise_weaken;
                   [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
           assert (Hconsβ : {{ Ψsub ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ˢ
                     (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                     ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad)
             by (apply Hcof; auto).
           (* the consistency/wf premises now speak of the IMAGE, which opens directly;
              [subst_msubst_uskl_syn_open] moves to the ρ premise, the only one still ideal-side *)
           assert (Hrhoβ : uskl_rsubst NM Θs Δρ Ψρ
                     (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                     (subst_uskl_in_uskl ψa α
                        (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β))))).
           { rewrite (@subst_msubst_uskl_syn_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
             apply Hrhobody; auto. }
           assert (HβΘs : β `notin` dom Θs) by (clear - HβΘ HΘsdom; fsetdec).
           assert (HΘsβ : forall x b, binds x b Θs -> binds x b ((β ~ abind_tvar) ++ Θ))
             by (intros x b Hb; apply binds_app_3; apply HΘs; exact Hb).
           assert (Hrfrβ : rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
             by (apply rsubst_fresh_weaken_tvar; exact Hrfr).
           assert (HwfSubβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                     (uskl_to_pskl (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))) }}a).
           { rewrite uskl_to_pskl_open.
             eapply a_wf_pskl_delta_mono;
               [ apply (Hsbody β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
           assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                     (pskl_to_bskl_inh (msubst_pskl κ (pskl_univ_ghost P0s)))
                     ⊳ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad)
             by (cbn [msubst_pskl pskl_to_bskl_inh]; apply Hfill; auto).
           assert (Hmeas : size_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                             + size_pskl (pskl_univ_ghost P0s) <= n).
           { rewrite size_uskl_open_uskl_wrt_uskl_var. cbn in Hn |- *; lia. }
           (* the Θw pack under the binder — see the C-ForallInh row above *)
           destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
             as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
           assert (HLβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β L)
             by (rewrite ftvar_in_aenv_cons_tvar; clear - HL; fsetdec).
           edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) Θw
                        κ Δ Ψ'
                        Ψi Ψa Ψsub ψa (open_bskl_wrt_bskl Q0 (bskl_var_f β))
                        (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                        (pskl_univ_ghost P0s) Pi
                        (open_uskl_wrt_uskl R0 (uskl_var_f β)) α
                        Θs Δρ Ψρ (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                        Hmeas Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ HwfP0β HwfPiβ Hκβ Hκwβ
                        Hψaw HαΘβ HαΘ0β eq_refl
                        HscopeSβ (Hlcbody β) Htags Hdisjβ Hsub Hdfreshβ Hpreβ
                        HΨs1β HΨs2 Hconsβ ltac:(lc_tgt) HwfSubβ Hrefβ
                        Hrhoβ HΘsβ HΨρ Hrfrβ HΔρΔ HΔρw HΔρftv HΔρPi Hψaap
                        (add β L) HLβ)
             as (𝒞 & Ξc & Ξs & Pa & κc & κs
                   & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
                   & HwfPa & HwfΞ & HαΞ
                   & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
           (* --- β-freeness of every output --- *)
           pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
           assert (HβΞc : β `notin` dom Ξc).
           { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
             apply Hκfresh. simpl; clear; fsetdec. }
           assert (HβΞs : β `notin` dom Ξs)
             by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
           assert (HβC : β `notin` ftvar_in_a_cstrs 𝒞).
           { (* β is a rigid of the PREMISE's context, hence not a name the
                run can have invented — [a_lookeq_ftv_ctx] restores the exact
                bound for exactly such variables *)
             pose proof (a_wf_pskl_ftv_dom HwfP0) as Hfd. simpl in Hfd.
             eapply a_lookeq_ftv_ctx;
               [ exact HLK | simpl; clear; fsetdec
               | simpl; clear - Hfd HβΘ0; fsetdec | exact HβΞc ]. }
           assert (HβPa : β `notin` ftvar_in_pskl Pa).
           { pose proof (a_solve_cstr_ftv_eq HSolve (a_lookeq_cstr_eq HLK)) as Hpf.
             pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
             clear - Hpf Hfi HβC HβΘ0 HβΞs; fsetdec. }
           assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
           { rewrite Forall_forall in Himg |- *. intros p Hp.
             specialize (Himg p Hp). clear - Himg Fr; fsetdec. }

           assert (Hβκs : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κs).
           { rewrite Forall_forall. intros p Hp.
             pose proof (forall_wf_mono_images_dom HFs p Hp) as Hb.
             clear - Hb HβΘw; fsetdec. }
           assert (Hfmc : all_flex_mono Ξc) by (eapply a_lookeq_all_flex_mono; exact HLK).
           exists 𝒞, Ξc, Ξs, Pa, κc, κs.
           repeat split.
           ++ (* a_lookeq : LE-ForallSyn — exists-fresh, fire at the picked β *)
              rewrite uskl_to_pskl_open in HLK.
              apply a_lookeq_forall_syn_adm with (β := β);
                [ clear - Fr; solve_notin | exact HLK ].
           ++ (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
           ++ (* all_flex_mono Ξs *) exact Hfms.
           ++ (* uniq Ξs *) exact Hus.
           ++ (* keys κs = keys Ξs *) exact Hks.
           ++ (* dom Ξs ∩ L = ∅ *)
              intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
           ++ (* the SOLVE block's payloads — at the FIXED Θw *) exact HFs.
           ++ (* wf Pa *)
              rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
              apply (@a_wf_pskl_strip_tvar (Ξs ++ Ξc) β Θ0 empty Pa);
                [ rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
                  exact HwfPa
                | exact HβPa ].
           ++ (* a_wf_aenv *)
              eapply a_wf_aenv_strip_mid;
                [ apply all_flex_mono_decls; exact Hfmc | exact HwfΞ ].
           ++ (* α ∉ dom Ξc *) exact HαΞ.
           ++ (* keys *) exact Hmapfst.
           ++ (* κc images *) exact Himg.
           ++ (* ftv 𝒞 : [def_ftv] ignores the rigid binder β *)
              cbn [def_ftv] in HftvC. exact HftvC.
           ++ (* a_inc *)
              rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
              rewrite <- (list_app_assoc κs κc κ).
              eapply a_inc_strip_tvar_mid;
                [ apply all_flex_mono_app; [ exact Hfms | exact Hfmc ]
                | rewrite !keys_app; rewrite Hks, Hmapfst; reflexivity
                | apply Forall_app; split; [ exact Hβκs | exact Hβκc ]
                | exact HβΘ
                | rewrite (list_app_assoc κs κc κ);
                  rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
                  exact Hinc ].
           ++ (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
           ++ (* κc fresh *)
              intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
              clear - Hκfresh; fsetdec.
           ++ (* precision *)
              eapply ad_partial_precise_strengthen_tvar; exact Hprec.
           ++ (* the SOLVE's block vs the constraints: both pass through *)
              exact Hapart.
  - (* R' = all_tag εr R0 : the ε-TAGGED mirror of the previous case
       (C-ForallInh's tagged row splits the index [Ψ = Ψ0, ε]). *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    (* ρ-INVERSION: a ∀^ε ideal forces a ∀^ε image with the SAME ε and Ψρ *)
    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_all_tag_r_inv Hrho) as (Lρ & Rsub0 & HRs & Hrhobody).
    subst Rsub.
    assert (Hlcψa : lc_uskl ψa) by (apply is_dskl_lc; inversion Htags; assumption).
    cbn [uskl_to_pskl] in HwfSub.
    inversion HwfSub; subst.
    match goal with H : forall α0, α0 `notin` ?Ls -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
      rename H into Hsbody; remember Ls as Ls0 eqn:HeqLs; clear HeqLs end.
    inversion HlcS; subst.
    match goal with H : forall α0, lc_uskl _ |- _ => rename H into Hlcbody end.
    destruct (ad_pat_consis_all_tag_refine_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HlcQ)
      as (Lcof & Q0 & Ψ0 & Hcof & HlcQ0 & [[HrefInh HΨeq] | [HrefSyn HΨeq]]).
    + (* C-ForallInh: Q = ∀ᴵ.Q0.  Refinement inversion gives P0 = ∀.P0' and the
         binder in Θ and Δ; dropping it from Δ ([ad_refine_syn_delta_mono])
         matches the consistency's; LE-ForallInh then needs a β-FREE
         constraint set, which the conclusion's ftv-bound supplies. *)
      destruct P0 as [ | n0 | β0 | P01 P02 | P0' | | P0s ].
      * (* unit *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefInh | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__unit ]. }
        inversion Hbad.
      * (* var_b *) inversion HwfP0.
      * (* var_f *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefInh | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__var ]. }
        inversion Hbad.
      * (* arrow *)
        exfalso.
        assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
        { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption. }
        assert (Hbad : guarded_bskl (bskl_all_inh Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefInh | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
        inversion Hbad.
      * (* P0 = ∀.P0' : LE-ForallInh *)
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
        inversion HrefInh; subst.
        match goal with H : forall α0, α0 `notin` ?Lr -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
          rename H into Hrbody; remember Lr as Lr0 eqn:HeqLr; clear HeqLr end.
        inversion HwfP0; subst.
        match goal with H : forall α0, α0 `notin` ?L0 -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
          rename H into Hw0body; remember L0 as Lw0 eqn:HeqLw0; clear HeqLw0 end.
        pick fresh β for
          (Lcof `union` Lρ `union` Lr0 `union` Lw0 `union` dom Θ `union` dom Θ0
             `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
             `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
             `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0'
             `union` def_ftv Θ
             (* the ∀ rule's own avoid-input (cluster 3) *)
             `union` ftvar_in_aenv Θ0
                `union` Ls0).
        assert (HβΘ : β `notin` dom Θ) by auto.
        assert (HβΘ0 : β `notin` dom Θ0) by auto.
        assert (Hβα : β <> α) by auto.
        assert (Hβκ : β `notin` dom κ) by auto.
        destruct (solve_context_open_tvar
                    HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0)
          as (Hweak & _ & Hwfβ & Hwfβ0 & HαΘβ & HαΘ0β & Hκβ & _ & HwfPiβ).
        assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                  ⊢ₚₛ (open_pskl_wrt_pskl P0' (pskl_var_f β)) }}a).
        { eapply a_wf_pskl_delta_mono;
            [ apply (Hw0body β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
        assert (HscopeSβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                  [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
        { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β)) as Hup.
          simpl in Hup, HscopeS |- *. clear - Hup HscopeS; fsetdec. }
        assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) ∩ Ψ' [=] empty).
        { rewrite ftag_in_uskl_open_var. simpl in Hdisj.
          clear - Hdisj; fsetdec. }
        assert (HΨs1β : Ψ0 [<=] union
                  (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) (union Ψρ Ψa)).
        { rewrite ftag_in_uskl_open_var.
          pose proof (ad_pat_consis_ftag_sub (Hcof β ltac:(auto))) as Hfb.
          rewrite ftag_in_uskl_open_var in Hfb.   (* Ψ0 ⊆ ftag of the IMAGE body *)
          (* …and the image's tags are ρ's plus the ideal's *)
          pose proof (uskl_rsubst_ftag_sub (Hrhobody β ltac:(auto))) as Hrft.
          rewrite !ftag_in_uskl_open_var in Hrft.
          pose proof (ftag_in_uskl_subst_uskl_in_uskl ψa α
                        (msubst_uskl_syn κ R0)) as Hsb.
          rewrite ftag_in_uskl_msubst_uskl_syn in Hsb.
          pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
          simpl in HΨs1, Hdisj.
          rewrite <- Hψatag in Hsb.
          intros x Hx.
          pose proof (Hrft x (Hfb x Hx)) as Hxr.
          apply union_1 in Hxr; destruct Hxr as [Hxr | Hxr];
            [ clear - Hxr; fsetdec | ].
          pose proof (Hsb x Hxr) as Hx2.
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
        assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ))
          by (eapply delta_def_fresh_weaken_tvar; eassumption).
        assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                  ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
          by (eapply ad_partial_precise_weaken;
                [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
        assert (Hconsβ : {{ Ψ0 ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ˢ
                  (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                  ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad)
          by (apply Hcof; auto).
        (* the consistency/wf premises now speak of the IMAGE, which opens directly;
           [subst_msubst_uskl_syn_open] moves to the ρ premise, the only one still ideal-side *)
        assert (Hrhoβ : uskl_rsubst NM Θs Δρ Ψρ
                  (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                  (subst_uskl_in_uskl ψa α
                     (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β))))).
        { rewrite (@subst_msubst_uskl_syn_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
          apply Hrhobody; auto. }
        assert (HβΘs : β `notin` dom Θs) by (clear - HβΘ HΘsdom; fsetdec).
        assert (HΘsβ : forall x b, binds x b Θs -> binds x b ((β ~ abind_tvar) ++ Θ))
          by (intros x b Hb; apply binds_app_3; apply HΘs; exact Hb).
        assert (Hrfrβ : rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
          by (apply rsubst_fresh_weaken_tvar; exact Hrfr).
        assert (HΔρftvβ : forall α0, α0 `in` Δρ ->
                  α0 `notin` ftvar_in_pskl
                       (open_pskl_wrt_pskl P0' (pskl_var_f β))
                     `union` ftvar_in_pskl Pi).
        { intros α0 Hα0.
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0'
                        (pskl_var_f β)) as Hup.
          pose proof (HΔρftv α0 Hα0) as Hd0. pose proof (HΔρΘ α0 Hα0) as Hd1.
          cbn [ftvar_in_pskl] in Hup, Hd0.
          clear - Hup Hd0 Hd1 HβΘ; fsetdec. }
        assert (HwfSubβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                  (uskl_to_pskl (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))) }}a).
        { rewrite uskl_to_pskl_open.
          eapply a_wf_pskl_delta_mono;
            [ apply (Hsbody β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
        assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                  (pskl_to_bskl_inh (msubst_pskl κ (open_pskl_wrt_pskl P0'
                                                      (pskl_var_f β))))
                  ⊳ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad).
        { rewrite (@msubst_pskl_open Θ0 κ Θ P0' β Hκ Hβκ).
          rewrite pskl_to_bskl_inh_open.
          eapply ad_refine_syn_delta_mono;
            [ apply (Hrbody β ltac:(auto)) | clear; fsetdec ]. }
        assert (Hmeas : size_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                          + size_pskl (open_pskl_wrt_pskl P0' (pskl_var_f β)) <= n).
        { rewrite size_uskl_open_uskl_wrt_uskl_var.
          rewrite size_pskl_open_pskl_wrt_pskl_var. cbn in Hn |- *; lia. }
        (* ⭐ THE Θw PACK UNDER A BINDER (2026-08-04).  [Θw] does NOT move — it
           is the fixed context the SOLVE block's payloads are well-formed in,
           and keeping it fixed is exactly what lets β be stripped out of the
           [a_inc] below.  Only the two binds conditions and the κ-image bound
           have to be re-established at [(β ~ tvar) ++ Θ], and each is one
           line: the new entry is a RIGID, so it is on the [b = abind_tvar]
           side of [Hnr] and it is invisible to [a_flex_tvar]. *)
        destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
          as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
        (* ⚙️ THE IH's AVOID-SET IS [add β L], not [L].  The block is emitted
           OUTSIDE the ∀ and the fold renames the binder, so the row's own β
           must be dodged — otherwise [β ∉ dom Ξs] is unavailable, and both
           [HβPa] (the solve's ftv bound now carries a [dom Ξs] term) and the
           [a_inc] strip need it.  It costs nothing: the avoid-set premise is
           about [(β ~ tvar) ++ Θ0], which mentions β anyway. *)
        assert (HLβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β L)
          by (rewrite ftvar_in_aenv_cons_tvar; clear - HL; fsetdec).
        edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) Θw
                     κ Δ Ψ'
                     Ψi Ψa Ψ0 ψa (open_bskl_wrt_bskl Q0 (bskl_var_f β))
                     (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                     (open_pskl_wrt_pskl P0' (pskl_var_f β)) Pi
                     (open_uskl_wrt_uskl R0 (uskl_var_f β)) α
                     Θs Δρ Ψρ (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                     Hmeas Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ HwfP0β HwfPiβ Hκβ Hκwβ
                     Hψaw HαΘβ HαΘ0β eq_refl
                     HscopeSβ (Hlcbody β) Htags Hdisjβ Hsub Hdfreshβ Hpreβ
                     HΨs1β HΨs2β Hconsβ ltac:(lc_tgt) HwfSubβ Hrefβ
                     Hrhoβ HΘsβ HΨρ Hrfrβ HΔρΔ HΔρw HΔρftvβ HΔρPi Hψaap
                     (add β L) HLβ)
          as (𝒞 & Ξc & Ξs & Pa & κc & κs
                & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
                & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
        (* --- β-freeness of every output (this time 𝒞 comes from the bound) --- *)
        pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
        assert (HβΞc : β `notin` dom Ξc).
        { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
          apply Hκfresh. simpl; clear; fsetdec. }
        assert (HβΞs : β `notin` dom Ξs)
          by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
        assert (Hβψa : β `notin` ftvar_in_uskl ψa) by auto.
        assert (Hβdef : β `notin` def_ftv Θ) by auto.
        assert (HβC : β `notin` ftvar_in_a_cstrs 𝒞).
        { cbn [def_ftv] in HftvC.
          clear - HftvC HβΞc Hβκ Hβψa Hβdef HβΘs; fsetdec. }
        assert (HβPa : β `notin` ftvar_in_pskl Pa).
        { pose proof (a_solve_cstr_ftv_eq HSolve (a_lookeq_cstr_eq HLK)) as Hpf.
          pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
          clear - Hpf Hfi HβC HβΘ0 HβΞs; fsetdec. }
        assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
        { rewrite Forall_forall in Himg |- *. intros p Hp.
          specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
        (* ⭐ and the SOLVE block's payloads dodge β for a DIFFERENT reason: they
           are well-formed in the FIXED [Θw], which predates the binder. *)

        assert (Hβκs : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κs).
        { rewrite Forall_forall. intros p Hp.
          pose proof (forall_wf_mono_images_dom HFs p Hp) as Hb.
          clear - Hb HβΘw; fsetdec. }
        assert (Hfmc : all_flex_mono Ξc) by (eapply a_lookeq_all_flex_mono; exact HLK).
        exists 𝒞, Ξc, Ξs, Pa, κc, κs.
        repeat split.
        -- (* a_lookeq : LE-ForallInh.  Exists-fresh: the rule fires at the very
              β this row already picked, so there is no representative to rename
              back — the payoff the campaign predicted. *)
           rewrite uskl_to_pskl_open in HLK.
           apply a_lookeq_forall_inh_adm with (β := β);
             [ clear - Fr; solve_notin | exact HLK ].
        -- (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
        -- (* all_flex_mono Ξs *) exact Hfms.
        -- (* uniq Ξs *) exact Hus.
        -- (* keys κs = keys Ξs *) exact Hks.
        -- (* dom Ξs ∩ L = ∅ *)
           intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
        -- (* the SOLVE block's payloads — at the FIXED Θw, so unchanged *)
           exact HFs.
        -- (* wf Pa *)
           rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
           apply (@a_wf_pskl_strip_tvar (Ξs ++ Ξc) β Θ0 empty Pa);
             [ rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
               exact HwfPa
             | exact HβPa ].
        -- (* a_wf_aenv *)
           eapply a_wf_aenv_strip_mid;
             [ apply all_flex_mono_decls; exact Hfmc | exact HwfΞ ].
        -- (* α ∉ dom Ξc *) exact HαΞ.
        -- (* keys *) exact Hmapfst.
        -- (* κc images *) exact Himg.
        -- (* ftv 𝒞 *) cbn [def_ftv] in HftvC. exact HftvC.
        -- (* a_inc — the strip now peels BOTH blocks at once *)
           rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
           rewrite <- (list_app_assoc κs κc κ).
           eapply a_inc_strip_tvar_mid;
             [ apply all_flex_mono_app; [ exact Hfms | exact Hfmc ]
             | rewrite !keys_app; rewrite Hks, Hmapfst; reflexivity
             | apply Forall_app; split; [ exact Hβκs | exact Hβκc ]
             | exact HβΘ
             | rewrite (list_app_assoc κs κc κ);
               rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
               exact Hinc ].
        -- (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
        -- (* κc fresh *)
           intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
           clear - Hκfresh; fsetdec.
        -- (* precision *)
           eapply ad_partial_precise_strengthen_tvar; exact Hprec.
        -- (* the SOLVE's block vs the constraints: both pass through the
              ∀ row unchanged *)
           exact Hapart.
      * (* ghost : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
      * (* ∀◇P0s : a ∀◇ source refines to ∀ᴵ only by [__univ_ghost_remove], whose
           (guarded) body cannot reach an inherited quantifier *)
        exfalso.
        destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
        assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
          by (apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefInh.
        inversion HrefInh; subst.
        match goal with
          H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_inh _ }}ad |- _ =>
            pose proof (ad_refine_syn_guarded_r_all HwfΘ H HgL
                          ltac:(eexists; (left + right); reflexivity)) as Hbad end.
        inversion Hbad.
    + (* C-ForallSyn: Q = ∀ˢ.Q0.  The refinement can only reach a SYNTHESISED
         ∀ by FILLING a universal ghost, so P0 = ∀◇P0s (paper: "since P0 ≠ □,
         inversion on the refinement premise gives P0 = ∀◇.P0'"), and the
         fill rule's binder enters Θ — matching the consistency's. *)
      destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
      * (* unit : guarded source ⇒ guarded target, but ∀ˢ is not guarded *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefSyn | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__unit ]. }
        inversion Hbad.
      * (* var_b : not well-formed *) inversion HwfP0.
      * (* var_f : guarded *)
        exfalso.
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefSyn | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | apply guarded_pskl__var ]. }
        inversion Hbad.
      * (* arrow : guarded *)
        exfalso.
        assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
        { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
          apply guarded_pskl__arrow; assumption. }
        assert (Hbad : guarded_bskl (bskl_all_syn Q0)).
        { eapply ad_refine_syn_guarded_r_all;
          [ exact HwfΘ | exact HrefSyn | | eexists; (left + right); reflexivity ].
          apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
        inversion Hbad.
      * (* all_syn : an INHERITED ∀ source never refines to a SYNTHESISED ∀ *)
        exfalso. cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
        inversion HrefSyn.
      * (* ghost : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
      * (* P0 = ∀◇P0s : LE-ForallSyn *)
        destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
        assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
          by (apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
        cbn [msubst_pskl pskl_to_bskl_inh] in HrefSyn.
        inversion HrefSyn; subst.
        -- (* __univ_ghost_remove : guarded source ⇒ guarded target — absurd *)
           exfalso.
           match goal with
             H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ bskl_all_syn _ }}ad |- _ =>
               pose proof (ad_refine_syn_guarded_r_all HwfΘ H HgL
                          ltac:(eexists; (left + right); reflexivity)) as Hbad end.
           inversion Hbad.
        -- (* __univ_ghost_fill : the ghost is filled — run the IH under β *)
           match goal with H : forall α0, α0 `notin` ?Lf -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
             rename H into Hfill end.
           match goal with H : forall α0, α0 `notin` ?Lf -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ _ }}ad |- _ =>
             let Lf' := fresh "Lf" in
             remember Lf as Lf' eqn:HeqLf; clear HeqLf end.
           pick fresh β for
             (Lcof `union` Lρ `union` Lf `union` dom Θ `union` dom Θ0
                `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
                `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
                `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0s
                (* the ∀ rule's own avoid-input (cluster 3) *)
                `union` ftvar_in_aenv Θ0
                `union` Ls0).
           assert (HβΘ : β `notin` dom Θ) by auto.
           assert (HβΘ0 : β `notin` dom Θ0) by auto.
           assert (Hβα : β <> α) by auto.
           assert (Hβκ : β `notin` dom κ) by auto.
           destruct (solve_context_open_tvar
                       HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0)
             as (Hweak & _ & Hwfβ & Hwfβ0 & HαΘβ & HαΘ0β & Hκβ & HwfP0β & HwfPiβ).
           assert (HscopeSβ : ftvar_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                     [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
           { pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper R0 (uskl_var_f β)) as Hup.
             simpl in Hup, HscopeS |- *. clear - Hup HscopeS; fsetdec. }
           assert (Hdisjβ : (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) ∩ Ψ' [=] empty).
           { rewrite ftag_in_uskl_open_var. simpl in Hdisj.
             clear - Hdisj; fsetdec. }
           assert (HΨs1β : Ψ0 [<=] union
                     (ftag_in_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))) (union Ψρ Ψa)).
           { rewrite ftag_in_uskl_open_var.
             (* the tagged row's index is [Ψsub = Ψ0]; the extra tag ε sits in
                [ftag R'] but is disjoint from Ψ', while the body's own bound
                comes from the sub-consistency *)
             pose proof (ad_pat_consis_ftag_sub (Hcof β ltac:(auto))) as Hfb.
             rewrite ftag_in_uskl_open_var in Hfb.   (* Ψ0 ⊆ the IMAGE's tags *)
             pose proof (uskl_rsubst_ftag_sub (Hrhobody β ltac:(auto))) as Hrft.
             rewrite !ftag_in_uskl_open_var in Hrft.
             pose proof (ftag_in_uskl_subst_uskl_in_uskl ψa α
                           (msubst_uskl_syn κ R0)) as Hsb.
             rewrite ftag_in_uskl_msubst_uskl_syn in Hsb.
             pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags)) as Hψatag.
             simpl in HΨs1, Hdisj.
             rewrite HΨeq in HΨs1.
             rewrite <- Hψatag in Hsb.
             intros x Hx.
             pose proof (Hrft x (Hfb x Hx)) as Hxr.
             apply union_1 in Hxr; destruct Hxr as [Hxr | Hxr];
               [ clear - Hxr; fsetdec | ].
             pose proof (Hsb x Hxr) as Hx2.
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
           assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ))
             by (eapply delta_def_fresh_weaken_tvar; eassumption).
           assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                     ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
             by (eapply ad_partial_precise_weaken;
                   [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
           assert (Hconsβ : {{ Ψ0 ⨟ ((β ~ abind_tvar) ++ Θ) ⊢ˢ
                     (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                     ∼ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad)
             by (apply Hcof; auto).
           (* the consistency/wf premises now speak of the IMAGE, which opens directly;
              [subst_msubst_uskl_syn_open] moves to the ρ premise, the only one still ideal-side *)
           assert (Hrhoβ : uskl_rsubst NM Θs Δρ Ψρ
                     (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                     (subst_uskl_in_uskl ψa α
                        (msubst_uskl_syn κ (open_uskl_wrt_uskl R0 (uskl_var_f β))))).
           { rewrite (@subst_msubst_uskl_syn_open Θ0 κ Θ ψa α R0 β Hκ Hακdom Hβκ Hβα Hlcψa).
             apply Hrhobody; auto. }
           assert (HβΘs : β `notin` dom Θs) by (clear - HβΘ HΘsdom; fsetdec).
           assert (HΘsβ : forall x b, binds x b Θs -> binds x b ((β ~ abind_tvar) ++ Θ))
             by (intros x b Hb; apply binds_app_3; apply HΘs; exact Hb).
           assert (Hrfrβ : rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
             by (apply rsubst_fresh_weaken_tvar; exact Hrfr).
           assert (HwfSubβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                     (uskl_to_pskl (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))) }}a).
           { rewrite uskl_to_pskl_open.
             eapply a_wf_pskl_delta_mono;
               [ apply (Hsbody β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
           assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                     (pskl_to_bskl_inh (msubst_pskl κ (pskl_univ_ghost P0s)))
                     ⊳ (open_bskl_wrt_bskl Q0 (bskl_var_f β)) }}ad)
             by (cbn [msubst_pskl pskl_to_bskl_inh]; apply Hfill; auto).
           assert (Hmeas : size_uskl (open_uskl_wrt_uskl R0 (uskl_var_f β))
                             + size_pskl (pskl_univ_ghost P0s) <= n).
           { rewrite size_uskl_open_uskl_wrt_uskl_var. cbn in Hn |- *; lia. }
           (* the Θw pack under the binder — see the C-ForallInh row above *)
           destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
             as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
           assert (HLβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β L)
             by (rewrite ftvar_in_aenv_cons_tvar; clear - HL; fsetdec).
           edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) Θw
                        κ Δ Ψ'
                        Ψi Ψa Ψ0 ψa (open_bskl_wrt_bskl Q0 (bskl_var_f β))
                        (uskl_to_pskl (open_uskl_wrt_uskl R0 (uskl_var_f β)))
                        (pskl_univ_ghost P0s) Pi
                        (open_uskl_wrt_uskl R0 (uskl_var_f β)) α
                        Θs Δρ Ψρ (open_uskl_wrt_uskl Rsub0 (uskl_var_f β))
                        Hmeas Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ HwfP0β HwfPiβ Hκβ Hκwβ
                        Hψaw HαΘβ HαΘ0β eq_refl
                        HscopeSβ (Hlcbody β) Htags Hdisjβ Hsub Hdfreshβ Hpreβ
                        HΨs1β HΨs2β Hconsβ ltac:(lc_tgt) HwfSubβ Hrefβ
                        Hrhoβ HΘsβ HΨρ Hrfrβ HΔρΔ HΔρw HΔρftv HΔρPi Hψaap
                        (add β L) HLβ)
             as (𝒞 & Ξc & Ξs & Pa & κc & κs
                   & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
                   & HwfPa & HwfΞ & HαΞ
                   & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
           (* --- β-freeness of every output --- *)
           pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
           assert (HβΞc : β `notin` dom Ξc).
           { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
             apply Hκfresh. simpl; clear; fsetdec. }
           assert (HβΞs : β `notin` dom Ξs)
             by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
           assert (HβC : β `notin` ftvar_in_a_cstrs 𝒞).
           { (* β is a rigid of the PREMISE's context, hence not a name the
                run can have invented — [a_lookeq_ftv_ctx] restores the exact
                bound for exactly such variables *)
             pose proof (a_wf_pskl_ftv_dom HwfP0) as Hfd. simpl in Hfd.
             eapply a_lookeq_ftv_ctx;
               [ exact HLK | simpl; clear; fsetdec
               | simpl; clear - Hfd HβΘ0; fsetdec | exact HβΞc ]. }
           assert (HβPa : β `notin` ftvar_in_pskl Pa).
           { pose proof (a_solve_cstr_ftv_eq HSolve (a_lookeq_cstr_eq HLK)) as Hpf.
             pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
             clear - Hpf Hfi HβC HβΘ0 HβΞs; fsetdec. }
           assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
           { rewrite Forall_forall in Himg |- *. intros p Hp.
             specialize (Himg p Hp). clear - Himg Fr; fsetdec. }

           assert (Hβκs : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κs).
           { rewrite Forall_forall. intros p Hp.
             pose proof (forall_wf_mono_images_dom HFs p Hp) as Hb.
             clear - Hb HβΘw; fsetdec. }
           assert (Hfmc : all_flex_mono Ξc) by (eapply a_lookeq_all_flex_mono; exact HLK).
           exists 𝒞, Ξc, Ξs, Pa, κc, κs.
           repeat split.
           ++ (* a_lookeq : LE-ForallSyn — exists-fresh, fire at the picked β *)
              rewrite uskl_to_pskl_open in HLK.
              apply a_lookeq_forall_syn_adm with (β := β);
                [ clear - Fr; solve_notin | exact HLK ].
           ++ (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
           ++ (* all_flex_mono Ξs *) exact Hfms.
           ++ (* uniq Ξs *) exact Hus.
           ++ (* keys κs = keys Ξs *) exact Hks.
           ++ (* dom Ξs ∩ L = ∅ *)
              intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
           ++ (* the SOLVE block's payloads — at the FIXED Θw *) exact HFs.
           ++ (* wf Pa *)
              rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
              apply (@a_wf_pskl_strip_tvar (Ξs ++ Ξc) β Θ0 empty Pa);
                [ rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
                  exact HwfPa
                | exact HβPa ].
           ++ (* a_wf_aenv *)
              eapply a_wf_aenv_strip_mid;
                [ apply all_flex_mono_decls; exact Hfmc | exact HwfΞ ].
           ++ (* α ∉ dom Ξc *) exact HαΞ.
           ++ (* keys *) exact Hmapfst.
           ++ (* κc images *) exact Himg.
           ++ (* ftv 𝒞 : [def_ftv] ignores the rigid binder β *)
              cbn [def_ftv] in HftvC. exact HftvC.
           ++ (* a_inc *)
              rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
              rewrite <- (list_app_assoc κs κc κ).
              eapply a_inc_strip_tvar_mid;
                [ apply all_flex_mono_app; [ exact Hfms | exact Hfmc ]
                | rewrite !keys_app; rewrite Hks, Hmapfst; reflexivity
                | apply Forall_app; split; [ exact Hβκs | exact Hβκc ]
                | exact HβΘ
                | rewrite (list_app_assoc κs κc κ);
                  rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
                  exact Hinc ].
           ++ (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
           ++ (* κc fresh *)
              intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
              clear - Hκfresh; fsetdec.
           ++ (* precision *)
              eapply ad_partial_precise_strengthen_tvar; exact Hprec.
           ++ (* the SOLVE's block vs the constraints: both pass through *)
              exact Hapart.
  - (* R' = ghost : α ∈ ∅ absurd *) clear - HαR; fsetdec.
  - (* R' = univ_ghost R0 : C-UnivGhost / C-UnivGhost1 / C-UnivGhost2.
       [⌊∀◇R0⌋ = ∀◇⌊R0⌋]; well-formedness of P makes ⌊R0⌋ GUARDED, which is
       the paper's handle on this case.  The P0-grid follows the paper's
       "case analysis on P0" in Case C-UnivGhost2. *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    pose proof (lc_uskl_univ_ghost_inv HlcS) as HlcS0.
    (* ρ-INVERSION: a ∀◇ ideal forces a ∀◇ image at the SAME Ψρ *)
    pose proof Hrho as Hrho0.   (* FOLDED copy: the ∀-P0 row keeps R' = ∀◇R0 *)
    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_univ_ghost_r_inv Hrho) as (Rsub0 & HRs & Hrhobody).
    subst Rsub.
    cbn [uskl_to_pskl] in HwfSub.
    destruct (a_wf_pskl_univ_ghost_inv HwfSub) as [HgSub0 HwfSub0].
    assert (Hmeas0 : forall P0', size_pskl P0' <= size_pskl P0 ->
                     size_uskl R0 + size_pskl P0' <= n)
      by (intros P0' HP0'; cbn in Hn; lia).
    destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
    + (* P0 = unit : GUARDED ⇒ the ghost is dropped ⇒ LE-UnivGhost2 *)
      assert (HgP0 : guarded_pskl pskl_unit) by apply guarded_pskl__unit.
      assert (HgQ : guarded_bskl Q).
      { eapply ad_refine_syn_guarded_r;
        [ exact HwfΘ | exact Hrefine | | lc_tgt ].
        apply guarded_pskl_to_bskl_inh;
          eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
      destruct (ad_pat_consis_univ_ghost_guarded_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HgQ HlcQ)
        as (Q0 & Hc0 & Href0 & HgQ0 & HlcQ0).
      edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                   (uskl_to_pskl R0) pskl_unit Pi R0 α Θs Δρ Ψρ Rsub0
                   (Hmeas0 pskl_unit ltac:(cbn; lia))
                   HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw HαΘ HαΘ0 eq_refl
                   HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 ltac:(lc_tgt) HwfSub0 Href0
                   Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
        as (𝒞 & Ξc & Ξs & Pa & κc & κs
              & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
              & HwfPa & HwfΞ & HαΞ
              & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
      exists 𝒞, Ξc, Ξs, Pa, κc, κs.
      repeat split; try assumption.
      apply a_lookeq__univ_ghost2;
         [ exact HgP0
         | apply flex_r_off_nonvar; intros ?; discriminate
         | exact HLK ].
    + (* P0 = var_b : not well-formed *) inversion HwfP0.
    + (* P0 = var_f β0 : ⭐ THE FlexR-PRIORITY SPLIT (2026-08-18).  At a RIGID
         β0 the row is still LE-UnivGhost2; at a FLEXIBLE one it is BARRED, and
         the case IS the arrow grid's flex-P0 one — which is why that block was
         factored out ([a_lookeq_flex_p0_complete]).  ⚙ The block never looked
         at the subject's shape, so it applies here verbatim. *)
      assert (HgP0 : guarded_pskl (pskl_var_f β0)) by apply guarded_pskl__var.
      assert (Hbt0 : a_binds_tvar β0 Θ0).
      { inversion HwfP0; subst; assumption. }
      destruct Hbt0 as [Hrig | Hflx].
      2:{ (* FLEXIBLE β0 — the factored flex-P0 block *)
        eapply (@a_lookeq_flex_p0_complete NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa
                  Q Pi (uskl_univ_ghost R0) α Θs Δρ Ψρ (uskl_univ_ghost Rsub0)
                  β0 L);
          solve [ eassumption | reflexivity | right; exact Hflx
                | assumption | cbn; assumption ]. }
      (* RIGID β0 — LE-UnivGhost2 survives, and the guard reads off rigidity *)
      assert (HgQ : guarded_bskl Q).
      { eapply ad_refine_syn_guarded_r;
        [ exact HwfΘ | exact Hrefine | | lc_tgt ].
        apply guarded_pskl_to_bskl_inh;
          eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
      destruct (ad_pat_consis_univ_ghost_guarded_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HgQ HlcQ)
        as (Q0 & Hc0 & Href0 & HgQ0 & HlcQ0).
      edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                   (uskl_to_pskl R0) (pskl_var_f β0) Pi R0 α Θs Δρ Ψρ Rsub0
                   (Hmeas0 (pskl_var_f β0) ltac:(cbn; lia))
                   HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw HαΘ HαΘ0 eq_refl
                   HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 ltac:(lc_tgt) HwfSub0 Href0
                   Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
        as (𝒞 & Ξc & Ξs & Pa & κc & κs
              & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
              & HwfPa & HwfΞ & HαΞ
              & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
      exists 𝒞, Ξc, Ξs, Pa, κc, κs.
      repeat split; try assumption.
      apply a_lookeq__univ_ghost2;
        [ exact HgP0
        | apply flex_r_off_rigid; intro Hf;
          pose proof (a_wf_aenv_uniq HwfΘ0) as Huq;
          destruct Hf as [Hb2 | [τx Hb2]];
          [ assert (Hc : abind_tvar = abind_flex_mono)
              by (eapply binds_unique; [ exact Hrig | exact Hb2 | exact Huq ])
          | assert (Hc : abind_tvar = abind_flex_mono_def τx)
              by (eapply binds_unique; [ exact Hrig | exact Hb2 | exact Huq ]) ];
          discriminate Hc
        | exact HLK ].
    + (* P0 = arrow P01 P02 : GUARDED ⇒ LE-UnivGhost2 *)
      assert (HgP0 : guarded_pskl (pskl_arrow P01 P02)).
      { pose proof (a_wf_pskl_lc HwfP0) as Hlc0; inversion Hlc0; subst.
        apply guarded_pskl__arrow; assumption. }
      assert (HgQ : guarded_bskl Q).
      { eapply ad_refine_syn_guarded_r;
        [ exact HwfΘ | exact Hrefine | | lc_tgt ].
        apply guarded_pskl_to_bskl_inh;
          eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0 ]. }
      destruct (ad_pat_consis_univ_ghost_guarded_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HgQ HlcQ)
        as (Q0 & Hc0 & Href0 & HgQ0 & HlcQ0).
      edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                   (uskl_to_pskl R0) (pskl_arrow P01 P02) Pi R0 α Θs Δρ Ψρ Rsub0
                   (Hmeas0 (pskl_arrow P01 P02) ltac:(cbn; lia))
                   HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0 HwfPi Hκ Hκw Hψaw HαΘ HαΘ0 eq_refl
                   HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 ltac:(lc_tgt) HwfSub0 Href0
                   Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
        as (𝒞 & Ξc & Ξs & Pa & κc & κs
              & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
              & HwfPa & HwfΞ & HαΞ
              & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
      exists 𝒞, Ξc, Ξs, Pa, κc, κs.
      repeat split; try assumption.
      apply a_lookeq__univ_ghost2;
         [ exact HgP0
         | apply flex_r_off_nonvar; intros ?; discriminate
         | exact HLK ].
    + (* P0 = ∀.P0' : C-UnivGhost1 → LE-UnivGhost1.  The ∀-binder kit applies:
         the refinement's binder is dropped from Δ by
         [ad_refine_syn_delta_mono], the IH runs at β,Θ / β,Θ0 with R'
         UNCHANGED (only P0 shrinks), and β is stripped from every output. *)
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      * (* refinement __all *)
        match goal with
          H : forall α0, α0 `notin` ?Lr -> {{ _ ⨟ _ ⊢ᵣ _ ⊳ open_bskl_wrt_bskl ?Qb _ }}ad |- _ =>
            rename H into Hrbody;
            remember Lr as Lr0 eqn:HeqLr; clear HeqLr;
            remember Qb as Qb0 eqn:HeqQb; clear HeqQb
        end.
        inversion HwfP0; subst.
        match goal with H : forall α0, α0 `notin` ?L0 -> {{ _ ⨟ _ ⊢ₚₛ _ }}a |- _ =>
          rename H into Hw0body; remember L0 as Lw0 eqn:HeqLw0; clear HeqLw0 end.
        (* consistency: C-UnivGhost1 (the ghost is kept under the ∀) or
           C-UnivGhost2 (dropped) *)
        inversion Hconsis; subst.
        -- (* C-UnivGhost1 *)
           match goal with H : forall α0, α0 `notin` ?Lc -> {{ _ ⨟ _ ⊢ˢ _ ∼ _ }}ad |- _ =>
             rename H into Hcbody; remember Lc as Lc0 eqn:HeqLc; clear HeqLc end.
           pick fresh β for
             (Lr0 `union` Lw0 `union` Lc0 `union` dom Θ `union` dom Θ0
                `union` dom κ `union` singleton α `union` ftvar_in_uskl ψa
                `union` ftvar_in_uskl R0 `union` ftvar_in_pskl (uskl_to_pskl R0)
                `union` ftvar_in_pskl Pi `union` ftvar_in_pskl P0s
                (* the ∀ rule's own avoid-input (cluster 3) *)
                `union` ftvar_in_aenv Θ0
                `union` def_ftv Θ).
           assert (HβΘ : β `notin` dom Θ) by auto.
           assert (HβΘ0 : β `notin` dom Θ0) by auto.
           assert (Hβα : β <> α) by auto.
           assert (Hβκ : β `notin` dom κ) by auto.
           assert (Hβψa : β `notin` ftvar_in_uskl ψa) by auto.
           assert (Hβdef : β `notin` def_ftv Θ) by auto.
           destruct (solve_context_open_tvar
                       HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 Hβα HβΘ HβΘ0)
             as (Hweak & _ & Hwfβ & Hwfβ0 & HαΘβ & HαΘ0β & Hκβ & _ & HwfPiβ).
           assert (HwfP0β : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                     ⊢ₚₛ (open_pskl_wrt_pskl P0s (pskl_var_f β)) }}a).
           { eapply a_wf_pskl_delta_mono;
               [ apply (Hw0body β ltac:(auto)) | intros γ _ Hγ; clear - Hγ; fsetdec ]. }
           assert (HscopeSβ : ftvar_in_uskl (uskl_univ_ghost R0)
                     [<=] add α (dom ((β ~ abind_tvar) ++ Θ0) `union` dom ((β ~ abind_tvar) ++ Θ))).
           { simpl in HscopeS |- *. clear - HscopeS; fsetdec. }
           assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ))
             by (eapply delta_def_fresh_weaken_tvar; eassumption).
           assert (Hpreβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                     ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad)
             by (eapply ad_partial_precise_weaken;
                   [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
           assert (HwfSubβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ₚₛ
                     (uskl_to_pskl (uskl_univ_ghost Rsub0)) }}a)
             by (eapply a_wf_pskl_weaken;
                   [ intros x b Hb; apply binds_app_3; exact Hb | exact HwfSub ]).
           (* ρ transports: Θs and Δρ do not move, only Θ / Θ0 grow by β *)
           assert (HβΘs : β `notin` dom Θs) by (clear - HβΘ HΘsdom; fsetdec).
           assert (HΘsβ : forall x b, binds x b Θs -> binds x b ((β ~ abind_tvar) ++ Θ))
             by (intros x b Hb; apply binds_app_3; apply HΘs; exact Hb).
           assert (Hrfrβ : rsubst_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ)
             by (apply rsubst_fresh_weaken_tvar; exact Hrfr).
           assert (HΔρftvβ : forall α0, α0 `in` Δρ ->
                     α0 `notin` ftvar_in_pskl
                          (open_pskl_wrt_pskl P0s (pskl_var_f β))
                        `union` ftvar_in_pskl Pi).
           { intros α0 Hα0.
             pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0s
                           (pskl_var_f β)) as Hup.
             pose proof (HΔρftv α0 Hα0) as Hd0. pose proof (HΔρΘ α0 Hα0) as Hd1.
             cbn [ftvar_in_pskl] in Hup, Hd0.
             clear - Hup Hd0 Hd1 HβΘ; fsetdec. }
           assert (Hrefβ : {{ ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣ
                     (pskl_to_bskl_inh (msubst_pskl κ (open_pskl_wrt_pskl P0s
                                                         (pskl_var_f β))))
                     ⊳ (open_bskl_wrt_bskl Qb0 (bskl_var_f β)) }}ad).
           { rewrite (@msubst_pskl_open Θ0 κ Θ P0s β Hκ Hβκ).
             rewrite pskl_to_bskl_inh_open.
             eapply ad_refine_syn_delta_mono;
               [ apply (Hrbody β ltac:(auto)) | clear; fsetdec ]. }
           assert (Hmeas : size_uskl (uskl_univ_ghost R0)
                             + size_pskl (open_pskl_wrt_pskl P0s (pskl_var_f β))
                             <= n).
           { rewrite size_pskl_open_pskl_wrt_pskl_var. cbn in Hn |- *; lia. }
           (* the Θw pack under the binder — see the C-ForallInh row above.  [Θw] does
              NOT move; keeping it fixed is what lets β be stripped from the [a_inc]. *)
           destruct (solve_scope_open_tvar (conj Hmon (conj Hnr Hκw)) HβΘ)
             as (HβΘw & Hmonβ & Hnrβ & Hκwβ).
           (* ⚙️ the IH's avoid-set is [add β L]: the block is emitted OUTSIDE the ∀,
              so the row's own binder must be dodged — [β ∉ dom Ξs] is what [HβPa]
              and the [a_inc] strip need. *)
           assert (HLβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β L)
             by (rewrite ftvar_in_aenv_cons_tvar; clear - HL; fsetdec).
           edestruct (IHn NM ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) Θw κ Δ
                        Ψ' Ψi Ψa Ψsub ψa (open_bskl_wrt_bskl Qb0 (bskl_var_f β))
                        (pskl_univ_ghost (uskl_to_pskl R0))
                        (open_pskl_wrt_pskl P0s (pskl_var_f β)) Pi
                        (uskl_univ_ghost R0) α Θs Δρ Ψρ (uskl_univ_ghost Rsub0)
                        Hmeas Hwfβ Hwfβ0 HwfΘw Hmonβ Hnrβ HwfP0β HwfPiβ Hκβ Hκwβ
                        Hψaw HαΘβ HαΘ0β eq_refl
                        HscopeSβ HlcS Htags Hdisj Hsub Hdfreshβ Hpreβ
                        HΨs1 HΨs2 (Hcbody β ltac:(auto)) ltac:(lc_tgt) HwfSubβ Hrefβ
                        Hrho0 HΘsβ HΨρ Hrfrβ HΔρΔ HΔρw HΔρftvβ HΔρPi Hψaap
                        (add β L) HLβ)
             as (𝒞 & Ξc & Ξs & Pa & κc & κs
              & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
              & HwfPa & HwfΞ & HαΞ
                   & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
           assert (HβΞs : β `notin` dom Ξs)
             by (intro Hc; pose proof (Hfrs β Hc) as Hf; clear - Hf; fsetdec).
           (* ⭐ the SOLVE block's payloads dodge β for a DIFFERENT reason: they are
              well-formed in the FIXED [Θw], which predates the binder. *)

           assert (Hβκs : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κs).
           { rewrite Forall_forall. intros p Hp.
             pose proof (forall_wf_mono_images_dom HFs p Hp) as Hb.
             clear - Hb HβΘw; fsetdec. }
           pose proof (@keys_eq_dom _ _ κc Ξc Hmapfst) as Hdκ.
           assert (HβΞc : β `notin` dom Ξc).
           { intro Hc. rewrite <- Hdκ in Hc. specialize (Hκfresh β Hc).
             apply Hκfresh. simpl; clear; fsetdec. }
           assert (HβC : β `notin` ftvar_in_a_cstrs 𝒞).
           { cbn [def_ftv] in HftvC.
             clear - HftvC HβΞc Hβκ Hβψa Hβdef HβΘs; fsetdec. }
           assert (HβPa : β `notin` ftvar_in_pskl Pa).
           { pose proof (a_solve_cstr_ftv_eq HSolve (a_lookeq_cstr_eq HLK)) as Hpf.
             pose proof (a_wf_pskl_ftv_dom HwfPi) as Hfi.
             clear - Hpf Hfi HβC HβΘ0 HβΞs; fsetdec. }
           assert (Hβκc : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κc).
           { rewrite Forall_forall in Himg |- *. intros p Hp.
             specialize (Himg p Hp). clear - Himg Hβψa; fsetdec. }
           assert (Hfmc : all_flex_mono Ξc)
             by (eapply a_lookeq_all_flex_mono; exact HLK).
           exists 𝒞, Ξc, Ξs, Pa, κc, κs.
           repeat split.
           ++ (* a_lookeq : LE-UnivGhost1 — exists-fresh, fire at the picked β *)
              apply a_lookeq_univ_ghost1_adm with (β := β);
                [ clear - Fr; solve_notin | exact HLK ].
           ++ (* solve *) eapply a_solve_cstr_strip_tvar_mid; exact HSolve.
           ++ (* all_flex_mono Ξs *) exact Hfms.
           ++ (* uniq Ξs *) exact Hus.
           ++ (* keys κs = keys Ξs *) exact Hks.
           ++ (* dom Ξs ∩ L = ∅ *)
              intros α0 Hα0; pose proof (Hfrs α0 Hα0) as Hf; clear - Hf; fsetdec.
           ++ (* the SOLVE block's payloads — at the FIXED Θw *) exact HFs.
           ++ (* wf Pa *)
              rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
              apply (@a_wf_pskl_strip_tvar (Ξs ++ Ξc) β Θ0 empty Pa);
                [ rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
                  exact HwfPa
                | exact HβPa ].
           ++ (* a_wf_aenv *)
              eapply a_wf_aenv_strip_mid;
                [ apply all_flex_mono_decls; exact Hfmc | exact HwfΞ ].
           ++ (* α ∉ dom Ξc *) exact HαΞ.
           ++ (* keys *) exact Hmapfst.
           ++ (* ρc images *) exact Himg.
           ++ (* ftv 𝒞 *) cbn [def_ftv] in HftvC. exact HftvC.
           ++ (* a_inc — the strip peels BOTH blocks at once *)
              rewrite <- (aenv_app_assoc Ξs Ξc Θ0).
              rewrite <- (list_app_assoc κs κc κ).
              eapply a_inc_strip_tvar_mid;
                [ apply all_flex_mono_app; [ exact Hfms | exact Hfmc ]
                | rewrite !keys_app; rewrite Hks, Hmapfst; reflexivity
                | apply Forall_app; split; [ exact Hβκs | exact Hβκc ]
                | exact HβΘ
                | rewrite (list_app_assoc κs κc κ);
                  rewrite (aenv_app_assoc Ξs Ξc ((β ~ abind_tvar) ++ Θ0));
                  exact Hinc ].
           ++ (* a_inc_equiv *) apply a_inc_equiv_refl; exact Hκ.
           ++ (* ρc fresh *)
              intros α0 Hα0. specialize (Hκfresh α0 Hα0). simpl in Hκfresh.
              clear - Hκfresh; fsetdec.
           ++ (* precision *)
              eapply ad_partial_precise_strengthen_tvar; exact Hprec.
           ++ (* the SOLVE's block vs the constraints: both pass through *)
              exact Hapart.
        -- (* C-UnivGhost2: the ghost is DROPPED against an inherited ∀.  The
              residual subject is the ∀◇-BODY, which well-formedness of the
              SUBJECT makes guarded (ghost bodies are guarded) — and a guarded
              subject never faces a quantifier.  [This is the row that is FALSE
              without the subject-wf premise: with R0 = α the body's subject is
              ψa itself, which may be a ∀ or a ∀◈.] *)
           exfalso.
           pose proof (guarded_uskl_head
                         (@guarded_uskl_of_uskl_to_pskl
                            (Rsub0) HgSub0))
             as Hghsub.
           match goal with
             H : {{ _ ⨟ _ ⊢ˢ Rsub0
                   ∼ bskl_all_inh _ }}ad |- _ =>
               pose proof (ad_pat_consis_guarded_head_target H HwfΘ Hghsub) as Hgh
           end.
           destruct Hgh as [Habs | [[α0 Habs] | [Q1 [Q2 Habs]]]];
             discriminate Habs.
      * (* refinement __flex_r : the target is a defined flex VAR, hence
           guarded — and an inherited ∀ never refines to a guarded skeleton *)
        exfalso.
        eapply ad_refine_syn_all_inh_guarded_absurd;
          [ exact HwfΘ | exact Hrefine | apply guarded_bskl__var ].
    + (* P0 = ghost : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
    + (* P0 = ∀◇P0s : LE-UnivGhost (ghost kept on both sides) *)
      destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
      assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
        by (apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      * (* refinement __univ_ghost_remove: the target is guarded, so the
           consistency drops its ghost too — LE-UnivGhost *)
        match goal with
          H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ Q }}ad |- _ =>
            rename H into Href1 end.
        assert (HgQ : guarded_bskl Q)
          by (eapply ad_refine_syn_guarded_r;
              [ exact HwfΘ | exact Href1 | exact HgL
              | lc_tgt ]).
        destruct (ad_pat_consis_univ_ghost_guarded_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HgQ HlcQ)
          as (Q0 & Hc0 & Href0 & HgQ0 & HlcQ0).
        assert (Href2 : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0s)) ⊳ Q0 }}ad)
          by (eapply ad_refine_syn_univ_ghost_guarded_inv;
                [ exact HwfΘ | exact Href0 | exact HgQ0 ]).
        edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                     (uskl_to_pskl R0) P0s Pi R0 α Θs Δρ Ψρ Rsub0
                     (Hmeas0 P0s ltac:(cbn; lia))
                     HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0s HwfPi Hκ Hκw Hψaw HαΘ HαΘ0 eq_refl
                     HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 ltac:(lc_tgt) HwfSub0 Href2
                     Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
          as (𝒞 & Ξc & Ξs & Pa & κc & κs
              & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
              & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
        exists 𝒞, Ξc, Ξs, Pa, κc, κs.
        repeat split; try assumption.
        apply a_lookeq__univ_ghost; exact HLK.
      * (* refinement __univ_ghost_fill: Q = ∀ˢ.Q0.  A ∀◇ subject can only meet a
           SYNTHESISED ∀ by dropping its ghost (C-UnivGhost2), and the residual
           subject is guarded (subject wf) — impossible against a ∀. *)
        exfalso.
        inversion Hconsis; subst.
        pose proof (guarded_uskl_head
                      (@guarded_uskl_of_uskl_to_pskl
                         (Rsub0) HgSub0))
          as Hghsub.
        match goal with
          H : {{ _ ⨟ _ ⊢ˢ Rsub0
                ∼ bskl_all_syn _ }}ad |- _ =>
            pose proof (ad_pat_consis_guarded_head_target H HwfΘ Hghsub) as Hgh
        end.
        destruct Hgh as [Habs | [[α0 Habs] | [Q1 [Q2 Habs]]]]; discriminate Habs.
      * (* refinement __univ_ghost_keep: Q = ∀◇Q0 with [inh κP0s ⊳ Q0].  The
           consistency keeps its ghost too (C-UnivGhost); the dropping
           alternative is refuted because the residual subject is guarded. *)
        match goal with
          H : {{ _ ⨟ _ ⊢ᵣ pskl_to_bskl_inh (msubst_pskl κ P0s) ⊳ ?Q0' }}ad |- _ =>
            rename H into Href1 end.
        inversion Hconsis; subst.
        -- (* C-UnivGhost : the ghost is kept on both sides *)
           match goal with
             H : {{ _ ⨟ _ ⊢ˢ Rsub0 ∼ _ }}ad |- _ =>
               rename H into Hc0 end.
           edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa _
                        (uskl_to_pskl R0) P0s Pi R0 α Θs Δρ Ψρ Rsub0
                        (Hmeas0 P0s ltac:(cbn; lia))
                        HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0s HwfPi Hκ Hκw Hψaw HαΘ HαΘ0 eq_refl
                        HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2
                        Hc0 ltac:(lc_tgt) HwfSub0 Href1
                        Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
             as (𝒞 & Ξc & Ξs & Pa & κc & κs
              & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
              & HwfPa & HwfΞ & HαΞ
                   & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
           exists 𝒞, Ξc, Ξs, Pa, κc, κs.
           repeat split; try assumption.
           apply a_lookeq__univ_ghost; exact HLK.
        -- (* C-UnivGhost2 : impossible against a ∀◇ target *)
           exfalso.
           pose proof (guarded_uskl_head
                         (@guarded_uskl_of_uskl_to_pskl
                            (Rsub0) HgSub0))
             as Hghsub.
           match goal with
             H : {{ _ ⨟ _ ⊢ˢ Rsub0
                   ∼ bskl_univ_ghost _ }}ad |- _ =>
               pose proof (ad_pat_consis_guarded_head_target H HwfΘ Hghsub) as Hgh
           end.
           destruct Hgh as [Habs | [[α0 Habs] | [Q1 [Q2 Habs]]]];
             discriminate Habs.
      * (* refinement __flex_r: the target is a defined flex VAR — guarded,
           so this is the ghost-dropping path again *)
        match goal with H : binds ?αf (abind_flex_mono_def ?τ) Θ |- _ =>
          rename H into Hbf end.
        assert (HgQ : guarded_bskl (bskl_var_f α0)) by apply guarded_bskl__var.
        destruct (ad_pat_consis_univ_ghost_guarded_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HgQ HlcQ)
          as (Q0 & Hc0 & Href0 & HgQ0 & HlcQ0).
        assert (Href2 : {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0s)) ⊳ Q0 }}ad)
          by (eapply ad_refine_syn_univ_ghost_guarded_inv;
                [ exact HwfΘ | exact Href0 | exact HgQ0 ]).
        edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                     (uskl_to_pskl R0) P0s Pi R0 α Θs Δρ Ψρ Rsub0
                     (Hmeas0 P0s ltac:(cbn; lia))
                     HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0s HwfPi Hκ Hκw Hψaw HαΘ HαΘ0 eq_refl
                     HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0 ltac:(lc_tgt) HwfSub0 Href2
                     Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
          as (𝒞 & Ξc & Ξs & Pa & κc & κs
              & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
              & HwfPa & HwfΞ & HαΞ
                & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
        exists 𝒞, Ξc, Ξs, Pa, κc, κs.
        repeat split; try assumption.
        apply a_lookeq__univ_ghost; exact HLK.
  - (* R' = dot_ghost : α ∈ ∅ absurd *) clear - HαR; fsetdec.
  - (* R' = dot_univ_ghost R0 : C-UnivGhostG → LE-UnivGhost.
       [⌊∀◈R0⌋ = ∀◇⌊R0⌋], the consistency target is [∀◇Q0] (up to the
       defined-flex chain), and only [P0 = ∀◇P0s] can refine to a [∀◇]. *)
    cbn [uskl_to_pskl] in HeraseR; subst P.
    pose proof (lc_uskl_dot_univ_ghost_inv HlcS) as HlcS0.
    (* ρ-INVERSION: a ∀◈ ideal forces a ∀◈ image at the SAME Ψρ *)
    cbn [msubst_uskl_syn subst_uskl_in_uskl] in Hrho.
    destruct (uskl_rsubst_dot_univ_ghost_r_inv Hrho) as (Rsub0 & HRs & Hrhobody).
    subst Rsub.
    cbn [uskl_to_pskl] in HwfSub.
    destruct (a_wf_pskl_univ_ghost_inv HwfSub) as [HgSub0 HwfSub0].
    destruct (ad_pat_consis_dot_univ_ghost_refine_unify HwfΘ Hconsis eq_refl
        (delta_def_fresh_empty Θ) Hrefine HlcQ)
      as (Q0 & Hc0 & Href0 & HlcQ0).
    clear Hconsis Hrefine.
    assert (Hsrc : (exists L0, pskl_to_bskl_inh (msubst_pskl κ P0) = bskl_univ_ghost L0)
                   \/ pskl_to_bskl_inh (msubst_pskl κ P0) = bskl_ghost)
      by (eapply ad_refine_syn_univ_ghost_rhs_src;
            [ exact HwfΘ | exact Href0 | reflexivity ]).
    destruct P0 as [ | n0 | β0 | P01 P02 | P0s | | P0s ].
    + (* unit *)
      exfalso; destruct Hsrc as [[L0 HL0] | HL0]; cbn in HL0; discriminate.
    + (* var_b : not well-formed *) inversion HwfP0.
    + (* var_f β0 : κβ0 is a ptyp painting — never a ∀◇ or □ *)
      exfalso; destruct Hsrc as [[L0 HL0] | HL0];
        cbn [msubst_pskl] in HL0; destruct (msubst_lookup κ β0);
        cbn in HL0; discriminate.
    + (* arrow *)
      exfalso; destruct Hsrc as [[L0 HL0] | HL0]; cbn in HL0; discriminate.
    + (* all_syn *)
      exfalso; destruct Hsrc as [[L0 HL0] | HL0]; cbn in HL0; discriminate.
    + (* ghost : excluded by HP0nh *) exfalso; apply HP0nh; reflexivity.
    + (* P0 = ∀◇P0s : the surviving shape — LE-UnivGhost *)
      clear Hsrc.
      destruct (a_wf_pskl_univ_ghost_inv HwfP0) as [HgP0s HwfP0s].
      cbn [msubst_pskl pskl_to_bskl_inh] in Href0.
      (* the source's ∀◇ must be KEPT: its body is guarded, so it cannot
         itself refine to the ∀◇ target *)
      assert (HgL : guarded_bskl (pskl_to_bskl_inh (msubst_pskl κ P0s)))
        by (apply guarded_pskl_to_bskl_inh;
            eapply guarded_pskl_msubst_inc; [ exact Hκ | exact HgP0s ]).
      pose proof (ad_refine_syn_univ_ghost_keep_inv HwfΘ HgL Href0) as Href1.
      assert (Hmeas : size_uskl R0 + size_pskl P0s <= n) by (cbn in Hn; lia).
      edestruct (IHn NM Θ0 Θ Θw κ Δ Ψ' Ψi Ψa Ψsub ψa Q0
                   (uskl_to_pskl R0) P0s Pi R0 α Θs Δρ Ψρ Rsub0
                   Hmeas HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfP0s HwfPi Hκ Hκw Hψaw HαΘ HαΘ0 eq_refl
                   HscopeS HlcS0 Htags Hdisj Hsub Hdfresh Hpre HΨs1 HΨs2 Hc0
                   ltac:(lc_tgt) HwfSub0 Href1
                   Hrhobody HΘs HΨρ Hrfr HΔρΔ HΔρw ltac:(eapply rsubst_ftv_apart_mono;
                          [ exact HΔρftv | cbn; clear; solve_notin_auto
                          | cbn; clear; solve_notin_auto ]) HΔρPi Hψaap L HL)
        as (𝒞 & Ξc & Ξs & Pa & κc & κs
              & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
              & HwfPa & HwfΞ & HαΞ
              & Hmapfst & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart).
      exists 𝒞, Ξc, Ξs, Pa, κc, κs.
      repeat split; try assumption.
      apply a_lookeq__univ_ghost; exact HLK.
Qed.

(* ===================================================================== *)
(*  P6-Cs — the PAPER'S statement, as the ρ = IDENTITY corollary.          *)
(*                                                                        *)
(*  [a_lookeq_solve_complete_gen] above generalizes the subject to a       *)
(*  ρ-IMAGE because P6-Ss's Sub-ForallL absorbs its guess into an          *)
(*  accumulated rigid substitution and a ForallL can sit above a Check.    *)
(*  At ρ = identity — [Θs := ·], [Δρ = Ψρ = ∅], subject = the ideal —      *)
(*  EVERY added premise is discharged here, so what the paper claims is    *)
(*  recovered with no residue:                                            *)
(*    · [uskl_rsubst] degenerates to [ursubst__refl] (the subject's local        *)
(*      closure comes from the subject-wf premise the paper already owes); *)
(*    · [Θs := ·] keeps the ftv-𝒞 bound at exactly the paper's;            *)
(*    · [rsubst_fresh] / [Δρ ⊆ Δ] / [Δρ ∩ dom Θ0] / the shielded-ftv          *)
(*      condition are all vacuous over an empty Δρ;                       *)
(*    · the guess's Δρ-apartness is vacuous over an empty Δρ.            *)
(*  Use THIS one unless you are threading a ρ down from a Sub-ForallL.     *)
(* ===================================================================== *)

Theorem a_lookeq_solve_complete :
  forall NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
  κ ∷ Θ0 ⊑ Θ ->
  (* α is the binder [a_sub__forall_l] opens (algo/def_rules.v) — COFINITELY, and
     only to run the lookup: it is never added to Θ0 or Θ, and the rule's own
     recursive call is already at [open P P1] with α replaced by the solved
     P1.  So it is FREE in R' and in NO context, which the scope premise below
     records as [add α …].  The paper writes only [α ∉ Θ]; the second
     conjunct is what actually does the work — with [dom κ ⊆ dom Θ0] it gives
     [α ∉ dom κ], i.e. κ leaves α alone, without which [(κR)[ψa/α]] would not
     mean anything.  (NB [α ∉ Θ] alone does NOT imply it: [a_inc__flex] SOLVES
     a source flexible, so [dom Θ0 ⊆ dom Θ] is false.)  Non-vacuity, with α
     genuinely occurring, is machine-checked in cex/cex_p6cs_subject_wf.v. *)
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  (* …R' may mention the contexts' variables PLUS α *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψ' ψa ->
  (ftag_in_uskl R') ∩ Ψ' [=] empty ->
  Ψi `union` Ψa [<=] Ψ' ->
  delta_def_fresh Δ Θ ->
  {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* ⭐ THE IDEAL GUESS IS Θ-SCOPED (2026-08-04, the SolE-FlexR repair).  [ψa]
     is an INPUT, and the repaired SolE-FlexR reads the solve block's payloads
     off it, so they are well-formed only if it is — the paper's prose "all
     inputs are well-formed" again.  It is NOT derivable from the premises
     below: when α does not occur in [κR] the subject does not mention ψa at
     all, so the subject-wf premise says nothing about it.
     [paper-external wf side condition — docs/WF-SIDE-CONDITIONS.md] *)
  ftvar_in_uskl ψa [<=] dom Θ ->
  (* subject = (κR)[ψa/α], EXACTLY the paper's form.  Note it is α-FREE — the
     guess has replaced every α-occurrence — which is why a Θ-scoped judgment
     is content never to have seen α. *)
  {{ Ψsub ⨟ Θ ⊢ˢ (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) ∼ Q }}ad ->
  (* the counterpart is well formed — the paper's presupposition of skeleton
     consistency (declarative.tex:2074); docs/WF-SIDE-CONDITIONS.md §2a *)
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  (* … and that subject is WELL-FORMED — the paper's prose side condition;
     without it the statement is FALSE (fresco/algo/cex/cex_p6cs_subject_wf.v).
     [paper-external wf side condition — docs/WF-SIDE-CONDITIONS.md] *)
  {{ Θ ⨟ empty ⊢ₚₛ (uskl_to_pskl (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R'))) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  (* ⭐ the avoid-set parameter of the repaired statement: the SOLVE generates
     its own block now, and P6-L needs to place that block's names.  [Θ0]'s own
     variables are all it is required to dodge. *)
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  exists 𝒞 Ξc Ξs Pa κc κs,
    ({{ Θ0 ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
    {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
    all_flex_mono Ξs /\
    uniq Ξs /\
    keys κs = keys Ξs /\
    (forall α0, α0 `in` dom Ξs -> α0 `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κs /\
    {{ (Ξs ++ Ξc ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξc ++ Θ0) }}a /\
    α `notin` dom Ξc /\
    keys κc = keys Ξc /\
    Forall (fun p => ftvar_in_ptyp (snd p) [<=] ftvar_in_uskl ψa) κc /\
    ftvar_in_a_cstrs 𝒞 [<=] ftvar_in_uskl ψa `union` dom Ξc `union` dom κ
                          `union` def_ftv Θ /\
    (κs ++ κc ++ κ) ∷ (Ξs ++ Ξc ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    (forall α0, α0 `in` dom κc ->
       α0 `notin` add α (dom Θ0 `union` dom Θ `union` ftvar_in_uskl ψa)) /\
    {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad.
Proof.
  intros NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α.
  intros HwfΘ HwfΘ0 HwfP0 HwfPi Hκ HαΘ HαΘ0 HeraseR HscopeS HlcS Htags Hdisj
         Hsub Hdfresh Hpre HΨs1 HΨs2 Hψaw Hconsis HwfQ HwfSub Hrefine L HL.
  (* the FUEL is an artefact of the strong induction, not part of the claim:
     instantiate it at the measure itself.  [Θw := Θ] collapses the whole Θw
     pack: the two binds conditions are the identity and the κ-image bound is
     [a_inc_lookup_flex_ftv_dom] on [Hκ]. *)
  edestruct (@a_lookeq_solve_complete_gen
               (size_uskl R' + size_pskl P0)
               NM Θ0 Θ Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R' α
               nil empty empty
               (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')))
    as (𝒞 & Ξc & Ξs & Pa & κc & κs
        & HLK & HSolve & Hfms & Hus & Hks & Hfrs & HFs
        & HwfPa & HwfΞ & HαΞ & Hmapfst
        & Himg & HftvC & Hinc & Hinceq & Hκfresh & Hprec & Hapart);
    [ exact (le_n _) | exact HwfΘ | exact HwfΘ0
    | exact HwfΘ | intros x b Hb; exact Hb | intros x b Hb; left; exact Hb
    | exact HwfP0 | exact HwfPi | exact Hκ
    | intros α0 Hf; eapply a_inc_lookup_flex_ftv_dom; [ exact Hκ | exact Hf ]
    | exact Hψaw
    | exact HαΘ | exact HαΘ0 | exact HeraseR | exact HscopeS
    | exact HlcS | exact Htags | exact Hdisj | exact Hsub | exact Hdfresh
    | exact Hpre | clear - HΨs1; fsetdec | exact HΨs2 | exact Hconsis
    | apply lc_bskl_of_bskl_to_pskl; exact (a_wf_pskl_lc HwfQ)
    | exact HwfSub | exact Hrefine
    | apply ursubst__refl;
        [ apply lc_uskl_of_pskl; eapply a_wf_pskl_lc; exact HwfSub
        | clear; fsetdec ]
    | intros x b Hb; inversion Hb
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | clear; fsetdec
    | clear; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | intros α0 Hα0; clear - Hα0; exfalso; fsetdec
    | clear; fsetdec
    | exact HL
    | ].
  exists 𝒞, Ξc, Ξs, Pa, κc, κs.
  (* the ftv-𝒞 conjunct no longer needs its [dom Θs] slack collapsed: the
     general statement names no context at all (docs §8 (h)) *)
  repeat split; assumption.
Qed.

