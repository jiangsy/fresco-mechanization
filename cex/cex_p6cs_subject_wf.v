(** COUNTEREXAMPLE — P6-Cs ("Completeness of consistency constraint
    collection and solving", consistency-proofs.tex:920) is FALSE without a
    well-formedness premise on the CONSISTENCY SUBJECT [(κR)[ψa/α]].

    This file does not argue in prose: it states the lemma with EXACTLY the
    premises of [a_lookeq_solve_complete] MINUS the subject-wf one (and with
    the conclusion WEAKENED to its three essential conjuncts, which only makes
    the refuted statement stronger), and derives False.

    The witness is
      Θ = Θ₀ = ·   κ = ·   R = ∀◇α   ψa = ∀◈⟨⟩   P₀ = Pi = ∀◇⟨⟩   Q = ∀◇⟨⟩
    so the subject is [∀◇(∀◈⟨⟩)] — a universal ghost whose body is another
    ghost, which [a_wf_pskl__tophole] / [d_wf_uskl__tophole] forbid (a ghost
    body must be GUARDED).  Every other premise holds; the algorithm is then
    forced into [𝒞 = [α ≐ ⟨⟩]] (LE-UnivGhost, then LE-Var) and [Pa = ⟨⟩]
    (SE-GhostGuarded, then SE-Unit), and the resulting precision obligation
    [⟨⟩ ⊑ᵖ ∀◈⟨⟩] has no rule.

    Conclusion: the subject-wf premise is not a convenience — it is what makes
    the paper's statement true.  Registered in docs/WF-SIDE-CONDITIONS.md. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo_decl.def_decl_algo.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_decl_algo_sub.
Require Import src.frost.algo.sub.look.prop_rho_relation.  (* [delta_def_fresh] *)
Require Import src.frost.algo.sub.look.prop_eq_cstr.  (* P6-Cs + [msubst_uskl_syn] *)

(* ===================================================================== *)
(*  The witness                                                           *)
(* ===================================================================== *)

Definition cex_ψa : uskl := uskl_topholeg uskl_unit.
Definition cex_S (α : atom) : uskl := uskl_tophole (uskl_var_f α).
Definition cex_P (α : atom) : pskl := pskl_tophole (pskl_var_f α).
Definition cex_P0 : pskl := pskl_tophole pskl_unit.
Definition cex_Q : bskl := bskl_tophole bskl_unit.

(* the subject [(κR)[ψa/α]] at κ = · is [∀◇(∀◈⟨⟩)] *)
Lemma cex_subject : forall α,
  subst_uskl_in_uskl cex_ψa α (msubst_uskl_syn nil (cex_S α))
  = uskl_tophole cex_ψa.
Proof.
  intros α. cbn [cex_S msubst_uskl_syn msubst_lookup subst_uskl_in_uskl].
  unfold ptyp_to_uskl_syn; cbn.
  destruct (eq_var α α); [ reflexivity | contradiction ].
Qed.

(* ===================================================================== *)
(*  (1)  the subject is NOT well-formed — a ghost over a ghost            *)
(* ===================================================================== *)

Lemma cex_subject_not_wf : forall α,
  ~ ({{ nil ⨟ empty ⊢ₚₛ
       (uskl_to_pskl (subst_uskl_in_uskl cex_ψa α (msubst_uskl_syn nil (cex_S α)))) }}a).
Proof.
  intros α Hwf. rewrite cex_subject in Hwf.
  cbn [uskl_to_pskl cex_ψa] in Hwf.
  inversion Hwf; subst.
  match goal with Hg : guarded_pskl _ |- _ => inversion Hg end.
Qed.

(* ===================================================================== *)
(*  (2)  the algorithm's answer is FORCED, and its precision goal fails   *)
(* ===================================================================== *)

(* the collected constraints can only be [α ≐ ⟨⟩] (LE-UnivGhost + LE-Var) *)
Lemma cex_lookeq_forced : forall α Ξc 𝒞,
  ({{ nil ⊢ cex_P α ∼[ α ] cex_P0 ⤳ Ξc ⨾ 𝒞 }}a) ->
  Ξc = nil /\ 𝒞 = a_cstr_eq pskl_unit :: nil.
Proof.
  intros α Ξc 𝒞 H.
  inversion H; subst;
    try solve [ simpl in *; exfalso; fsetdec
              | match goal with Hg : guarded_pskl _ |- _ => inversion Hg end ].
  - (* LE-UnivGhost : recurse on [α ∼[α] ⟨⟩] *)
    match goal with Hsub : {{ _ ⊢ _ ∼[ _ ] _ ⤳ _ ⨾ _ }}a |- _ =>
      inversion Hsub; subst;
        try solve [ simpl in *; exfalso; fsetdec
                  | match goal with Hg : guarded_pskl _ |- _ => inversion Hg end ]
    end.
    split; reflexivity.
Qed.

(* solving [α ≐ ⟨⟩] against [Pi = ∀◇⟨⟩] can only produce [⟨⟩] (SE-GhostGuarded) *)
(* ⚙️ The SOLVE now emits a block too, but not on this run: the eq row's
   subject here is a GHOST, and [nonghost_pskl] bars SolE-FlexR from a ghost
   subject, so SolE-GhostGuarded is the only rule and it generates nothing. *)
Lemma cex_solve_forced : forall Θ Ξ Pa,
  {{ Θ ⊩ (a_cstr_eq pskl_unit :: nil) ⨾ cex_P0 ⤳ Ξ ⨾ Pa }}a ->
  Pa = pskl_unit.
Proof.
  intros Θ Ξ Pa H.
  inversion H; subst.
  match goal with Heq : {{ _ ⊢ₑ _ ∼ _ ⤳ _ ⨾ ?Pmid }}a |- _ =>
    inversion Heq; subst;
      try solve [ match goal with Hg : guarded_pskl _ |- _ => inversion Hg end ]
  end.
  - (* SE-GhostGuarded : the body solve is [⟨⟩ ∼ ⟨⟩ ⤳ ⟨⟩] *)
    match goal with Heq2 : {{ _ ⊢ₑ pskl_unit ∼ pskl_unit ⤳ _ ⨾ _ }}a |- _ =>
      inversion Heq2; subst end;
      match goal with Hc : {{ _ ⊩ nil ⨾ _ ⤳ _ ⨾ _ }}a |- _ => inversion Hc; subst end;
      reflexivity.
Qed.

(* and [⟨⟩] is not precise to [∀◈⟨⟩] under ANY tag index *)
Lemma cex_precision_fails : forall Θ Δ Ψ,
  ~ ({{ Θ ⨟ Δ ⊢ˢ pskl_unit ⊑ᵖ[ Ψ ] cex_ψa }}ad).
Proof.
  intros Θ Δ Ψ H. unfold cex_ψa in H. inversion H.
Qed.

(* ===================================================================== *)
(*  (3)  P6-Cs WITHOUT the subject-wf premise is FALSE                     *)
(* ===================================================================== *)

Theorem p6cs_without_subject_wf_is_false :
  ~ (forall n NM Θ0 Θ κ Δ Ψ' Ψi Ψa Ψsub ψa Q P P0 Pi R α,
       size_uskl R + size_pskl P0 <= n ->
       {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
       {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a -> {{ Θ0 ⨟ empty ⊢ₚₛ Pi }}a ->
       κ ∷ Θ0 ⊑ Θ ->
       α `notin` dom Θ -> α `notin` dom Θ0 ->
       ⌊ R ⌋ˢ = P ->
       ftvar_in_uskl R [<=] add α (dom Θ0) ->
       lc_uskl R ->
       a_tags_sort NM Ψ' ψa ->
       (ftag_in_uskl R) ∩ Ψ' [=] empty ->
       Ψi `union` Ψa [<=] Ψ' ->
       delta_def_fresh Δ Θ ->
       {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa }}ad ->
       Ψsub [<=] ftag_in_uskl R `union` Ψa ->
       Ψa [<=] Ψsub ->
       {{ Ψsub ⨟ Θ ⊢ˢ (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R)) ∼ Q }}ad ->
       (* NB: the subject-wf premise
            [{{ Θ ⨟ empty ⊢ₚₛ ⌊ (κR)[ψa/α] ⌋ˢ }}a]
          is exactly what is MISSING here *)
       {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
       (* conclusion, weakened to its three essential conjuncts *)
       exists 𝒞 Ξc Ξs Pa (ρc : list (atom * ptyp)),
         ({{ Θ0 ⊢ P ∼[ α ] P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
         {{ (Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Ξs ⨾ Pa }}a /\
         {{ Θ ⨟ Δ ⊢ˢ (msubst_pskl (ρc ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa }}ad).
Proof.
  intros Hthm.
  pick fresh α.
  (* every premise of P6-Cs except the subject wf, at the witness *)
  destruct (Hthm 10 a_sub_mode_sk nil nil nil empty empty empty empty empty
              cex_ψa cex_Q (cex_P α) cex_P0 cex_P0 (cex_S α) α)
    as (𝒞 & Ξc & Ξs & Pa & ρc & HLK & HSolve & Hprec).
  - (* measure *) cbn; lia.
  - (* {{ ⊢ Θ }}a *) apply a_wf_aenv__nil.
  - (* {{ ⊢ Θ0 }}a *) apply a_wf_aenv__nil.
  - (* Θ0 ⊢ P0 *)
    apply a_wf_pskl__tophole;
      [ apply guarded_pskl__unit | apply a_wf_pskl__unit ].
  - (* Θ0 ⊢ Pi *)
    apply a_wf_pskl__tophole;
      [ apply guarded_pskl__unit | apply a_wf_pskl__unit ].
  - (* κ ∷ Θ0 ⊑ Θ *) apply a_inc__empty; apply a_suffix__nil.
  - (* α ∉ dom Θ *) simpl; clear; fsetdec.
  - (* α ∉ dom Θ0 *) simpl; clear; fsetdec.
  - (* ⌊R⌋ = P *) reflexivity.
  - (* scoping *) cbn; clear; fsetdec.
  - (* lc R *) apply lc_uskl_tophole; apply lc_uskl_var_f.
  - (* tags-sorted ψa *)
    apply a_tags_sort__sk;
      [ apply is_tskl__topholeg; apply is_tskl__unit
      | apply d_tags_skl__topholeg; apply d_tags_skl__unit; clear; fsetdec ].
  - (* ftag R ⊥ Ψ' *) cbn; clear; fsetdec.
  - (* Ψi, Ψa ⊆ Ψ' *) clear; fsetdec.
  - (* delta_def_fresh *) intros β α0 τ0 Hβ Hb; inversion Hb.
  - (* precision of the INPUT: ∀◇⟨⟩ ⊑ᵖ ∀◈⟨⟩ *)
    cbn [msubst_pskl cex_P0]. unfold cex_ψa.
    apply ad_ppre__tophole_keep. apply ad_ppre__unit; clear; fsetdec.
  - (* Ψsub ⊆ ftag R ∪ Ψa *) clear; fsetdec.
  - (* Ψa ⊆ Ψsub *) clear; fsetdec.
  - (* consistency: ∀◇(∀◈⟨⟩) ∼ ∀◇⟨⟩ — C-UnivGhost2 then C-UnivGhostG *)
    rewrite cex_subject. unfold cex_ψa, cex_Q.
    apply ad_pat_consis__tophole_drop.
    apply ad_pat_consis__topholeg.
    apply ad_pat_consis__unit; clear; fsetdec.
  - (* refinement: ∀◇⟨⟩ ⊳ ∀◇⟨⟩ — R-UnivGhostKeep *)
    cbn [msubst_pskl pskl_to_bskl_inh cex_P0]. unfold cex_Q.
    apply ad_refine_syn__tophole_keep;
      [ apply guarded_bskl__unit | apply ad_refine_syn__unit ].
  - (* … and now the conclusion is refuted *)
    destruct (@cex_lookeq_forced α Ξc 𝒞 HLK) as [-> ->].
    simpl in HSolve.
    apply (@cex_solve_forced nil Ξs Pa) in HSolve; subst Pa.
    cbn [msubst_pskl] in Hprec.
    exact (@cex_precision_fails nil empty (union empty empty) Hprec).
Qed.

(* For the record: the witness DOES violate the subject-wf premise (so the
   closed theorem is untouched by this counterexample). *)
Check cex_subject_not_wf.

(* ===================================================================== *)
(*  (4)  NON-VACUITY — the premise set of the CLOSED theorem is           *)
(*  satisfiable on the very same shape: replacing the ill-formed          *)
(*  [ψa = ∀◈⟨⟩] by [ψa = ⟨⟩] makes the subject [∀◇⟨⟩] well-formed, and    *)
(*  [a_lookeq_solve_complete] then FIRES and returns a real answer.       *)
(* ===================================================================== *)

Theorem p6cs_fires_when_the_subject_is_wf : forall α,
  exists 𝒞 Ξc Ξs Pa (ρc : list (atom * ptyp)),
    ({{ nil ⊢ cex_P α ∼[ α ] cex_P0 ⤳ Ξc ⨾ 𝒞 }}a) /\
    {{ (Ξc ++ nil) ⊩ 𝒞 ⨾ cex_P0 ⤳ Ξs ⨾ Pa }}a /\
    {{ nil ⨟ empty ⊢ˢ (msubst_pskl ρc Pa)
      ⊑ᵖ[ union empty empty ] uskl_unit }}ad.
Proof.
  intros α.
  edestruct (@a_lookeq_solve_complete a_sub_mode_sk nil nil nil empty empty
               empty empty empty uskl_unit (bskl_tophole bskl_unit)
               (cex_P α) cex_P0 cex_P0 (cex_S α) α
               (a_wf_aenv__nil) (a_wf_aenv__nil)
               ltac:(apply a_wf_pskl__tophole;
                       [ apply guarded_pskl__unit | apply a_wf_pskl__unit ])
               ltac:(apply a_wf_pskl__tophole;
                       [ apply guarded_pskl__unit | apply a_wf_pskl__unit ])
               ltac:(apply a_inc__empty; apply a_suffix__nil)
               ltac:(simpl; clear; fsetdec)
               ltac:(simpl; clear; fsetdec)
               (eq_refl : ⌊ cex_S α ⌋ˢ = cex_P α)
               ltac:(cbn; clear; fsetdec)
               ltac:(apply lc_uskl_tophole; apply lc_uskl_var_f)
               ltac:(apply a_tags_sort__sk;
                       [ apply is_tskl__unit
                       | apply d_tags_skl__unit; clear; fsetdec ])
               ltac:(cbn; clear; fsetdec)
               ltac:(clear; fsetdec)
               ltac:(intros β α0 τ0 Hβ Hb; inversion Hb)
               ltac:(cbn [msubst_pskl cex_P0];
                     apply ad_ppre__tophole_remove;
                     apply ad_ppre__unit; clear; fsetdec)
               ltac:(clear; fsetdec)
               ltac:(clear; fsetdec)
               (* ⭐ the repaired statement's guess-scope premise: [ψa = ⟨⟩] *)
               ltac:(cbn; clear; fsetdec)
               ltac:(cbn [cex_S msubst_uskl_syn msubst_lookup subst_uskl_in_uskl];
                     unfold ptyp_to_uskl_syn; cbn;
                     match goal with |- context [if ?c then _ else _] =>
                       destruct c end; [ | contradiction ];
                     apply ad_pat_consis__tophole;
                     apply ad_pat_consis__unit; clear; fsetdec)
               ltac:(cbn [cex_S msubst_uskl_syn msubst_lookup subst_uskl_in_uskl];
                     unfold ptyp_to_uskl_syn; cbn;
                     match goal with |- context [if ?c then _ else _] =>
                       destruct c end; [ | contradiction ];
                     cbn [uskl_to_pskl];
                     apply a_wf_pskl__tophole;
                       [ apply guarded_pskl__unit | apply a_wf_pskl__unit ])
               ltac:(cbn [msubst_pskl pskl_to_bskl_inh cex_P0];
                     apply ad_refine_syn__tophole_keep;
                       [ apply guarded_bskl__unit | apply ad_refine_syn__unit ])
               (* the avoid-set parameter of the repaired statement *)
               empty ltac:(cbn; clear; fsetdec))
    as (𝒞 & Ξc & Ξs & Pa & ρc & κs & HLK & HSolve & Hrest).
  exists 𝒞, Ξc, Ξs, Pa, (κs ++ ρc ++ nil).
  split; [ exact HLK | split; [ exact HSolve | ] ].
  (* the last conjunct of the package is the precision *)
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H as [_ H]
         end.
  exact Hrest.
Qed.

