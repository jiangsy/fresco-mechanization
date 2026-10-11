(** P6-L — COMPLETENESS OF LOOK  [a_extract_complete_gen]
    (paper [lemma:complete-look], subtyping-proofs.tex:2730).

    [a_extract] has ONE rule, so P6-L's shape is fixed:

      P ≼[α,m] P' ⤳ Ξ ⨾ 𝒞  →  (Ξ ++ Θ0) ⊩ 𝒞 ⨾ □ ⤳ Q  →  guess^N(Q) = (Ξ';Q')
        →  Θ0 ⊢ P ⊳[N,α,m] P' ⤳ (Ξ ++ Ξ') ↪ Q'

    Premises 1-2 are P6-Ss ([a_looksub_solve_complete]) instantiated at
    [Pi := pskl_ghost] and [Ψi := empty], so [Ψ' = Ψa]; then
    [ad_partial_precise_complete] (P5b-i) upgrades the ⊑ᵖ[Ψa] output to plain
    ⊑ against [⌊ψa⌋ˢ], exactly as the paper does at tex:2764.

    THE WORK IS THE THIRD PREMISE — the paper's one-line "by induction on the
    definition of guess^N(P_s)", which must produce a metasubstitution
    EXTENSION κ' over the guessed flexibles Ξ' with four conclusions at once
    (wf, [a_inc], [a_inc_equiv], precision).  Two observations shape it:

    - **We CHOOSE the guess.**  P6-L's conclusion is existential in Ξ and the
      extract's output, so the induction may build [a_guess_mono] and κ'
      SIMULTANEOUSLY rather than consuming a given guess.
    - **[guess_join_witness] (prop_completeness_consis.v (PART B):4624) does NOT serve
      here**, though DESIGN §7's table said so: it is CONSISTENCY-driven and
      demands a MONOTYPE counterpart, whereas guess^TY passes ∀ through
      ([a_guess_mono__forall] returns a [ptyp_all]) and P6-L's counterpart
      [⌊ψa⌋ˢ] is a general ghost-free skeleton.  See DESIGN §7.3.

    At [N = SK] the guess is the identity ([a_guess__sk]: Ξ' = ·, Q' = Q), so
    κ' = · and every conclusion is P6-Ss's verbatim.  This file builds the
    TY side. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.def_shapes.
Require Import src.fresco.coercions.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.prop_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.
Require Import src.fresco.deco_algo.def_decorated.
Require Import src.fresco.algo.basic.prop_inc.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_swap.          (* a_wf_pskl_ftv_binds *)
Require Import src.fresco.algo_decl.prop_refinement.
Require Import src.fresco.algo_decl.prop_ctx_mono.
Require Import src.fresco.algo.consistency.prop_soundness_consis.
Require Import src.fresco.algo.consistency.prop_completeness_consis.
Require Import src.fresco.algo.consistency.prop_consis_monotype_equiv.
Require Import src.fresco.algo_decl.prop_precision.
Require Import src.fresco.algo_decl.prop_subtyping.
Require Import src.fresco.algo.subtyping.prop_looksub.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.algo.basic.prop_inc_strengthen.
Require Import src.fresco.algo.basic.prop_metasubst_composition.
Require Import src.fresco.algo.basic.prop_metasubst.
Require Import src.fresco.algo.basic.prop_context_normalization.
Require Import src.fresco.algo.subtyping.prop_completeness_sub_precise.
Require Import src.fresco.algo.subtyping.prop_rigid_substitution.
Require Import src.fresco.algo.subtyping.prop_solve_extension.
Require Import src.fresco.algo.subtyping.prop_completeness_solve_eq_var.
Require Import src.fresco.algo.subtyping.prop_completeness_lookeq_solve.
Require Import src.fresco.algo.subtyping.prop_completeness_looksub_solve.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  WHERE A HOLE FACES THE COUNTERPART, THE COUNTERPART IS A MONOTYPE  *)
(*                                                                        *)
(*  guess^TY replaces each ◇ of the solve output by a FRESH flexible, and  *)
(*  the θ-extension must send that flexible to the counterpart's skeleton  *)
(*  AT THAT POSITION — so the position had better hold a monotype, since   *)
(*  a metasubstitution's images are monotypes.  It does, and the reason is *)
(*  purely the PAINTING: [ad_refine_syn__ghost] demands a SYNTHESISED       *)
(*  target, precision hands it an INHERITED one, and the two paintings     *)
(*  agree exactly on ∀-free skeletons ([pskl_all_syn] is the ONE           *)
(*  constructor where they differ — [bskl_all_inh] vs [bskl_all_syn]).     *)
(*                                                                        *)
(*  This is the mechanical content of the paper's side remark at tex:2812 — *)
(*  for each quantifier in the erased ψa, premise (f) ensures it does not   *)
(*  correspond to a universal ghost in P_s.                                *)
(* ===================================================================== *)

(** ∀-freeness, the exact condition under which the two paintings agree. *)
Inductive pskl_all_free : pskl -> Prop :=
| paf_unit   : pskl_all_free pskl_unit
| paf_var_b  : forall n, pskl_all_free (pskl_var_b n)
| paf_var_f  : forall α, pskl_all_free (pskl_var_f α)
| paf_arrow  : forall P1 P2,
    pskl_all_free P1 -> pskl_all_free P2 -> pskl_all_free (pskl_arrow P1 P2)
| paf_ghost   : pskl_all_free pskl_ghost
| paf_univ_ghost : forall P, pskl_all_free P -> pskl_all_free (pskl_univ_ghost P).

#[export] Hint Constructors pskl_all_free : fresco.

(** The two paintings agree EXACTLY on the ∀-free skeletons, and where they
    agree they agree on the same skeleton. *)
Lemma pskl_inh_eq_syn_inv : forall P Q,
  pskl_to_bskl_inh P = pskl_to_bskl_syn Q ->
  P = Q /\ pskl_all_free P.
Proof.
  induction P; intros Q Heq; destruct Q; cbn in Heq; try discriminate Heq.
  - split; [ reflexivity | apply paf_unit ].
  - injection Heq as ->. split; [ reflexivity | apply paf_var_b ].
  - injection Heq as ->. split; [ reflexivity | apply paf_var_f ].
  - injection Heq as Heq1 Heq2.
    destruct (IHP1 _ Heq1) as [-> Hf1]. destruct (IHP2 _ Heq2) as [-> Hf2].
    split; [ reflexivity | apply paf_arrow; assumption ].
  (* NB no ∀ bullet: [bskl_all_inh] vs [bskl_all_syn] IS discriminable, so
     [try discriminate Heq] above already closed that diagonal case — that
     disagreement is exactly what this lemma is about *)
  - split; [ reflexivity | apply paf_ghost ].
  - injection Heq as Heq0. destruct (IHP _ Heq0) as [-> Hf].
    split; [ reflexivity | apply paf_univ_ghost; assumption ].
Qed.

(** …and a ∀-free, GHOST-free skeleton IS a monotype painting.  Ghost-freeness
    is [pskl_ghost_free] (the FIXPOINT of prop_subtyping.v — [◇]/[∀◇] map to
    [False]); what [a_tags_sort] at TY supplies for ψa is its uskl twin
    [uskl_ghost_free], and §5's [uskl_ghost_free_to_pskl] bridges them, so
    [⌊ψa⌋ˢ] has no ◇ / ∀◇ to obstruct this. *)
Lemma pskl_all_ghost_free_mono : forall P,
  pskl_all_free P -> pskl_ghost_free P -> lc_pskl P ->
  exists τ, ptyp_to_pskl τ = P /\ mono_ptyp τ.
Proof.
  intros P Ha; induction Ha; intros Hg Hlc; cbn in Hg;
    try solve [ contradiction ].
  - exists ptyp_unit; split; [ reflexivity | apply mono_ptyp__unit ].
  - (* a BOUND variable is ruled out by local closure, not by ghost-freeness *)
    inversion Hlc.
  - exists (ptyp_var_f α); split; [ reflexivity | apply mono_ptyp__var ].
  - destruct Hg as [Hg1 Hg2]. inversion Hlc; subst.
    destruct (IHHa1 Hg1 ltac:(assumption)) as [τ1 [Heq1 Hm1]].
    destruct (IHHa2 Hg2 ltac:(assumption)) as [τ2 [Heq2 Hm2]].
    exists (ptyp_arrow τ1 τ2); cbn; rewrite Heq1, Heq2.
    split; [ reflexivity | apply mono_ptyp__arrow; assumption ].
Qed.

(* ===================================================================== *)
(*  §3  THE HOLE CASE, WHICH IS WHAT MAKES THE θ-EXTENSION WELL-DEFINED   *)
(*                                                                        *)
(*  guess^TY sends a ◇ to a fresh flexible α̂, so κ' must send α̂ to the     *)
(*  counterpart's skeleton at that position — and a metasubstitution's     *)
(*  images are Θ-scoped MONOTYPES.  Both are delivered by inverting        *)
(*  precision at a ghost, and there are only two ways to derive it:         *)
(*                                                                        *)
(*   · [ad_refine_syn__ghost] — its target is a SYNTHESISED painting while  *)
(*     precision supplies an INHERITED one, so §1 forces ∀-freeness, and   *)
(*     ghost-freeness (from [a_tags_sort] at TY) then forces a monotype.   *)
(*     Its fill premise is [Δ ∩ ftv P = ∅], so a ghost under a ∀ can never  *)
(*     be filled with the bound variable; with the counterpart's own      *)
(*     scoping (every free name outside Δ is bound in Θ) the images stay  *)
(*     Θ-well-formed.                                                     *)
(*   · [ad_refine_syn__flex_r] — the target IS a defined flexible, so the  *)
(*     monotype is that variable itself.                                  *)
(* ===================================================================== *)

(** Inverting the refinement with the source pinned to ◇ and the TARGET still
    a variable — [inversion] then produces clean equations we control.  Only
    two rules have a ◇ source: [__ghost] and [__flex_r]. *)
Lemma ad_refine_syn_ghost_l_inv : forall Θ Δ Y,
  {{ Θ ⨟ Δ ⊢ᵣ bskl_ghost ⊳ Y }}ad ->
  (exists P, Δ ∩ ftvar_in_pskl P [=] empty /\ Y = pskl_to_bskl_syn P)
  \/ (exists α τ, binds α (abind_flex_mono_def τ) Θ /\ Y = bskl_var_f α).
Proof.
  intros Θ Δ Y H; inversion H; subst;
    [ left; eexists; split; [ eassumption | reflexivity ]
    | right; do 2 eexists; split; [ eassumption | reflexivity ] ].
Qed.

Lemma ad_precise_ghost_inv_mono : forall Θ Δ X,
  {{ Θ ⨟ Δ ⊢ₚᵣ pskl_ghost ⊑ X }}ad ->
  pskl_ghost_free X -> lc_pskl X ->
  (forall γ, γ `in` ftvar_in_pskl X -> γ `notin` Δ -> a_binds_tvar γ Θ) ->
  exists τ, ptyp_to_pskl τ = X /\ mono_ptyp τ /\ {{ Θ ⨟ empty ⊢ₚₛ X }}a.
Proof.
  intros Θ Δ X Hp Hgf Hlc HscX. unfold ad_precise in Hp. cbn in Hp.
  destruct (ad_refine_syn_ghost_l_inv Hp) as [[P [HΔP Heq]] | [α [τ0 [Hb Heq]]]].
  - (* __ghost : the SYN/INH painting clash pins X ∀-free, hence a monotype;
       the fill misses Δ, so the counterpart's scoping binds all of it *)
    destruct (@pskl_inh_eq_syn_inv _ _ Heq) as [-> Haf].
    destruct (@pskl_all_ghost_free_mono _ Haf Hgf Hlc) as [τ [Heqτ Hmτ]].
    exists τ; repeat split; [ exact Heqτ | exact Hmτ | ].
    subst. apply a_wf_pskl_of_ptyp_vis;
      [ apply mono_ptyp_lc; exact Hmτ | ].
    rewrite ftvar_ptyp_to_pskl in HΔP.
    intros γ Hγ. apply HscX;
      [ rewrite ftvar_ptyp_to_pskl; exact Hγ | clear - Hγ HΔP; fsetdec ].
  - (* __flex_r : the target is a defined flexible — the monotype is IT *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in Heq;
      try discriminate Heq.
    (* X = α0, and the equation pins α0 = α *)
    assert (Hαe : α0 = α) by congruence; subst α0.
    exists (ptyp_var_f α); split; [ reflexivity | split ];
      [ apply mono_ptyp__var
      | (* the third [a_binds_tvar] disjunct *)
        apply a_wf_pskl__var; right; right; exists τ0; exact Hb ].
Qed.

(* ===================================================================== *)
(*  §4  A ∀-HEADED SOURCE NEVER REFINES TO A MONOTYPE                     *)
(*                                                                        *)
(*  The ∀ case of the witness induction must refute the [__flex_r] reading *)
(*  of its precision premise: if the counterpart were a defined flexible   *)
(*  α̂, precision would demand [∀… ⊳ syn τ] for α̂'s MONOTYPE definition τ,  *)
(*  and no rule can do that — [__all] needs an inherited-∀ target, which a *)
(*  monotype painting never is, and [__flex_r] only chains to another      *)
(*  monotype definition.  The chain terminates because every definition in *)
(*  a well-formed context is a monotype.                                  *)
(* ===================================================================== *)

Lemma ad_refine_syn_all_l_not_mono : forall Θ Δ Y τ,
  {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh Y) ⊳ (ptyp_to_bskl_syn τ) }}ad ->
  {{ ⊢ Θ }}a -> mono_ptyp τ -> False.
Proof.
  intros Θ Δ Y τ H. remember (bskl_all_inh Y) as Src eqn:HeqS.
  remember (ptyp_to_bskl_syn τ) as Tgt eqn:HeqT.
  revert Y τ HeqS HeqT.
  induction H; intros Y0 τ0 HeqS HeqT HwfΘ Hmτ; subst;
    try discriminate HeqS.
  - (* __all : NO monotype painting is an inherited ∀ — and note [ptyp_all]
       is discriminated too, since its painting is [bskl_all_SYN].  So every
       shape of τ0 dies on [HeqT] and there is nothing left to do. *)
    destruct τ0; cbn in HeqT; discriminate HeqT.
  - (* __flex_r : only a VARIABLE painting survives [HeqT]; chain to its
       definition, which a well-formed context keeps a monotype *)
    destruct τ0; cbn in HeqT; try discriminate HeqT.
    assert (Hαe : α = α0) by congruence; subst α0.
    eapply IHad_refine_syn;
      [ reflexivity | reflexivity | exact HwfΘ
      | eapply a_wf_aenv_binds_def_mono; eassumption ].
Qed.

(* ===================================================================== *)
(*  §5  BRIDGES AND TRANSPORTS THE WITNESS INDUCTION CONSUMES             *)
(*                                                                        *)
(*  Four small facts, each of which the paper uses silently:               *)
(*                                                                        *)
(*   · ghost-freeness is invariant under opening (both ways), so the ∀     *)
(*     case may descend into [⌊ψa⌋ˢ]'s body and come back out;             *)
(*   · [a_tags_sort] at TY hands ghost-freeness on the DECORATED ψa, and   *)
(*     the witness needs it on the ERASURE [⌊ψa⌋ˢ];                        *)
(*   · a metasubstitution's image must be [a_wf_ptyp], while §3 delivers   *)
(*     [a_wf_pskl] of its painting — the two agree on monotypes;           *)
(*   · a Δ-BOUND variable of a precision derivation can be renamed.  This  *)
(*     is the "removing β as necessary" move: the ∀ case runs the IH at    *)
(*     ONE fresh β and must hand [ad_refine_syn__all] a COFINITE family.   *)
(* ===================================================================== *)

(** [a_tags_sort a_sub_mode_ty] gives ghost-freeness of the DECORATED ψa;
    the witness induction runs against the erasure.  The ε-tagged ∀ erases
    to a plain [pskl_all_syn], which is exactly [pgf_all]. *)

(** The converse of [a_wf_ptyp_to_wf_pskl] on a MONOTYPE: a monotype has no
    binder, so its painting's well-formedness is its own — and the Δ slot is
    irrelevant because §3 always delivers the CLOSED reading. *)
Lemma a_wf_ptyp_of_wf_pskl_mono : forall Θ τ,
  mono_ptyp τ ->
  {{ Θ ⨟ empty ⊢ₚₛ (ptyp_to_pskl τ) }}a ->
  a_wf_ptyp Θ τ.
Proof.
  intros Θ τ Hm; induction Hm; intros Hwf; cbn in Hwf.
  - apply a_wf_ptyp__unit.
  - inversion Hwf; subst.
    apply a_wf_ptyp__var.
    assumption.
  - inversion Hwf; subst. apply a_wf_ptyp__arrow; auto.
Qed.

(** Every definition of a well-formed context is scoped by its domain, so a
    name outside the domain is fresh for all of them — the side condition
    [ad_refine_syn_rename] asks for, discharged by freshness alone. *)
Lemma a_wf_aenv_def_ftv_fresh : forall Θ β,
  {{ ⊢ Θ }}a -> β `notin` dom Θ ->
  forall α τ, binds α (abind_flex_mono_def τ) Θ -> β `notin` ftvar_in_ptyp τ.
Proof.
  intros Θ β Hwf Hβ α τ Hb.
  assert (Hwfτ : a_wf_ptyp Θ τ)
    by (eapply a_wf_aenv_binds_def_wf; eassumption).
  assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ)
    by (eapply a_wf_ptyp_ftv_dom; exact Hwfτ).
  clear - Hβ Hsc; fsetdec.
Qed.

(** Renaming a Δ-BOUND variable of a refinement derivation, via
    [ad_refine_syn_rename]: the renamed name is in Δ, so every ghost fill
    misses it.  The new name [α0] must avoid the target (a fill could
    mention it) and the context's definitions. *)
(* ⚙ RENAMED from [ad_refine_syn_rename_delta] 2026-08-09 (cleanup audit §8.1c): it collided with a
   DIFFERENT lemma of that name, and this one delivers Δ as [add α0 (remove β Δ)]; prop_soundness_pat.v's takes [Δ0 [=] add α Δ]. *)
Lemma ad_refine_syn_rename_delta_remove : forall Θ Δ Q Q' β α0,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
  {{ ⊢ Θ }}a ->
  β `notin` dom Θ -> β `in` Δ ->
  α0 `notin` dom Θ -> α0 `notin` ftvar_in_bskl Q' ->
  {{ Θ ⨟ (add α0 (remove β Δ)) ⊢ᵣ
    (subst_bskl_in_bskl (bskl_var_f α0) β Q) ⊳
    (subst_bskl_in_bskl (bskl_var_f α0) β Q') }}ad.
Proof.
  intros Θ Δ Q Q' β α0 H HwfΘ Hβ HβΔ Hα0 Hα0Q.
  eapply ad_refine_syn_delta_mono;
    [ apply ad_refine_syn_rename;
        [ exact H | exact HβΔ | exact Hβ
        | eapply a_wf_aenv_def_ftv_fresh; eassumption
        | exact Hα0Q
        | eapply a_wf_aenv_def_ftv_fresh; eassumption ]
    | clear; fsetdec ].
Qed.

(** …and its precision reading, which is what the ∀ case applies. *)
Lemma ad_precise_rename_delta : forall Θ Δ P X β α0,
  {{ Θ ⨟ Δ ⊢ₚᵣ P ⊑ X }}ad ->
  {{ ⊢ Θ }}a ->
  β `notin` dom Θ -> β `in` Δ ->
  α0 `notin` dom Θ -> α0 `notin` ftvar_in_pskl X ->
  {{ Θ ⨟ (add α0 (remove β Δ)) ⊢ₚᵣ
    (subst_pskl_in_pskl (pskl_var_f α0) β P) ⊑
    (subst_pskl_in_pskl (pskl_var_f α0) β X) }}ad.
Proof.
  intros Θ Δ P X β α0 H HwfΘ Hβ HβΔ Hα0 Hα0X. unfold ad_precise in *.
  rewrite <- ! subst_var_bskl_inh.
  apply ad_refine_syn_rename_delta_remove; try assumption.
  rewrite ftvar_in_bskl_inh; exact Hα0X.
Qed.

(* ===================================================================== *)
(*  §6  INVERTING PRECISION AT A COMPOSITE SOURCE — WITH A REPLAY          *)
(*                                                                        *)
(*  The witness induction descends the SOURCE [P_s], so at an arrow / ∀◇ / *)
(*  ∀ it must read the counterpart's matching piece off the precision      *)
(*  premise.  Three rules can conclude precision at a non-atomic source,   *)
(*  and only ONE of them is the structural one: [__flex_r] fires whenever  *)
(*  the counterpart is a DEFINED FLEXIBLE, replacing the target by that    *)
(*  definition's monotype painting and leaving the source untouched.       *)
(*                                                                        *)
(*  ⚠️ At the ∀ that chain REFUTES (§4).  At the ARROW and the ∀◇ IT DOES  *)
(*  NOT: κs can turn a flexible into an arrow, so the source's shape does  *)
(*  not clash with a monotype painting, and the chain must be CHASED.  So  *)
(*  those two lemmas each return, besides the counterpart's pieces, a      *)
(*  REPLAY function rebuilding precision against the ORIGINAL X — the      *)
(*  chased [__flex_r] steps re-applied.  (This is one-step re-application, *)
(*  not transitivity of refinement, which is proved only under the wf      *)
(*  presupposition — [ad_refine_syn_trans].)  The chase terminates on the  *)
(*  DERIVATION, which is why these are inductions on it, not on a size.    *)
(* ===================================================================== *)

Lemma ad_precise_arrow_l_inv : forall Θ Δ Src Tgt,
  {{ Θ ⨟ Δ ⊢ᵣ Src ⊳ Tgt }}ad ->
  forall S1 S2 X,
  Src = bskl_arrow (pskl_to_bskl_inh S1) (pskl_to_bskl_inh S2) ->
  Tgt = pskl_to_bskl_inh X ->
  {{ ⊢ Θ }}a -> pskl_ghost_free X -> lc_pskl X ->
  (forall γ, γ `in` ftvar_in_pskl X -> γ `notin` Δ -> a_binds_tvar γ Θ) ->
  exists X1 X2,
    pskl_ghost_free X1 /\ pskl_ghost_free X2 /\ lc_pskl X1 /\ lc_pskl X2 /\
    (forall γ, γ `in` ftvar_in_pskl X1 -> γ `notin` Δ -> a_binds_tvar γ Θ) /\
    (forall γ, γ `in` ftvar_in_pskl X2 -> γ `notin` Δ -> a_binds_tvar γ Θ) /\
    {{ Θ ⨟ Δ ⊢ₚᵣ S1 ⊑ X1 }}ad /\ {{ Θ ⨟ Δ ⊢ₚᵣ S2 ⊑ X2 }}ad /\
    (forall Y1 Y2,
       {{ Θ ⨟ Δ ⊢ₚᵣ Y1 ⊑ X1 }}ad -> {{ Θ ⨟ Δ ⊢ₚᵣ Y2 ⊑ X2 }}ad ->
       {{ Θ ⨟ Δ ⊢ₚᵣ (pskl_arrow Y1 Y2) ⊑ X }}ad).
Proof.
  intros Θ Δ Src Tgt H; induction H;
    intros S1 S2 X HeqS HeqT HwfΘ Hgf Hlc HscX;
    try discriminate HeqS.
  - (* __arrow : the structural case *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    inversion HeqS; inversion HeqT; subst.
    cbn in Hgf; destruct Hgf as [Hgf1 Hgf2]. inversion Hlc; subst.
    exists X1, X2. unfold ad_precise.
    split; [ assumption | ]. split; [ assumption | ].
    split; [ assumption | ]. split; [ assumption | ].
    split; [ intros γ Hγ; apply HscX; cbn; clear - Hγ; fsetdec | ].
    split; [ intros γ Hγ; apply HscX; cbn; clear - Hγ; fsetdec | ].
    split; [ assumption | ]. split; [ assumption | ].
    intros Y1 Y2 HY1 HY2. cbn.
    apply ad_refine_syn_arrow_intro; assumption.
  - (* __flex_r : chase the definition, then re-apply the rule *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    assert (Hαe : α0 = α) by congruence; subst α0.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eassumption).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eassumption).
    assert (Hpaint : ptyp_to_bskl_syn τ = pskl_to_bskl_inh (ptyp_to_pskl τ))
      by (symmetry; apply ptyp_to_bskl_inh_syn_eq; exact Hmτ).
    destruct (IHad_refine_syn S1 S2 (ptyp_to_pskl τ) HeqS Hpaint HwfΘ
                ltac:(apply ptyp_to_pskl_ghost_free)
                ltac:(apply ptyp_to_pskl_lc; eapply a_wf_ptyp_lc; exact Hwfτ)
                ltac:(intros γ Hγ _; eapply a_wf_pskl_ftv_binds;
                      [ apply a_wf_ptyp_to_wf_pskl with (Δ := empty);
                        exact Hwfτ
                      | exact Hγ ]))
      as (X1 & X2 & Hg1 & Hg2 & Hl1 & Hl2 & Hs1 & Hs2 & Hp1 & Hp2 & Hreplay).
    exists X1, X2.
    split; [ exact Hg1 | ]. split; [ exact Hg2 | ].
    split; [ exact Hl1 | ]. split; [ exact Hl2 | ].
    split; [ exact Hs1 | ]. split; [ exact Hs2 | ].
    split; [ exact Hp1 | ]. split; [ exact Hp2 | ].
    intros Y1 Y2 HY1 HY2. unfold ad_precise; cbn.
    apply ad_refine_syn__flex_r with (τ := τ); [ assumption | ].
    rewrite Hpaint. exact (Hreplay Y1 Y2 HY1 HY2).
Qed.

Lemma ad_precise_univ_ghost_l_inv : forall Θ Δ Src Tgt,
  {{ Θ ⨟ Δ ⊢ᵣ Src ⊳ Tgt }}ad ->
  forall S0 X,
  Src = bskl_univ_ghost (pskl_to_bskl_inh S0) ->
  Tgt = pskl_to_bskl_inh X ->
  {{ ⊢ Θ }}a -> pskl_ghost_free X -> lc_pskl X ->
  (forall γ, γ `in` ftvar_in_pskl X -> γ `notin` Δ -> a_binds_tvar γ Θ) ->
  exists X',
    pskl_ghost_free X' /\ lc_pskl X' /\
    (forall γ, γ `in` ftvar_in_pskl X' -> γ `notin` Δ -> a_binds_tvar γ Θ) /\
    {{ Θ ⨟ Δ ⊢ₚᵣ S0 ⊑ X' }}ad /\
    (forall Y, {{ Θ ⨟ Δ ⊢ₚᵣ Y ⊑ X' }}ad -> {{ Θ ⨟ Δ ⊢ₚᵣ Y ⊑ X }}ad).
Proof.
  intros Θ Δ Src Tgt H; induction H;
    intros S0 X HeqS HeqT HwfΘ Hgf Hlc HscX;
    try discriminate HeqS.
  - (* __univ_ghost_remove : the ghost is dropped, X is unchanged *)
    inversion HeqS; subst.
    exists X.
    split; [ exact Hgf | ]. split; [ exact Hlc | ]. split; [ exact HscX | ].
    (* [subst] has already rewritten the rule's target to [inh X] and, in
       doing so, consumed HeqT — hence the guarded rewrite *)
    split; [ unfold ad_precise; try rewrite <- HeqT; assumption | ].
    intros Y HY; exact HY.
  - (* __univ_ghost_fill : the target is a SYNTHESISED ∀, which no inherited
       painting is — [pskl_all_syn] paints to [bskl_all_INH] *)
    exfalso.
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      discriminate HeqT.
  - (* __univ_ghost_keep : the target keeps the ghost, so X would carry a ∀◇ —
       excluded by ghost-freeness *)
    exfalso.
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    cbn in Hgf; contradiction.
  - (* __flex_r : chase *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    assert (Hαe : α0 = α) by congruence; subst α0.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eassumption).
    assert (Hwfτ : a_wf_ptyp Θ τ)
      by (eapply a_wf_aenv_binds_def_wf; eassumption).
    assert (Hpaint : ptyp_to_bskl_syn τ = pskl_to_bskl_inh (ptyp_to_pskl τ))
      by (symmetry; apply ptyp_to_bskl_inh_syn_eq; exact Hmτ).
    destruct (IHad_refine_syn S0 (ptyp_to_pskl τ) HeqS Hpaint HwfΘ
                ltac:(apply ptyp_to_pskl_ghost_free)
                ltac:(apply ptyp_to_pskl_lc; eapply a_wf_ptyp_lc; exact Hwfτ)
                ltac:(intros γ Hγ _; eapply a_wf_pskl_ftv_binds;
                      [ apply a_wf_ptyp_to_wf_pskl with (Δ := empty);
                        exact Hwfτ
                      | exact Hγ ]))
      as (X' & Hg' & Hl' & Hs' & Hp' & Hreplay).
    exists X'.
    split; [ exact Hg' | ]. split; [ exact Hl' | ]. split; [ exact Hs' | ].
    split; [ exact Hp' | ].
    intros Y HY. unfold ad_precise; cbn.
    apply ad_refine_syn__flex_r with (τ := τ); [ assumption | ].
    rewrite Hpaint. exact (Hreplay Y HY).
Qed.

(** At a ∀ source there is NO chase: §4 refutes the [__flex_r] reading, so the
    counterpart is a ∀ too and the inversion is exact — no replay needed, the
    caller rebuilds with [ad_refine_syn__all]. *)
Lemma ad_precise_all_l_inv : forall Θ Δ Src Tgt,
  {{ Θ ⨟ Δ ⊢ᵣ Src ⊳ Tgt }}ad ->
  forall S0 X,
  Src = bskl_all_inh (pskl_to_bskl_inh S0) ->
  Tgt = pskl_to_bskl_inh X ->
  {{ ⊢ Θ }}a -> pskl_ghost_free X -> lc_pskl X ->
  exists X0 L,
    X = pskl_all_syn X0 /\
    (forall β, β `notin` L ->
       {{ Θ ⨟ (add β Δ) ⊢ₚᵣ (open_pskl_wrt_pskl S0 (pskl_var_f β))
                       ⊑ (open_pskl_wrt_pskl X0 (pskl_var_f β)) }}ad).
Proof.
  intros Θ Δ Src Tgt H; induction H;
    intros S0 X HeqS HeqT HwfΘ Hgf Hlc;
    try discriminate HeqS.
  - (* __all *)
    destruct X as [ | n0 | α0 | X1 X2 | X0 | | X0 ]; cbn in HeqT;
      try discriminate HeqT.
    inversion HeqS; inversion HeqT; subst.
    exists X0, L. split; [ reflexivity | ].
    intros β Hβ. unfold ad_precise.
    rewrite ! pskl_to_bskl_inh_open.
    (* the rule pushes β as a rigid tvar, which no flexible lookup sees *)
    eapply ad_refine_syn_defs_mono; [ apply H0; exact Hβ | ].
    intros γ τ Hb. apply binds_app_iff in Hb as [Hb | Hb];
      [ apply binds_one_iff in Hb; destruct Hb as [_ Hc]; discriminate Hc
      | exact Hb ].
  - (* __flex_r : REFUTED — a ∀-headed source never refines to a monotype *)
    exfalso.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eassumption).
    subst.
    eapply ad_refine_syn_all_l_not_mono; eassumption.
Qed.

(* ===================================================================== *)
(*  §7  FOUR SMALL TOOLS THE WITNESS INDUCTION ASSEMBLES WITH             *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  §8  THE TWO PROPERTIES OF THE INCOMING κ THE INDUCTION NEEDS           *)
(*                                                                        *)
(*  The ∀ case opens at a fresh β and must (a) push κ through the opener   *)
(*  and (b) know β does not appear in the κ-IMAGE of the body — otherwise  *)
(*  the renaming that builds the cofinite family would move it.  Both are  *)
(*  properties of the incoming κ, and an [a_inc] supplies both: images are *)
(*  locally closed ([a_inc_msubst_lc]) and SCOPED BY THE TARGET.           *)
(* ===================================================================== *)

(** A metasubstitution's images are scoped by the target context (an
    unbound variable maps to itself, hence the [add α]). *)
Lemma a_inc_lookup_ftv : forall Θ0 κ Θ α,
  κ ∷ Θ0 ⊑ Θ ->
  ftvar_in_ptyp (msubst_lookup κ α) [<=] add α (dom Θ).
Proof.
  intros Θ0 κ Θ α H; revert α; induction H; intros α0; cbn.
  - clear; fsetdec.
  - destruct (α0 == α) as [-> | Hne].
    + assert (Hsc : ftvar_in_ptyp τ [<=] dom Θ')
        by (eapply a_wf_ptyp_ftv_dom; eassumption).
      clear - Hsc; fsetdec.
    + apply IHa_inc.
  - destruct (α0 == α) as [-> | Hne].
    + assert (Hsc : ftvar_in_ptyp τ' [<=] dom Θ')
        by (eapply a_wf_ptyp_ftv_dom; eassumption).
      clear - Hsc; fsetdec.
    + apply IHa_inc.
  - specialize (IHa_inc α0); simpl_env; clear - IHa_inc; fsetdec.
  - specialize (IHa_inc α0); simpl_env; clear - IHa_inc; fsetdec.
  - specialize (IHa_inc α0); simpl_env; clear - IHa_inc; fsetdec.
Qed.

(** Both properties survive prefixing a block of wf monotype images — which
    is what the ∀ / arrow cases hand back up.  [msubst_lc_app_wf] MOVED UP to
    algo/basic/prop_metasubst.v (2026-10-11): under the SolE-FlexR repair every P6 ∀
    row prefixes such a block, not only P6-L. *)

Lemma msubst_ftv_app_wf : forall Θ κa κb,
  Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κa ->
  (forall α, ftvar_in_ptyp (msubst_lookup κb α) [<=] add α (dom Θ)) ->
  forall α, ftvar_in_ptyp (msubst_lookup (κa ++ κb) α) [<=] add α (dom Θ).
Proof.
  intros Θ κa κb Hall Hsc α.
  induction κa as [ | [α1 τ1] κa' IH ]; cbn; [ apply Hsc | ].
  inversion Hall as [ | ph pt [Hwf1 Hm1] Hall' ]; subst; cbn in Hwf1.
  destruct (α == α1) as [-> | Hne].
  - assert (Hs1 : ftvar_in_ptyp τ1 [<=] dom Θ)
      by (eapply a_wf_ptyp_ftv_dom; exact Hwf1).
    clear - Hs1; fsetdec.
  - apply IH; exact Hall'.
Qed.

(** A name fresh for the skeleton and for the target context is fresh for the
    κ-image too — the fact that keeps the ∀ case's renaming honest. *)
Lemma msubst_pskl_ftv_fresh : forall (Θ : aenv) κ P β,
  (forall α, ftvar_in_ptyp (msubst_lookup κ α) [<=] add α (dom Θ)) ->
  β `notin` ftvar_in_pskl P ->
  β `notin` dom Θ ->
  β `notin` ftvar_in_pskl (msubst_pskl κ P).
Proof.
  intros Θ κ P β Hsc; revert P;
    induction P as [ | n | α | P1 IH1 P2 IH2 | P0 IH0 | | P0 IH0 ];
    intros HβP HβΘ; cbn in *; try solve [ clear; fsetdec ].
  - assert (Hb : ftvar_in_pskl (ptyp_to_pskl (msubst_lookup κ α))
                 [<=] ftvar_in_ptyp (msubst_lookup κ α))
      by (apply ptyp_to_pskl_ftv).
    specialize (Hsc α). clear - Hb Hsc HβP HβΘ; fsetdec.
  - specialize (IH1 ltac:(clear - HβP; solve_notin_auto) HβΘ).
    specialize (IH2 ltac:(clear - HβP; solve_notin_auto) HβΘ).
    clear - IH1 IH2; fsetdec.
  - apply IH0; assumption.
  - apply IH0; assumption.
Qed.

(** One instance at a fresh β becomes the cofinite family for precision:
    re-express the α-instance as a β-renaming of the β-instance
    ([subst_*_intro]), rename ([ad_precise_rename_delta]), then relax Δ.
    (The wf twin is [a_wf_pskl_all_of_one_at], sub/look/prop_rigid_substitution.v.) *)
Lemma ad_precise_all_of_one : forall Θ Δ S0 X0 β,
  {{ Θ ⨟ (add β Δ) ⊢ₚᵣ (open_pskl_wrt_pskl S0 (pskl_var_f β))
                  ⊑ (open_pskl_wrt_pskl X0 (pskl_var_f β)) }}ad ->
  {{ ⊢ Θ }}a ->
  β `notin` dom Θ -> β `notin` Δ ->
  β `notin` ftvar_in_pskl S0 -> β `notin` ftvar_in_pskl X0 ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (pskl_all_syn S0) ⊑ (pskl_all_syn X0) }}ad.
Proof.
  intros Θ Δ S0 X0 β Hpre HwfΘ HβΘ HβΔ HβS HβX.
  unfold ad_precise; cbn [pskl_to_bskl_inh].
  apply ad_refine_syn_all_intro
    with (L := add β (Δ `union` dom Θ `union` ftvar_in_pskl S0
                        `union` ftvar_in_pskl X0)).
  intros α0 Hα0.
  rewrite <- ! pskl_to_bskl_inh_open.
  eapply ad_refine_syn_defs_mono;
    [ | intros γ τ Hb; apply binds_app_iff; right; exact Hb ].
  change (ad_refine_syn Θ (add α0 Δ)
            (pskl_to_bskl_inh (open_pskl_wrt_pskl S0 (pskl_var_f α0)))
            (pskl_to_bskl_inh (open_pskl_wrt_pskl X0 (pskl_var_f α0)))).
  assert (Hsub : add α0 Δ [<=] add α0 (remove β (add β Δ)))
    by (clear - HβΔ; fsetdec).
  (* precision is antitone in Δ *)
  eapply ad_refine_syn_delta_mono; [ | exact Hsub ].
  rewrite (subst_pskl_in_pskl_intro β S0 (pskl_var_f α0)) by exact HβS.
  rewrite (subst_pskl_in_pskl_intro β X0 (pskl_var_f α0)) by exact HβX.
  apply ad_precise_rename_delta;
    [ exact Hpre | exact HwfΘ | exact HβΘ | clear; fsetdec
    | clear - Hα0; fsetdec | ].
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper X0 (pskl_var_f β)) as Hup.
  cbn in Hup. clear - Hup Hα0; fsetdec.
Qed.

(** A tvar of [Ξ ++ Θ∖Δ] is a tvar of [Ξ ++ Θ] that is either guessed in
    [Ξ] or outside Δ — what the ∀◇ case needs to put a guess wf at the
    ghost's body context back at the enclosing one. *)
Lemma a_binds_tvar_app_minus : forall (Ξ Θ : aenv) Δ γ,
  a_binds_tvar γ (Ξ ++ aenv_minus Θ Δ) ->
  a_binds_tvar γ (Ξ ++ Θ) /\ (γ `in` dom Ξ \/ γ `notin` Δ).
Proof.
  intros Ξ Θ Δ γ H. unfold a_binds_tvar in *.
  destruct H as [Hb | [Hb | [τ Hb]]]; apply binds_app_iff in Hb;
    destruct Hb as [Hb | Hb];
    [ | apply binds_aenv_minus in Hb; destruct Hb as [Hb HγΔ]
    | | apply binds_aenv_minus in Hb; destruct Hb as [Hb HγΔ]
    | | apply binds_aenv_minus in Hb; destruct Hb as [Hb HγΔ] ];
    (split;
     [ first [ left; apply binds_app_iff; solve [ auto ]
             | right; left; apply binds_app_iff; solve [ auto ]
             | right; right; exists τ; apply binds_app_iff; solve [ auto ] ]
     | first [ right; exact HγΔ | left; eapply binds_In; exact Hb ] ]).
Qed.

(* ===================================================================== *)
(*  §9  THE WITNESS INDUCTION                                             *)
(*                                                                        *)
(*  The paper's "by induction on the definition of guess^N(P_s)" — but     *)
(*  read the other way round.  P6-L's conclusion is EXISTENTIAL in Ξ and   *)
(*  in the extract's output, so we do not consume a given guess: we BUILD  *)
(*  [a_guess_mono] and the metasubstitution extension κ' SIMULTANEOUSLY,   *)
(*  descending [P_s] and reading the counterpart's matching piece off the  *)
(*  precision premise (§6) at each step.  The extension is POSITIONAL, as  *)
(*  the paper says: at a ◇ the guess invents a fresh flexible and κ' sends *)
(*  it to the monotype §3 finds at that position in [⌊ψa⌋ˢ].               *)
(*                                                                        *)
(*  The measure is [size_pskl P_s] — the ∀ case opens at a fresh β, and    *)
(*  opening by a variable preserves size.                                 *)
(*                                                                        *)
(*  BOTH Δ's move.  [Δ0] carries [P_s]'s own binders (wf) and [Δ] the      *)
(*  counterpart's (precision); [a_wf_pskl__all] grows Θ0 and Δ0, and       *)
(*  [ad_refine_syn__all] grows Δ (its rigid tvar is invisible to flexible  *)
(*  lookups, so Θ stays put); the ∀◇ case RESETS Δ0 to ∅ at [Θ0∖Δ0].       *)
(*  They are therefore independent parameters of the induction.           *)
(*                                                                        *)
(*  κ''s images are Θ-well-formed no matter how deep the ∀-nesting goes,   *)
(*  which is what makes the extension legal: [ad_refine_syn__ghost]'s fill  *)
(*  misses Δ, and the counterpart's scoping premise binds every free name  *)
(*  outside Δ in Θ — so a ghost under a binder is never filled with the     *)
(*  bound variable (§3).                                                   *)
(* ===================================================================== *)

Lemma a_guess_ty_witness : forall n Θ0 Θ κs Δ Δ0 Ps X,
  size_pskl Ps <= n ->
  {{ ⊢ Θ }}a ->
  {{ Θ0 ⨟ Δ0 ⊢ₚₛ Ps }}a ->
  msubst_lc κs ->
  (forall α, ftvar_in_ptyp (msubst_lookup κs α) [<=] add α (dom Θ)) ->
  pskl_ghost_free X -> lc_pskl X ->
  (* the counterpart's scoping: every free name outside its binders Δ is
     bound in Θ (the paper presupposes the counterpart well-formed) *)
  (forall γ, γ `in` ftvar_in_pskl X -> γ `notin` Δ -> a_binds_tvar γ Θ) ->
  {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_pskl κs Ps) ⊑ X }}ad ->
  forall L, exists Ξ' A κ',
    (* L-BOUNDED CONTEXT QUANTIFICATION (freshness campaign): the guess is
       valid at any context whose mentioned names stay inside [L] — the
       bound is fixed BEFORE the ∀ case picks its witness, which is what
       makes that case provable; the old context-generic
       [a_guess_mono nil …] is an artifact of the pre-campaign inert
       context parameter.  Consumers instantiate [Θg := nil]. *)
    (forall Θg, ftvar_in_aenv Θg [<=] L -> a_guess_mono Θg Ps Ξ' A) /\
    all_flex_mono Ξ' /\
    uniq Ξ' /\
    keys κ' = keys Ξ' /\
    (forall α, α `in` dom Ξ' -> α `notin` L) /\
    Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ' /\
    {{ (Ξ' ++ Θ0) ⨟ Δ0 ⊢ₚₛ (ptyp_to_pskl A) }}a /\
    {{ Θ ⨟ Δ ⊢ₚᵣ (msubst_pskl (κ' ++ κs) (ptyp_to_pskl A)) ⊑ X }}ad.
Proof.
  intros n; induction n as [ | n IH ];
    intros Θ0 Θ κs Δ Δ0 Ps X Hsz HwfΘ HwfPs Hκlc Hκsc Hgf Hlc HscX Hprec L.
  - (* no skeleton has size 0 *)
    exfalso. pose proof (size_pskl_min Ps) as Hm.
    clear - Hsz Hm. inversion Hsz; lia.
  - assert (HlcPs : lc_pskl Ps) by (eapply a_wf_pskl_lc; exact HwfPs).
    destruct Ps as [ | m | α | Ps1 Ps2 | Ps0 | | Ps0 ].
    + (* ------------------------------ unit ------------------------------ *)
      exists nil, ptyp_unit, nil.
      split; [ intros Θg _; apply a_guess_mono__unit | ].
      split; [ apply Forall_nil | ].
      split; [ apply uniq_nil | ].
      split; [ reflexivity | ].
      split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
      split; [ apply Forall_nil | ].
      split; [ cbn; apply a_wf_pskl__unit | ].
      cbn [app ptyp_to_pskl]. exact Hprec.
    + (* var_b : excluded by local closure, not by ghost-freeness *)
      exfalso. inversion HlcPs.
    + (* ------------------------------ var ------------------------------- *)
      (* guess^TY returns the variable itself, so BOTH remaining goals are
         the corresponding hypotheses verbatim *)
      exists nil, (ptyp_var_f α), nil.
      split; [ intros Θg _; apply a_guess_mono__var | ].
      split; [ apply Forall_nil | ].
      split; [ apply uniq_nil | ].
      split; [ reflexivity | ].
      split; [ intros α0 Hα0; cbn in Hα0; exfalso; clear - Hα0; fsetdec | ].
      split; [ apply Forall_nil | ].
      split; [ cbn [app ptyp_to_pskl]; exact HwfPs | ].
      cbn [app ptyp_to_pskl]. exact Hprec.
    + (* ----------------------------- arrow ------------------------------ *)
      cbn in Hsz.
      assert (HwfPs1 : {{ Θ0 ⨟ Δ0 ⊢ₚₛ Ps1 }}a) by (inversion HwfPs; subst; assumption).
      assert (HwfPs2 : {{ Θ0 ⨟ Δ0 ⊢ₚₛ Ps2 }}a) by (inversion HwfPs; subst; assumption).
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ᵣ
                (bskl_arrow (pskl_to_bskl_inh (msubst_pskl κs Ps1))
                            (pskl_to_bskl_inh (msubst_pskl κs Ps2)))
                ⊳ (pskl_to_bskl_inh X) }}ad)
        by (unfold ad_precise in Hprec; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_arrow_l_inv Θ Δ _ _ Hpre'
                  (msubst_pskl κs Ps1) (msubst_pskl κs Ps2) X
                  eq_refl eq_refl HwfΘ Hgf Hlc HscX)
        as (X1 & X2 & Hg1 & Hg2 & Hl1 & Hl2 & Hs1 & Hs2 & Hp1 & Hp2 & Hreplay).
      destruct (IH Θ0 Θ κs Δ Δ0 Ps1 X1 ltac:(clear - Hsz; lia)
                   HwfΘ HwfPs1 Hκlc Hκsc Hg1 Hl1 Hs1 Hp1
                   (L `union` ftvar_in_pskl Ps1 `union` ftvar_in_pskl Ps2))
        as (Ξ1 & A1 & κa & Hgu1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hwf1 & Hpr1).
      destruct (IH Θ0 Θ κs Δ Δ0 Ps2 X2 ltac:(clear - Hsz; lia)
                   HwfΘ HwfPs2 Hκlc Hκsc Hg2 Hl2 Hs2 Hp2
                   (L `union` ftvar_in_pskl Ps1 `union` ftvar_in_pskl Ps2
                      `union` dom Ξ1))
        as (Ξ2 & A2 & κb & Hgu2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hwf2 & Hpr2).
      (* the two guessed blocks are apart, and each misses the OTHER branch's
         source variables — which is what makes each branch's own κ invisible
         to the other's payload *)
      assert (Hdκa : dom κa [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
      assert (Hdκb : dom κb [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
      assert (HA1 : ftvar_in_pskl (ptyp_to_pskl A1)
                    [<=] ftvar_in_pskl Ps1 `union` dom Ξ1).
      { assert (Hb : ftvar_in_ptyp A1 [<=] ftvar_in_pskl Ps1 `union` dom Ξ1)
          by (eapply a_guess_mono_ftv; apply (Hgu1 nil); simpl; fsetdec).
        assert (Hc : ftvar_in_pskl (ptyp_to_pskl A1) [<=] ftvar_in_ptyp A1)
          by (apply ptyp_to_pskl_ftv).
        clear - Hb Hc; fsetdec. }
      assert (HA2 : ftvar_in_pskl (ptyp_to_pskl A2)
                    [<=] ftvar_in_pskl Ps2 `union` dom Ξ2).
      { assert (Hb : ftvar_in_ptyp A2 [<=] ftvar_in_pskl Ps2 `union` dom Ξ2)
          by (eapply a_guess_mono_ftv; apply (Hgu2 nil); simpl; fsetdec).
        assert (Hc : ftvar_in_pskl (ptyp_to_pskl A2) [<=] ftvar_in_ptyp A2)
          by (apply ptyp_to_pskl_ftv).
        clear - Hb Hc; fsetdec. }
      assert (Hdisj : disjoint Ξ1 Ξ2).
      { unfold disjoint. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hα0 Hfr2; fsetdec. }
      assert (Heq1 : msubst_pskl (κa ++ κb ++ κs) (ptyp_to_pskl A1)
                     = msubst_pskl (κa ++ κs) (ptyp_to_pskl A1)).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin2 : α0 `in` dom Ξ2) by (clear - Hα0 Hdκb; fsetdec).
        specialize (Hfr2 α0 Hin2). clear - Hfr2 HA1; fsetdec. }
      assert (Heq2 : msubst_pskl (nil ++ κa ++ (κb ++ κs)) (ptyp_to_pskl A2)
                     = msubst_pskl (nil ++ (κb ++ κs)) (ptyp_to_pskl A2)).
      { apply msubst_pskl_mid_skip. intros α0 Hα0.
        assert (Hin1 : α0 `in` dom Ξ1) by (clear - Hα0 Hdκa; fsetdec).
        specialize (Hfr1 α0 Hin1).
        assert (Hne : α0 `notin` dom Ξ2)
          by (clear - Hin1 Hdisj; unfold disjoint in Hdisj; fsetdec).
        clear - Hfr1 Hne HA2; fsetdec. }
      cbn [app] in Heq2.
      exists (Ξ1 ++ Ξ2), (ptyp_arrow A1 A2), (κa ++ κb).
      split; [ intros Θg Hsub; apply a_guess_mono__arrow;
               [ apply Hgu1 | apply Hgu2 ]; clear - Hsub; fsetdec | ].
      split; [ apply all_flex_mono_app; assumption | ].
      split; [ clear - Hu1 Hu2 Hdisj; solve_uniq | ].
      split; [ rewrite ! keys_app; rewrite Hk1, Hk2; reflexivity | ].
      split; [ intros α0 Hα0; rewrite dom_app in Hα0;
               destruct (union_1 Hα0) as [Hin1 | Hin2];
                 [ specialize (Hfr1 α0 Hin1); clear - Hfr1; fsetdec
                 | specialize (Hfr2 α0 Hin2); clear - Hfr2; fsetdec ] | ].
      split; [ apply Forall_app; split; assumption | ].
      split.
      { rewrite app_assoc. cbn [ptyp_to_pskl]. apply a_wf_pskl__arrow.
        - eapply a_wf_pskl_weaken; [ | exact Hwf1 ].
          intros x b Hb. apply binds_weaken. exact Hb.
        - eapply a_wf_pskl_weaken; [ | exact Hwf2 ].
          intros x b Hb. apply binds_app_3. exact Hb. }
      rewrite app_assoc. cbn [ptyp_to_pskl msubst_pskl].
      rewrite Heq1, Heq2.
      apply Hreplay; assumption.
    + (* ------------------------------- ∀ -------------------------------- *)
      cbn in Hsz.
      assert (HwfF : exists Lw, forall β, β `notin` Lw ->
                {{ ((β ~ abind_tvar) ++ Θ0) ⨟ (add β Δ0) ⊢ₚₛ
                   (open_pskl_wrt_pskl Ps0 (pskl_var_f β)) }}a)
        by (inversion HwfPs; subst; eexists; eassumption).
      destruct HwfF as [Lw HwfF].
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ᵣ
                (bskl_all_inh (pskl_to_bskl_inh (msubst_pskl κs Ps0)))
                ⊳ (pskl_to_bskl_inh X) }}ad)
        by (unfold ad_precise in Hprec; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_all_l_inv Θ Δ _ _ Hpre' (msubst_pskl κs Ps0) X
                  eq_refl eq_refl HwfΘ Hgf Hlc)
        as (X0 & Lp & HeqX & HprF).
      subst X.
      assert (HgfX0 : pskl_ghost_free X0) by (cbn in Hgf; exact Hgf).
      assert (HlcX0 : forall α0,
                lc_pskl (open_pskl_wrt_pskl X0 (pskl_var_f α0)))
        by (inversion Hlc; subst; assumption).
      pick fresh β for (L `union` Lw `union` Lp `union` Δ `union` Δ0
                          `union` ftvar_in_pskl Ps0 `union` ftvar_in_pskl X0
                          `union` dom Θ `union` dom Θ0 `union` dom κs).
      assert (HwfβPs : {{ ((β ~ abind_tvar) ++ Θ0) ⨟ (add β Δ0) ⊢ₚₛ
                (open_pskl_wrt_pskl Ps0 (pskl_var_f β)) }}a)
        by (apply HwfF; clear - Fr; fsetdec).
      (* the opened counterpart's scoping: β joins Δ, everything else is
         the original counterpart's *)
      assert (HscβX : forall γ,
                γ `in` ftvar_in_pskl (open_pskl_wrt_pskl X0 (pskl_var_f β)) ->
                γ `notin` add β Δ -> a_binds_tvar γ Θ).
      { intros γ Hγ HγΔ. apply HscX; [ | clear - HγΔ; fsetdec ].
        pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper X0 (pskl_var_f β))
          as Hup.
        cbn in Hup |- *. clear - Hup Hγ HγΔ; fsetdec. }
      assert (HprβX : {{ Θ ⨟ (add β Δ) ⊢ₚᵣ
                (msubst_pskl κs (open_pskl_wrt_pskl Ps0 (pskl_var_f β)))
                ⊑ (open_pskl_wrt_pskl X0 (pskl_var_f β)) }}ad).
      { rewrite (@msubst_pskl_open_lc κs Ps0 β Hκlc
                   ltac:(clear - Fr; solve_notin_auto)).
        apply HprF; clear - Fr; fsetdec. }
      destruct (IH ((β ~ abind_tvar) ++ Θ0) Θ κs (add β Δ) (add β Δ0)
                   (open_pskl_wrt_pskl Ps0 (pskl_var_f β))
                   (open_pskl_wrt_pskl X0 (pskl_var_f β))
                   ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var;
                         clear - Hsz; lia)
                   HwfΘ HwfβPs Hκlc Hκsc
                   ltac:(unfold open_pskl_wrt_pskl;
                         apply pskl_ghost_free_open_rec; exact HgfX0)
                   ltac:(apply HlcX0)
                   HscβX HprβX
                   (add β (L `union` dom Θ `union` dom Θ0
                             `union` ftvar_in_pskl Ps0
                             `union` ftvar_in_pskl X0)))
        as (Ξ' & A' & κ' & Hgu & Hfm & Hu & Hk & Hfr & HF & Hwf' & Hpr).
      (* CLOSE the guessed payload over β (the rule's own discipline) *)
      assert (HβΞ : β `notin` dom Ξ')
        by (intro Hc; specialize (Hfr β Hc); clear - Hfr; fsetdec).
      assert (HopenA : open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp β A')
                         (ptyp_var_f β) = A')
        by (apply open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp).
      assert (HβA : β `notin` ftvar_in_ptyp (close_ptyp_wrt_ptyp β A'))
        by (rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp; clear; fsetdec).
      assert (HβPA : β `notin` ftvar_in_pskl
                       (ptyp_to_pskl (close_ptyp_wrt_ptyp β A'))).
      { assert (Hc : ftvar_in_pskl (ptyp_to_pskl (close_ptyp_wrt_ptyp β A'))
                     [<=] ftvar_in_ptyp (close_ptyp_wrt_ptyp β A'))
          by (apply ptyp_to_pskl_ftv).
        clear - Hc HβA; fsetdec. }
      assert (HopenPA : ptyp_to_pskl A'
                = open_pskl_wrt_pskl
                    (ptyp_to_pskl (close_ptyp_wrt_ptyp β A')) (pskl_var_f β))
        by (rewrite <- ptyp_to_pskl_open; rewrite HopenA; reflexivity).
      exists Ξ', (ptyp_all (close_ptyp_wrt_ptyp β A')), κ'.
      split.
      { (* the L-bound is what makes this case go through: the IH's guess is
           instantiated at [(β~tvar) ++ Θg], whose mentioned names sit inside
           the IH's own (β-extended) bound *)
        intros Θg Hsub.
        eapply a_guess_mono_all_of_one with (β := β);
          [ rewrite HopenA; apply Hgu;
            rewrite ftvar_in_aenv_app; rewrite ftvar_in_aenv_one;
            cbn [ftvar_in_abind]; clear - Hsub; fsetdec
          | clear - Hsub Fr; fsetdec
          | clear - Fr; fsetdec
          | exact HβA ]. }
      split; [ exact Hfm | ].
      split; [ exact Hu | ].
      split; [ exact Hk | ].
      split; [ intros α0 Hα0; specialize (Hfr α0 Hα0);
               clear - Hfr; fsetdec | ].
      split; [ exact HF | ].
      split.
      { cbn [ptyp_to_pskl].
        apply a_wf_pskl_all_of_one_at with (β := β); [ | exact HβPA ].
        rewrite <- HopenPA.
        eapply a_wf_pskl_tvar_mono; [ exact Hwf' | ].
        intros γ [Hb | [Hb | [τ Hb]]];
          [ left | right; left | right; right; exists τ ];
          apply binds_mid_to_front; exact Hb. }
      (* precision: the β-instance, closed back into the cofinite family *)
      assert (Hβκ : β `notin` ftvar_in_pskl
                (msubst_pskl (κ' ++ κs)
                   (ptyp_to_pskl (close_ptyp_wrt_ptyp β A')))).
      { eapply msubst_pskl_ftv_fresh;
          [ eapply msubst_ftv_app_wf; [ exact HF | exact Hκsc ]
          | exact HβPA
          | clear - Fr; fsetdec ]. }
      cbn [ptyp_to_pskl msubst_pskl].
      eapply ad_precise_all_of_one with (β := β);
        [ | exact HwfΘ | clear - Fr; fsetdec | clear - Fr; fsetdec
        | exact Hβκ | clear - Fr; fsetdec ].
      rewrite <- (@msubst_pskl_open_lc (κ' ++ κs)
                    (ptyp_to_pskl (close_ptyp_wrt_ptyp β A')) β
                    (msubst_lc_app_wf HF Hκlc)
                    ltac:(rewrite dom_app;
                          assert (Hd : dom κ' [=] dom Ξ')
                            by (apply keys_eq_dom; exact Hk);
                          clear - Hd HβΞ Fr; solve_notin_auto)).
      rewrite <- HopenPA. exact Hpr.
    + (* ------------------------------- ◇ -------------------------------- *)
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ₚᵣ pskl_ghost ⊑ X }}ad)
        by (unfold ad_precise in Hprec |- *; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_ghost_inv_mono Θ Δ X Hpre' Hgf Hlc HscX)
        as (τ & Heqτ & Hmτ & HwfX).
      assert (Hwfτ : a_wf_ptyp Θ τ)
        by (apply a_wf_ptyp_of_wf_pskl_mono;
            [ exact Hmτ | rewrite Heqτ; exact HwfX ]).
      pick fresh α1 for (L `union` dom Θ `union` dom Θ0 `union` dom κs).
      exists ((α1 ~ abind_flex_mono) ++ nil), (ptyp_var_f α1),
             ((α1, τ) :: nil).
      split; [ intros Θg Hsub; apply a_guess_mono__ghost;
               clear - Hsub Fr; fsetdec | ].
      split; [ unfold all_flex_mono; repeat constructor | ].
      split; [ solve_uniq | ].
      split; [ reflexivity | ].
      split; [ intros α0 Hα0; simpl_env in Hα0;
               assert (Hα1 : α0 = α1) by (clear - Hα0; fsetdec);
               subst α0; clear - Fr; fsetdec | ].
      split; [ constructor; [ split; assumption | apply Forall_nil ] | ].
      split.
      { cbn [app ptyp_to_pskl]. apply a_wf_pskl__var. right. left.
        unfold binds. left. reflexivity. }
      (* κ' sends the guessed flexible to exactly the monotype §3 found *)
      cbn [app ptyp_to_pskl msubst_pskl].
      rewrite msubst_lookup_cons_eq. rewrite Heqτ.
      unfold ad_precise. exact (ad_refine_syn_refl_inh_gen HwfX Θ Δ).
    + (* ------------------------------ ∀◇ -------------------------------- *)
      cbn in Hsz.
      assert (Hguard : guarded_pskl Ps0) by (inversion HwfPs; subst; assumption).
      assert (HwfPs0 : {{ (aenv_minus Θ0 Δ0) ⨟ empty ⊢ₚₛ Ps0 }}a)
        by (inversion HwfPs; subst; assumption).
      assert (Hpre' : {{ Θ ⨟ Δ ⊢ᵣ
                (bskl_univ_ghost (pskl_to_bskl_inh (msubst_pskl κs Ps0)))
                ⊳ (pskl_to_bskl_inh X) }}ad)
        by (unfold ad_precise in Hprec; cbn in Hprec; exact Hprec).
      destruct (@ad_precise_univ_ghost_l_inv Θ Δ _ _ Hpre' (msubst_pskl κs Ps0) X
                  eq_refl eq_refl HwfΘ Hgf Hlc HscX)
        as (X' & Hg' & Hl' & Hs' & Hp' & Hreplay).
      destruct (IH (aenv_minus Θ0 Δ0) Θ κs Δ empty Ps0 X'
                   ltac:(clear - Hsz; lia)
                   HwfΘ HwfPs0 Hκlc Hκsc Hg' Hl' Hs' Hp' (L `union` Δ0))
        as (Ξ' & A & κ' & Hgu & Hfm & Hu & Hk & Hfr & HF & Hwf' & Hpr).
      exists Ξ', A, κ'.
      split; [ intros Θg Hsub; apply a_guess_mono__univ_ghost;
               apply Hgu; clear - Hsub; fsetdec | ].
      split; [ exact Hfm | ].
      split; [ exact Hu | ].
      split; [ exact Hk | ].
      split; [ intros α0 Hα0; specialize (Hfr α0 Hα0);
               clear - Hfr; fsetdec | ].
      split; [ exact HF | ].
      split.
      { (* the guess is wf at [Θ0∖Δ0], so it mentions no Δ0 name: the
           guessed block dodges Δ0 by the L-bound *)
        eapply a_wf_pskl_delta_mono.
        - eapply a_wf_pskl_tvar_mono; [ exact Hwf' | ].
          intros γ Hγ. apply (proj1 (@a_binds_tvar_app_minus _ _ _ _ Hγ)).
        - intros γ Hγ HγΔ0. exfalso.
          destruct (proj2 (@a_binds_tvar_app_minus _ _ _ _
                             (a_wf_pskl_ftv_binds Hwf' Hγ))) as [HγΞ | Hγn].
          + specialize (Hfr γ HγΞ). clear - Hfr HγΔ0; fsetdec.
          + exact (Hγn HγΔ0). }
      apply Hreplay; exact Hpr.
Qed.

(* ===================================================================== *)
(*  §10  P6-L — [a_extract_complete_gen]  (paper [lemma:complete-look])        *)
(*                                                                        *)
(*  The assembly the paper describes at tex:2755-2833, in its order:       *)
(*                                                                        *)
(*   (a)-(f)  P6-Ss ([a_looksub_solve_complete]) at [Pi := □], [Ψi := ∅],  *)
(*            so [Ψ' = Ψa]; its precision premise                          *)
(*            [{{ Θ ⨟ Δ ⊢ˢ κ□ ⊑ᵖ[∅] ψa }}ad] IS the precision ghost rule.     *)
(*   (g)      [ad_partial_precise_complete] (P5b-i) upgrades ⊑ᵖ[Ψa] to     *)
(*            plain ⊑ against [⌊ψa⌋ˢ] — the paper's step at tex:2764.      *)
(*   (h),(i)-(12)  the guess.  At SK it is the identity, so κ' = · and     *)
(*            every conclusion is P6-Ss's verbatim; at TY it is §9.        *)
(*   (13)     [a_extract__solve] on (a), (b) and the guess.                *)
(*                                                                        *)
(*  The [a_inc] and wf conclusions are assembled with the HOMOGENEOUS-FLEX *)
(*  REORDER KIT of sub/look/prop_completeness_lookeq_solve.v: [a_extract] emits [Ξc,Ξ']    *)
(*  where the natural build order is [Ξ',Ξc] (both blocks are undefined    *)
(*  flexibles, so the order is immaterial — but not syntactically so).     *)
(*                                                                        *)
(*  As in P6-Ss, the paper's [inc[θ≡θa]{Θ0}{Θ}] appears as the REFLEXIVE   *)
(*  [a_inc_equiv Θ0 κ κ Θ]: the mech's [a_inc_equiv] is POSITIONAL, so the *)
(*  content "θa agrees with θ on Θ0" is carried instead by the a_inc       *)
(*  conclusion exhibiting θa as the EXTENSION [κa ++ κ].                   *)
(* ===================================================================== *)

(** P6-L, GENERALIZED in the join's ambient tag context [Ψsub] (P7b's
    Sub-ForallL runs its premise at [Ψ ∪ Ψa]).  The paper-facing statement is
    the [Ψsub := Ψa] corollary [a_extract_complete] at the end of the file. *)
Theorem a_extract_complete_gen :
  forall n NM M Θ0 Θ κ Ψa Ψsub ψa Q P P0 R' α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->                            (* erase R' = P (R' is κ-FREE) *)
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψa ψa ->
  (ftag_in_uskl R') ∩ Ψa [=] empty ->       (* the paper's "Ψ disjoint from Ψa" *)
  (* ⭐ THE IDEAL GUESS IS Θ-SCOPED (2026-08-05, the SolE-FlexR repair): the
     repaired SolE-FlexR reads the SOLVE block's payloads off [ψa].
     [paper-external wf side condition — docs/WF-SIDE-CONDITIONS.md] *)
  ftvar_in_uskl ψa [<=] dom Θ ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψa ⌋ˢ }}a ->                     (* the paper's wf premise for ψa *)
  (* the join's AMBIENT tag context: the paper's [Ψ,Ψa] — P6-Ss's range
     parameter, surfaced (2026-07-31) for P7b's Sub-ForallL, whose row
     premise runs at [Ψ ∪ Ψa] with the ambient [Ψ ⊆ ftag R'] *)
  Ψsub [<=] ftag_in_uskl R' `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* subject = (κR')[ψa/α], EXACTLY the paper's form *)
  ad_pat_sub_fuel n NM M Ψsub Θ
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  {{ Θ ⨟ empty ⊢ₚₛ
    (uskl_to_pskl (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R'))) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  (* the counterpart is well formed — the paper's presupposition
     (declarative.tex:2074); docs/WF-SIDE-CONDITIONS.md §2a *)
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  exists Ξ Pa κa,
    ({{ Θ0 ⊢ P ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ Pa }}a) /\      (* look succeeds *)
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\                 (* Θ0,Ξ ⊢ Pa *)
    {{ ⊢ (Ξ ++ Θ0) }}a /\
    a_decls Ξ /\                                 (* Ξ is a flex-decl block *)
    keys κa = keys Ξ /\
    (κa ++ κ) ∷ (Ξ ++ Θ0) ⊑ Θ /\                 (* inc[θa]{Θ0,Ξ}{Θ} *)
    a_inc_equiv Θ0 κ κ Θ /\                      (* inc[θ≡θa]{Θ0}{Θ} *)
    {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl (κa ++ κ) Pa) ⊑ ⌊ ψa ⌋ˢ }}ad.
Proof.
  intros n NM M Θ0 Θ κ Ψa Ψsub ψa Q P P0 R' α.
  intros HwfΘ HwfΘ0 HwfP0 HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR HscopeR HlcR
         Htags Hdisj Hψaw Hwfψ HΨsubU HΨsubL Hsubty
         HwfSubj Hrefine HwfQ.
  (* ---- (a)-(f) : P6-Ss at [Pi := □], [Ψi := ∅] ---- *)
  (* ⭐ THE SOLVE'S OWN BLOCK [Ξs] (2026-08-05, the SolE-FlexR repair).  The
     look's suffix is now three blocks, [Ξc ++ Ξs ++ Ξ'] — collection,
     solving, final guess — and each stage's avoid-input is everything
     generated before it ([a_extract__solve], algo/def_rules.v).  So P6-Ss's
     avoid-set parameter is instantiated at the CONTEXT's own variables, the
     guess is run at [Ξs ++ Ξc ++ Θ0], and the three blocks are pairwise
     disjoint by construction rather than by a side condition. *)
  destruct (@a_looksub_solve_complete n NM M Θ0 Θ κ empty Ψa empty Ψa Ψsub ψa Q
              P P0 pskl_ghost R' α
              HwfΘ HwfΘ0 HwfP0 ltac:(apply a_wf_pskl__ghost)
              HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR HscopeR HlcR Htags Hdisj
              ltac:(clear; solve_notin_auto) Hψaw (delta_def_fresh_empty Θ)
              ltac:(cbn [msubst_pskl];
                    apply ad_ppre__ghost; [ clear; solve_notin_auto | clear; fsetdec ])
              HΨsubU HΨsubL
              Hsubty HwfSubj Hrefine HwfQ
              (ftvar_in_aenv Θ0) ltac:(clear; solve_notin_auto))
    as (𝒞 & Ξc & Ξs & Pa & κc & κs
        & Hlook & Hsolve & Hfms & Hus & Hks & Hfrs & HFs
        & HwfPa & HwfΞc & HαΞc & Hkeysc
        & HForc & Hincc & Heqv & Hκcfresh & Hprec & _ & Hapart).
  (* ---- (g) : P5b-i upgrades ⊑ᵖ[Ψa] to plain ⊑ ⌊ψa⌋ˢ ---- *)
  assert (Hpre : {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl (κs ++ κc ++ κ) Pa) ⊑ ⌊ ψa ⌋ˢ }}ad).
  { eapply ad_partial_precise_complete;
      [ exact HwfΘ | exact Htags | exact Hwfψ | ].
    eapply ad_partial_precise_psi_cong; [ exact Hprec | clear; fsetdec ]. }
  (* ---- the reorder kit's prerequisites on the COLLECTED block ---- *)
  assert (HfmΞc : all_flex_mono Ξc)
    by (eapply a_looksub_all_flex_mono; exact Hlook).
  assert (HwmΞc : Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κc).
  { destruct (@a_inc_flex_prefix_split Ξs κs (Ξc ++ Θ0) (κc ++ κ) Θ
                Hfms Hks Hincc) as [_ HincC].
    destruct (@a_inc_flex_prefix_split Ξc κc Θ0 κ Θ HfmΞc Hkeysc HincC)
      as [Hw _]; exact Hw. }
  assert (HwmΞs : Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κs)
    by (destruct (@a_inc_flex_prefix_split Ξs κs (Ξc ++ Θ0) (κc ++ κ) Θ
                    Hfms Hks Hincc) as [Hw _]; exact Hw).
  assert (HuqΞc : uniq (Ξc ++ Θ0)) by (apply a_wf_aenv_uniq; exact HwfΞc).
  (* the SOLVE block dodges everything its own context MENTIONS — the Ξ
     scoping kit's master invariant, and what makes [Ξs ++ Ξc ++ Θ0] wf *)
  assert (HfrsC : forall x, x `in` dom Ξs ->
            x `notin` ftvar_in_aenv (Ξc ++ Θ0))
    by (intros x Hx; eapply a_solve_cstr_generated_fresh;
          [ exact Hsolve | exact Hx ]).
  assert (HwfΞs : {{ ⊢ (Ξs ++ Ξc ++ Θ0) }}a).
  { apply a_wf_aenv_flex_prefix; [ exact Hfms | | exact HwfΞc ].
    assert (Hdd : dom Ξs ∩ dom (Ξc ++ Θ0) [<=] empty).
    { intros x Hx.
      assert (Hx1 : x `in` dom Ξs) by (clear - Hx; fsetdec).
      assert (Hx2 : x `in` dom (Ξc ++ Θ0)) by (clear - Hx; fsetdec).
      pose proof (HfrsC x Hx1) as Hf.
      pose proof (dom_subset_ftvar_in_aenv (Ξc ++ Θ0)) as Hds.
      exfalso; clear - Hf Hds Hx2; fsetdec. }
    apply uniq_app_4; [ exact Hus | exact HuqΞc | exact Hdd ]. }
  assert (HuqΞsc : uniq (Ξs ++ Ξc ++ Θ0)) by (apply a_wf_aenv_uniq; exact HwfΞs).
  assert (Hdcs : forall β0, β0 `in` dom κc -> β0 `notin` dom κs).
  { intros β0 Hβ0 Hc.
    pose proof (@keys_eq_dom _ _ κc Ξc Hkeysc) as Hdc0.
    pose proof (@keys_eq_dom _ _ κs Ξs Hks) as Hds0.
    assert (Hinc : β0 `in` dom Ξc) by (clear - Hβ0 Hdc0; fsetdec).
    assert (Hins : β0 `in` dom Ξs) by (clear - Hc Hds0; fsetdec).
    pose proof (HfrsC β0 Hins) as Hf.
    pose proof (dom_subset_ftvar_in_aenv (Ξc ++ Θ0)) as Hdd.
    rewrite dom_app in Hdd. clear - Hf Hdd Hinc; fsetdec. }
  (* ---- (h) : the guess.  SK is the identity; TY is §9 ---- *)
  destruct NM.
  - (* ================================ TY ============================== *)
    assert (Hgfψ : pskl_ghost_free ⌊ ψa ⌋ˢ)
      by (inversion Htags; subst; apply uskl_ghost_free_to_pskl; assumption).
    assert (Hlcψ : lc_pskl ⌊ ψa ⌋ˢ) by (eapply a_wf_pskl_lc; exact Hwfψ).
    destruct (@a_guess_ty_witness (size_pskl Pa) (Ξs ++ Ξc ++ Θ0) Θ
                (κs ++ κc ++ κ) empty empty Pa ⌊ ψa ⌋ˢ
                (le_n _) HwfΘ HwfPa
                ltac:(unfold msubst_lc; intros α0;
                      eapply a_inc_msubst_lc; exact Hincc)
                ltac:(intros α0; eapply a_inc_lookup_ftv; exact Hincc)
                Hgfψ Hlcψ
                ltac:(intros γ Hγ _; eapply a_wf_pskl_ftv_binds;
                      [ exact Hwfψ | exact Hγ ])
                Hpre
                (* the guess runs at [Ξs ++ Ξc ++ Θ0] ([a_extract__solve]), so
                   the L-bound must cover that context's PAYLOADS too, not just
                   its domain — cluster 3's avoid-input is [ftvar_in_aenv] *)
                (* ⭐ AND THE GUESS'S HALF OF THE CROSS-LAYER GUARD
                   (2026-08-21): the L-BOUNDED family makes it free — just
                   name the two sets the new premise talks about. *)
                (add α (ftvar_in_aenv (Ξs ++ Ξc ++ Θ0) `union` dom Θ
                          `union` dom Θ0 `union` dom Ξc `union` dom Ξs
                          `union` dom κ
                          `union` ftvar_in_a_cstrs 𝒞
                          `union` ftvar_in_pskl Pa)))
      as (Ξ' & A & κ' & Hgu & HfmΞ' & HuqΞ' & Hkeys' & Hfr' & HF' & Hwf'
          & Hpr').
    assert (HdomΞ' : dom κ' [=] dom Ξ') by (apply keys_eq_dom; exact Hkeys').
    assert (Hdc : dom κc [=] dom Ξc) by (apply keys_eq_dom; exact Hkeysc).
    assert (Hds : dom κs [=] dom Ξs) by (apply keys_eq_dom; exact Hks).
    assert (HuqAll : uniq (Ξc ++ Ξs ++ Ξ' ++ Θ0)).
    { assert (Hd1 : disjoint Ξ' Ξc)
        by (unfold disjoint; intros α0 Hα0;
            assert (Hin : α0 `in` dom Ξ') by (clear - Hα0; fsetdec);
            specialize (Hfr' α0 Hin); clear - Hα0 Hfr'; fsetdec).
      assert (Hd1s : disjoint Ξ' Ξs)
        by (unfold disjoint; intros α0 Hα0;
            assert (Hin : α0 `in` dom Ξ') by (clear - Hα0; fsetdec);
            specialize (Hfr' α0 Hin); clear - Hα0 Hfr'; fsetdec).
      assert (Hd2 : disjoint Ξ' Θ0)
        by (unfold disjoint; intros α0 Hα0;
            assert (Hin : α0 `in` dom Ξ') by (clear - Hα0; fsetdec);
            specialize (Hfr' α0 Hin); clear - Hα0 Hfr'; fsetdec).
      clear - HuqΞsc HuqΞ' Hd1 Hd1s Hd2; solve_uniq. }
    exists (Ξc ++ Ξs ++ Ξ'), (ptyp_to_pskl A), (κc ++ κs ++ κ').
    split.
    { eapply a_extract__solve;
        [ exact Hlook | exact Hsolve
        | apply a_guess__ty; apply Hgu; clear; fsetdec
        (* ⭐ THE CROSS-LAYER GUARD, and it is exactly what P6-Ss's new
           conjunct reports: no scoping fact could give it, because the
           escaping constraint variables are LEAKED OPENERS. *)
        | apply inter_dom_empty_of_forall; exact Hapart
        (* ⭐ the GUESS's half — the L-bound above names both sets *)
        | apply inter_dom_empty_of_forall;
          intros x Hx; specialize (Hfr' x Hx); clear - Hfr'; fsetdec ]. }
    split.
    { (* [Ξ' ++ Ξs ++ Ξc ++ Θ0] → [Ξc ++ Ξs ++ Ξ' ++ Θ0]: all three blocks are
         undefined flexibles, so any reordering is binds-preserving *)
      eapply a_wf_pskl_weaken; [ | exact Hwf' ].
      intros x b Hb. simpl_env. analyze_binds Hb. }
    split.
    { apply (@a_wf_aenv_flex_prefix (Ξc ++ Ξs ++ Ξ') Θ0);
        [ repeat apply all_flex_mono_app; assumption
        | simpl_env; clear - HuqAll; solve_uniq
        | exact HwfΘ0 ]. }
    split.
    { apply all_flex_mono_decls. repeat apply all_flex_mono_app; assumption. }
    split; [ rewrite ! keys_app; rewrite Hkeysc, Hks, Hkeys'; reflexivity | ].
    split.
    { apply (@a_inc_flex_prefix_build (Ξc ++ Ξs ++ Ξ') (κc ++ κs ++ κ') Θ0 κ Θ);
        [ repeat apply all_flex_mono_app; assumption
        | rewrite ! keys_app; rewrite Hkeysc, Hks, Hkeys'; reflexivity
        | repeat (apply Forall_app; split); assumption
        | exact Hκ ]. }
    split; [ exact Heqv | ].
    (* the ONE reorder on the metasubstitution side: §9 built [κ',κs,κc,κ],
       [a_extract] wants [κc,κs,κ',κ]; the blocks are pairwise apart, so it is
       a lookup-level identity *)
    assert (Hd'c : forall β0, β0 `in` dom κ' -> β0 `notin` dom κc)
      by (intros β0 Hβ0;
          assert (Hin : β0 `in` dom Ξ') by (clear - Hβ0 HdomΞ'; fsetdec);
          specialize (Hfr' β0 Hin); clear - Hfr' Hdc; fsetdec).
    assert (Hd's : forall β0, β0 `in` dom κ' -> β0 `notin` dom κs)
      by (intros β0 Hβ0;
          assert (Hin : β0 `in` dom Ξ') by (clear - Hβ0 HdomΞ'; fsetdec);
          specialize (Hfr' β0 Hin); clear - Hfr' Hds; fsetdec).
    assert (Hdc' : forall β0, β0 `in` dom κc -> β0 `notin` dom κ')
      by (intros β0 Hβ0 Hc; exact (Hd'c β0 Hc Hβ0)).
    assert (Hperm : msubst_pskl ((κc ++ κs ++ κ') ++ κ) (ptyp_to_pskl A)
                  = msubst_pskl (κ' ++ κs ++ κc ++ κ) (ptyp_to_pskl A)).
    { rewrite (list_app_assoc κc (κs ++ κ') κ).
      rewrite (list_app_assoc κs κ' κ).
      apply msubst_pskl_lookup_congr. intro β0.
      (* bring BOTH sides to a common [κs] head, then peel and swap once *)
      rewrite (@msubst_lookup_app_swap κc κs (κ' ++ κ) β0 Hdcs).
      rewrite (@msubst_lookup_app_swap κ' κs (κc ++ κ) β0 Hd's).
      apply msubst_lookup_app_agree.
      apply (@msubst_lookup_app_swap κc κ' κ β0 Hdc'). }
    rewrite Hperm. exact Hpr'.
  - (* ================================ SK ============================== *)
    (* [a_guess__sk] : Ξ' = ·, Q' = Q, so κ' = · and every conclusion is
       P6-Ss's verbatim — modulo the SOLVE's own block, which stays *)
    exists (Ξc ++ Ξs ++ nil), Pa, (κc ++ κs ++ nil).
    split.
    { eapply a_extract__solve;
        [ exact Hlook | exact Hsolve | apply a_guess__sk
        | apply inter_dom_empty_of_forall; exact Hapart
        (* the SK guess generates nothing *)
        | simpl; clear; fsetdec ]. }
    (* only NOW may the empty guess block be absorbed — [a_extract__solve]'s
       conclusion is [Ξ ++ Ξs ++ Ξ'], which no longer unifies once it is gone *)
    rewrite ! app_nil_r.
    split.
    { eapply a_wf_pskl_weaken; [ | exact HwfPa ].
      intros x b Hb. simpl_env. analyze_binds Hb. }
    split.
    { apply (@a_wf_aenv_flex_prefix (Ξc ++ Ξs) Θ0);
        [ apply all_flex_mono_app; assumption
        | simpl_env; clear - HuqΞsc; solve_uniq
        | exact HwfΘ0 ]. }
    split; [ apply all_flex_mono_decls; apply all_flex_mono_app; assumption | ].
    split; [ rewrite ! keys_app; rewrite Hkeysc, Hks; reflexivity | ].
    split.
    { apply (@a_inc_flex_prefix_build (Ξc ++ Ξs) (κc ++ κs) Θ0 κ Θ);
        [ apply all_flex_mono_app; assumption
        | rewrite ! keys_app; rewrite Hkeysc, Hks; reflexivity
        | apply Forall_app; split; assumption
        | exact Hκ ]. }
    split; [ exact Heqv | ].
    rewrite (list_app_assoc κc κs κ).
    rewrite (@msubst_pskl_app_swap κc κs κ Pa Hdcs).
    exact Hpre.
Qed.

(** P6-L — THE PAPER'S STATEMENT ([lemma:complete-look]): the ambient tag
    context [Ψsub] of [a_extract_complete_gen] at its smallest, [Ψa].  The
    remaining premises are the paper's own EXTERNAL well-formedness side
    conditions (docs/WF-SIDE-CONDITIONS.md), and α's freshness is
    Barendregt. *)
Corollary a_extract_complete :
  forall n NM M Θ0 Θ κ Ψa ψa Q P P0 R' α,
  {{ ⊢ Θ }}a -> {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  κ ∷ Θ0 ⊑ Θ ->
  α `notin` dom Θ -> α `notin` dom Θ0 ->
  ⌊ R' ⌋ˢ = P ->
  ftvar_in_uskl R' [<=] add α (dom Θ0 `union` dom Θ) ->
  lc_uskl R' ->
  a_tags_sort NM Ψa ψa ->
  (ftag_in_uskl R') ∩ Ψa [=] empty ->
  (* ⭐ THE IDEAL GUESS IS Θ-SCOPED (2026-08-05, the SolE-FlexR repair).
     [paper-external wf side condition — docs/WF-SIDE-CONDITIONS.md] *)
  ftvar_in_uskl ψa [<=] dom Θ ->
  {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψa ⌋ˢ }}a ->
  ad_pat_sub_fuel n NM M Ψa Θ
    (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R')) Q ->
  {{ Θ ⨟ empty ⊢ₚₛ
    (uskl_to_pskl (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R'))) }}a ->
  {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
  (* the counterpart is well formed — the paper's presupposition
     (declarative.tex:2074); docs/WF-SIDE-CONDITIONS.md §2a *)
  {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
  exists Ξ Pa κa,
    ({{ Θ0 ⊢ P ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ Pa }}a) /\
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ Pa }}a /\
    {{ ⊢ (Ξ ++ Θ0) }}a /\
    a_decls Ξ /\
    keys κa = keys Ξ /\
    (κa ++ κ) ∷ (Ξ ++ Θ0) ⊑ Θ /\
    a_inc_equiv Θ0 κ κ Θ /\
    {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl (κa ++ κ) Pa) ⊑ ⌊ ψa ⌋ˢ }}ad.
Proof.
  intros n NM M Θ0 Θ κ Ψa ψa Q P P0 R' α.
  intros HwfΘ HwfΘ0 HwfP0 HmodSK HmodTY Hκ HαΘ HαΘ0 HeraseR HscopeR HlcR
         Htags Hdisj Hψaw Hwfψ Hsubty HwfSubj Hrefine HwfQ.
  eapply a_extract_complete_gen with (Ψsub := Ψa);
    [ exact HwfΘ | exact HwfΘ0 | exact HwfP0 | exact HmodSK | exact HmodTY
    | exact Hκ | exact HαΘ | exact HαΘ0 | exact HeraseR | exact HscopeR
    | exact HlcR | exact Htags | exact Hdisj
    | exact Hψaw
    | exact Hwfψ
    | clear; fsetdec | clear; fsetdec                (* Ψsub := Ψa *)
    | exact Hsubty | exact HwfSubj | exact Hrefine | exact HwfQ ].
Qed.

(* ===================================================================== *)
(*  Sub-ForallL item 4 — [a_sub__forall_l]'s extract family from the ONE   *)
(*  instance P6-L produces.  The look's outputs (Ξ ⨾ 𝒞) never mention the  *)
(*  looked variable and the solve/guess components do not see it at all,   *)
(*  so the family is the renamed look ([a_looksub_rename_var]) + the SAME  *)
(*  solve + the SAME guess.                                               *)
(*                                                                        *)
(* ===================================================================== *)
