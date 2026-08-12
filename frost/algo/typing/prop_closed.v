(** THE CLOSED-PROGRAM COROLLARIES of the two section-D typing theorems —
    the form a reader of the paper wants, and the only thing in this
    directory that is not machinery.

    At the EMPTY context a typing problem's input can only be in one of the
    two user-facing modes — INFERENCE, whose input is the ghost [□], and
    CHECKING, whose input is a closed type — so each flagship splits in two,
    and the premises that are bookkeeping at a general context disappear.
    What is left is stated in [README.v] and nothing else in the development
    consumes it.

    ⭐ SOUNDNESS reads the paper's own §declarative system on the declarative
    side ([d_sd_typing] and [d_typing] over a DECLARATIVE context), through
    the conservativity bridge [prop_conserv.v] — the prose-completion of
    app:decl-in-algo-context's "it is easy to extend them to algorithmic
    contexts Θ", which the paper asserts and never states.

    ⭕ COMPLETENESS still reads [ad_sd_typing] over [nil : aenv]: it needs the
    OTHER direction of the bridge, which is blocked twice over — the base
    rows' LEAF-VALID join is not recoverable from the plain [d_sub] at a
    ghosty subject (cex/cex_ad_pat_join_not_leaf_valid.v), and the mirrors'
    ForallL rows demand a tag hygiene the declarative rules state only
    against the tag context.  Both are analysed at prop_conserv.v §12; the
    routes are in docs/HANDOFF-closed-corollaries-declarative.md. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.def_meta.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.algo_decl.def_subtyping.
Require Import src.frost.algo_decl.def_typing.
Require Import src.frost.algo_decl.prop_ctx_mono.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_inc_strengthen.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.sub.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.sub.prop_completeness_sub_gen.
Require Import src.frost.algo.sub.prop_completeness_sub.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.consis.prop_consis_rename.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.prop_wf_preservation.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Require Import src.frost.algo.sub.prop_soundness_subtag.
Require Import src.frost.algo.pat.prop_soundness_pat.
Require Import src.frost.algo.prop_suffix_erase.
Require Import src.frost.algo.typing.prop_soundness_typing.
Require Import src.frost.algo.prop_precise_sub.
Require Import src.frost.algo.pat.prop_completeness_pat.
Require Import src.frost.algo.typing.prop_rigidity.
Require Import src.frost.algo.typing.prop_shape.
Require Import src.frost.algo.typing.prop_scope.
Require Import src.frost.algo.typing.prop_completeness_typing.
Require Import src.frost.algo_decl.prop_conserv.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_syntax_directed.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §14  THE CLOSED-PROGRAM COROLLARIES.                                  *)
(*                                                                        *)
(*  At the EMPTY context the input can only be in one of the two          *)
(*  user-facing modes — INFERENCE, whose input is the ghost [□], and      *)
(*  CHECKING, whose input is a closed type [⌈A0⌉] — so each flagship      *)
(*  splits into two, and three premises go with the split: [{{ ⊢ · }}a]  *)
(*  is a constructor, [{{ · ⨟ ∅ ⊢ₚₛ P0 }}a] is [a_wf_pskl__hole] resp. the *)
(*  annotation's own wf, and [a_ty_mode_compat] is read off the shape.    *)
(*                                                                        *)
(*  ⭐ COMPLETENESS needs NO condition on the term at all.  Since          *)
(*  [ad_sd_typing__anno] carries [a_wf_ptyp Θ A] (like its four           *)
(*  type-carrying siblings), a declarative derivation EXHIBITS its own    *)
(*  subject as well formed — [ad_sd_typing_wf_exp] — so at the empty      *)
(*  context "[e] is closed" is a theorem, not a hypothesis.               *)
(*                                                                        *)
(*  ⚠️ SOUNDNESS still asks for it, as [{{ · ⊢ᵉ e }}a].  It is an INPUT     *)
(*  condition on the problem (the paper's "M is well-formed in Θ₀") and   *)
(*  the algorithmic run does NOT imply it: [a_typing__abs] runs the body  *)
(*  under the flexibles [guess^TY] just invented, and nothing stops a     *)
(*  nested annotation from mentioning one, so a run can accept a term     *)
(*  whose type variables are not those of its INPUT context.              *)
(* ===================================================================== *)

(** The shared soundness engine at the empty context: peel [a_typing_sound]'s
    existential, read the answer's colouring off the mode, and CLOSE the run's
    output context.  What comes back is the run's answer [A] with its residual
    flexibles instantiated by a metasubstitution [ζ] into [·], and the paper's
    PURELY DECLARATIVE typing of [e] at that closed answer. *)
Lemma a_typing_sound_nil : forall m P0 e A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat m P0 ->
  {{ nil ⊢[ m ; P0 ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  exists Bt, btyp_to_ptyp Bt = A /\ mod_comp_ty Bt m /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl Bt) }}ad) /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ msubst_mono ζ /\
      ({{ nil ⊢ˢᵈ[ m ] e ⦂ (msubst_btyp ζ Bt) }}d) /\
      ({{ nil ⊢[ m ] e ⦂ (msubst_btyp ζ Bt) }}d).
Proof.
  intros m P0 e A Θ1 Hexp HwfP0 Hmod Hrun.
  destruct (a_typing_sound Hrun a_wf_aenv__nil HwfP0 Hmod Hexp)
    as [Hisub [Hwf1 [HwfA [Bt [HBt [Hd Href]]]]]].
  split; [ exact Hisub | ]. split; [ exact Hwf1 | ]. split; [ exact HwfA | ].
  exists Bt. split; [ exact HBt | ].
  split; [ exact (ad_sd_typing_mod_comp_ty Hd Hwf1) | ]. split; [ exact Href | ].
  (* the run started at [·], so its output context is a pure SUFFIX *)
  assert (Hsuf : a_suffix Θ1)
    by (destruct Hisub as [[κ [_ Hinc]] _]; exact (a_inc_nil_suffix κ Θ1 Hinc)).
  assert (Hftv : ftvar_in_exp e [<=] empty)
    by (pose proof (a_wf_exp_ftv_dom Hexp) as Hx; simpl in Hx; exact Hx).
  destruct (ad_sd_typing_close_suffix Θ1 Hsuf Hwf1 m e Bt Hd Hftv)
    as [ζ [Hinc [Hmo [_ Hdnil]]]].
  exists ζ. split; [ exact Hinc | ]. split; [ exact Hmo | ].
  assert (Hsd : {{ nil ⊢ˢᵈ[ m ] e ⦂ (msubst_btyp ζ Bt) }}d)
    by exact (ad_sd_typing_to_d m nil e (msubst_btyp ζ Bt) Hdnil nil eq_refl).
  split; [ exact Hsd | apply d_sd_typing_sound; exact Hsd ].
Qed.

(** ⭐ Soundness at a closed program, INFERENCE mode (input the ghost [□]).
    (thm:sound-type-inference)  The answer's colouring is forced at [TI], so
    the general statement's existential [Bt] is [syn{A}] and disappears. *)
Corollary a_typing_sound_infer : forall e A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_ti ; pskl_hole ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  ({{ Θ1 ⨟ empty ⊢ᵣ bskl_hole ⊳ (btyp_to_bskl (ptyp_to_btyp_syn A)) }}ad) /\
  exists ζ, ζ ∷ Θ1 ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ A)) }}d) /\
    ({{ nil ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ A)) }}d).
Proof.
  intros e A Θ1 Hexp Hrun.
  destruct (a_typing_sound_nil Hexp (a_wf_pskl__hole _ _)
              a_ty_mode_compat__ti Hrun)
    as [Hisub [Hwf1 [HwfA [Bt [HBt [Hmc [Href [ζ [Hinc [Hmo [Hsd Hty]]]]]]]]]]].
  (* at [TI] the answer is a SYNTHESISED painting, so [Bt = syn{A}] *)
  assert (HBteq : Bt = ptyp_to_btyp_syn A)
    by (rewrite <- HBt; apply btyp_syn_colouring_inv;
        apply mod_comp_ty_ti_inv; exact Hmc).
  subst Bt. rewrite msubst_btyp_ptyp_to_btyp_syn in Hsd, Hty.
  split; [ exact Hisub | ]. split; [ exact Hwf1 | ]. split; [ exact HwfA | ].
  split; [ exact Href | ]. exists ζ. split; [ exact Hinc | ].
  split; [ exact Hsd | exact Hty ].
Qed.

(** ⭐ Soundness at a closed program, CHECKING mode (input a closed type).
    At [TC] the colouring is forced the other way, so [Bt = inh{A}]. *)
Corollary a_typing_sound_check : forall e A0 A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  a_wf_ptyp nil A0 ->
  {{ nil ⊢[ mode_tc ; (ptyp_to_pskl A0) ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl A0))
     ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A)) }}ad) /\
  exists ζ, ζ ∷ Θ1 ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ A)) }}d) /\
    ({{ nil ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ A)) }}d).
Proof.
  intros e A0 A Θ1 Hexp HwfA0 Hrun.
  destruct (a_typing_sound_nil Hexp (a_wf_ptyp_to_wf_pskl empty HwfA0)
              (a_ty_mode_compat__tc A0) Hrun)
    as [Hisub [Hwf1 [HwfA [Bt [HBt [Hmc [Href [ζ [Hinc [Hmo [Hsd Hty]]]]]]]]]]].
  assert (HBteq : Bt = ptyp_to_btyp_inh A)
    by (rewrite <- HBt; apply btyp_inh_painting_inv;
        apply mod_comp_ty_tc_inv; exact Hmc).
  subst Bt. rewrite (msubst_btyp_ptyp_to_btyp_inh ζ A Hmo) in Hsd, Hty.
  split; [ exact Hisub | ]. split; [ exact Hwf1 | ]. split; [ exact HwfA | ].
  split; [ exact Href | ]. exists ζ. split; [ exact Hinc | ].
  split; [ exact Hsd | exact Hty ].
Qed.

(** The shared completeness engine.  ⭐ [κ ∷ · ⊑ ·] holds at [κ = ·]
    ([a_inc__empty]), so no metasubstitution is quantified; the term's
    closedness is read off the derivation ([ad_sd_typing_wf_exp]); and the
    optimality is applied at the identity increase SOUNDNESS hands back, so
    what comes out is the readable "the answer, closed off by ζ, IS the
    declarative type". *)
Lemma a_typing_complete_nil : forall m P0 e (B : btyp),
  {{ nil ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat m P0 ->
  {{ nil ⊢ˢᵈ[ m ] e ⦂ B }}ad ->
  {{ nil ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl B) }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ m ; P0 ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros m P0 e B HwfP0 Hmod Hd Href.
  pose proof (ad_sd_typing_wf_exp Hd) as Hexp.
  pose proof (a_wf_exp_lc Hexp) as Hlc.
  pose proof (a_wf_exp_ftv_dom Hexp) as Hftv. simpl in Hftv.
  assert (Hrig : forall α, α `in` ftvar_in_exp e -> binds α abind_tvar nil)
    by (intros α Hα; exfalso; clear - Hα Hftv; fsetdec).
  assert (Hinc : nil ∷ nil ⊑ nil)
    by (apply a_inc__empty; apply a_suffix__nil).
  rewrite <- (msubst_pskl_nil P0) in Href.
  destruct (a_typing_complete a_wf_aenv__nil a_wf_aenv__nil HwfP0 Hmod
              Hinc Hrig Hlc Hd Href) as [A1 [Θ1 [Hrun Hopt]]].
  exists A1, Θ1. split; [ exact Hrun | ].
  destruct (a_typing_sound Hrun a_wf_aenv__nil HwfP0 Hmod Hexp)
    as [[[κ1 [Hid1 Hinc1]] _] _].
  destruct (Hopt κ1 Hid1 Hinc1) as [ζ [Hζ [_ Heq]]].
  exists ζ. split; [ exact Hζ | exact Heq ].
Qed.

(** ⭐ Completeness + optimality at a closed program, INFERENCE mode
    (thm:complete-type-inference).  ⭐ The general statement's refinement
    premise is GONE here too: at [P0 = □] it says only that the declarative
    result is a SYNTHESISED painting of a well-formed type, and both halves
    are read off the derivation itself ([ad_sd_typing_mod_comp_ty] +
    [ad_sd_typing_target_wf]).  So the derivation is the ONLY premise. *)
Corollary a_typing_complete_infer : forall e (B : btyp),
  {{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ B }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_hole ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hd.
  eapply a_typing_complete_nil;
    [ apply a_wf_pskl__hole | apply a_ty_mode_compat__ti | exact Hd | ].
  (* the ghost refines into ANY well-formed synthesised painting *)
  assert (HB : B = ptyp_to_btyp_syn (btyp_to_ptyp B)).
  { apply btyp_syn_colouring_inv. apply mod_comp_ty_ti_inv.
    eapply ad_sd_typing_mod_comp_ty; [ exact Hd | apply a_wf_aenv__nil ]. }
  rewrite HB, btyp_to_bskl_ptyp_to_btyp_syn. cbn [pskl_to_bskl_inh].
  apply ad_refine_syn__hole. apply a_wf_ptyp_to_wf_pskl.
  eapply ad_sd_typing_target_wf; [ exact Hd | apply a_wf_aenv__nil ].
Qed.

(** ⭐ Completeness + optimality at a closed program, CHECKING mode.  ⭐ The
    checked type is the DECLARATIVE RESULT itself — at [TC] the colouring is
    forced ([mod_comp_ty_tc_inv] + [btyp_inh_painting_inv]), so the general
    statement's refinement premise at an arbitrary annotation [A0] is
    REFLEXIVITY at [⌊B⌋], and [A0] can go with it.  Nothing is lost at the
    empty context: refinement of a GHOST-FREE painting can only take the
    structural rows there — the two flexible rows need a definition in the
    context, and [·] has none — so [inh{A0} ⊳ ⌊B⌋] forces [A0 = ⌊B⌋] anyway.
    Like the inference twin, the derivation is the ONLY premise. *)
Corollary a_typing_complete_check : forall e (B : btyp),
  {{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ B }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hd.
  assert (HwfB : a_wf_ptyp nil (btyp_to_ptyp B))
    by (eapply ad_sd_typing_target_wf; [ exact Hd | apply a_wf_aenv__nil ]).
  eapply a_typing_complete_nil;
    [ apply a_wf_ptyp_to_wf_pskl; exact HwfB | apply a_ty_mode_compat__tc
    | exact Hd | ].
  (* at TC the colouring is forced, so the refinement is REFLEXIVITY *)
  assert (HB : B = ptyp_to_btyp_inh (btyp_to_ptyp B)).
  { apply btyp_inh_painting_inv. apply mod_comp_ty_tc_inv.
    eapply ad_sd_typing_mod_comp_ty; [ exact Hd | apply a_wf_aenv__nil ]. }
  replace (btyp_to_bskl B)
    with (btyp_to_bskl (ptyp_to_btyp_inh (btyp_to_ptyp B)))
    by (rewrite <- HB; reflexivity).
  rewrite <- pskl_to_bskl_inh_ptyp.
  apply ad_refine_syn_refl_inh. apply a_wf_ptyp_to_wf_pskl. exact HwfB.
Qed.

(* ===================================================================== *)
(*  ⭐ THE COMPLETENESS COROLLARIES OVER THE PAPER'S OWN DECLARATIVE       *)
(*  SYSTEM.                                                               *)
(*                                                                        *)
(*  The two corollaries above read the decl-in-algo judgement [{{ … }}ad], which *)
(*  a reader of the paper's §declarative figure has never met.  These read *)
(*  [⊢ˢ] and [⊢], matching what the SOUNDNESS corollaries already deliver, *)
(*  so soundness and completeness now meet on the same judgement.         *)
(*                                                                        *)
(*  ⚙ What made this possible: [d_sd_typing_to_ad]                        *)
(*  (algo_decl/prop_conserv.v §15) is unconditional since 2026-08-11, *)
(*  when [d_pat_sub] / [d_pat] took on the two presuppositions the paper   *)
(*  states in prose and the mechanisation had deferred (declarative.tex:   *)
(*  2074 and :1595).  Before that the bridge carried a hypothesis that was *)
(*  provably FALSE, so it said nothing.  docs/ghost-capture.tex.           *)
(*                                                                        *)
(*  ⚠️ [{{ nil ⊢ᵉ e }}a] is a real premise here, not bookkeeping, and it is  *)
(*  the SAME one the soundness corollaries take.  On the [ad] side it was  *)
(*  free ([ad_sd_typing_wf_exp]); on the declarative side it is not,       *)
(*  because [d_sd_typing__anno] states no well-formedness for its          *)
(*  annotation — the [sd-Anno] gap, docs/PAPER-GAPS.md.                    *)
(* ===================================================================== *)

(** ⭐ Completeness + optimality at a closed program, INFERENCE mode, stated
    over the paper's syntax-directed declarative judgement. *)
Corollary a_typing_complete_sd_infer : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_hole ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hwfe Hd.
  apply a_typing_complete_infer.
  exact (d_sd_typing_to_ad mode_ti nil e B Hd d_wf_denv__nil Hwfe).
Qed.

Corollary a_typing_complete_sd_check : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hwfe Hd.
  apply a_typing_complete_check.
  exact (d_sd_typing_to_ad mode_tc nil e B Hd d_wf_denv__nil Hwfe).
Qed.

(** …and over the ORIGINAL declarative judgement [⊢], through
    [d_sd_typing_complete] (the syntax-directed system is complete for it). *)
Corollary a_typing_complete_decl_infer : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_hole ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hwfe Hd.
  apply a_typing_complete_sd_infer;
    [ exact Hwfe | apply d_sd_typing_complete; [ exact Hd | apply d_wf_denv__nil ] ].
Qed.

Corollary a_typing_complete_decl_check : forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_tc ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Proof.
  intros e B Hwfe Hd.
  apply a_typing_complete_sd_check;
    [ exact Hwfe | apply d_sd_typing_complete; [ exact Hd | apply d_wf_denv__nil ] ].
Qed.
