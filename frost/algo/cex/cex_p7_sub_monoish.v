(** ⚠️ THE SUBTYPING-SIDE ANALOGUE OF [ad_pat_consis_monoish_counterpart] IS
    FALSE — SO P7's PLANNED ROUTE FOR SUPPLYING [sub_shield] DOES NOT WORK AS
    SKETCHED.  [ad_pat_sub_g__forall_l_tagged] is the culprit again.

    docs/DESIGN-completeness-subtyping.md §9.0 registered P7's TASK 0: P7b's
    Sub-ForallL case is the sole consumer of P6-L, and P6-L carries the
    P6-Sv/P6-Ss repair premise [sub_shield Θ0 Ψa empty P0 ψa], which P7 must
    SUPPLY (the paper's P6-Sv WITHOUT it is false — cex_p6sv_forall_flex.v).
    The route recorded there (and in §6 (z) item 3) was: at a flexible position
    of P0 the metasubstitution's image is a MONOTYPE, so the refinement premise
    makes the facing part of Q MONO-ISH ([ad_refine_mono_paint_rhs_monoish],
    Qed), and then the consistency-side

        Ψs ⨟ Θ ⊢ₛᵃ ψ ∼ Q  →  is_tskl ψ  →  bskl_monoish Q
          →  Ψs = ∅  ∧  ψ is a mono PAINT               ([ad_pat_consis_monoish_counterpart])

    would give tag-freeness of the facing ψa-region, i.e. [fsh_clean].  The plan
    said the missing piece was "one [ad_pat_sub_g] analogue" of that lemma.

    THERE IS NO SUCH ANALOGUE.  Consistency's ∀ rules all require the
    COUNTERPART to be a quantifier too, which is why a mono-ish counterpart
    forces the subject mono there.  Subtyping's ForallL does not: it
    INSTANTIATES, so a tagged-∀ subject can face a mono-ish counterpart
    directly.  Below, [∀^ε α. α] — which IS [is_tskl], and ghost-free, so
    legal at [a_sub_mode_ty] — is instantiated with the context's rigid [β]
    and lands on the target [β], which is [bskl_monoish] by [bmi_var].  The
    subject is not a mono paint (a mono paint is unit / var / arrow; it is
    never a [uskl_all_etag]), so the conclusion fails outright.

    WHAT THIS DOES AND DOES NOT SETTLE.  It does NOT refute the shield supply
    itself — only the monoish route to it.  Unfolding [sub_shield] at Δρ = ∅,
    the hard leaf is a RAW Θ0-FLEXIBLE position of P0, where the only
    applicable [flex_shield] rule is [fsh_clean], whose
    [ftag ψa ∩ Ψa = ∅] plus [d_tags_skl]'s [Ψa ⊆ ftag ψa] forces **Ψa = ∅**:
    the ForallL guess must be TAG-FREE, i.e. (with [a_tags_sort]'s
    ghost-freeness at TY) a MONOTYPE.  So the real obligation is the
    flex-mono WALL stated directly —

        a raw-Θ0-flexible position of P0 forces the ForallL guess facing it
        to be a monotype

    — and NOT a "monoish counterpart" argument about the subject.  ⚠️ That wall
    currently rests on an AUTHOR DECISION recorded against an IMPLEMENTATION
    CRASH (docs/PAPER-GAPS.md, "broom_flex_poly: should not happen"), not
    against a proof.  See DESIGN §9.0.

    This is the same shape of finding as cex_p6ss_sub_target_ftv.v — indeed the
    very same witness derivation — and for the same reason: [is_tskl] excludes
    every ghost row of [ad_pat_sub_g] but NOT [__forall_l_tagged]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.def_tags.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.algo.prop_look_complete.   (* bskl_monoish *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  The witness — one rigid β, one instantiation tag ε                     *)
(* ===================================================================== *)

Section CexP7SubMonoish.

Variables β ε : atom.

Definition Θw : aenv := (β ~ abind_tvar) ++ nil.

(** Subject: the decorated identity quantifier [∀^ε α. α]. *)
Definition Rw : uskl := uskl_all_etag ε (uskl_var_b 0).

(** Counterpart: the context's rigid — and a variable IS mono-ish. *)
Definition Qw : bskl := bskl_var_f β.

Lemma Θw_wf : a_wf_aenv Θw.
Proof. apply a_wf_aenv__tvar; [ simpl; auto | apply a_wf_aenv__nil ]. Qed.

Lemma Rw_tskl : is_tskl Rw.
Proof.
  apply is_tskl__all_etag with (L := empty); intros α _; cbn.
  apply is_tskl__var.
Qed.

Lemma Qw_monoish : bskl_monoish Qw.
Proof. apply bmi_var. Qed.

(** The guess ForallL instantiates with: the rigid β itself — a legitimate
    instantiation (decorated, TAG-FREE, ghost-free, Θ-scoped). *)
Lemma guess_tags_sort : a_tags_sort a_sub_mode_ty empty (uskl_var_f β).
Proof.
  apply a_tags_sort__ty;
    [ apply is_tskl__var
    | apply d_tags_skl__var; clear; fsetdec
    | apply uskl_ghost_free__var ].
Qed.

Lemma guess_wf : Θw ⨟ empty ⊢ₚₛᵃ ⌊ uskl_var_f β ⌋ˢ.
Proof. cbn. apply a_wf_pskl__var. right. left. simpl; auto. Qed.

(** The derivation: ForallL (tagged) instantiates with β, and the premise is
    the Check leaf, whose consistency is the plain variable rule. *)
Lemma cex_derivation :
  ad_pat_sub_g 1 a_sub_mode_ty mode_tc empty Θw Rw Qw.
Proof.
  unfold Rw, Qw, Θw.
  apply ad_pat_sub_g__forall_l_tagged
    with (Ψ' := empty) (ψ := uskl_var_f β).
  - intro Hc; discriminate Hc.
  - clear; fsetdec.
  - clear; fsetdec.
  - apply guess_tags_sort.
  - apply guess_wf.
  - cbn [open_uskl_wrt_uskl open_uskl_wrt_uskl_rec].
    change (bskl_var_f β) with (pskl_to_bskl_inh (pskl_var_f β)).
    apply ad_pat_sub_g__check;
      [ apply guarded_uskl__var | apply guarded_pskl__var | ].
    cbn. apply ad_pat_consis__var; [ clear; fsetdec | left; simpl; auto ].
Qed.

(** A [uskl_all_etag] is never a monotype's painting — mono paints are
    unit / var / arrow, by [mono_ptyp]'s three constructors. *)
Lemma cex_not_a_mono_paint :
  ~ (exists τ, mono_ptyp τ /\ Rw = ptyp_to_uskl_syn τ).
Proof.
  unfold Rw. intros (τ & Hm & Heq).
  destruct Hm; cbn in Heq; discriminate Heq.
Qed.

End CexP7SubMonoish.

(* ===================================================================== *)
(*  The refutation                                                        *)
(* ===================================================================== *)

(** THE SUB-SIDE MONOISH-COUNTERPART LEMMA IS FALSE, even with [is_tskl] on
    the subject and [a_wf_aenv] on the context — so P7's TASK 0 needs the
    flex-mono wall stated directly, not this route. *)
Theorem p7_sub_monoish_counterpart_is_false :
  ~ (forall n NM M Ψ Θ ψ Q,
       ad_pat_sub_g n NM M Ψ Θ ψ Q ->
       a_wf_aenv Θ ->
       is_tskl ψ ->
       bskl_monoish Q ->
       Ψ [=] empty /\ exists τ, mono_ptyp τ /\ ψ = ptyp_to_uskl_syn τ).
Proof.
  intro Hall.
  (* two distinct atoms: the rigid β and the instantiation tag ε *)
  pick fresh β. pick fresh ε.
  (* NB [Section]-discharge gives each lemma only the variables it USES:
     Θw / Qw depend on β alone, Rw on ε alone. *)
  apply (@cex_not_a_mono_paint ε).
  refine (proj2 (Hall _ _ _ _ _ _ _ (cex_derivation β ε) (Θw_wf β)
                   (Rw_tskl ε) (Qw_monoish β))).
Qed.

Print Assumptions p7_sub_monoish_counterpart_is_false.

(** NB the conclusion's OTHER conjunct ([Ψ = ∅]) happens to hold here — the
    witness runs at Ψ = ∅ — so the falsity is squarely in the "the subject is
    a mono paint" half.  Strengthening the statement to demand only [Ψ = ∅]
    would survive this witness but is USELESS for the shield: [fsh_clean]
    needs tag-freeness of ψa itself, and [__forall_l_tagged] drops its own ε
    from the conclusion's Ψ (conclusion [Ψ], premise [Ψ ∪ Ψ']), so a small
    conclusion-Ψ says nothing about [ftag ψa]. *)
