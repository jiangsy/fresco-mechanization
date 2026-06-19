(** Frost — declarative skeleton metatheory for the split syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.

Set Implicit Arguments.

(** * Splitting / inversion lemmas for refinement.

    Only the coloured refinement relation [d_refine_syn] remains; the
    former uncoloured [d_refine] split lemmas were removed with it. *)


(* No [tophole] split lemma: a universal ghost [⫯] now refines by three
   rules (remove / fill-with-∀α / keep), so the output is not uniquely a
   [bskl_tophole].  Invert [d_refine_syn] directly where needed. *)

(** Refinement preserves well-formedness (paper "Refinement preserves
    well-formedness", declarative.tex).  The two skeleton-scope contexts
    of refinement — [Δs] (syn-quantifier vars) and [Δi] (inh-quantifier
    vars) — collapse, on the colour-erased [pskl] output, into the single
    [d_wf_pskl] scope set [Ψ := Δs ++ Δi] (colours do not affect skeleton
    well-formedness, so both kinds of ∀-bound var live in the one [Ψ]).
    The three-context refinement (which clears [Δs] under a kept [TopHole]
    and [Δi] at [Hole]-fills) is exactly what guarantees the colour-erased
    output is [d_wf_pskl]; with the old "syn var dumped into [Γ]"
    encoding this lemma was false (e.g. [⫯.(□→unit)] refined to
    [∀^syn α.⫯.(α→unit)], which is not well-formed).

    Each [TopHole] / [Hole] rule clears some context, so its premise's
    IH yields wf at a [Ψ] that is a *subset* of the one the conclusion
    needs; we close the gap with [d_wf_pskl_Psi_mono] (monotone in [Ψ]). *)
Lemma d_refine_preserves_wf : forall Γ Δs Δi Q P,
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P ->
    (Δs ++ Δi) ⨟ Γ ⊢ₚₛ (bskl_to_pskl P).
Proof.
  intros Γ Δs Δi Q P H. induction H; simpl.
  - (* unit *) constructor.
  - (* var *) constructor.
    destruct H as [HS | [HI | HG]].
    + left. apply in_or_app; auto.
    + left. apply in_or_app; auto.
    + right; auto.
  - (* arrow *) constructor; auto.
  - (* all (inh): bound var joins Δi; wf Ψ gains it under the binder.
       [d_wf_pskl_Psi_mono] leaves the wf premise first, the [Ψ ⊆ Ψ'] last. *)
    inst_cofinites_for d_wf_pskl__all. intros X HX.
    rewrite <- bskl_to_pskl_open.
    apply d_wf_pskl_Psi_mono with (Ψ := Δs ++ (X :: Δi)); [ apply H0; auto | ].
    intros Y HY. simpl. rewrite in_app_iff in *. simpl in HY |- *. tauto.
  - (* hole: fill is wf with Ψ := Δs; weaken to Δs ++ Δi *)
    rewrite bskl_to_pskl_pskl_to_bskl_syn.
    apply d_wf_pskl_Psi_mono with (Ψ := Δs); [ assumption | ].
    intros Y HY. rewrite in_app_iff. tauto.
  - (* tophole_remove: keeps Δs, clears Δi; IH gives Ψ := Δs ++ nil *)
    apply d_wf_pskl_Psi_mono with (Ψ := Δs ++ nil); [ assumption | ].
    intros Y HY. rewrite in_app_iff in *. simpl in HY. tauto.
  - (* tophole_fill: output ∀^syn; body wf with Ψ := (X :: Δs) ++ nil *)
    inst_cofinites_for d_wf_pskl__all. intros X HX.
    rewrite <- bskl_to_pskl_open.
    apply d_wf_pskl_Psi_mono with (Ψ := (X :: Δs) ++ nil); [ apply H0; auto | ].
    intros Y HY. simpl. rewrite in_app_iff in *. simpl in HY |- *. tauto.
  - (* tophole_keep: output ⫯; clears both; guarded + wf-under-nil *)
    apply d_wf_pskl__tophole.
    + apply guarded_bskl_to_pskl; auto.
    + apply d_wf_pskl_Psi_mono with (Ψ := nil ++ nil); [ assumption | ].
      intros Y HY. inversion HY.
Qed.

(** A well-scoped type's skeleton is a well-formed [pskl].  ([ptyp_to_pskl]
    images are ghost-free, so a scope-coverage premise lets the [∀] case
    route the bound var into [Ψ].) *)
Lemma d_wf_pskl_of_ptyp : forall A,
    lc_ptyp A ->
    forall Γ Ψ,
      (forall X, X `in` ftvar_in_ptyp A -> List.In X Ψ \/ binds X dbind_tvar Γ) ->
      Ψ ⨟ Γ ⊢ₚₛ (ptyp_to_pskl A).
Proof.
  intros A Hlc. induction Hlc; intros Γ Ψ Hcov; simpl.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. apply Hcov. simpl. fsetdec.
  - apply d_wf_pskl__arrow;
      [ apply IHHlc1 | apply IHHlc2 ]; intros Y HY; apply Hcov; simpl; fsetdec.
  - inst_cofinites_for d_wf_pskl__all. intros X HX.
    rewrite <- ptyp_to_pskl_open. apply H0. intros Y HY.
    apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY. simpl in HY.
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + left. apply AtomSetImpl.singleton_1 in HY. simpl. left. assumption.
    + specialize (Hcov Y HY).
      destruct Hcov as [HΨ | HG]; [ left; simpl; right; assumption | right; assumption ].
Qed.

(** UNIVERSAL FILL ENGINE for [d_pat_safety]: a plain ghost [□] refines to
    *any* well-scoped type's syn-skeleton — INCLUDING polytypes, since the
    [hole] rule fills with any well-formed [pskl] (which may carry concrete
    [∀]s).  This is the "fills every checking type" half of safety, once the
    safe inference is hole-rich.  (NB this corrects the misconception that
    [□] fills only monotypes: it is the [inh]-painted target that blocked
    polytypes, not the fill itself — see [d_pat_safety].) *)
Lemma d_refine_syn_hole_fills : forall A,
    lc_ptyp A ->
    forall Γ Δs Δi,
      (forall X, X `in` ftvar_in_ptyp A -> List.In X Δs \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Δs ⨟ Δi ⊢ᵣ bskl_hole ⊳ (pskl_to_bskl_syn (ptyp_to_pskl A)).
Proof.
  intros A Hlc Γ Δs Δi Hcov.
  apply d_refine_syn__hole. eapply d_wf_pskl_of_ptyp; eassumption.
Qed.

(** A universal ghost over a hole [⫯.□] also refines any well-scoped type
    (drop the [⫯] via [tophole_remove], then the [□] fills via the engine).
    Together with [d_refine_syn_hole_fills] this is the full fill side of
    safety: a ghost-rich skeleton refines every checking type. *)
Lemma d_refine_syn_tophole_hole_fills : forall A,
    lc_ptyp A ->
    forall Γ Δs Δi,
      (forall X, X `in` ftvar_in_ptyp A -> binds X dbind_tvar Γ) ->
      Γ ⨟ Δs ⨟ Δi ⊢ᵣ (bskl_tophole bskl_hole) ⊳ (pskl_to_bskl_syn (ptyp_to_pskl A)).
Proof.
  intros A Hlc Γ Δs Δi Hcov.
  apply d_refine_syn__tophole_remove.
  apply d_refine_syn_hole_fills; auto.
Qed.

(** CONSISTENCY REFLEXIVITY for a syn-painted skeleton (on [pskl], so it
    covers BOTH hole-free type skeletons AND skeletons carrying ghost holes
    [pskl_hole]/[pskl_tophole]): the [uskl] erasure of a syn-painted skeleton
    is consistent with that skeleton.  This is the foundational brick of the
    inference side — [d_pat_sub__univ_ghost_r] / [__infer] consume an
    [R ≈ Q] to wrap a base term's skeleton core into a (ghost-)bidirectional
    one, and the core that arises AFTER [forall_l] instantiates a top-level
    [∀] with [□] carries exactly such holes.  All tags are empty (no ε-tags):
    [unit]/[var]/[hole] give [nil], [arrow] combines [nil ++ nil], and the
    syn-painting sends each [∀] to [bskl_all_syn] (matched by [__forall_syn]).
    A [pskl_hole] matches [inh{□}] (= [bskl_hole]) via [__hole]. *)
Lemma d_pat_consis_refl_pskl : forall P,
    lc_pskl P ->
    forall Γ,
      (forall X, X `in` ftvar_in_pskl P -> binds X dbind_tvar Γ) ->
      nil ⨟ Γ ⊨ₛ (bskl_to_uskl (pskl_to_bskl_syn P)) ≈ (pskl_to_bskl_syn P).
Proof.
  intros P Hlc. induction Hlc; intros Γ Hcov; simpl.
  - (* unit *) apply d_pat_consis__unit.
  - (* var_f X *) apply d_pat_consis__var. apply Hcov. simpl. fsetdec.
  - (* arrow *) apply d_pat_consis__arrow with (Δ1 := nil) (Δ2 := nil);
      [ apply IHHlc1 | apply IHHlc2 ]; intros Y HY; apply Hcov; simpl; fsetdec.
  - (* all_syn: syn-painting → bskl_all_syn, matched by __forall_syn *)
    inst_cofinites_for d_pat_consis__forall_syn. intros X HX.
    rewrite <- bskl_to_uskl_open. rewrite <- pskl_to_bskl_syn_open.
    apply H0. intros Y HY.
    apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in HY. simpl in HY.
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + (* Y = X *) apply AtomSetImpl.singleton_1 in HY. subst.
      apply binds_app_2. apply binds_one_3; reflexivity.
    + (* Y ∈ ftvar P *) apply binds_app_3. apply (Hcov Y HY).
  - (* hole: □ ≈ inh{□} = bskl_hole via __hole *)
    change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply d_pat_consis__hole. apply d_wf_pskl__hole.
  - (* tophole: ⫯ ≈ ⫯ via __tophole, recurse *)
    apply d_pat_consis__tophole. apply IHHlc. assumption.
Qed.

(** Helpers for the ghostified-inference lemma below. *)

(** Opening with the closed ghost [□] preserves skeleton size (both
    [pskl_var_b] and [pskl_hole] have size 1) — gives the size decrease the
    [∀]-prefix recursion needs. *)
Lemma size_pskl_open_hole_rec : forall P k,
    size_pskl (open_pskl_wrt_pskl_rec k pskl_hole P) = size_pskl P.
Proof.
  induction P; intros k; simpl; try reflexivity;
    try (rewrite IHP; reflexivity);
    try (rewrite IHP1, IHP2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma size_pskl_open_hole : forall P,
    size_pskl (open_pskl_wrt_pskl P pskl_hole) = size_pskl P.
Proof. intro P. apply (size_pskl_open_hole_rec P 0). Qed.

(** The syn-painting of any (lc) skeleton is a synthesised bskl. *)
Lemma is_sskl_pskl_to_bskl_syn : forall P,
    lc_pskl P -> is_sskl (pskl_to_bskl_syn P).
Proof.
  intros P H. induction H; simpl; try (constructor; auto; fail).
  - (* all_syn *) inst_cofinites_for is_sskl__all. intros X HX.
    rewrite <- pskl_to_bskl_syn_open. auto.
Qed.

(** BRICK 2 — GHOSTIFICATION as a RELATION [ghost_of P Q]: [Q] is the
    ghost-rich skeleton obtained from skeleton [P] by instantiating each
    leading [∀] with [□] (the [__all] case strips one [∀] by opening its
    body with [□]) and wrapping the resulting core in a universal ghost [⫯]
    (a bare-hole core stays [□]).  Naming [Q] via a relation (rather than an
    existential) lets the FILL side (brick 3) refer to the SAME [Q] the
    inference side produced. *)
Inductive ghost_of : pskl -> bskl -> Prop :=
| ghost_of__unit : ghost_of pskl_unit (bskl_tophole bskl_unit)
| ghost_of__var  : forall X, ghost_of (pskl_var_f X) (bskl_tophole (bskl_var_f X))
| ghost_of__arrow : forall P1 P2,
    ghost_of (pskl_arrow P1 P2)
             (bskl_tophole (bskl_arrow (pskl_to_bskl_syn P1) (pskl_to_bskl_syn P2)))
| ghost_of__hole : ghost_of pskl_hole bskl_hole
| ghost_of__tophole : forall P0 Q,
    ghost_of P0 Q -> ghost_of (pskl_tophole P0) Q
| ghost_of__all : forall body Q,
    ghost_of (open_pskl_wrt_pskl body pskl_hole) Q ->
    ghost_of (pskl_all_syn body) Q.

(** Every (lc) skeleton HAS a ghostification.  Size induction: stripping a
    [∀] opens its body with the closed [□], which preserves size, so the
    recursion is well-founded ([size_pskl_open_hole]). *)
Lemma ghost_of_total : forall n P,
    size_pskl P <= n -> lc_pskl P -> exists Q, ghost_of P Q.
Proof.
  induction n; intros P Hsz Hlc.
  - destruct Hlc; simpl in Hsz; lia.
  - destruct Hlc as [ | X | P1 P2 _ _ | body Hbody | | P0 HP0 ]; simpl in Hsz.
    + exists (bskl_tophole bskl_unit). apply ghost_of__unit.
    + exists (bskl_tophole (bskl_var_f X)). apply ghost_of__var.
    + eexists. apply ghost_of__arrow.
    + destruct (IHn (open_pskl_wrt_pskl body pskl_hole)) as [Q HQ].
      * rewrite size_pskl_open_hole. lia.
      * apply lc_body_pskl_wrt_pskl; [ exact Hbody | apply lc_pskl_hole ].
      * exists Q. apply ghost_of__all. exact HQ.
    + exists bskl_hole. apply ghost_of__hole.
    + destruct (IHn P0) as [Q HQ]; [ lia | exact HP0 | ].
      exists Q. apply ghost_of__tophole. exact HQ.
Qed.

(** INFERENCE side: the [uskl] erasure of [syn P] subtypes (in [mode_tc]) to
    any ghostification [Q] of [P].  By induction on [ghost_of]: [__all] via
    [forall_l(□)], cores via [univ_ghost_r]+[consis_refl] (bare hole via
    [__ghost], leading ⫯ dropped by [univ_ghost_l]). *)
Lemma ghost_of_infer : forall P Q,
    ghost_of P Q ->
    lc_pskl P ->
    forall Γ,
      (forall X, X `in` ftvar_in_pskl P -> binds X dbind_tvar Γ) ->
      nil ⨟ Γ ⊢ₛ[ mode_tc ] (bskl_to_uskl (pskl_to_bskl_syn P)) ⊑ Q.
Proof.
  intros P Q Hg. induction Hg; intros Hlc Γ Hcov; simpl.
  - (* unit *) apply d_pat_sub__univ_ghost_r;
      [ apply guarded_uskl__unit | apply guarded_bskl__unit
      | apply is_sskl__unit | apply d_pat_consis__unit ].
  - (* var *) apply d_pat_sub__univ_ghost_r;
      [ apply guarded_uskl__var | apply guarded_bskl__var | apply is_sskl__var | ].
    apply d_pat_consis__var. apply Hcov. simpl. fsetdec.
  - (* arrow *) inversion Hlc; subst. apply d_pat_sub__univ_ghost_r.
    + apply guarded_uskl__arrow; apply lc_bskl_to_uskl; apply lc_pskl_to_bskl_syn; assumption.
    + apply guarded_bskl__arrow; apply lc_pskl_to_bskl_syn; assumption.
    + apply is_sskl__arrow; apply is_sskl_pskl_to_bskl_syn; assumption.
    + apply (@d_pat_consis_refl_pskl (pskl_arrow P1 P2));
        [ apply lc_pskl_arrow; assumption | assumption ].
  - (* hole *) change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply d_pat_sub__ghost. apply d_wf_pskl__hole.
  - (* tophole *) inversion Hlc; subst.
    apply d_pat_sub__univ_ghost_l; [ discriminate | ].
    apply IHHg; [ assumption | intros Y HY; apply Hcov; simpl; assumption ].
  - (* all: forall_l(□) then IH on the instantiated body *)
    eapply d_pat_sub__forall_l_untagged with (Δ' := nil) (psi := uskl_hole);
      [ discriminate | apply list_disjoint_nil_l | apply d_tags_skl__hole
      | apply d_wf_uskl__hole | apply is_tskl__hole | ].
    simpl.
    replace (open_uskl_wrt_uskl (bskl_to_uskl (pskl_to_bskl_syn body)) uskl_hole)
      with (bskl_to_uskl (pskl_to_bskl_syn (open_pskl_wrt_pskl body pskl_hole))).
    2:{ unfold open_pskl_wrt_pskl, open_uskl_wrt_uskl.
        rewrite pskl_to_bskl_syn_open_rec. rewrite bskl_to_uskl_open_rec.
        reflexivity. }
    apply IHHg.
    + apply lc_body_pskl_wrt_pskl; [ apply lc_body_pskl_all_syn_1; exact Hlc | apply lc_pskl_hole ].
    + intros Y HY. apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in HY.
      simpl in HY. apply Hcov. simpl. fsetdec.
Qed.

(** Corollary (the existential inference, brick 2's headline). *)
Lemma d_pat_sub_infer_ghost : forall P,
    lc_pskl P ->
    forall Γ,
      (forall X, X `in` ftvar_in_pskl P -> binds X dbind_tvar Γ) ->
      exists Q, nil ⨟ Γ ⊢ₛ[ mode_tc ] (bskl_to_uskl (pskl_to_bskl_syn P)) ⊑ Q.
Proof.
  intros P Hlc Γ Hcov.
  destruct (ghost_of_total (le_n (size_pskl P)) Hlc) as [Q HQ].
  exists Q. apply ghost_of_infer; assumption.
Qed.

(** ===================================================================== *)
(** BRICK 3 — FILL SIDE, and THE OBSTACLE.                                  *)
(**
   Goal: [ghost_of (ptyp_to_pskl C) Q -> empty ⨟ Γ ⊢[tc] (ptyp_to_utyp_syn C)
          ⊑ (ptyp_to_btyp_inh A') -> inh{Q} ⊳ syn{A'}], i.e. the ghost [Q]
   produced for a base term's principal type [C] refines every checking type
   [A'] the term subsumes to.  (The [inh{Q}] / [syn{A'}] painting is the
   safety statement's; the syn-RHS is what the fill engines target.)

   THE OBSTACLE — [forall_l] / ghost mis-alignment.  Induct on the [d_sub]
   derivation.  The [tc] cases are [__check] (consistency core), [__forall_r]
   (RHS adds an inherited ∀, absorbed by the [⫯] via [tophole_fill]) and
   [__forall_l].  In [__forall_l] the LHS ∀ of [C] is instantiated with a
   CONCRETE [φ] ([is_ttyp]), reducing to [open(C-body) φ ⊑ inh{A'}] — but
   [ghost_of] stripped the SAME ∀ by opening its body with [□]
   ([ghost_of__all]).  So I hold [ghost_of (open (skel C-body) □) Q] while a
   naive IH wants [ghost_of (open (skel C-body) (skel φ)) Q].  They differ
   exactly at the instantiated position, where [Q] has a [□].

   Why it is still TRUE: that [□] fills ANYTHING ([d_refine_syn__hole]), so it
   absorbs whatever [φ] became in [A'].  Mechanically this needs a GENERALISED
   statement / a hole-monotonicity of the fill ("replacing a sub-skeleton of
   [Q] by [□] only enlarges what [inh{Q}] refines"), so the [□]s uniformly
   absorb the [forall_l] instantiations.  Plus the tags ([ε]) carried by [φ]
   add a second axis to track.

   SECOND subtlety — the RHS colouring is NOT uniformly syn.  [inh{Q}] repaints
   [Q]'s ∀-colours to *inherited* ([bskl_to_pskl] collapses to [pskl_all_syn],
   then [pskl_to_bskl_inh] → [bskl_all_inh]).  So a NESTED concrete ∀ kept by
   [ghost_of] (e.g. the codomain of [unit→∀β.β], untouched by the shallow
   subtyping) appears as [bskl_all_inh] on the LHS, and [d_refine_syn__all]
   matches it ONLY against an *inherited* ∀ on the RHS.  Hence the witnessing
   [B] in [∃B, bskl_to_pskl B = ptyp_to_pskl A' ∧ inh{Q} ⊳ B] is a
   POSITION-DEPENDENT colouring of [A']: syn at the ghost/[forall_l]-varied
   leaves ([□] fills them via [__hole] → [pskl_to_bskl_syn]) but inh at the
   kept nested ∀s (matched by [__all]).  So [B] must be built FROM [Q] (track
   it alongside the [d_sub] induction), not fixed to [pskl_to_bskl_syn A'].

   NET: brick 3 is a focused multi-lemma development (≈ brick 2 in size):
   (1) a [more_ghost] relation + hole-monotonicity of the fill (for the [□]/[φ]
   absorption); (2) a relating lemma [ghost_of(open S □) Q□ ∧ ghost_of(open S V)
   Qᵥ → more_ghost Q□ Qᵥ]; (3) a [Q]-driven colouring [B] of [A'] with
   [bskl_to_pskl B = ptyp_to_pskl A']; (4) [ghost_of_fill] by [d_sub] induction
   (with the [ε]-tag bookkeeping) assembling all of the above.  The inference
   side (bricks 1-2 above) is complete and Qed; this is the remaining work. *)

(** [more_ghost Q' Q]: [Q'] is [Q] with some sub-skeletons replaced by the
    plain ghost [□].  The tool for lemma (1)/(2) of the plan above — the [□]s
    in the [forall_l]-instantiated [Q] are [more_ghost] than any concrete
    instantiation, and the fill is monotone in this order (at the syn-painted
    leaves).  Defined now (independent of the open design questions); the
    monotonicity + relating lemmas that consume it are next session's first
    targets. *)
Inductive more_ghost : bskl -> bskl -> Prop :=
| more_ghost__hole  : forall Q, more_ghost bskl_hole Q
| more_ghost__unit  : more_ghost bskl_unit bskl_unit
| more_ghost__var   : forall X, more_ghost (bskl_var_f X) (bskl_var_f X)
| more_ghost__arrow : forall Q1 Q2 R1 R2,
    more_ghost Q1 R1 -> more_ghost Q2 R2 ->
    more_ghost (bskl_arrow Q1 Q2) (bskl_arrow R1 R2)
| more_ghost__all_syn : forall L Q R,
    (forall X, X `notin` L ->
       more_ghost (open_bskl_wrt_bskl Q (bskl_var_f X))
                  (open_bskl_wrt_bskl R (bskl_var_f X))) ->
    more_ghost (bskl_all_syn Q) (bskl_all_syn R)
| more_ghost__all_inh : forall L Q R,
    (forall X, X `notin` L ->
       more_ghost (open_bskl_wrt_bskl Q (bskl_var_f X))
                  (open_bskl_wrt_bskl R (bskl_var_f X))) ->
    more_ghost (bskl_all_inh Q) (bskl_all_inh R)
| more_ghost__tophole : forall Q R,
    more_ghost Q R -> more_ghost (bskl_tophole Q) (bskl_tophole R).

(** ===================================================================== *)
(** PATH (b) INFRASTRUCTURE — tag-erasing [utyp] skeleton + the holed-subsumes
    invariant the [d_sub] induction carries. *)

(** [utyp_to_pskl]: the tag-erased skeleton of a [utyp] (both ∀-colours and
    ε-tags collapse to [pskl_all_syn], as in [utyp_to_btyp]). *)
Fixpoint utyp_to_pskl (C : utyp) : pskl :=
  match C with
  | utyp_unit => pskl_unit
  | utyp_var_b n => pskl_var_b n
  | utyp_var_f X => pskl_var_f X
  | utyp_arrow C1 C2 => pskl_arrow (utyp_to_pskl C1) (utyp_to_pskl C2)
  | utyp_all_syn C0 => pskl_all_syn (utyp_to_pskl C0)
  | utyp_all_etag _ C0 => pskl_all_syn (utyp_to_pskl C0)
  end.

(** The skeleton of a type's syn-painting is the type's skeleton. *)
Lemma utyp_to_pskl_ptyp_to_utyp_syn : forall C,
    utyp_to_pskl (ptyp_to_utyp_syn C) = ptyp_to_pskl C.
Proof. induction C; simpl; try reflexivity; try (rewrite IHC; reflexivity);
  try (rewrite IHC1, IHC2; reflexivity). Qed.

Lemma utyp_to_pskl_open_rec : forall C V k,
    utyp_to_pskl (open_utyp_wrt_utyp_rec k V C) =
    open_pskl_wrt_pskl_rec k (utyp_to_pskl V) (utyp_to_pskl C).
Proof.
  induction C; intros V k; simpl; try reflexivity;
    try (rewrite IHC; reflexivity); try (rewrite IHC1, IHC2; reflexivity).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
Qed.

Lemma utyp_to_pskl_open : forall C V,
    utyp_to_pskl (open_utyp_wrt_utyp C V) =
    open_pskl_wrt_pskl (utyp_to_pskl C) (utyp_to_pskl V).
Proof. intros. unfold open_utyp_wrt_utyp, open_pskl_wrt_pskl.
  apply (utyp_to_pskl_open_rec C V 0). Qed.

(** [pskl_subsumes P S]: [P] is [S] with some sub-skeletons replaced by [□].
    The invariant the [d_sub] induction carries — [P] (the skeleton driving
    [ghost_of]/[Q]) is the LHS-skeleton with [forall_l]-instantiated positions
    holed out. *)
Inductive pskl_subsumes : pskl -> pskl -> Prop :=
| pskl_subsumes__hole  : forall S, pskl_subsumes pskl_hole S
| pskl_subsumes__unit  : pskl_subsumes pskl_unit pskl_unit
| pskl_subsumes__var_f : forall X, pskl_subsumes (pskl_var_f X) (pskl_var_f X)
| pskl_subsumes__var_b : forall n, pskl_subsumes (pskl_var_b n) (pskl_var_b n)
| pskl_subsumes__arrow : forall P1 P2 S1 S2,
    pskl_subsumes P1 S1 -> pskl_subsumes P2 S2 ->
    pskl_subsumes (pskl_arrow P1 P2) (pskl_arrow S1 S2)
| pskl_subsumes__all   : forall P S,
    pskl_subsumes P S -> pskl_subsumes (pskl_all_syn P) (pskl_all_syn S)
| pskl_subsumes__tophole : forall P S,
    pskl_subsumes P S -> pskl_subsumes (pskl_tophole P) (pskl_tophole S).

Lemma pskl_subsumes_refl : forall S, pskl_subsumes S S.
Proof. induction S; constructor; assumption. Qed.

(** Subsumption is preserved by opening, where the LHS opens with [□]
    ([□] subsumes anything) and the RHS with the corresponding instantiation. *)
Lemma pskl_subsumes_open_rec : forall P S,
    pskl_subsumes P S ->
    forall V W k, pskl_subsumes V W ->
    pskl_subsumes (open_pskl_wrt_pskl_rec k V P) (open_pskl_wrt_pskl_rec k W S).
Proof.
  intros P S H. induction H; intros V W k Hvw; simpl;
    try (constructor; auto; fail).
  - (* var_b *) destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl;
      [ apply pskl_subsumes__var_b | assumption | apply pskl_subsumes__var_b ].
Qed.

(** HOLE-MONOTONICITY (lemma (1) of the plan), for a syn-painted RHS: making
    the LHS [Q] more ghost ([more_ghost Q' Q]) preserves the refinement when
    the RHS is [pskl_to_bskl_syn Pp] (well-formed).  Proof by induction on the
    refinement derivation: wherever [more_ghost] turns a subterm into [□] the
    [__hole] rule fires (the matching RHS sub-skeleton is syn-painted and wf);
    the [__all] case is vacuous (a syn RHS is never [bskl_all_inh]); the [⫯]
    cases reconstruct via the same rule, the IH applied at [Q' = ⫯ …]. *)
Lemma d_refine_syn_more_ghost_syn : forall Γ Δs Δi Q Bsyn,
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ Bsyn ->
    forall Pp, Bsyn = pskl_to_bskl_syn Pp ->
    Δs ⨟ Γ ⊢ₚₛ Pp ->
    forall Q', more_ghost Q' Q ->
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q' ⊳ Bsyn.
Proof.
  intros Γ Δs Δi Q Bsyn Href.
  induction Href; intros Pp Heq Hwf Q' Hmg.
  - (* __unit *) inversion Hmg; subst.
    + rewrite Heq. apply d_refine_syn__hole. assumption.
    + apply d_refine_syn__unit.
  - (* __var *) inversion Hmg; subst.
    + rewrite Heq. apply d_refine_syn__hole. assumption.
    + apply d_refine_syn__var; assumption.
  - (* __arrow *) inversion Hmg; subst.
    + rewrite Heq. apply d_refine_syn__hole. assumption.
    + destruct Pp; simpl in Heq; try discriminate. inversion Heq; subst.
      inversion Hwf; subst.
      apply d_refine_syn__arrow;
        [ eapply IHHref1 with (Pp := Pp1) | eapply IHHref2 with (Pp := Pp2) ];
        solve [ reflexivity | assumption ].
  - (* __all: RHS bskl_all_inh, never a syn-painting ⟹ vacuous *)
    destruct Pp; simpl in Heq; discriminate.
  - (* __hole: Q = bskl_hole ⟹ Q' = bskl_hole *)
    inversion Hmg; subst. apply d_refine_syn__hole. assumption.
  - (* __tophole_remove (RHS is a var P; [subst] already rewrote it to syn Pp) *)
    inversion Hmg; subst.
    + apply d_refine_syn__hole. assumption.
    + apply d_refine_syn__tophole_remove. eapply IHHref with (Pp := Pp); auto.
  - (* __tophole_fill: Bsyn = bskl_all_syn P = syn Pp ⟹ Pp = pskl_all_syn Pp0 *)
    inversion Hmg; subst.
    + rewrite Heq. apply d_refine_syn__hole. assumption.
    + destruct Pp; simpl in Heq; try discriminate. inversion Heq; subst.
      inversion Hwf; subst.
      inst_cofinites_for d_refine_syn__tophole_fill. intros X HX.
      eapply H0 with (Pp := open_pskl_wrt_pskl Pp (pskl_var_f X)).
      * auto.
      * rewrite pskl_to_bskl_syn_open. reflexivity.
      * match goal with
        | Hb : forall _ : atom, _ `notin` _ -> _ ⨟ _ ⊢ₚₛ _ |- _ =>
            apply Hb; auto
        end.
      * apply more_ghost__tophole. assumption.
  - (* __tophole_keep: Bsyn = bskl_tophole P = syn Pp ⟹ Pp = pskl_tophole Pp0 *)
    inversion Hmg; subst.
    + rewrite Heq. apply d_refine_syn__hole. assumption.
    + destruct Pp; simpl in Heq; try discriminate. inversion Heq; subst.
      inversion Hwf; subst.
      apply d_refine_syn__tophole_keep; [ assumption | ].
      eapply IHHref with (Pp := Pp); auto.
Qed.

(** A well-formed type is locally closed. *)
Lemma d_wf_ptyp_lc_loc : forall Γ A, d_wf_ptyp Γ A -> lc_ptyp A.
Proof.
  intros Γ A H. induction H.
  - constructor.
  - constructor.
  - constructor; assumption.
  - pick fresh X. apply (lc_ptyp_all_exists X). apply H0. auto.
Qed.

(** A well-formed type's free tvars are all bound in the context. *)
Lemma d_wf_ptyp_ftvar : forall Γ A,
    d_wf_ptyp Γ A ->
    forall X, X `in` ftvar_in_ptyp A -> binds X dbind_tvar Γ.
Proof.
  intros Γ A H. induction H; intros Y HY; simpl in HY.
  - fsetdec.
  - apply AtomSetImpl.singleton_1 in HY. subst. assumption.
  - apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY]; auto.
  - pick fresh X for (L `union` ftvar_in_ptyp A `union` dom Γ `union` singleton Y).
    assert (HYo : Y `in` ftvar_in_ptyp (open_ptyp_wrt_ptyp A (ptyp_var_f X))).
    { eapply ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower. eassumption. }
    specialize (H0 X ltac:(auto) Y HYo).
    analyze_binds H0.
Qed.

(** Hence a well-formed type's skeleton is a well-formed [pskl] (any scope). *)
Lemma d_wf_pskl_of_wf_ptyp : forall Γ A,
    d_wf_ptyp Γ A ->
    forall Ψ, Ψ ⨟ Γ ⊢ₚₛ (ptyp_to_pskl A).
Proof.
  intros Γ A H Ψ. apply d_wf_pskl_of_ptyp.
  - eapply d_wf_ptyp_lc_loc; eassumption.
  - intros X HX. right. eapply d_wf_ptyp_ftvar; eassumption.
Qed.

(** The DETERMINISTIC witness colouring [colour Q A]: colour the checking type
    [A] guided by the inferred ghost [Q] — syn where [Q] is a ghost/leaf, inh
    at a nested [∀] that [Q] kept ([bskl_all_inh]), syn at a [∀] the universal
    ghost [⫯] fills.  Recurses on [A] (so it commutes with opening [A], which
    [__forall_r] needs); the single leading [⫯] is peeked (not recursed) to
    stay structural. *)
Fixpoint colour (Q : bskl) (A : ptyp) {struct A} : bskl :=
  match A with
  | ptyp_unit => bskl_unit
  | ptyp_var_b n => bskl_var_b n
  | ptyp_var_f X => bskl_var_f X
  | ptyp_arrow A1 A2 =>
      match (match Q with bskl_tophole Q0 => Q0 | _ => Q end) with
      | bskl_arrow Q1 Q2 => bskl_arrow (colour Q1 A1) (colour Q2 A2)
      | _ => bskl_arrow (pskl_to_bskl_syn (ptyp_to_pskl A1))
                        (pskl_to_bskl_syn (ptyp_to_pskl A2))
      end
  | ptyp_all A0 =>
      match Q with
      | bskl_all_inh Q0 => bskl_all_inh (colour Q0 A0)
      | bskl_tophole Q0 => bskl_all_syn (colour (bskl_tophole Q0) A0)
      | _ => bskl_all_syn (pskl_to_bskl_syn (ptyp_to_pskl A0))
      end
  end.

(** [colour] erases to [A]'s skeleton (independent of [Q]). *)
Lemma colour_erasure : forall A Q,
    bskl_to_pskl (colour Q A) = ptyp_to_pskl A.
Proof.
  induction A; intros Q; simpl; try reflexivity.
  - (* arrow *)
    destruct Q; simpl;
      try (rewrite IHA1, IHA2; reflexivity);
      try (rewrite ! bskl_to_pskl_pskl_to_bskl_syn; reflexivity).
    (* Q = bskl_tophole Q0: peek Q0 *)
    destruct Q; simpl;
      try (rewrite IHA1, IHA2; reflexivity);
      rewrite ! bskl_to_pskl_pskl_to_bskl_syn; reflexivity.
  - (* all *)
    destruct Q; simpl;
      try (rewrite IHA; reflexivity);
      rewrite bskl_to_pskl_pskl_to_bskl_syn; reflexivity.
Qed.

(** [colour] commutes with opening [A] by a fresh tvar (what [__forall_r]
    needs to close the cofinite premise; specialised to a variable so the
    [colour Q V] / [colour Q0 V] divergence at the nested-∀ case vanishes). *)
Lemma colour_open_rec : forall A Q X k,
    colour Q (open_ptyp_wrt_ptyp_rec k (ptyp_var_f X) A) =
    open_bskl_wrt_bskl_rec k (bskl_var_f X) (colour Q A).
Proof.
  induction A; intros Q X k; simpl.
  - reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - reflexivity.
  - (* arrow *)
    destruct Q as [ | ? | ? | qa qb | ? | ? | | q0 ]; simpl;
      try (rewrite IHA1, IHA2; reflexivity);
      try (rewrite !ptyp_to_pskl_open_rec, !pskl_to_bskl_syn_open_rec; reflexivity).
    (* tophole: peek q0 *)
    destruct q0 as [ | | | qa qb | | | | ]; simpl;
      try (rewrite IHA1, IHA2; reflexivity);
      rewrite !ptyp_to_pskl_open_rec, !pskl_to_bskl_syn_open_rec; reflexivity.
  - (* all *)
    destruct Q as [ | ? | ? | ? ? | ? | ? | | ? ]; simpl;
      try (rewrite IHA; reflexivity);
      rewrite !ptyp_to_pskl_open_rec, !pskl_to_bskl_syn_open_rec; reflexivity.
Qed.

Lemma colour_open : forall A Q X,
    colour Q (open_ptyp_wrt_ptyp A (ptyp_var_f X)) =
    open_bskl_wrt_bskl (colour Q A) (bskl_var_f X).
Proof. intros. unfold open_ptyp_wrt_ptyp, open_bskl_wrt_bskl.
  apply colour_open_rec. Qed.

(** Generalised fill, by induction on the [d_sub] derivation, carrying the
    [pskl_subsumes] invariant.  KEY: the [forall_l] case (the original
    obstacle) closes cleanly — the invariant is preserved by
    [pskl_subsumes_open_rec] ([□] subsumes the instantiation [φ]'s skeleton)
    with the SAME [Q], so the IH applies; no monotonicity needed.

    STATUS (WIP): the [forall_l] cases (the ORIGINAL obstacle) AND both
    [P = □] subcases are PROVED.  TWO [admit]s remain: [__check]
    (consistency→refinement base) and [__forall_r].  NOTE: [__forall_r] will
    need the existential witness [B] replaced by a DETERMINISTIC colouring
    function of [Q] and [A'] — the cofinite premise gives [B_X] per fresh [X]
    but a plain existential cannot be closed back over [X]; a function
    [colour Q A'] with [colour Q (open A'0 X) = open (colour Q A'0) X] fixes
    it (and threads through [__check] too). *)
Lemma ghost_of_fill_gen : forall Δ Γ U V,
    Δ ⨟ Γ ⊢[ mode_tc ] U ⊑ V ->
    forall A' P Q,
      V = ptyp_to_btyp_inh A' ->
      d_wf_ptyp Γ A' ->
      pskl_subsumes P (utyp_to_pskl U) ->
      ghost_of P Q ->
      exists B, bskl_to_pskl B = ptyp_to_pskl A' /\
                Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B.
Proof.
  intros Δ Γ U V H. remember mode_tc as m eqn:Hm. revert Hm.
  induction H; intros Hm A' P Q Heq Hwfa Hsub Hg; try discriminate Hm.
  - (* __check — delegate to the consistency→refinement base (next) *) admit.
  - (* __forall_r — RHS adds an inh ∀; ⫯ fills via tophole_fill (next) *) admit.
  - (* __forall_l_tagged: U = utyp_all_etag ε C *)
    simpl in Hsub. inversion Hsub; subst.
    + (* P = □ ⟹ Q = □, fills any type *)
      inversion Hg; subst. exists (pskl_to_bskl_syn (ptyp_to_pskl A')). split.
      * apply bskl_to_pskl_pskl_to_bskl_syn.
      * simpl. apply d_refine_syn__hole. apply d_wf_pskl_of_wf_ptyp; exact Hwfa.
    + (* P = pskl_all_syn P' : the KEY case — recurse with □ absorbing φ *)
      inversion Hg; subst.
      eapply IHd_sub; [ reflexivity | reflexivity | exact Hwfa | | eassumption ].
      rewrite utyp_to_pskl_open.
      apply pskl_subsumes_open_rec; [ assumption | apply pskl_subsumes__hole ].
  - (* __forall_l_untagged: U = utyp_all_syn C — identical to tagged *)
    simpl in Hsub. inversion Hsub; subst.
    + inversion Hg; subst. exists (pskl_to_bskl_syn (ptyp_to_pskl A')). split.
      * apply bskl_to_pskl_pskl_to_bskl_syn.
      * simpl. apply d_refine_syn__hole. apply d_wf_pskl_of_wf_ptyp; exact Hwfa.
    + inversion Hg; subst.
      eapply IHd_sub; [ reflexivity | reflexivity | exact Hwfa | | eassumption ].
      rewrite utyp_to_pskl_open.
      apply pskl_subsumes_open_rec; [ assumption | apply pskl_subsumes__hole ].
Admitted.

(** BRICK 3 GOAL (next session's first task).  The fill side: the ghost [Q]
    inferred for a base term's principal type [C] refines some colouring [B]
    of every checking type [A'] the term subsumes to.  [B] is existential
    precisely because it is the [Q]-driven position-dependent colouring (syn
    at hole-filled leaves, inh at kept nested ∀s — see the obstacle note).
    Once proved, the [__sub] case of [d_pat_safety] is: take [Q] from
    [ghost_of_total]+[ghost_of_infer] (inference), then [ghost_of_fill] gives
    the per-[A'] refinement.  PROOF PLAN: induction on the [d_sub] derivation —
    [more_ghost]+hole-monotonicity for [__forall_l] ([□] absorbs [φ]),
    consistency→refinement for [__check], [tophole_fill] for [__forall_r].

    STATUS: lemma (1), hole-monotonicity, is PROVED ([d_refine_syn_more_ghost_syn]
    above, Qed) — but for a *whole*-syn RHS.  DESIGN FORK discovered while
    assembling: the witness [B] is MIXED (syn at hole-filled leaves, inh at
    kept nested ∀s), so the whole-syn [mono] does not directly absorb [φ]
    against [B].  Two ways forward: (a) generalise [mono] to be POSITIONAL
    (holed positions face syn-RHS, others arbitrary); or (b) drop [mono] and
    CONSTRUCT [B] directly by recursion on [inh{Q}] / the [d_sub] core — which
    needs a [utyp→pskl] skeleton + a "holed-subsumes" invariant (neither
    exists yet).  (b) is the cleaner long-term shape.  This fork is the next
    decision; the inference side (bricks 1-2) is complete and Qed. *)
Lemma ghost_of_fill : forall C Q Γ A',
    ghost_of (ptyp_to_pskl C) Q ->
    empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn C) ⊑ (ptyp_to_btyp_inh A') ->
    exists B, bskl_to_pskl B = ptyp_to_pskl A' /\
              Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B.
Proof.
  (* NEXT SESSION — see the 4-lemma plan in the obstacle note above. *)
Admitted.

(** Γ-weakening for refinement (local copy — the general
    [d_refine_syn_weakening] lives in [prop_weakening], built later).  Used
    by [denv_coh_lookup] to lift a binding's refinement to the full
    context. *)
Lemma d_refine_syn_wkn : forall Γ1 Γ2 Γ3 Δs Δi Q P,
    (Γ1 ++ Γ3) ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P ->
    (Γ1 ++ Γ2 ++ Γ3) ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ1 Γ2 Γ3 Δs Δi Q P H.
  remember (Γ1 ++ Γ3) as Γ eqn:Heq. revert Γ1 Γ3 Heq.
  induction H; intros Γ1 Γ3 Heq; subst Γ.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var.
    match goal with H : _ \/ _ |- _ => destruct H as [HS | [HI | Hb]] end;
      [ left; assumption | right; left; assumption | right; right; analyze_binds Hb ].
  - apply d_refine_syn__arrow; auto.
  - apply d_refine_syn__all with (L := L `union` dom (Γ1 ++ Γ3)). intros X HX.
    eapply (H0 X ltac:(fsetdec) Γ1 Γ3). reflexivity.
  - apply d_refine_syn__hole. apply d_wf_pskl_weakening. assumption.
  - apply d_refine_syn__tophole_remove; auto.
  - apply d_refine_syn__tophole_fill with (L := L `union` dom (Γ1 ++ Γ3)). intros X HX.
    eapply (H0 X ltac:(fsetdec) Γ1 Γ3). reflexivity.
  - apply d_refine_syn__tophole_keep; [ assumption | auto ].
Qed.

(** A *typing context*: only type/tvar bindings, no ghost-bearing
    skeleton bindings.  (The user's "context has only A, not P" predicate.)
    Every context a [d_typing] derivation actually uses is of this shape. *)
Inductive typ_denv : list (atom * dbind) -> Prop :=
| typ_denv__nil  : typ_denv nil
| typ_denv__tvar : forall Γ X, typ_denv Γ -> typ_denv ((X ~ dbind_tvar) ++ Γ)
| typ_denv__typ  : forall Γ x A, typ_denv Γ -> typ_denv ((x ~ dbind_typ A) ++ Γ).

(** Context coherence between a skeleton-inference context [Γs] and a
    typing context [Γt].  Every term variable is [dbind_skl □] in [Γs] (so
    [d_pat__var] applies and infers [□], which fills ANY type via
    [d_refine_syn_hole_fills]) and [dbind_typ A] in [Γt] (so [d_typing__var]
    applies).  Binding [□] for *every* term var is exactly the constructive
    safety witness for the [var] case — no refinement side-condition is
    needed, because the leaf fill is discharged by [hole_fills], not by a
    stored refinement.  This is the bridge the safety induction needs to
    cross a λ where the two judgments bind a variable differently. *)
Inductive denv_coh : list (atom * dbind) -> list (atom * dbind) -> Prop :=
| denv_coh__nil  : denv_coh nil nil
| denv_coh__tvar : forall Γs Γt X,
    denv_coh Γs Γt ->
    denv_coh ((X ~ dbind_tvar) ++ Γs) ((X ~ dbind_tvar) ++ Γt)
| denv_coh__skl  : forall Γs Γt x A,
    denv_coh Γs Γt ->
    denv_coh ((x ~ dbind_skl pskl_hole) ++ Γs) ((x ~ dbind_typ A) ++ Γt).

(** Lookup: a [dbind_typ A] term-var in [Γt] is matched by a [dbind_skl □]
    in [Γs].  This discharges the [var] case of safety: [d_pat__var] then
    infers [□], and [□] fills [inh{A'}] for every checking [A']. *)
Lemma denv_coh_lookup : forall Γs Γt x A,
    denv_coh Γs Γt ->
    binds x (dbind_typ A) Γt ->
    binds x (dbind_skl pskl_hole) Γs.
Proof.
  intros Γs Γt x A Hcoh. induction Hcoh; intros Hb.
  - inversion Hb.
  - (* tvar *) apply binds_app_1 in Hb. destruct Hb as [Hb | Hb].
    + apply binds_one_iff in Hb. destruct Hb as [_ Hd]. inversion Hd.
    + apply binds_app_3. apply (IHHcoh Hb).
  - (* skl *) apply binds_app_1 in Hb. destruct Hb as [Hb | Hb].
    + apply binds_one_iff in Hb. destruct Hb as [Hx Hd]. inversion Hd. subst.
      apply binds_app_2. apply binds_one_3; auto.
    + apply binds_app_3. apply (IHHcoh Hb).
Qed.

(** Every type-only context [Γ] (a typing context — all term vars are
    [dbind_typ], all type vars [dbind_tvar]) has a coherent skeleton
    context: coerce each [dbind_typ] to [dbind_skl □].  This builds the
    [denv_coh] the top-level safety theorem feeds to the generalisation. *)
Lemma denv_coh_exists : forall Γ,
    typ_denv Γ ->
    exists Γs, denv_coh Γs Γ.
Proof.
  intros Γ H. induction H.
  - exists nil. apply denv_coh__nil.
  - destruct IHtyp_denv as [Γs Hcoh]. exists ((X ~ dbind_tvar) ++ Γs).
    apply denv_coh__tvar; auto.
  - destruct IHtyp_denv as [Γs Hcoh]. exists ((x ~ dbind_skl pskl_hole) ++ Γs).
    apply denv_coh__skl; auto.
Qed.

(** * Paper-facing skeleton properties.

    The statements below are native to the new syntax. They remain
    research-level obligations while the main D1/D12 path is being
    re-established. *)

Lemma d_pat_preserves_skel_wf : forall Γ e Q,
    Γ ⊢[ mode_tc ] e ⇨ Q ->
    d_wf_denv Γ ->
    nil ⨟ Γ ⊢ₚₛ Q.
Proof.
  intros Γ e Q H _.
  apply (proj2 d_typing_pat_preserves_wf) with (m := mode_tc) (e := e); auto.
Qed.

(** Paper "Safety of skeleton inference" (declarative.tex:1950): for a
    well-typed [M] there *exists* an inference [Γ ⊢ti M ⇨ Q] whose [Q] is
    *safe* — it fills *every* checking type [A].

    This is an **existential** over inference derivations, and it holds.
    The paper's WT note (declarative.tex:1956) that declarative inference
    "does not *always* give safe skeletons" is the **universal** statement
    — not every derivation is safe, because inference is non-deterministic
    ([tophole_remove]/[keep]/[fill] are distinct rules; [ForallL] may pick
    a ghost or a monotype) and some choices drop universal ghosts or guess
    monotypes.  Safety only asks for *one* good derivation, which always
    exists (the algorithmic inference is precisely a decision procedure
    that computes such a [Q], and it is sound w.r.t. this declarative
    relation).

    Note: the liberal-[d_pat__abs] gap (an over-specific, ghost-free
    argument skeleton) does NOT affect safety — being existential, safety
    just *picks* a well-behaved derivation (e.g. the unannotated-λ argument
    skeleton [□]), so over-specific inferences are simply not chosen.  In
    particular [freeze (λx.(x:unit))] is not a counterexample: [freeze] is
    not a value, so the term checks only at [unit→unit], which [□→unit]
    fills.

    PAINTING (per the current def — see statement below).  The LHS is
    *inherited* ([inh{P}]) and the target *bidirectional* ([bid{A}]).  This
    is what makes it work: concrete [∀]s in [P] become inh-[∀] (handled by
    [d_refine_syn__all]); ghosts fill via [hole] (any well-formed pskl) /
    [tophole] (universal ghost → syn-[∀] by [tophole_fill]).  Filling a
    ghost to an *inherited* [∀] stays (correctly) banned — the inh-painting
    is on [P], not the target.

    ENGINES (proved): [d_refine_syn_hole_fills] / [d_refine_syn_tophole_hole_fills]
    handle ghosts ([□] / [⫯.□] ⊳ any well-scoped type's syn-skeleton,
    polytypes included).

    REMAINING — the witness: a safe inferable [Q] per well-typed [e] whose
    [inh{Q}] refines every checking type.  Two viable strategies (the
    per-case refinement is discharged by the engines above either way):
    (a) a direct declarative induction on the typing that builds [Q]
        (threading [denv_coh] through λ; the existential IH may well suffice
        with the right invariant); or
    (b) algorithmically — the "looking" relation [a_pat_solution] /
        [a_pat_optimal] (algo/def_question.v:114) computes the skeleton, and
        [a_pat_solution] already *embeds* the declarative inference
        [⌊Θ1⌋ ⊢[M] e ⇨ pskl_to_bskl_syn P1], its [≼]-optimality giving
        fills-every-type; this reduces safety to the Phase-3 algorithmic
        results.
    Still [Admitted] (true) pending the witness. *)
(** Updated to the current paper "Safe Skeleton" definition
    (declarative.tex:1925): [P] is safe for [M] under [Γ] if for every [A]
    with [Γ ⊢tc M ⦂ inh{A}], [inh{P} ⊳ bid{A}] — the inferred skeleton
    *painted inherited* fills to *some bidirectional colouring* of [A].
    Encoding: [inh{P}] = [pskl_to_bskl_inh (bskl_to_pskl Q)] (erase the
    inferred [Q]'s colours, repaint inherited); [bid{A}] = an existential
    [B] with [bskl_to_pskl B = ptyp_to_pskl A] (the refinement output,
    unique by "Refinement determines colours").  The inh-painted LHS is
    what makes this work — concrete [∀]s in [P] become inh-[∀] (handled by
    [d_refine_syn__all]); ghosts fill via [hole]/[tophole]. *)
Theorem d_pat_safety : forall Γ e B0,
    Γ ⊢[ mode_tc ] e ⦂ B0 ->
    d_wf_denv Γ ->
    exists Q, Γ ⊢[ mode_tc ] e ⇨ Q /\
              (forall A, Γ ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) ->
                 exists B, bskl_to_pskl B = ptyp_to_pskl A /\
                   Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B).
Proof.
  (* Attempted directly: [intros Γ e B0 Hty Hwf; induction Hty] gives 11
     cases.  The [var] case is STUCK: its hypothesis is
     [binds x (dbind_typ A) Γ] (typing binds term-vars as [dbind_typ]), but
     constructing the inference [x ⇨ Q] needs [d_pat__var], which requires
     [binds x (dbind_skl P) Γ] — a [dbind_typ]-bound variable is not
     inferable.  So the single-[Γ] statement cannot be proved by direct
     induction: safety must be generalised over [denv_coh Γs Γt] (inference
     context with [dbind_skl] vs typing context with [dbind_typ]); the leaves
     then close with the ghost-fill engines [d_refine_syn_hole_fills] /
     [d_refine_syn_tophole_hole_fills].

     The witness is CONSTRUCTIVE (not the algorithm's optimality): the
     declarative inference is permissive enough to pick a fully-ghostified
     skeleton.  Per case: [var] → [□] (the [denv_coh]-bound skeleton);
     [unit] → [⫯.unit] (univ_ghost_r); annotations → [d_pat__sub] generalises
     the concrete skeleton, instantiating each top-level [∀] with [□] via
     [d_pat_sub__forall_l_*] (see [d_pat_sub_forall_hole_witness]); λ →
     [⫯.(□→Q)] via [abs_check].  The per-[A] fill then holds because [d_sub]
     check-mode is SHALLOW (one-level consistency + top-level [forall_l]
     only): the only [A'] a term checks at differ from its principal type at
     positions [forall_l] instantiated, exactly where the witness placed a
     [□] (which fills anything via [__hole]); nested [∀]s stay concrete and
     are matched structurally by [__all]/[__arrow].  The remaining work is
     to (i) build [denv_coh] for the top-level [Γ] (coerce typ→[□] skl) and
     (ii) grind the 11-case induction with these witnesses + a bridge lemma
     [d_sub C B -> inh{ghostify C} ⊳ bid{B}]. *)
Admitted.

(** GHOSTIFICATION WITNESS (the mechanism the safety witness relies on).
    A *top-level* [∀] in an annotation's concrete skeleton can be
    generalised to a ghost by [d_pat__sub]: [d_pat_sub__forall_l_untagged]
    instantiates the [∀] with [ψ = □] ([is_tskl □] holds — ghosts ARE
    tagged skeletons), and [d_pat_sub__ghost] then yields [□].  So
    [(e:∀α.α) ⇨tc □], and [□] fills every type ([d_refine_syn_hole_fills]).

    This is why the existential safety is constructive (and why it is NOT
    the algorithm's optimality): the declarative inference is permissive
    enough to pick the fully-ghostified skeleton directly.  No nested-ghost
    problem arises because [d_sub] check-mode is shallow — one-level
    consistency + top-level [forall_l] only, never deep instantiation under
    an arrow — so a term never checks at an instance of a nested covariant
    [∀], and that [∀] need not be ghostified (it stays concrete, matched by
    [d_refine_syn__all] / [__arrow]). *)
Lemma d_pat_sub_forall_hole_witness : forall Γ,
  nil ⨟ Γ ⊢ₛ[ mode_tc ]
    (bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl (ptyp_all (ptyp_var_b 0)))))
      ⊑ bskl_hole.
Proof.
  intros Γ. simpl.
  eapply d_pat_sub__forall_l_untagged with (Δ' := nil) (psi := uskl_hole).
  - discriminate.
  - apply list_disjoint_nil_l.
  - apply d_tags_skl__hole.
  - apply d_wf_uskl__hole.
  - apply is_tskl__hole.
  - simpl. change bskl_hole with (pskl_to_bskl_inh pskl_hole).
    apply d_pat_sub__ghost. apply d_wf_pskl__hole.
Qed.
