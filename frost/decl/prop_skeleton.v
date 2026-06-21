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
(** BRICK 3 — FILL SIDE ([ghost_of_fill], below).                          *)
(**
   [ghost_of (ptyp_to_pskl C) Q -> ... empty⨟Γ ⊢[tc] (ptyp_to_utyp_syn C) ⊑
   (ptyp_to_btyp_inh A') -> exists B, bskl_to_pskl B = ptyp_to_pskl A' ∧
   inh{Q} ⊳ B]: the ghost [Q] for a base term's principal type [C] refines a
   colouring of every checking type [A'].  PROVED (Qed, axiom-free) by a
   DETERMINISTIC witness [colour] (B := colour inh{Q} A') + a [d_sub] induction
   ([ghost_of_fill_gen]) carrying [hole_safe_u nil P U]: the [forall_l] [□]/[φ]
   absorption is handled by [hole_safe_u_subst]; the [__check] base by
   [hole_safe_u_transport] (to A') + [refine_colour_core] / [refine_colour_tophole]
   (the ghost's top [⫯]).  (The earlier [more_ghost]-monotonicity plan was
   abandoned in favour of the [colour] witness.) *)


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

(** [colour] inspects only the guide [Q]'s CONSTRUCTORS, never its leaves, so
    opening the guide leaves [colour] unchanged. *)
Lemma colour_guide_open_rec : forall A Q X k,
    colour (open_bskl_wrt_bskl_rec k (bskl_var_f X) Q) A = colour Q A.
Proof.
  induction A; intros Q X k; simpl; try reflexivity.
  - (* arrow *) destruct Q as [ | n0 | X0 | qa qb | qs | qi | | q0 ]; simpl.
    + reflexivity.
    + destruct (lt_eq_lt_dec n0 k) as [[?|?]|?]; reflexivity.
    + reflexivity.
    + rewrite IHA1, IHA2; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + (* tophole q0: peek *) destruct q0 as [ | n1 | X1 | qa qb | qs | qi | | q1 ]; simpl.
      * reflexivity.
      * destruct (lt_eq_lt_dec n1 k) as [[?|?]|?]; reflexivity.
      * reflexivity.
      * rewrite IHA1, IHA2; reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
  - (* all *) destruct Q as [ | n0 | X0 | qa qb | qs | qi | | q0 ]; simpl.
    + reflexivity.
    + destruct (lt_eq_lt_dec n0 k) as [[?|?]|?]; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + (* all_inh qi *) rewrite IHA; reflexivity.
    + reflexivity.
    + (* tophole q0 *) f_equal.
      change (bskl_tophole (open_bskl_wrt_bskl_rec k (bskl_var_f X) q0))
        with (open_bskl_wrt_bskl_rec k (bskl_var_f X) (bskl_tophole q0)).
      rewrite IHA. reflexivity.
Qed.

Lemma colour_guide_open : forall A Q X,
    colour (open_bskl_wrt_bskl Q (bskl_var_f X)) A = colour Q A.
Proof. intros. unfold open_bskl_wrt_bskl. apply colour_guide_open_rec. Qed.

(** [colour] with a [□] guide is the plain syn-painting. *)
Lemma colour_hole : forall A,
    colour bskl_hole A = pskl_to_bskl_syn (ptyp_to_pskl A).
Proof. induction A; simpl; reflexivity. Qed.

(** A ghostification is always a hole or a universal ghost (top-level shape). *)
Lemma ghost_of_shape : forall P Q,
    ghost_of P Q -> Q = bskl_hole \/ exists Q0, Q = bskl_tophole Q0.
Proof.
  intros P Q H. induction H; eauto.
Qed.

(** [⫯]-free skeletons.  [colour] never emits a [⫯], which is what lets the
    Γ→Δs context-move below go through (a [⫯] would clear the scope). *)
Inductive no_tophole_pskl : pskl -> Prop :=
| nthp_unit  : no_tophole_pskl pskl_unit
| nthp_var_b : forall n, no_tophole_pskl (pskl_var_b n)
| nthp_var_f : forall X, no_tophole_pskl (pskl_var_f X)
| nthp_arrow : forall P1 P2, no_tophole_pskl P1 -> no_tophole_pskl P2 ->
    no_tophole_pskl (pskl_arrow P1 P2)
| nthp_all   : forall P, no_tophole_pskl P -> no_tophole_pskl (pskl_all_syn P)
| nthp_hole  : no_tophole_pskl pskl_hole.

Inductive no_tophole_bskl : bskl -> Prop :=
| nthb_unit  : no_tophole_bskl bskl_unit
| nthb_var_b : forall n, no_tophole_bskl (bskl_var_b n)
| nthb_var_f : forall X, no_tophole_bskl (bskl_var_f X)
| nthb_arrow : forall Q1 Q2, no_tophole_bskl Q1 -> no_tophole_bskl Q2 ->
    no_tophole_bskl (bskl_arrow Q1 Q2)
| nthb_all_syn : forall Q, no_tophole_bskl Q -> no_tophole_bskl (bskl_all_syn Q)
| nthb_all_inh : forall Q, no_tophole_bskl Q -> no_tophole_bskl (bskl_all_inh Q)
| nthb_hole  : no_tophole_bskl bskl_hole.

Lemma no_tophole_pskl_of_ptyp : forall A, no_tophole_pskl (ptyp_to_pskl A).
Proof. induction A; simpl; constructor; assumption. Qed.

Lemma no_tophole_syn : forall P,
    no_tophole_pskl P -> no_tophole_bskl (pskl_to_bskl_syn P).
Proof. intros P H. induction H; simpl; constructor; assumption. Qed.

Lemma colour_no_tophole : forall A Q, no_tophole_bskl (colour Q A).
Proof.
  induction A; intros Q; simpl.
  - constructor.
  - constructor.
  - constructor.
  - (* arrow *) destruct (match Q with bskl_tophole Q0 => Q0 | _ => Q end);
      try (constructor; auto; fail);
      constructor; apply no_tophole_syn; apply no_tophole_pskl_of_ptyp.
  - (* all *) destruct Q;
      try (constructor; apply no_tophole_syn; apply no_tophole_pskl_of_ptyp; fail);
      constructor; auto.
Qed.

Lemma no_tophole_pskl_open_rec : forall P X k,
    no_tophole_pskl P ->
    no_tophole_pskl (open_pskl_wrt_pskl_rec k (pskl_var_f X) P).
Proof.
  intros P X k H. revert k. induction H; intros k; simpl;
    try (constructor; auto; fail).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; constructor.
Qed.

Lemma no_tophole_bskl_open_rec : forall Q X k,
    no_tophole_bskl Q ->
    no_tophole_bskl (open_bskl_wrt_bskl_rec k (bskl_var_f X) Q).
Proof.
  intros Q X k H. revert k. induction H; intros k; simpl;
    try (constructor; auto; fail).
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; constructor.
Qed.

Lemma no_tophole_syn_inv : forall P,
    no_tophole_bskl (pskl_to_bskl_syn P) -> no_tophole_pskl P.
Proof.
  induction P; simpl; intros H; try (constructor; fail);
    inversion H; subst; constructor; auto.
Qed.

(** Move a tvar from the type context into the [pskl] scope set [Ψ] (valid
    for [⫯]-free skeletons — a [⫯] would clear [Ψ]). *)
Lemma d_wf_pskl_move : forall Ψ Γ' P,
    Ψ ⨟ Γ' ⊢ₚₛ P ->
    no_tophole_pskl P ->
    forall X Γ, Γ' = (X ~ dbind_tvar) ++ Γ ->
    (X :: Ψ) ⨟ Γ ⊢ₚₛ P.
Proof.
  intros Ψ Γ' P H. induction H; intros Hnt X0 Γ0 HΓ; subst.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [HΨ | Hb].
    + left. simpl. right. assumption.
    + apply binds_app_1 in Hb. destruct Hb as [Hb | Hb].
      * apply binds_one_iff in Hb. destruct Hb as [HX _]. subst.
        left. simpl. left. reflexivity.
      * right. assumption.
  - inversion Hnt; subst. apply d_wf_pskl__arrow; auto.
  - inversion Hnt; subst. inst_cofinites_for d_wf_pskl__all. intros Y HY.
    apply d_wf_pskl_Psi_mono with (Ψ := X0 :: (Y :: Ψ)).
    + apply H0; auto. apply no_tophole_pskl_open_rec. assumption.
    + intros Z HZ. simpl in *. tauto.
  - apply d_wf_pskl__hole.
  - inversion Hnt.
Qed.

(** Refinement is monotone in the syn-scope [Δs] (for [⫯]-free RHS). *)
Lemma d_refine_syn_Ds_mono : forall Γ Δs Δi Q P,
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P ->
    no_tophole_bskl P ->
    forall Δs', (forall X, List.In X Δs -> List.In X Δs') ->
    Γ ⨟ Δs' ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ Δs Δi Q P H. induction H; intros Hnt Δs' Hmono.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HS | [HI | Hb]];
      [ left; auto | right; left; assumption | right; right; assumption ].
  - inversion Hnt; subst. apply d_refine_syn__arrow; auto.
  - inversion Hnt; subst. inst_cofinites_for d_refine_syn__all. intros X HX.
    apply H0; auto. apply no_tophole_bskl_open_rec. assumption.
  - apply d_refine_syn__hole.
    apply d_wf_pskl_Psi_mono with (Ψ := Δs); assumption.
  - apply d_refine_syn__tophole_remove. apply IHd_refine_syn; auto.
  - inversion Hnt; subst. inst_cofinites_for d_refine_syn__tophole_fill. intros X HX.
    apply H0; auto.
    + apply no_tophole_bskl_open_rec. assumption.
    + intros Y HY. simpl in HY |- *. destruct HY as [HY | HY]; [ left; assumption | right; auto ].
  - inversion Hnt.
Qed.

(** Move a tvar from the type context into the syn-scope [Δs] ([⫯]-free RHS). *)
Lemma d_refine_syn_move : forall Γ' Δs Δi Q P,
    Γ' ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P ->
    no_tophole_bskl P ->
    forall X Γ, Γ' = (X ~ dbind_tvar) ++ Γ ->
    Γ ⨟ (X :: Δs) ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ' Δs Δi Q P H. induction H; intros Hnt X0 Γ0 HΓ; subst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HS | [HI | Hb]].
    + left. simpl. right. assumption.
    + right. left. assumption.
    + apply binds_app_1 in Hb. destruct Hb as [Hb | Hb].
      * apply binds_one_iff in Hb. destruct Hb as [HX _]. subst.
        left. simpl. left. reflexivity.
      * right. right. assumption.
  - inversion Hnt; subst. apply d_refine_syn__arrow; auto.
  - inversion Hnt; subst. inst_cofinites_for d_refine_syn__all. intros Y HY.
    apply H0; auto. apply no_tophole_bskl_open_rec. assumption.
  - apply d_refine_syn__hole.
    eapply d_wf_pskl_move; [ eassumption | | reflexivity ].
    apply no_tophole_syn_inv. assumption.
  - apply d_refine_syn__tophole_remove. apply IHd_refine_syn; auto.
  - inversion Hnt; subst. inst_cofinites_for d_refine_syn__tophole_fill. intros Y HY.
    (* IH gives [X0 :: (Y :: Δs)]; reorder to [Y :: (X0 :: Δs)] via Ds_mono *)
    apply d_refine_syn_Ds_mono with (Δs := X0 :: (Y :: Δs)).
    + apply H0; auto. apply no_tophole_bskl_open_rec. assumption.
    + apply no_tophole_bskl_open_rec. assumption.
    + intros Z HZ. simpl in HZ |- *. tauto.
  - inversion Hnt.
Qed.

(** THE HOLE/Δi INVARIANT.  [hole_safe L P A]: [P] structurally matches the
    type [A] (with holes), and EVERY hole in [P] faces an [A]-subterm whose
    free vars avoid [L] (the enclosing-∀ vars).  This is the formal "ghosts
    fill only NON-inherited-∀ positions" discipline: under refinement, a kept
    nested ∀ routes its var into [Δi], and a hole there would be the banned
    "ghost fills an inh-∀" — [hs_hole]'s side condition rules it out, and is
    exactly what lets the hole case's well-formedness use [Δs ∪ Γ] (not Δi). *)
Inductive hole_safe : list atom -> pskl -> ptyp -> Prop :=
| hs_hole  : forall L A,
    (forall X, X `in` ftvar_in_ptyp A -> ~ List.In X L) -> hole_safe L pskl_hole A
| hs_unit  : forall L, hole_safe L pskl_unit ptyp_unit
| hs_var_f : forall L X, hole_safe L (pskl_var_f X) (ptyp_var_f X)
| hs_var_b : forall L n, hole_safe L (pskl_var_b n) (ptyp_var_b n)
| hs_arrow : forall L P1 P2 A1 A2,
    hole_safe L P1 A1 -> hole_safe L P2 A2 ->
    hole_safe L (pskl_arrow P1 P2) (ptyp_arrow A1 A2)
| hs_all   : forall L Lc P0 A0,
    (forall X, X `notin` Lc ->
       hole_safe (X :: L) (open_pskl_wrt_pskl P0 (pskl_var_f X))
                          (open_ptyp_wrt_ptyp A0 (ptyp_var_f X))) ->
    hole_safe L (pskl_all_syn P0) (ptyp_all A0).

(** CONSISTENCY→REFINEMENT CORE (the heart of [__check]): an [inh]-painted
    [hole_safe] skeleton refines the [colour]ing of its type.  By induction on
    [A]; at a hole [hs_hole]'s condition + the coverage give [Δs ∪ Γ] (so
    [hole_fills] applies); the ∀ case routes the var into [Δi] and recurses
    using [colour_open] + [colour_guide_open] + [pskl_to_bskl_inh_open]. *)
Lemma refine_colour_core : forall A,
    lc_ptyp A ->
    forall P Γ Δs Δi,
      hole_safe Δi P A ->
      (forall X, X `in` ftvar_in_ptyp A ->
         List.In X Δs \/ List.In X Δi \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Δs ⨟ Δi ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (colour (pskl_to_bskl_inh P) A).
Proof.
  intros A Hlc. induction Hlc; intros P Γ Δs Δi Hhs Hcov.
  - (* unit *) inversion Hhs; subst.
    + replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn_hole_fills;
        [ apply lc_ptyp_unit | intros X HX; simpl in HX; fsetdec ].
    + simpl. apply d_refine_syn__unit.
  - (* var X *) inversion Hhs; subst.
    + replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn_hole_fills.
      * apply lc_ptyp_var_f.
      * intros Y HY. destruct (Hcov Y HY) as [HS | [HI | HG]];
          [ left; assumption | exfalso; match goal with Hc : forall _ : atom, _ -> ~ List.In _ _ |- _ => eapply Hc; eauto end | right; assumption ].
    + simpl. apply d_refine_syn__var. apply Hcov. simpl. fsetdec.
  - (* arrow *) inversion Hhs; subst.
    + replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn_hole_fills.
      * apply lc_ptyp_arrow; assumption.
      * intros Y HY. destruct (Hcov Y HY) as [HS | [HI | HG]];
          [ left; assumption | exfalso; match goal with Hc : forall _ : atom, _ -> ~ List.In _ _ |- _ => eapply Hc; eauto end | right; assumption ].
    + simpl. apply d_refine_syn__arrow;
        [ apply IHHlc1 | apply IHHlc2 ]; try assumption;
        intros Y HY; apply Hcov; simpl; fsetdec.
  - (* all *) inversion Hhs; subst.
    + replace (pskl_to_bskl_inh pskl_hole) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn_hole_fills.
      * pick fresh X; apply (lc_ptyp_all_exists X); auto.
      * intros Y HY. destruct (Hcov Y HY) as [HS | [HI | HG]];
          [ left; assumption | exfalso; match goal with Hc : forall _ : atom, _ -> ~ List.In _ _ |- _ => eapply Hc; eauto end | right; assumption ].
    + simpl. inst_cofinites_for d_refine_syn__all. intros X HX.
      rewrite <- colour_open.
      rewrite <- (colour_guide_open _ (pskl_to_bskl_inh P0) X).
      rewrite <- !pskl_to_bskl_inh_open.
      apply H0; auto.
      intros Y HY. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY.
      simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
      * apply AtomSetImpl.singleton_1 in HY. subst. right. left. simpl. left. reflexivity.
      * destruct (Hcov Y HY) as [HS | [HI | HG]];
          [ left; assumption | right; left; simpl; right; assumption | right; right; assumption ].
Qed.

(** [utyp]-level hole-safety, the invariant [ghost_of_fill_gen] carries (since
    [forall_l] changes [P] and the LHS [U] together while keeping the RHS
    [A'] fixed, hole-safety must relate [P] to [U]). *)
Inductive hole_safe_u : list atom -> pskl -> utyp -> Prop :=
| hsu_hole  : forall L C,
    (forall X, X `in` ftvar_in_utyp C -> ~ List.In X L) -> hole_safe_u L pskl_hole C
| hsu_unit  : forall L, hole_safe_u L pskl_unit utyp_unit
| hsu_var_f : forall L X, hole_safe_u L (pskl_var_f X) (utyp_var_f X)
| hsu_var_b : forall L n, hole_safe_u L (pskl_var_b n) (utyp_var_b n)
| hsu_arrow : forall L P1 P2 C1 C2,
    hole_safe_u L P1 C1 -> hole_safe_u L P2 C2 ->
    hole_safe_u L (pskl_arrow P1 P2) (utyp_arrow C1 C2)
| hsu_all_syn : forall L Lc P0 C0,
    (forall X, X `notin` Lc ->
       hole_safe_u (X :: L) (open_pskl_wrt_pskl P0 (pskl_var_f X))
                            (open_utyp_wrt_utyp C0 (utyp_var_f X))) ->
    hole_safe_u L (pskl_all_syn P0) (utyp_all_syn C0)
| hsu_all_etag : forall L Lc e P0 C0,
    (forall X, X `notin` Lc ->
       hole_safe_u (X :: L) (open_pskl_wrt_pskl P0 (pskl_var_f X))
                            (open_utyp_wrt_utyp C0 (utyp_var_f X))) ->
    hole_safe_u L (pskl_all_syn P0) (utyp_all_etag e C0).

(** Anti-monotone in [L] (a smaller forbidden set is a weaker condition). *)
Lemma hole_safe_u_weaken : forall L P C,
    hole_safe_u L P C ->
    forall L', (forall X, List.In X L' -> List.In X L) ->
    hole_safe_u L' P C.
Proof.
  intros L P C H. induction H; intros L' Hsub; try (constructor; auto; fail).
  - apply hsu_hole. intros X HX HInL'. eapply H; eauto.
  - apply hsu_all_syn with (Lc := Lc). intros X HX. apply H0; auto.
    intros Y HY. simpl in HY |- *. destruct HY; [ left; assumption | right; auto ].
  - apply hsu_all_etag with (Lc := Lc). intros X HX. apply H0; auto.
    intros Y HY. simpl in HY |- *. destruct HY; [ left; assumption | right; auto ].
Qed.

(** Substituting [X] with [□] (in [P]) and [φ] (in [C]) preserves hole-safety
    (keeping [L]), provided [φ]'s free vars avoid [L].  [X] is a free param
    (not [L]'s head), so it composes under the [∀] binders. *)
Lemma hole_safe_u_subst : forall L P C,
    hole_safe_u L P C ->
    forall X phi, lc_utyp phi ->
    (forall Y, Y `in` ftvar_in_utyp phi -> ~ List.In Y L) ->
    hole_safe_u L (subst_pskl_in_pskl pskl_hole X P)
                  (subst_utyp_in_utyp phi X C).
Proof.
  intros L P C H. induction H; intros X0 phi Hlcphi Hphi; simpl.
  - (* hole *) apply hsu_hole. intros Y HY HInL.
    apply ftvar_in_utyp_subst_utyp_in_utyp_upper in HY. simpl in HY.
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
    + eapply Hphi; eauto.
    + apply AtomSetImpl.remove_3 in HY. eapply H; eauto.
  - (* unit *) apply hsu_unit.
  - (* var_f X *) destruct (X == X0); subst.
    + apply hsu_hole. intros Y HY. eapply Hphi; eauto.
    + apply hsu_var_f.
  - (* var_b *) apply hsu_var_b.
  - (* arrow *) apply hsu_arrow; [ apply IHhole_safe_u1 | apply IHhole_safe_u2 ]; assumption.
  - (* all_syn *) apply hsu_all_syn with (Lc := Lc \u singleton X0 \u ftvar_in_utyp phi).
    intros Y HY. assert (HYX : X0 <> Y) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var by (try assumption; apply lc_pskl_hole).
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (try assumption).
    eapply H0; [ fsetdec | assumption | ].
    intros Z HZ HZin. simpl in HZin. destruct HZin as [HZeq | HZL].
    * subst Z. assert (Y `notin` ftvar_in_utyp phi) by fsetdec. contradiction.
    * eapply Hphi; eauto.
  - (* all_etag *) apply hsu_all_etag with (Lc := Lc \u singleton X0 \u ftvar_in_utyp phi).
    intros Y HY. assert (HYX : X0 <> Y) by fsetdec.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var by (try assumption; apply lc_pskl_hole).
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (try assumption).
    eapply H0; [ fsetdec | assumption | ].
    intros Z HZ HZin. simpl in HZin. destruct HZin as [HZeq | HZL].
    * subst Z. assert (Y `notin` ftvar_in_utyp phi) by fsetdec. contradiction.
    * eapply Hphi; eauto.
Qed.

(** A type's skeleton is hole-safe w.r.t. the type's syn-painting (trivially —
    no holes).  Establishes the [hole_safe_u] invariant at the [ghost_of_fill]
    entry, where [P = ptyp_to_pskl C0]. *)
Lemma hole_safe_u_of_ptyp : forall C0,
    lc_ptyp C0 ->
    forall L, hole_safe_u L (ptyp_to_pskl C0) (ptyp_to_utyp_syn C0).
Proof.
  intros C0 Hlc. induction Hlc; intros L; simpl.
  - apply hsu_unit.
  - apply hsu_var_f.
  - apply hsu_arrow; auto.
  - apply hsu_all_syn with (Lc := empty). intros X HX.
    rewrite <- ptyp_to_pskl_open. rewrite <- (ptyp_to_utyp_syn_open _ (ptyp_var_f X)). auto.
Qed.

Lemma ptyp_to_btyp_inh_open_var : forall A X,
    open_btyp_wrt_btyp (ptyp_to_btyp_inh A) (btyp_var_f X) =
    ptyp_to_btyp_inh (open_ptyp_wrt_ptyp A (ptyp_var_f X)).
Proof.
  intros. unfold open_btyp_wrt_btyp, open_ptyp_wrt_ptyp.
  rewrite ptyp_to_btyp_inh_open_rec. reflexivity.
Qed.

(** Consistency preserves free vars: [A']'s ftvars are among [C]'s. *)
Lemma d_consis_ftvar : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    forall A', B = ptyp_to_btyp_inh A' ->
    ftvar_in_ptyp A' [<=] ftvar_in_utyp C.
Proof.
  intros Δ Γ C B H. induction H; intros A' Heq;
    destruct A'; simpl in Heq; try discriminate; inversion Heq; subst; simpl.
  - fsetdec.
  - fsetdec.
  - specialize (IHd_consis1 A'1 eq_refl). specialize (IHd_consis2 A'2 eq_refl). fsetdec.
  - (* forall_inh_tagged: A' = ptyp_all A'0 *)
    pick fresh X for (L \u ftvar_in_ptyp A' \u ftvar_in_utyp C).
    assert (Hsub : ftvar_in_ptyp (open_ptyp_wrt_ptyp A' (ptyp_var_f X)) [<=]
                   ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f X))).
    { eapply H0; [ auto | ]. rewrite ptyp_to_btyp_inh_open_var. reflexivity. }
    assert (HL : ftvar_in_ptyp A' [<=] ftvar_in_ptyp (open_ptyp_wrt_ptyp A' (ptyp_var_f X)))
      by apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower.
    assert (HU : ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f X)) [<=]
                 AtomSetImpl.union (ftvar_in_utyp (utyp_var_f X)) (ftvar_in_utyp C))
      by apply ftvar_in_utyp_open_utyp_wrt_utyp_upper.
    simpl in HU. fsetdec.
  - (* forall_inh_untagged *)
    pick fresh X for (L \u ftvar_in_ptyp A' \u ftvar_in_utyp C).
    assert (Hsub : ftvar_in_ptyp (open_ptyp_wrt_ptyp A' (ptyp_var_f X)) [<=]
                   ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f X))).
    { eapply H0; [ auto | ]. rewrite ptyp_to_btyp_inh_open_var. reflexivity. }
    assert (HL : ftvar_in_ptyp A' [<=] ftvar_in_ptyp (open_ptyp_wrt_ptyp A' (ptyp_var_f X)))
      by apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower.
    assert (HU : ftvar_in_utyp (open_utyp_wrt_utyp C (utyp_var_f X)) [<=]
                 AtomSetImpl.union (ftvar_in_utyp (utyp_var_f X)) (ftvar_in_utyp C))
      by apply ftvar_in_utyp_open_utyp_wrt_utyp_upper.
    simpl in HU. fsetdec.
Qed.

(** TRANSPORT: hole-safety on the [utyp] [C] transfers to the checking type
    [A'] consistent with it.  This bridges [gen]'s [utyp] invariant
    [hole_safe_u] to the [hole_safe] that [refine_colour_core] consumes. *)
Lemma hole_safe_u_transport : forall La Pa C,
    hole_safe_u La Pa C ->
    forall Δ Γ B A', Δ ⨟ Γ ⊨ C ≈ B -> B = ptyp_to_btyp_inh A' ->
    hole_safe La Pa A'.
Proof.
  intros La Pa C H. induction H; intros Δ Γ B A' Hd Heq.
  - (* hsu_hole *) apply hs_hole. intros Y HY.
    assert (Hsub : ftvar_in_ptyp A' [<=] ftvar_in_utyp C)
      by (eapply d_consis_ftvar; [ exact Hd | exact Heq ]).
    apply H. fsetdec.
  - (* hsu_unit *) revert Heq. inversion Hd; subst; intros Heq.
    destruct A'; simpl in Heq; try discriminate. apply hs_unit.
  - (* hsu_var_f *) revert Heq. inversion Hd; subst; intros Heq.
    destruct A'; simpl in Heq; try discriminate. inversion Heq; subst. apply hs_var_f.
  - (* hsu_var_b *) inversion Hd.
  - (* hsu_arrow *) revert Heq. inversion Hd; subst; intros Heq.
    destruct A'; simpl in Heq; try discriminate. inversion Heq; subst.
    apply hs_arrow; [ eapply IHhole_safe_u1 | eapply IHhole_safe_u2 ]; eauto.
  - (* hsu_all_syn *) revert Heq. inversion Hd; subst; intros Heq;
      destruct A'; simpl in Heq; try discriminate; inversion Heq; subst.
    match goal with Hsc : forall _ : atom, _ -> d_consis _ _ _ _ |- _ =>
      apply hs_all with (Lc := Lc \u L0); intros X HX;
      eapply H0; [ fsetdec | apply Hsc; fsetdec
                 | rewrite ptyp_to_btyp_inh_open_var; reflexivity ] end.
  - (* hsu_all_etag *) revert Heq. inversion Hd; subst; intros Heq;
      destruct A'; simpl in Heq; try discriminate; inversion Heq; subst.
    match goal with Hsc : forall _ : atom, _ -> d_consis _ _ _ _ |- _ =>
      apply hs_all with (Lc := Lc \u L0); intros X HX;
      eapply H0; [ fsetdec | apply Hsc; fsetdec
                 | rewrite ptyp_to_btyp_inh_open_var; reflexivity ] end.
Qed.

(** [tophole_safe P0 A]: a single top ghost [⫯] over a [hole_safe] core [P0],
    against [A].  The [⫯] skips [A]'s leading ∀s ([ths_all], → [__tophole_fill])
    and, at the first non-∀, the core [P0] must be [hole_safe] against that
    ∀-stripped [A] ([ths_leaf], → [__tophole_remove]).  This is exactly the
    shape [bskl_to_pskl Q] takes for a non-□ ghost [Q] (one top [⫯], syn-painted
    — hence [hole_safe], no nested [⫯] — below). *)
Inductive tophole_safe : pskl -> ptyp -> Prop :=
| ths_leaf : forall P0 A,
    (forall A0, A <> ptyp_all A0) -> hole_safe nil P0 A -> tophole_safe P0 A
| ths_all  : forall L P0 A0,
    (forall X, X `notin` L ->
       tophole_safe P0 (open_ptyp_wrt_ptyp A0 (ptyp_var_f X))) ->
    tophole_safe P0 (ptyp_all A0).

(** [colour] of a [⫯]-guide against a non-∀ type peeks past the [⫯] (provided
    the peeled guide isn't itself a [⫯]). *)
Lemma colour_tophole_peek : forall A Q0,
    (forall A0, A <> ptyp_all A0) ->
    (forall Q1, Q0 <> bskl_tophole Q1) ->
    colour (bskl_tophole Q0) A = colour Q0 A.
Proof.
  intros A Q0 HnA HnQ. destruct A; simpl; try reflexivity.
  - destruct Q0; simpl; try reflexivity. exfalso; eapply HnQ; reflexivity.
  - exfalso; eapply HnA; reflexivity.
Qed.

(** TOPHOLE refinement: the [⫯]-ghost refines [colour]'s output against [A].
    Leaf (non-∀ [A]): [__tophole_remove] + [refine_colour_core].
    ∀ [A]: [__tophole_fill] (the [⫯] persists into the body, joining [Δs]) +
    recursion on the body. *)
Lemma refine_colour_tophole : forall A,
    lc_ptyp A ->
    forall P0 Γ Δs Δi,
      tophole_safe P0 A ->
      (forall X, X `in` ftvar_in_ptyp A ->
         List.In X Δs \/ binds X dbind_tvar Γ) ->
      Γ ⨟ Δs ⨟ Δi ⊢ᵣ (bskl_tophole (pskl_to_bskl_inh P0))
                     ⊳ (colour (bskl_tophole (pskl_to_bskl_inh P0)) A).
Proof.
  intros A Hlc. induction Hlc; intros P0 Γ Δs Δi Hts Hcov.
  - (* unit *) inversion Hts; subst.
    match goal with Hhs : hole_safe nil P0 ptyp_unit |- _ =>
      assert (Hntp : forall Q1, pskl_to_bskl_inh P0 <> bskl_tophole Q1)
        by (intros Q1; inversion Hhs; subst; simpl; discriminate) end.
    rewrite colour_tophole_peek by (try (intros; discriminate); exact Hntp).
    apply d_refine_syn__tophole_remove.
    apply refine_colour_core; [ apply lc_ptyp_unit | assumption | intros Y HY; simpl in HY; fsetdec ].
  - (* var X *) inversion Hts; subst.
    match goal with Hhs : hole_safe nil P0 (ptyp_var_f _) |- _ =>
      assert (Hntp : forall Q1, pskl_to_bskl_inh P0 <> bskl_tophole Q1)
        by (intros Q1; inversion Hhs; subst; simpl; discriminate) end.
    rewrite colour_tophole_peek by (try (intros; discriminate); exact Hntp).
    apply d_refine_syn__tophole_remove.
    apply refine_colour_core; [ apply lc_ptyp_var_f | assumption
      | intros Y HY; destruct (Hcov Y HY) as [HS | HG]; [ left; assumption | right; right; assumption ] ].
  - (* arrow *) inversion Hts; subst.
    match goal with Hhs : hole_safe nil P0 (ptyp_arrow _ _) |- _ =>
      assert (Hntp : forall Q1, pskl_to_bskl_inh P0 <> bskl_tophole Q1)
        by (intros Q1; inversion Hhs; subst; simpl; discriminate) end.
    rewrite colour_tophole_peek by (try (intros; discriminate); exact Hntp).
    apply d_refine_syn__tophole_remove.
    apply refine_colour_core; [ apply lc_ptyp_arrow; assumption | assumption
      | intros Y HY; destruct (Hcov Y HY) as [HS | HG]; [ left; assumption | right; right; assumption ] ].
  - (* all *) inversion Hts; subst.
    + (* ths_leaf: impossible, A = ptyp_all *)
      match goal with H : forall _ : ptyp, _ |- _ => exfalso; apply (H _ eq_refl) end.
    + (* ths_all: __tophole_fill *)
      simpl. inst_cofinites_for d_refine_syn__tophole_fill. intros X HX.
      rewrite <- colour_open. apply H0.
      * match goal with Hb : forall _ : atom, _ -> tophole_safe _ _ |- _ => apply Hb; auto end.
      * intros Y HY. apply ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper in HY.
        simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [HY | HY].
        -- apply AtomSetImpl.singleton_1 in HY. subst. left. simpl. left. reflexivity.
        -- destruct (Hcov Y HY) as [HS | HG]; [ left; simpl; right; assumption | right; assumption ].
Qed.

(** [forall_l] maintenance: from the [hsu_all] body (one [∀] stripped), the
    instantiation [□]/[φ] re-establishes [hole_safe_u] at [nil] for the
    recursion — exactly [subst_intro] + [hole_safe_u_subst] + [weaken]. *)
Lemma hole_safe_u_open_fill : forall L P0 C ph,
    (forall X, X `notin` L ->
       hole_safe_u (X :: nil) (open_pskl_wrt_pskl P0 (pskl_var_f X))
                              (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    lc_utyp ph ->
    hole_safe_u nil (open_pskl_wrt_pskl P0 pskl_hole) (open_utyp_wrt_utyp C ph).
Proof.
  intros L P0 C ph Hbody Hlc.
  pick fresh X for (L \u ftvar_in_pskl P0 \u ftvar_in_utyp C \u ftvar_in_utyp ph).
  rewrite (subst_pskl_in_pskl_intro X P0 pskl_hole) by fsetdec.
  rewrite (subst_utyp_in_utyp_intro X C ph) by fsetdec.
  apply hole_safe_u_weaken with (L := X :: nil); [ | intros Y HY; inversion HY ].
  apply hole_safe_u_subst.
  - apply Hbody. fsetdec.
  - exact Hlc.
  - intros Y HY HIn. simpl in HIn. destruct HIn as [Heq | Hnil];
      [ subst Y; fsetdec | inversion Hnil ].
Qed.

(** A [__check] leaf: the ghost's top [⫯] over [P] refines [colour]'s output
    against the guarded checking type [A'].  Consumes the threaded
    [hole_safe_u nil P C] invariant (via [hole_safe_u_transport] to [A']) and
    feeds [refine_colour_tophole]. *)
Lemma check_leaf : forall Γ P C A' Δ,
    guarded_btyp (ptyp_to_btyp_inh A') ->
    Δ ⨟ Γ ⊨ C ≈ ptyp_to_btyp_inh A' ->
    hole_safe_u nil P C ->
    d_wf_ptyp Γ A' ->
    Γ ⨟ nil ⨟ nil ⊢ᵣ (bskl_tophole (pskl_to_bskl_inh P))
                   ⊳ (colour (bskl_tophole (pskl_to_bskl_inh P)) A').
Proof.
  intros Γ P C A' Δ Hgb Hcons Hhsu Hwf.
  assert (Hnall' : forall A0, A' <> ptyp_all A0)
    by (intros A0 Hc; subst A'; inversion Hgb).
  apply refine_colour_tophole.
  - eapply d_wf_ptyp_lc_loc; eauto.
  - apply ths_leaf;
      [ exact Hnall'
      | eapply hole_safe_u_transport; [ exact Hhsu | exact Hcons | reflexivity ] ].
  - intros X HX. right. eapply d_wf_ptyp_ftvar; eauto.
Qed.

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
      hole_safe_u nil P U ->
      Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q))
                       ⊳ (colour (pskl_to_bskl_inh (bskl_to_pskl Q)) A').
Proof.
  intros Δ Γ U V H. remember mode_tc as m eqn:Hm. revert Hm.
  induction H; intros Hm A' P Q Heq Hwfa Hsub Hg Hhsu; try discriminate Hm.
  - (* __check: ghost top-⫯ over P, refined against guarded A' via check_leaf;
       P=□ fills directly.  Δ/A' from Heq; C guarded ⟹ P is non-∀/non-⫯. *)
    subst B.
    destruct Hg as [ | Xg | Pg1 Pg2 | | Pgt Qgt | bdy Qbdy ].
    + (* ghost__unit: P = pskl_unit, Q = ⫯unit *)
      eapply check_leaf with (P := pskl_unit);
        [ eassumption | eassumption | exact Hhsu | exact Hwfa ].
    + (* ghost__var *)
      eapply check_leaf with (P := pskl_var_f Xg);
        [ eassumption | eassumption | exact Hhsu | exact Hwfa ].
    + (* ghost__arrow *)
      simpl. rewrite !bskl_to_pskl_pskl_to_bskl_syn.
      eapply check_leaf with (P := pskl_arrow Pg1 Pg2);
        [ eassumption | eassumption | exact Hhsu | exact Hwfa ].
    + (* ghost__hole: P = □, Q = □ — fills any type *)
      simpl. rewrite colour_hole. apply d_refine_syn__hole.
      apply d_wf_pskl_of_wf_ptyp; exact Hwfa.
    + (* ghost__tophole: P = ⫯P0 — impossible (skel C has no ⫯) *)
      exfalso. inversion Hsub; subst. destruct C; simpl in *; discriminate.
    + (* ghost__all: P = all_syn — impossible (C guarded) *)
      exfalso. inversion Hsub; subst. destruct C; simpl in *; try discriminate;
        match goal with Hg2 : guarded_utyp _ |- _ => inversion Hg2 end.
  - (* __forall_r: A' = ∀.A'0; the ⫯ in [inh{Q}] fills it (tophole_fill) *)
    destruct A' as [ | | | | A'0 ]; simpl in Heq; try discriminate.
    inversion Heq; subst.
    destruct (ghost_of_shape Hg) as [HQ | [Q0 HQ]]; subst.
    + (* Q = □: [inh{Q}] = □ fills any type *)
      replace (pskl_to_bskl_inh (bskl_to_pskl bskl_hole)) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn__hole.
      apply d_wf_pskl_of_wf_ptyp; exact Hwfa.
    + (* Q = ⫯Q0: tophole_fill; the cofinite IH gives the body at (X::Γ)⨟nil⨟nil,
         moved to Γ⨟(X::nil)⨟nil by [d_refine_syn_move] (colour output is
         [⫯]-free, so the move is valid). *)
      simpl. inversion Hwfa; subst.
      inst_cofinites_for d_refine_syn__tophole_fill. intros X HX.
      rewrite <- colour_open.
      eapply d_refine_syn_move; [ | apply colour_no_tophole | reflexivity ].
      eapply H0 with (P := P) (Q := bskl_tophole Q0).
      * auto.
      * reflexivity.
      * unfold open_btyp_wrt_btyp. symmetry. apply ptyp_to_btyp_inh_open_rec.
      * match goal with Hb : forall _, _ `notin` _ -> d_wf_ptyp _ _ |- _ => apply Hb; auto end.
      * exact Hsub.
      * exact Hg.
      * exact Hhsu.
  - (* __forall_l_tagged: U = utyp_all_etag ε C *)
    simpl in Hsub. inversion Hsub; subst.
    + (* P = □ ⟹ Q = □, fills any type *)
      inversion Hg; subst.
      replace (pskl_to_bskl_inh (bskl_to_pskl bskl_hole)) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn__hole. apply d_wf_pskl_of_wf_ptyp; exact Hwfa.
    + (* P = pskl_all_syn P' : the KEY case — recurse with □ absorbing φ *)
      inversion Hg; subst.
      eapply IHd_sub; [ reflexivity | reflexivity | exact Hwfa | | eassumption | ].
      * rewrite utyp_to_pskl_open.
        apply pskl_subsumes_open_rec; [ assumption | apply pskl_subsumes__hole ].
      * inversion Hhsu; subst.
        match goal with Hb : forall _ : atom, _ -> hole_safe_u _ _ _ |- _ =>
          eapply hole_safe_u_open_fill; [ exact Hb | apply is_ttyp_lc; eassumption ] end.
  - (* __forall_l_untagged: U = utyp_all_syn C — identical to tagged *)
    simpl in Hsub. inversion Hsub; subst.
    + inversion Hg; subst.
      replace (pskl_to_bskl_inh (bskl_to_pskl bskl_hole)) with (@bskl_hole) by reflexivity.
      rewrite colour_hole. apply d_refine_syn__hole. apply d_wf_pskl_of_wf_ptyp; exact Hwfa.
    + inversion Hg; subst.
      eapply IHd_sub; [ reflexivity | reflexivity | exact Hwfa | | eassumption | ].
      * rewrite utyp_to_pskl_open.
        apply pskl_subsumes_open_rec; [ assumption | apply pskl_subsumes__hole ].
      * inversion Hhsu; subst.
        match goal with Hb : forall _ : atom, _ -> hole_safe_u _ _ _ |- _ =>
          eapply hole_safe_u_open_fill; [ exact Hb | apply is_ttyp_lc; eassumption ] end.
Qed.

(** BRICK 3 GOAL — the fill side, now a corollary of [ghost_of_fill_gen]
    (path (b) was taken: deterministic witness [colour]).  The ghost [Q]
    inferred for a base term's principal type [C] refines the colouring
    [colour inh{Q} A'] of every checking type [A'] the term subsumes to.
    Depends on [ghost_of_fill_gen]'s two remaining admits ([__check],
    [forall_r/⫯]); the rest of the induction (incl. the original [forall_l]
    [φ]/[□] obstacle and [P=□]) is proved. *)
Lemma ghost_of_fill : forall C Q Γ A',
    lc_ptyp C ->
    ghost_of (ptyp_to_pskl C) Q ->
    d_wf_ptyp Γ A' ->
    empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn C) ⊑ (ptyp_to_btyp_inh A') ->
    exists B, bskl_to_pskl B = ptyp_to_pskl A' /\
              Γ ⨟ nil ⨟ nil ⊢ᵣ (pskl_to_bskl_inh (bskl_to_pskl Q)) ⊳ B.
Proof.
  intros C Q Γ A' Hlc Hg Hwfa Hsub.
  exists (colour (pskl_to_bskl_inh (bskl_to_pskl Q)) A'). split.
  - apply colour_erasure.
  - eapply ghost_of_fill_gen with (P := ptyp_to_pskl C);
      [ exact Hsub | reflexivity | exact Hwfa | | exact Hg | ].
    + rewrite utyp_to_pskl_ptyp_to_utyp_syn. apply pskl_subsumes_refl.
    + apply hole_safe_u_of_ptyp. exact Hlc.
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
  (* RE-PLAN (post model-fix: d_pat is self-contained over ONE Γ, "a type is a
     skel" via [d_pat__var]/[dbind_to_pskl]; the old [denv_coh] two-context plan
     and its [var]-case "stuck" worry are GONE).  Decoupled into:
     - [d_pat_total] (induction on [d_typing]): [exists Q, Γ ⊢[m] e ⇨ Q].
       Helpers: [d_pat_binding_eq] (abs: rebind [x:typ A] ↦ [x:skl (skel A)];
       cascades to [d_pat_sub]/[d_pat_consis]/[d_wf_pskl] binding-invariance,
       all routine since those read only tvar bindings); a weaken-to-[□] lemma
       (abs_check); tvar-strengthening (forall); [d_pat_sub_infer_ghost] (sub).
     - [d_pat_fill] (induction on [d_pat]): the per-[A] refinement; base-term
       leaves close with [ghost_of_fill] (Qed, axiom-free); λ/app recurse.
     Then [d_pat_safety] combines [d_pat_total] (the [Q]) with [d_pat_fill]. *)
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
