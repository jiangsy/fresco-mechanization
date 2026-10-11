(** Fresco — basic syntactic lemmas about the SHAPE PREDICATES.

    ⚙ Everything about the paint/erase CONVERSIONS — retractions, [open]
    commutation, [lc] transport — lives in [prop_coercions.v], which this file
    re-exports, so a consumer importing this one sees both.  What is here is
    the predicate layer: ghost-freeness. *)

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Export src.fresco.prop_coercions.

(** * Ghost-freeness — the TYPE sub-universe of [pskl] / [bskl].

    [pskl_ghost_free] (fresco/def_shapes.v) is how the algorithmic rules say
    "this position is one of the paper's [A] / [B], not one of its [P] / [Q]".
    The purely syntactic half of its kit lives here, where the RULE
    definitions (algo/def_rules.v) and the proofs that CONSTRUCT them can
    both reach it; the semantic half (fills, decorations) stays in
    algo/prop_pat_sub.v. *)

(** A painting of a [ptyp] has no ghosts — this is the "⇐" of the
    characterisation, and the one every consumer uses: [guess^TY] outputs,
    annotations and [skmod{TY}] inputs are all [⌈A⌉]. *)
Lemma ptyp_to_pskl_ghost_free : forall A, pskl_ghost_free (ptyp_to_pskl A).
Proof. induction A; simpl; auto. Qed.

(** …and conversely, a ghost-free skeleton IS a painted type ("⇒").  Needed
    nowhere in the rules, but it is what justifies calling the predicate a
    SORT rather than a side condition. *)
Lemma pskl_ghost_free_to_ptyp : forall P,
  pskl_ghost_free P -> exists A, P = ptyp_to_pskl A.
Proof.
  induction P; simpl; intros Hg; try contradiction.
  - exists ptyp_unit; reflexivity.
  - exists (ptyp_var_b n); reflexivity.
  - exists (ptyp_var_f α); reflexivity.
  - destruct Hg as [Hg1 Hg2].
    destruct (IHP1 Hg1) as [A1 ->]; destruct (IHP2 Hg2) as [A2 ->].
    exists (ptyp_arrow A1 A2); reflexivity.
  - destruct (IHP Hg) as [A ->]. exists (ptyp_all A); reflexivity.
Qed.

(** Opening by an arbitrary GHOST-FREE skeleton — what [Sub-ForallL]'s
    instantiation needs ([guess^TY]'s output is a painted monotype). *)
Lemma pskl_ghost_free_open_rec_gen : forall P P' k,
  pskl_ghost_free P -> pskl_ghost_free P' ->
  pskl_ghost_free (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k Hg Hg'; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma pskl_ghost_free_open_gen : forall P P',
  pskl_ghost_free P -> pskl_ghost_free P' ->
  pskl_ghost_free (open_pskl_wrt_pskl P P').
Proof. intros P P' Hg Hg'; apply pskl_ghost_free_open_rec_gen; assumption. Qed.

(** The variable instances. *)
Lemma pskl_ghost_free_open_rec : forall P α' k,
  pskl_ghost_free P ->
  pskl_ghost_free (open_pskl_wrt_pskl_rec k (pskl_var_f α') P).
Proof. intros; apply pskl_ghost_free_open_rec_gen; simpl; auto. Qed.

Lemma pskl_ghost_free_open : forall P α',
  pskl_ghost_free P ->
  pskl_ghost_free (open_pskl_wrt_pskl P (pskl_var_f α')).
Proof. intros; apply pskl_ghost_free_open_gen; simpl; auto. Qed.

Lemma pskl_ghost_free_close_rec : forall P α k,
  pskl_ghost_free P ->
  pskl_ghost_free (close_pskl_wrt_pskl_rec k α P).
Proof.
  induction P; intros α0 k Hg; simpl in *; try contradiction; auto.
  - destruct (lt_ge_dec n k); simpl; auto.
  - destruct_if; simpl; auto.
  - destruct Hg as [Hg1 Hg2]; split; auto.
Qed.

Lemma pskl_ghost_free_close : forall P α,
  pskl_ghost_free P -> pskl_ghost_free (close_pskl_wrt_pskl α P).
Proof. intros P α Hg; apply pskl_ghost_free_close_rec; exact Hg. Qed.

(** Ghost-freeness survives substitution by anything ghost-free. *)
Lemma pskl_ghost_free_subst : forall P P' β,
  pskl_ghost_free P -> pskl_ghost_free P' ->
  pskl_ghost_free (subst_pskl_in_pskl P' β P).
Proof.
  induction P; intros P' β Hg Hg'; simpl in *; intuition.
  destruct_if; simpl; auto.
Qed.

Lemma pskl_ghost_free_subst_var : forall P α β,
  pskl_ghost_free P ->
  pskl_ghost_free (subst_pskl_in_pskl (pskl_var_f α) β P).
Proof. intros P α β Hg; apply pskl_ghost_free_subst; [ exact Hg | exact I ]. Qed.

Lemma bskl_ghost_free_open_rec : forall Q α' k,
  bskl_ghost_free Q ->
  bskl_ghost_free (open_bskl_wrt_bskl_rec k (bskl_var_f α') Q).
Proof.
  induction Q; intros α' k Hg; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma pskl_to_bskl_inh_ghost_free : forall P,
  pskl_ghost_free P ->
  bskl_ghost_free (pskl_to_bskl_inh P).
Proof. induction P; simpl; intuition. Qed.

Lemma pskl_to_bskl_syn_ghost_free : forall P,
  pskl_ghost_free P ->
  bskl_ghost_free (pskl_to_bskl_syn P).
Proof. induction P; simpl; intuition. Qed.

Lemma is_iskl_pskl_to_bskl_inh : forall P,
  lc_pskl P -> is_iskl (pskl_to_bskl_inh P).
Proof.
  intros P Hlc; induction Hlc; simpl; try solve [ constructor; auto ].
  apply is_iskl__all with (L := {}). intros α _.
  rewrite <- pskl_to_bskl_inh_open. auto.
Qed.

(** The workhorse for discharging a rule's SORT premise.  Every algorithmic
    type position is reached from another one by opening, closing, renaming or
    instantiating with a [guess^TY] output, so the closure kit above is
    complete for them; the final [simpl; intuition] handles the concrete
    skeletons of the test/counterexample files. *)
Ltac ghost_free_auto :=
  solve [ assumption
        | apply ptyp_to_pskl_ghost_free
        | (apply pskl_ghost_free_subst_var; ghost_free_auto)
        | (apply pskl_ghost_free_open; ghost_free_auto)
        | (apply pskl_ghost_free_close; ghost_free_auto)
        | (apply pskl_ghost_free_subst; ghost_free_auto)
        | (simpl; intuition) ].

(** The INVERSE of [pskl_ghost_free_open_rec]: opening a body cannot destroy
    a ghost either, so the sort of a ∀-body is read off any of its instances.
    This is what turns the cofinite [uskl_ghost_free] into the [Fixpoint]
    [pskl_ghost_free] across an erasure. *)
Lemma pskl_ghost_free_open_rec_inv : forall P P' k,
  pskl_ghost_free (open_pskl_wrt_pskl_rec k P' P) ->
  pskl_ghost_free P.
Proof.
  induction P; intros P' k Hg; simpl in *; auto.
  - destruct Hg as [Hg1 Hg2]; split; eauto.
  - eauto.
Qed.

(** [pskl_ghost_free] is a [Fixpoint] into [Prop] built from [True], [False]
    and conjunction, so it is decidable by structural recursion — which is what lets a
    consumer CASE SPLIT on the ForallR-PRIORITY guard.  (The boolean [ghost_free_ck]
    of ext_algo/def_dec.v says the same thing, but it is downstream.) *)
(* ⚙ [sumbool …] spelled out: the tree's notation layer claims [+] at term
   level 50, so the usual [{A} + {B}] does not parse here. *)
Lemma pskl_ghost_free_dec : forall P,
  sumbool (pskl_ghost_free P) (~ pskl_ghost_free P).
Proof.
  induction P; simpl;
    try solve [ left; exact I | right; auto ].
  - destruct IHP1 as [H1 | H1]; [ | right; tauto ].
    destruct IHP2 as [H2 | H2]; [ left; split; assumption | right; tauto ].
  - exact IHP.
Qed.

(** * Mode/type compatibility ([mod_comp_ty], fresco/def_shapes.v). *)
Lemma mod_comp_ty_tc_inv : forall B, mod_comp_ty B mode_tc -> is_ityp B.
Proof. intros B H. inversion H; subst; assumption. Qed.

(* ===================================================================== *)
(*  HOLE-FREENESS is stable under the operations the rules perform         *)
(*                                                                        *)
(*  [_subst] serves ext_algo §8c.10 ([Assign-Assign] / [Flex-Flex-Assign], *)
(*  whose recursion substitutes a definition PAYLOAD into the skeletons).  *)
(* ===================================================================== *)

Lemma pskl_no_ghost_open_rec : forall P P' k,
  pskl_no_ghost P -> pskl_no_ghost P' ->
  pskl_no_ghost (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k HP HV; simpl in *; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
  - destruct HP; split; auto.
Qed.

Lemma pskl_no_ghost_open : forall P α,
  pskl_no_ghost P ->
  pskl_no_ghost (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof.
  intros P α HP. apply pskl_no_ghost_open_rec; simpl; auto.
Qed.

(* ===================================================================== *)
(*  MONOTYPE SUBSTITUTION preserves the shape predicates                   *)
(*                                                                        *)
(*  Substituting the painting of a monotype [τ] for a type variable keeps *)
(*  every colour / category / guardedness predicate.  ⭐ These are the ONE *)
(*  copy of each fact: the declarative [_subst_unit] (decl/              *)
(*  prop_syntax_directed.v, decl/prop_skeleton.v) and [_rename_tvar]      *)
(*  (decl/prop_renaming.v) lemmas, and the algorithmic / decorated        *)
(*  [_subst_var] ones, are their [τ := unit] / [τ := β] instances.        *)
(*  ⚙ Moved here 2026-10-10 from algo/prop_suffix_erase.v,               *)
(*  algo/prop_pat_sub.v and algo/prop_basic.v.  Instantiate them with     *)
(*  [exact], not [apply]: [apply] will not unfold [ptyp_to_btyp_syn ?τ].  *)
(* ===================================================================== *)

(* ⚙ [Set Implicit Arguments] is SCOPED to this section: these lemmas came
   from files that set it, and their call sites apply them with the
   inferable arguments implicit. *)
Set Implicit Arguments.

(** Monotype paintings: locally closed, guarded, and of every colour. *)
Lemma mono_ptyp_to_btyp_syn_lc : forall τ,
  mono_ptyp τ -> lc_btyp (ptyp_to_btyp_syn τ).
Proof. induction 1; simpl; auto. Qed.

Lemma mono_ptyp_to_utyp_syn_lc : forall τ,
  mono_ptyp τ -> lc_utyp (ptyp_to_utyp_syn τ).
Proof. induction 1; simpl; auto. Qed.

Lemma mono_ptyp_to_uskl_syn_lc : forall τ,
  mono_ptyp τ -> lc_uskl (ptyp_to_uskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply lc_uskl_unit | apply lc_uskl_var_f | apply lc_uskl_arrow; auto ].
Qed.

Lemma mono_ptyp_to_bskl_syn_lc : forall τ,
  mono_ptyp τ -> lc_bskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; simpl;
    [ apply lc_bskl_unit | apply lc_bskl_var_f | apply lc_bskl_arrow; auto ].
Qed.

Lemma mono_ptyp_to_pskl_guarded : forall τ,
  mono_ptyp τ -> guarded_pskl (ptyp_to_pskl τ).
Proof.
  destruct 1 as [ | α | A1 A2 ]; simpl;
    [ apply guarded_pskl__unit | apply guarded_pskl__var
    | apply guarded_pskl__arrow; apply mono_ptyp_to_pskl_lc; auto ].
Qed.

Lemma mono_ptyp_to_btyp_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_btyp (ptyp_to_btyp_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_btyp__unit | apply guarded_btyp__var
    | apply guarded_btyp__arrow; apply mono_ptyp_to_btyp_syn_lc; auto ].
Qed.

Lemma mono_ptyp_to_utyp_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_utyp (ptyp_to_utyp_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_utyp__unit | apply guarded_utyp__var
    | apply guarded_utyp__arrow; apply mono_ptyp_to_utyp_syn_lc; auto ].
Qed.

Lemma mono_ptyp_to_uskl_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_uskl (ptyp_to_uskl_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_uskl__unit | apply guarded_uskl__var
    | apply guarded_uskl__arrow; apply mono_ptyp_to_uskl_syn_lc; auto ].
Qed.

Lemma mono_ptyp_to_bskl_syn_guarded : forall τ,
  mono_ptyp τ -> guarded_bskl (ptyp_to_bskl_syn τ).
Proof.
  destruct 1; simpl;
    [ apply guarded_bskl__unit | apply guarded_bskl__var
    | apply guarded_bskl__arrow; apply mono_ptyp_to_bskl_syn_lc; auto ].
Qed.

(** A monotype carries no quantifier, so it is BOTH synthesised and
    inherited — which is what lets substitution by it keep either colour. *)
Lemma mono_ptyp_to_btyp_syn_is_styp : forall τ,
  mono_ptyp τ -> is_styp (ptyp_to_btyp_syn τ).
Proof.
  induction 1; simpl; eauto 3 using is_styp.
Qed.

Lemma mono_ptyp_to_btyp_syn_is_ityp : forall τ,
  mono_ptyp τ -> is_ityp (ptyp_to_btyp_syn τ).
Proof.
  induction 1; simpl; eauto 3 using is_ityp.
Qed.

Lemma mono_ptyp_to_utyp_syn_is_dtyp : forall τ,
  mono_ptyp τ -> is_dtyp (ptyp_to_utyp_syn τ).
Proof.
  induction 1; simpl; eauto 3 using is_dtyp.
Qed.

Lemma mono_ptyp_to_bskl_syn_is_sskl : forall τ,
  mono_ptyp τ -> is_sskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; cbn [ptyp_to_bskl_syn ptyp_to_pskl pskl_to_bskl_syn]; eauto 3 using is_sskl.
Qed.

Lemma mono_ptyp_to_bskl_syn_is_iskl : forall τ,
  mono_ptyp τ -> is_iskl (ptyp_to_bskl_syn τ).
Proof.
  induction 1; cbn [ptyp_to_bskl_syn ptyp_to_pskl pskl_to_bskl_syn]; eauto 3 using is_iskl.
Qed.

Lemma mono_ptyp_to_uskl_syn_is_dskl : forall τ,
  mono_ptyp τ -> is_dskl (ptyp_to_uskl_syn τ).
Proof.
  induction 1; cbn [ptyp_to_uskl_syn ptyp_to_bskl_syn ptyp_to_pskl pskl_to_bskl_syn bskl_to_uskl]; eauto 3 using is_dskl.
Qed.

(** ** The substitution lemmas, types. *)

Lemma is_styp_subst_mono : forall B τ α,
  is_styp B -> mono_ptyp τ ->
  is_styp (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B).
Proof.
  intros B τ α H Hm; induction H; simpl; try solve [eauto 3 using is_styp].
  - destruct_if; eauto 3 using is_styp, mono_ptyp_to_btyp_syn_is_styp.
  - apply is_styp__all with (L := L `union` singleton α). intros β Hβ.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var;
      [ | clear - Hβ; fsetdec | apply mono_ptyp_to_btyp_syn_lc; assumption ].
    apply H0. clear - Hβ; fsetdec.
Qed.

Lemma is_ityp_subst_mono : forall B τ α,
  is_ityp B -> mono_ptyp τ ->
  is_ityp (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B).
Proof.
  intros B τ α H Hm; induction H; simpl; try solve [eauto 3 using is_ityp].
  - destruct_if; eauto 3 using is_ityp, mono_ptyp_to_btyp_syn_is_ityp.
  - apply is_ityp__all with (L := L `union` singleton α). intros β Hβ.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var;
      [ | clear - Hβ; fsetdec | apply mono_ptyp_to_btyp_syn_lc; assumption ].
    apply H0. clear - Hβ; fsetdec.
Qed.

Lemma mod_comp_ty_subst_mono : forall B m τ α,
  mod_comp_ty B m -> mono_ptyp τ ->
  mod_comp_ty (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B) m.
Proof.
  intros B m τ α H Hm; induction H; simpl;
    eauto 3 using mod_comp_ty, is_styp_subst_mono, is_ityp_subst_mono.
Qed.

Lemma guarded_btyp_subst_mono : forall B τ α,
  guarded_btyp B -> mono_ptyp τ ->
  guarded_btyp (subst_btyp_in_btyp (ptyp_to_btyp_syn τ) α B).
Proof.
  intros B τ α H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_btyp_syn_guarded with fresco.
  - apply guarded_btyp__arrow;
      apply subst_btyp_in_btyp_lc_btyp;
      auto using mono_ptyp_to_btyp_syn_lc.
Qed.

Lemma guarded_utyp_subst_mono : forall C τ α,
  guarded_utyp C -> mono_ptyp τ ->
  guarded_utyp (subst_utyp_in_utyp (ptyp_to_utyp_syn τ) α C).
Proof.
  intros C τ α H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_utyp_syn_guarded with fresco.
  - apply guarded_utyp__arrow;
      apply subst_utyp_in_utyp_lc_utyp;
      auto using mono_ptyp_to_utyp_syn_lc.
Qed.

Lemma is_dtyp_subst_mono : forall C τ α,
  is_dtyp C -> mono_ptyp τ ->
  is_dtyp (subst_utyp_in_utyp (ptyp_to_utyp_syn τ) α C).
Proof.
  intros C τ α H Hm; induction H; simpl; try solve [eauto 3 using is_dtyp].
  - destruct_if; eauto 3 using is_dtyp, mono_ptyp_to_utyp_syn_is_dtyp.
  - apply is_dtyp__all_tag with (L := L `union` {{α}}). intros β Hβ.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var;
      [ auto | clear - Hβ; fsetdec | apply mono_ptyp_to_utyp_syn_lc; assumption ].
Qed.

(** ** …and skeletons. *)

Lemma guarded_pskl_subst_mono : forall P τ β,
  guarded_pskl P -> mono_ptyp τ ->
  guarded_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros P τ β H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_pskl_guarded with fresco.
  - apply guarded_pskl__arrow;
      apply subst_pskl_in_pskl_lc_pskl;
      auto using mono_ptyp_to_pskl_lc.
Qed.

Lemma guarded_uskl_subst_mono : forall R τ β,
  guarded_uskl R -> mono_ptyp τ ->
  guarded_uskl (subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β R).
Proof.
  intros R τ β H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_uskl_syn_guarded with fresco.
  - apply guarded_uskl__arrow;
      apply subst_uskl_in_uskl_lc_uskl;
      auto using mono_ptyp_to_uskl_syn_lc.
Qed.

Lemma guarded_bskl_subst_mono : forall Q τ β,
  guarded_bskl Q -> mono_ptyp τ ->
  guarded_bskl (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q).
Proof.
  intros Q τ β H Hm; destruct H; simpl.
  - auto with fresco.
  - destruct_if; auto using mono_ptyp_to_bskl_syn_guarded with fresco.
  - apply guarded_bskl__arrow;
      apply subst_bskl_in_bskl_lc_bskl;
      auto using mono_ptyp_to_bskl_syn_lc.
Qed.

Lemma is_sskl_subst_mono : forall Q τ β,
  is_sskl Q -> mono_ptyp τ ->
  is_sskl (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q).
Proof.
  intros Q τ β H Hm; induction H; simpl; try solve [eauto 3 using is_sskl].
  - destruct_if; eauto 3 using is_sskl, mono_ptyp_to_bskl_syn_is_sskl.
  - apply is_sskl__all with (L := L `union` {{β}}).
    intros α Hα.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ auto | intro He; subst; clear - Hα; fsetdec
      | apply mono_ptyp_to_bskl_syn_lc; assumption ].
Qed.

Lemma is_iskl_subst_mono : forall Q τ β,
  is_iskl Q -> mono_ptyp τ ->
  is_iskl (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q).
Proof.
  intros Q τ β H Hm; induction H; simpl; try solve [eauto 3 using is_iskl].
  - destruct_if; eauto 3 using is_iskl, mono_ptyp_to_bskl_syn_is_iskl.
  - apply is_iskl__all with (L := L `union` {{β}}).
    intros α Hα.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var;
      [ auto | intro He; subst; clear - Hα; fsetdec
      | apply mono_ptyp_to_bskl_syn_lc; assumption ].
Qed.

Lemma mod_comp_sk_subst_mono : forall Q m τ β,
  mod_comp_sk Q m -> mono_ptyp τ ->
  mod_comp_sk (subst_bskl_in_bskl (ptyp_to_bskl_syn τ) β Q) m.
Proof.
  intros Q m τ β H Hm; induction H.
  - auto using is_sskl_subst_mono with fresco.
  - auto using is_sskl_subst_mono with fresco.
  - simpl; auto with fresco.
Qed.

Lemma is_dskl_subst_mono : forall ψ τ β,
  is_dskl ψ -> mono_ptyp τ ->
  is_dskl (subst_uskl_in_uskl (ptyp_to_uskl_syn τ) β ψ).
Proof.
  intros ψ τ β H Hm; induction H; simpl; try solve [eauto 3 using is_dskl].
  - destruct_if; eauto 3 using is_dskl, mono_ptyp_to_uskl_syn_is_dskl.
  - apply is_dskl__all_tag with (L := L `union` {{β}}).
    intros α Hα.
    rewrite subst_uskl_in_uskl_open_uskl_wrt_uskl_var;
      [ auto | intro He; subst; clear - Hα; fsetdec
      | apply mono_ptyp_to_uskl_syn_lc; assumption ].
Qed.

Unset Implicit Arguments.

(** Ghost-freeness under closing, and decorated-quantifier inversion. *)
Set Implicit Arguments.

Lemma pskl_no_ghost_close_rec : forall P β k,
  pskl_no_ghost P -> pskl_no_ghost (close_pskl_wrt_pskl_rec k β P).
Proof.
  induction P; intros β k H; simpl in *; auto.
  - (* var_b *) destruct (lt_ge_dec n k); simpl; auto.
  - (* var_f *) destruct (β == α); simpl; auto.
  - (* arrow *) destruct H; split; auto.
Qed.

Lemma pskl_no_ghost_close : forall P β,
  pskl_no_ghost P -> pskl_no_ghost (close_pskl_wrt_pskl β P).
Proof.
  intros P β H; unfold close_pskl_wrt_pskl;
    apply pskl_no_ghost_close_rec; exact H.
Qed.

Lemma is_dskl_all_tag_inv : forall ε ψ,
  is_dskl (uskl_all_tag ε ψ) ->
  exists L, forall α, α `notin` L ->
    is_dskl (open_uskl_wrt_uskl ψ (uskl_var_f α)).
Proof. intros ε ψ H; inversion H; subst. eexists; eassumption. Qed.
Unset Implicit Arguments.
