(** Frost — basic syntactic lemmas about the SHAPE PREDICATES.

    ⚙ Everything about the paint/erase CONVERSIONS — retractions, [open]
    commutation, [lc] transport — lives in [prop_coercions.v], which this file
    re-exports, so a consumer importing this one sees both.  What is here is
    the predicate layer: ghost-freeness. *)

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Export src.frost.prop_coercions.

(** * Ghost-freeness — the TYPE sub-universe of [pskl] / [bskl].

    [pskl_ghost_free] (frost/predicates.v) is how the algorithmic rules say
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

Lemma pskl_ghost_free_open_rec : forall P α' k,
  pskl_ghost_free P ->
  pskl_ghost_free (open_pskl_wrt_pskl_rec k (pskl_var_f α') P).
Proof.
  induction P; intros α' k Hg; simpl in *; intuition.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma pskl_ghost_free_open : forall P α',
  pskl_ghost_free P ->
  pskl_ghost_free (open_pskl_wrt_pskl P (pskl_var_f α')).
Proof. intros P α' Hg; apply pskl_ghost_free_open_rec; exact Hg. Qed.

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

(** …and the same INVERSE for a substitution: replacing a free variable
    cannot delete a ghost either.  ⭐ This is what carries the ForallR-PRIORITY
    GUARD ([forall_r_off]) through the collection's structural lemmas, whose
    ∀-rows substitute into the counterpart. *)
Lemma pskl_ghost_free_subst_inv : forall P P' β,
  pskl_ghost_free (subst_pskl_in_pskl P' β P) -> pskl_ghost_free P.
Proof.
  induction P; intros P' β Hg; simpl in *; auto.
  - destruct Hg as [Hg1 Hg2]; split; eauto.
  - eauto.
Qed.

(** The two structural transports of the ForallR-PRIORITY GUARD.  A [∀]
    counterpart stays a [∀] under both, and the GHOSTY half of the guard is
    reflected by the two [_inv] lemmas above — so the guard is stable in the
    direction the rules need it. *)
(** ⚠️ A VARIABLE substitute, not an arbitrary one: substituting a GHOST-FREE
    [∀] for the counterpart's own head variable would turn the guard FALSE
    ([P' = γ] satisfies it vacuously, [P'[∀_.1/γ]] does not).  Every
    collection rule that moves the counterpart moves it by a RENAMING, so
    this is the form the tree needs. *)
Lemma forall_r_off_subst_var : forall m P' γ β,
  forall_r_off m P' -> forall_r_off m (subst_pskl_in_pskl (pskl_var_f γ) β P').
Proof.
  intros m P' γ β H B Heq Hm.
  destruct P' as [ | | γ0 | | P0 | | ]; simpl in Heq;
    try discriminate Heq;
    [ destruct (γ0 == β); discriminate Heq | ].
  injection Heq as Heq0; subst B.
  intro Hgf. apply (H P0 eq_refl Hm). simpl in Hgf |- *.
  eapply pskl_ghost_free_subst_inv; exact Hgf.
Qed.

Lemma forall_r_off_open_var : forall m P' β,
  forall_r_off m P' -> forall_r_off m (open_pskl_wrt_pskl P' (pskl_var_f β)).
Proof.
  intros m P' β H B Heq Hm.
  destruct P' as [ | n | | | P0 | | ]; unfold open_pskl_wrt_pskl in Heq;
    simpl in Heq; try discriminate Heq.
  - destruct (lt_eq_lt_dec n 0) as [[? | ?] | ?]; simpl in Heq;
      discriminate Heq.
  - injection Heq as Heq0; subst B.
    intro Hgf. apply (H P0 eq_refl Hm). simpl in Hgf |- *.
    eapply pskl_ghost_free_open_rec_inv; exact Hgf.
Qed.

(** * Mode/type compatibility.

    ⚙ LIFTED here 2026-08-09: it was proved identically in
    [algo/typing/prop_soundness_typing.v] and [decl/prop_syntax_directed.v],
    which do not see each other.  [mod_comp_ty] is declared in
    [frost/def_shapes.v], so its properties belong in this file. *)
Lemma mod_comp_ty_tc_inv : forall B, mod_comp_ty B mode_tc -> is_ityp B.
Proof. intros B H. inversion H; subst; assumption. Qed.

(* ===================================================================== *)
(*  HOLE-FREENESS is stable under the operations the rules perform         *)
(*                                                                        *)
(*  ⚙ The [_open] pair MOVED here 2026-08-16 from                          *)
(*  algo/sub/look/prop_flex_apart.v, following the predicate itself        *)
(*  (frost/def_shapes.v): a consumer that needs hole-freeness cannot be    *)
(*  asked to import the subtyping-completeness chain.  [_subst] is new —   *)
(*  ext_algo §8c.10 needs it for [Assign-Assign] / [Flex-Flex-Assign],     *)
(*  whose recursion substitutes a definition PAYLOAD into the skeletons.   *)
(* ===================================================================== *)

Lemma pskl_no_hole_open_rec : forall P P' k,
  pskl_no_hole P -> pskl_no_hole P' ->
  pskl_no_hole (open_pskl_wrt_pskl_rec k P' P).
Proof.
  induction P; intros P' k HP HV; simpl in *; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
  - destruct HP; split; auto.
Qed.

Lemma pskl_no_hole_open : forall P α,
  pskl_no_hole P ->
  pskl_no_hole (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof.
  intros P α HP. apply pskl_no_hole_open_rec; simpl; auto.
Qed.

