(** P7c — THE DISPATCHER for subtyping completeness
    ([thm:complete-subtyping], algorithmic.tex:1446).

    P7b's seven row lemmas and P7a's five walk rows are all [Qed] in
    prop_sub_complete_thm.v; what is missing is the bundle that ASSEMBLES
    them.  This file is that assembly.

    ⭐ THE DISPATCH IS ON THE JOIN, and it determines the subject.  Each row
    lemma reads its premises off one [ad_pat_sub_gv] constructor; the
    dispatcher inverts the join and delegates.  What the join does NOT fix is
    the UNRESOLVED subject [R] — the motive relates it only by the ≡ᵘ slack
    [Θ ⊢ R' ≡ᵘ κR] — so every shape-fixing row owes a transfer from [R'] to
    [R].  §1 below is that kit.  The transfer is total except at an ARROW,
    where [R] may instead be a bare flexible whose IMAGE is the arrow: that,
    and only that, is where P7a is entered.

    ⚠️ THE TERMINATION IS NOT lex(fuel, |Θ0|).  The two halves call each other
    at the SAME fuel — [a_sub__flex_mono] enters P7a at the same context, and
    P7a's [Flex-Solve] re-enters P7b at the same fuel with a context TWO
    ENTRIES LARGER (it deposits [α̂0 ≔ α̂→β̂] plus the two fresh flexibles).  So
    neither the fuel nor the context decreases on that cycle.  What breaks it
    is the SUBJECT: Flex-Solve re-enters at the subject [α̂ → β̂], an ARROW, and
    a main call at an arrow subject can never come back — the R-variable
    escape into P7a needs a VARIABLE subject, and no join row shrinks an arrow
    to a variable.  So the layering is

      §3  [main_arrow_subject]  — the main half at an ARROW subject, from the
          fuel IH ALONE (no P7a, no context induction);
      §4  the flex half, by induction on |Θ0| inside an induction on the FULL
          context, using §3 for Flex-Solve and the main half at a SMALLER
          context for Flex-Assign;
      §5  the main half at the same context, using §4 for the R-variable
          escape and the fuel IH for the shrinking rows.

    ⚠️ P7a's walk owes ONE obligation no row carries, because no RULE has it as
    a premise: the STUCK-CHECK.  A RIGID head [β] with [β ∈ ftv P0] matches no
    [a_sub_flex] rule (it cannot enter Ξ — Ξ is [a_decls] — and it cannot be
    dropped, P0 depends on it), so the dispatcher must REFUTE that
    configuration from the solution.  §4.1 is that refutation; it is the twin
    of consistency's ([assign_complete_step]'s rigid-head case,
    prop_consis_complete.v:5000-5090). *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.prop_basic.

Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_normal.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_consis_sound.
Require Import src.frost.algo.prop_sub_msubst_equiv.
Require Import src.frost.algo.prop_sub_complete_thm.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  THE SHAPE TRANSFER — from the JOIN's subject to the MOTIVE's       *)
(*                                                                        *)
(*  [msubst_uskl_syn] is structural except at a free variable, where it    *)
(*  installs a MONOTYPE PAINTING.  A painting is [unit] / a variable / an   *)
(*  arrow — never a ∀, never a ghost — so a κ-image of any OTHER shape     *)
(*  pins the pre-image's shape exactly, and only the arrow (and unit, and  *)
(*  variable) case admits the variable escape.                            *)
(* ===================================================================== *)

Lemma ptyp_to_uskl_syn_shape : forall τ,
  (exists n, ptyp_to_uskl_syn τ = uskl_var_b n)
  \/ ptyp_to_uskl_syn τ = uskl_unit
  \/ (exists α, ptyp_to_uskl_syn τ = uskl_var_f α)
  \/ (exists A B, ptyp_to_uskl_syn τ = uskl_arrow A B)
  \/ (exists A, ptyp_to_uskl_syn τ = uskl_all_syn A).
Proof.
  intros τ; destruct τ; unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn; cbn.
  - right; left; reflexivity.
  - left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; right; left; do 2 eexists; reflexivity.
  - right; right; right; right; eexists; reflexivity.
Qed.

(** A painting is never an ε-tagged ∀, never a ghost. *)
Lemma ptyp_to_uskl_syn_not_etag : forall τ ε R,
  ptyp_to_uskl_syn τ <> uskl_all_etag ε R.
Proof.
  intros τ ε R.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_hole : forall τ, ptyp_to_uskl_syn τ <> uskl_hole.
Proof.
  intros τ.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_holeg : forall τ, ptyp_to_uskl_syn τ <> uskl_holeg.
Proof.
  intros τ.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_tophole : forall τ R,
  ptyp_to_uskl_syn τ <> uskl_tophole R.
Proof.
  intros τ R.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

Lemma ptyp_to_uskl_syn_not_topholeg : forall τ R,
  ptyp_to_uskl_syn τ <> uskl_topholeg R.
Proof.
  intros τ R.
  destruct (ptyp_to_uskl_syn_shape τ)
    as [[? He] | [He | [[? He] | [[? [? He]] | [? He]]]]];
    rewrite He; discriminate.
Qed.

(** …hence the κ-image pins the pre-image at every shape the paintings miss. *)

Lemma msubst_uskl_syn_all_etag_inv : forall κ R ε X,
  msubst_uskl_syn κ R = uskl_all_etag ε X ->
  exists R0, R = uskl_all_etag ε R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros κ R ε X He; destruct R; cbn in He; try discriminate He.
  - exfalso; eapply ptyp_to_uskl_syn_not_etag; exact He.
  - injection He as <- <-. eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_all_syn_inv : forall κ R X,
  msubst_uskl_syn κ R = uskl_all_syn X ->
  (exists R0, R = uskl_all_syn R0 /\ msubst_uskl_syn κ R0 = X)
  \/ (exists α, R = uskl_var_f α).
Proof.
  intros κ R X He; destruct R; cbn in He; try discriminate He.
  - right; eexists; reflexivity.
  - left; injection He as <-; eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_tophole_inv : forall κ R X,
  msubst_uskl_syn κ R = uskl_tophole X ->
  exists R0, R = uskl_tophole R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros κ R X He; destruct R; cbn in He; try discriminate He.
  - exfalso; eapply ptyp_to_uskl_syn_not_tophole; exact He.
  - injection He as <-. eexists; split; reflexivity.
Qed.

Lemma msubst_uskl_syn_topholeg_inv : forall κ R X,
  msubst_uskl_syn κ R = uskl_topholeg X ->
  exists R0, R = uskl_topholeg R0 /\ msubst_uskl_syn κ R0 = X.
Proof.
  intros κ R X He; destruct R; cbn in He; try discriminate He.
  - exfalso; eapply ptyp_to_uskl_syn_not_topholeg; exact He.
  - injection He as <-. eexists; split; reflexivity.
Qed.

(** The ARROW is the one shape a painting CAN have, so here — and only here —
    the pre-image may be a bare variable.  That is exactly the [a_sub__flex_mono]
    entry into P7a. *)
Lemma msubst_uskl_syn_arrow_inv : forall κ R X Y,
  msubst_uskl_syn κ R = uskl_arrow X Y ->
  (exists Ra Rb, R = uskl_arrow Ra Rb /\
     msubst_uskl_syn κ Ra = X /\ msubst_uskl_syn κ Rb = Y)
  \/ (exists α, R = uskl_var_f α).
Proof.
  intros κ R X Y He; destruct R; cbn in He; try discriminate He.
  - right; eexists; reflexivity.
  - left; injection He as <- <-. do 2 eexists; repeat split.
Qed.

(* --------------------------------------------------------------------- *)
(*  …and the ≡ᵘ layer on top: the join's subject is only EQUIVALENT to the *)
(*  κ-image, and [a_uskl_tyequiv__mono] relates two paintings across a     *)
(*  definition chase.  A painting has none of the four shapes below, so    *)
(*  that row cannot fire and the equivalence is structural.                *)
(* --------------------------------------------------------------------- *)

Lemma a_uskl_tyequiv_all_etag_l_inv : forall Θ ε R X,
  Θ ⊢ (uskl_all_etag ε R) ≡ᵘ X ->
  exists X0, X = uskl_all_etag ε X0.
Proof.
  intros Θ ε R X H; inversion H; subst;
    [ exfalso; eapply ptyp_to_uskl_syn_not_etag; eassumption | eexists; reflexivity ].
Qed.

Lemma a_uskl_tyequiv_all_syn_l_inv : forall Θ R X,
  Θ ⊢ (uskl_all_syn R) ≡ᵘ X ->
  exists X0, X = uskl_all_syn X0.
Proof.
  intros Θ R X H; inversion H; subst.
  - exfalso.
    match goal with
    | Hm : mono_ptyp ?t, He : ptyp_to_uskl_syn ?t = uskl_all_syn _ |- _ =>
        destruct Hm; cbn in He; discriminate He
    end.
  - eexists; reflexivity.
Qed.

Lemma a_uskl_tyequiv_tophole_l_inv : forall Θ R X,
  Θ ⊢ (uskl_tophole R) ≡ᵘ X ->
  exists X0, X = uskl_tophole X0 /\ Θ ⊢ R ≡ᵘ X0.
Proof.
  intros Θ R X H; inversion H; subst;
    [ exfalso; eapply ptyp_to_uskl_syn_not_tophole; eassumption
    | eexists; split; [ reflexivity | assumption ] ].
Qed.

Lemma a_uskl_tyequiv_topholeg_l_inv : forall Θ R X,
  Θ ⊢ (uskl_topholeg R) ≡ᵘ X ->
  exists X0, X = uskl_topholeg X0 /\ Θ ⊢ R ≡ᵘ X0.
Proof.
  intros Θ R X H; inversion H; subst;
    [ exfalso; eapply ptyp_to_uskl_syn_not_topholeg; eassumption
    | eexists; split; [ reflexivity | assumption ] ].
Qed.

(** The ARROW case, where the [__mono] row DOES fire.  Either the image is a
    syntactic arrow, or both sides are monotype PAINTINGS — and a painting is
    [unit] / a variable / an arrow, with [unit] excluded because ⇓ is a
    congruence ([a_tyequiv_downarrow]) and [⇓unit] is not an arrow.  The
    surviving variable is exactly the [__flex_mono] escape into P7a. *)
Lemma a_uskl_tyequiv_arrow_l_inv : forall Θ R1 R2 X,
  a_wf_aenv Θ ->
  Θ ⊢ (uskl_arrow R1 R2) ≡ᵘ X ->
  (exists X1 X2, X = uskl_arrow X1 X2) \/ (exists β, X = uskl_var_f β).
Proof.
  intros Θ R1 R2 X Hwf H; inversion H; subst;
    [ | left; do 2 eexists; reflexivity ].
  (* __mono : τ1 is an arrow (its painting is), so ⇓τ2 is an arrow too *)
  match goal with
  | Hm1 : mono_ptyp ?t1, He1 : ptyp_to_uskl_syn ?t1 = uskl_arrow R1 R2,
    Hm2 : mono_ptyp ?t2, Heq : _ ⊢ ?t1 ≡ᵗ ?t2 |- _ =>
      destruct Hm1; cbn in He1; try discriminate He1;
      pose proof (a_tyequiv_downarrow Hwf Heq) as Hdn;
      destruct Hm2; cbn in Hdn |- *;
        [ (* unit : ⇓ of an arrow is an arrow *) exfalso; discriminate Hdn
        | right; eexists; reflexivity
        | left; do 2 eexists; reflexivity ]
  end.
Qed.

(* ===================================================================== *)
(*  §2  THE DISPATCH, SCOPED — the case map and the TERMINATION            *)
(*                                                                        *)
(*  ⚠️ This section is NOT yet proof; it is the scoping the kit above was   *)
(*  built for, recorded here so the next session starts from it rather     *)
(*  than re-deriving it.  docs/DESIGN-completeness-subtyping.md §12.1      *)
(*  carries the same content in prose.                                     *)
(*                                                                        *)
(*  THE CASE MAP.  Inverting [ad_pat_sub_gv] gives twelve rows.  What the  *)
(*  join does NOT fix is the motive's UNRESOLVED subject [R]; §1 is the    *)
(*  transfer, and it is total except at [__arrow]:                         *)
(*                                                                        *)
(*    __infer / __check / __univ_ghost_r / __forall_r   R arbitrary — the  *)
(*        row lemma takes any [R] and does its own transfer internally.    *)
(*    __ghost / __ghostg                                [R' = ◇ / ◈], and  *)
(*        the row lemma takes [R'] directly.                               *)
(*    __arrow                     [R' = R1'→R2'] ⟹ (§1) [κR] is an arrow   *)
(*        or a VARIABLE.  Arrow ⟹ [a_sub_complete_arrow]; variable ⟹ P7a   *)
(*        ([a_sub__flex_mono]).  ⭐ THIS IS THE ONLY ENTRY INTO P7a.        *)
(*    __forall_l_tagged / _untagged   [R] is the same ∀ (a painting is     *)
(*        never a ∀, so the variable escape cannot fire) ⟹ the two ForallL *)
(*        rows, each of which owes TASK 0's [sub_shield].                  *)
(*    __univ_ghost_l / __univ_ghost_lg   [R] is the same ghost ⟹ NO row    *)
(*        lemma exists; strip [pskl_tophole] with [a_sub__univ_ghost_l]    *)
(*        and recurse.  Both preserve the FUEL, so the fuel IH cannot      *)
(*        serve them — they are the inner induction's real work.           *)
(*    __flex_mono                  a pure PEEL: it chases a Θ-definition on *)
(*        the join's side and leaves [R] alone, so the ≡ᵘ slack is         *)
(*        re-established by [flex_def_paint_tyequiv] + transitivity.       *)
(*                                                                        *)
(*  ⚠️⚠️ THE TERMINATION IS **NOT** lex(fuel, |Θ0|) — §12's first cut is    *)
(*  wrong, and this is the finding that reshapes the assembly.  The two    *)
(*  halves call each other at the SAME fuel: [a_sub__flex_mono] enters P7a *)
(*  at the same context, and P7a's [Flex-Solve] re-enters P7b at the same  *)
(*  fuel with a context TWO ENTRIES LARGER (it deposits [α̂0 ≔ α̂→β̂] plus    *)
(*  the two fresh flexibles — prop_sub_complete_thm.v:4586).  So on that   *)
(*  cycle neither component decreases.  [Flex-Assign] is fine (it consumes *)
(*  the definition, so the context shrinks by one).                        *)
(*                                                                        *)
(*  ⭐ WHAT BREAKS THE CYCLE IS THE SUBJECT.  Flex-Solve re-enters at the   *)
(*  subject [α̂ → β̂] — an ARROW — and a main call at an arrow subject can   *)
(*  NEVER come back into P7a: the escape needs a VARIABLE subject, and no  *)
(*  join row shrinks an arrow to a variable ([__univ_ghost_l] needs a ∀◇    *)
(*  subject, [__flex_mono] leaves [R] alone).  So the layering that works  *)
(*  is                                                                     *)
(*                                                                        *)
(*    (a) [main_arrow_subject] — the main half at an ARROW subject, from   *)
(*        the fuel IH ALONE: no P7a, no context induction.                 *)
(*    (b) the flex half at |Ξ ++ Θ0| = k, by an inner induction on |Θ0|    *)
(*        (Flex-Depend keeps the total and shrinks Θ0), using (a) for      *)
(*        Flex-Solve and the main half at k-1 for Flex-Assign.             *)
(*    (c) the main half at k, using (b) for the R-variable escape and the  *)
(*        fuel IH for the fuel-consuming rows; its inner induction on the  *)
(*        join handles the three fuel-preserving ones.                     *)
(*    (d) strong induction on k, then on the fuel.                         *)
(*                                                                        *)
(*  TWO OBLIGATIONS ARE STILL OPEN, and neither is mechanical:             *)
(*                                                                        *)
(*  ⭕ (1) TASK 0's residual, at the two ForallL rows.  The premise is now  *)
(*     POSITIONALLY indexed and machine-checked SATISFIABLE at the node     *)
(*     that used to refute it ([p7_sub_shield_repaired_holds]), but        *)
(*     prop_sub_shield_supply.v still discharges it only for a flex-free / *)
(*     atomic / mono-counterpart / inh-free-counterpart / ∀-free [P0].     *)
(*     A [P0] carrying a ∀ below its head has no general route, so the     *)
(*     dispatcher must take it as a hypothesis (DESIGN §12 item 3).        *)
(*                                                                        *)
(*  ⭕ (2) P7a's STUCK-CHECK.  A RIGID head [β] with [β ∈ ftv P0] matches   *)
(*     no [a_sub_flex] rule — it cannot enter Ξ ([a_decls] holds only      *)
(*     flexible declarations) and it cannot be dropped ([Flex-SkipRigid]   *)
(*     needs [β ∉ ftv P0]) — so the dispatcher must REFUTE it from the      *)
(*     solution.  Consistency's twin is [assign_complete_step]'s rigid     *)
(*     head case (prop_consis_complete.v:5000-5090): [rigid_survives_      *)
(*     solution] puts β in [ftv (κP)], and [ad_pat_consis_rigid_ftv_rev_   *)
(*     scoped] confines the subject's rigid ftv to [κα̂]'s scope.           *)
(*     ⚠️ THE SUBTYPING CHAIN IS NOT THE SAME.  There the pattern IS the    *)
(*     join's subject; here [P0] sits on the FILL side ([Θ ⊢ᵣ inh{κP0} ⊳    *)
(*     Q]) and the join's subject is [κα̂].  So the chain must run          *)
(*     β ∈ ftv P0 ⟹ β ∈ ftv (κP0) ⟹ β ∈ ftv Q ⟹ β ∈ ftv (κα̂) — and its     *)
(*     last step is the direction "the SUBJECT confines the TARGET", which *)
(*     is FALSE for the join in general ([ad_pat_sub_gv__ghost] gives a ◇   *)
(*     subject an arbitrary target).  It has to be re-derived for the      *)
(*     MONOTYPE subject the walk actually has, where every row carries a   *)
(*     refinement premise off the subject's HOLE-FREE erasure.  That is    *)
(*     the piece to build first.                                          *)
(* ===================================================================== *)
