(** MODE COMPATIBILITY — the whole theory of [skmod{SK}] / [skmod{TY}], at
    both sorts, in one place.

    Two relations at two sorts, and every consumer asks the same questions of
    each:

      INVERSION   what compatibility forces at a HOLE and at an ARROW, and what
                  [mod_comp_sk] / [mod_comp_ty] give back at TI / TC / FN
      STABILITY   compatibility survives substituting a MONOTYPE
      BRIDGES     [a_sk_mode_compat] implies [mod_comp_sk] at the inherited
                  painting; and at TC, [a_ty_mode_compat] and ghost-freeness of
                  the skeleton are the SAME condition (both directions)

    ⚙ WHY ONE FILE.  These fourteen were spread over five: the SK inversions in
    [pat/prop_soundness_pat.v], the TY ones in [typing/prop_soundness_typing.v],
    the substitution halves in [sub/prop_completeness_sub_gen.v] and
    [sub/prop_soundness_subtag.v], and the [mod_comp_sk] bridge in
    [deco_algo/prop_soundness_sub.v] — so half the answers came with a soundness
    or completeness theorem attached, and the TY question was answered in a
    different file from its SK twin.

    ⚙ WHAT IS DELIBERATELY NOT HERE.  [a_sk_mode_compat] / [a_ty_mode_compat] are
    ALGORITHMIC ([algo/def_rules.v]), but [mod_comp_sk] / [mod_comp_ty] are
    cross-system ([fresco/def_shapes.v]) — so their TC inversion
    [mod_comp_ty_tc_inv] stays in [fresco/prop_basic.v], where the declarative
    layer can still reach it.  [mod_comp_sk_subst_mono] /
    [mod_comp_ty_subst_mono] stay with the [is_*_subst_mono] shape lemmas they
    are built from ([algo/prop_pat_sub.v], [algo/prop_suffix_erase.v]); pulling
    them down would drag that whole cluster along. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.

(* ⚠️ The two source files these lemmas came from both had it on, so their
   arguments were implicit at every call site. *)
Set Implicit Arguments.

(* ===================================================================== *)
(*  The SKELETON sort                                                     *)
(* ===================================================================== *)

Lemma a_sk_mode_compat_arrow_inv : forall m P Q,
  a_sk_mode_compat m (pskl_arrow P Q) ->
  exists m', m = mode_fn m' /\ a_sk_mode_compat m' Q.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma a_sk_mode_compat_hole_inv : forall m,
  a_sk_mode_compat m pskl_hole -> m = mode_ti \/ m = mode_tc.
Proof. intros * H; inversion H; auto. Qed.

Lemma mod_comp_sk_ti_inv : forall Q, mod_comp_sk Q mode_ti -> is_sskl Q.
Proof. intros Q H; inversion H; subst; assumption. Qed.

Lemma mod_comp_sk_tc_inv : forall Q, mod_comp_sk Q mode_tc -> is_sskl Q.
Proof. intros Q H; inversion H; subst; assumption. Qed.

Lemma mod_comp_sk_fn_inv : forall Q1 Q2 m,
  mod_comp_sk (bskl_arrow Q1 Q2) (mode_fn m) -> mod_comp_sk Q2 m.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma a_sk_mode_compat_subst_mono : forall M P τ β,
  a_sk_mode_compat M P -> mono_ptyp τ ->
  a_sk_mode_compat M (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros M P τ β H Hm; induction H; simpl;
    [ apply a_sk_mode_compat__ti | apply a_sk_mode_compat__tc
    | apply a_sk_mode_compat__fn; assumption ].
Qed.

(** The paper-shaped corollary. *)
(** The paper's [P0 :sk M] ([a_sk_mode_compat]) implies the internal
    [mod_comp_sk] on the inhabited [bskl] — so the user-facing statements use the
    direct [pskl] relation and the [bskl] detour stays hidden in the bundle. *)
Lemma a_sk_mode_compat_mod_comp_sk : forall M P0,
  a_sk_mode_compat M P0 -> mod_comp_sk (pskl_to_bskl_inh P0) M.
Proof.
  intros M P0 H; induction H; simpl.
  - apply mod_comp_sk__ti; apply is_sskl__hole.
  - apply mod_comp_sk__tc; apply is_sskl__hole.
  - apply mod_comp_sk__fn; assumption.
Qed.

(* ===================================================================== *)
(*  The TYPE sort                                                         *)
(* ===================================================================== *)

(** The TY-sorted twins of the three above.  ⚙ They live beside them (and
    not with type-inference soundness) because each pair is ONE fact at two
    sorts; [algo/typing/prop_scope.v] needs the TY ones without needing the
    theorem they used to travel with. *)
Lemma a_ty_mode_compat_hole_inv : forall m,
  a_ty_mode_compat m pskl_hole -> m = mode_ti.
Proof.
  intros m H. remember pskl_hole as Ps eqn:HPs.
  destruct H.
  - reflexivity.
  - destruct A; simpl in HPs; discriminate.
  - discriminate.
Qed.

Lemma a_ty_mode_compat_arrow_inv : forall m P Q,
  a_ty_mode_compat m (pskl_arrow P Q) ->
  m <> mode_tc ->
  exists m', m = mode_fn m' /\ a_ty_mode_compat m' Q.
Proof.
  intros m P Q H Hne. remember (pskl_arrow P Q) as Ps eqn:HPs.
  destruct H.
  - discriminate.
  - exfalso; apply Hne; reflexivity.
  - inversion HPs; subst. exists M; split; [ reflexivity | assumption ].
Qed.

Lemma mod_comp_ty_fn_inv : forall B1 B2 m,
  mod_comp_ty (btyp_arrow B1 B2) (mode_fn m) -> mod_comp_ty B2 m.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma mod_comp_ty_ti_inv : forall B, mod_comp_ty B mode_ti -> is_styp B.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma a_ty_mode_compat_subst_mono : forall M P τ β,
  a_ty_mode_compat M P -> mono_ptyp τ ->
  a_ty_mode_compat M (subst_pskl_in_pskl (ptyp_to_pskl τ) β P).
Proof.
  intros M P τ β H Hm; induction H; simpl.
  - apply a_ty_mode_compat__ti.
  - rewrite subst_ptyp_to_pskl_comm; apply a_ty_mode_compat__tc.
  - apply a_ty_mode_compat__fn; assumption.
Qed.

(** L-B threads the paper's [a_ty_mode_compat M P0] (:ty) instead of
    [ghost_free P0]: a TC input IS a type (⟹ ghost_free where the refinement
    needs it), an FN input is an arrow whose codomain recurses (the domain
    goes to consistency via WF, not ghost-freeness), a TI input is ◇. *)
Lemma a_ty_mode_compat_tc_ghost_free : forall P,
  a_ty_mode_compat mode_tc P -> pskl_ghost_free P.
Proof. intros P H; inversion H; subst; apply ptyp_to_pskl_ghost_free. Qed.

Lemma pskl_ghost_free_ty_mode_compat_tc : forall P,
  pskl_ghost_free P -> a_ty_mode_compat mode_tc P.
Proof.
  intros P H; destruct (pskl_ghost_free_to_ptyp _ H) as [A ->]; apply a_ty_mode_compat__tc.
Qed.
