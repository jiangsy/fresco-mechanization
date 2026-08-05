(** ⭕ TASK A OF docs/HANDOFF-close-subtyping-completeness.md — REACHABILITY OF
    THE REFUTING PAYLOAD, the positive half, machine-checked (2026-08-04).

    THE QUESTION.  [cex/probe_double_occ_run.v] refutes the completeness
    assembly's one hypothesis at the payload

        P0 = (∀γ.γ→γ) → f̂        (f̂ a RAW Θ0-flexible)   NM = TY, M = FN(TC)
        subject ⌈∀a.a→a⌉         (the marker occurs TWICE)

    — no [a_sub] run exists there while the declarative join is Qed-inhabited.
    The theorem is therefore false AS STATED and the repair depends on whether
    the typing can BUILD that payload.  The configuration needs BOTH

      (1) a raw Θ0-flexible at the payload's CODOMAIN — no inherited
          information — and
      (2) a BARE ∀ at the payload's DOMAIN, which is the position that feeds
          CONSISTENCY and hence the only place a guess's tag can be paid
          (only [d_consis__forall_inh_tagged] puts a tag into Ψ, and its
          counterpart must be a [bskl_all_inh], i.e. a ∀ of [inh{κP0}]).

    This file settles (2) at the RULE level, in the direction the hand-off
    said to look: a payload's arrow-LEFT is the ARGUMENT'S COLLECTION, an
    [a_pat] output at [(TC, ◇)], and

      ⭐ THE COLLECTION IS A BARE ∀ ONLY IF THE ARGUMENT CONTAINS A FREEZE
        ([a_pat_spine_all_out_freeze] / [app_payload_domain_all_needs_freeze]).

    Every other route ghosts the head: a ∀-headed subject at TC is
    ForallL-instantiated away, a guarded one is wrapped by UnivGhostR (⫯),
    and only [a_pat__freeze] reaches mode TI, where [a_sub__infer] returns the
    subject VERBATIM.  §1's theorem is the general form — at the SK sort, with
    a mode-compatible payload, an [a_sub] output's MODE-SPINE never ends in a
    bare ∀ — so no amount of Arrow/ForallL/UnivGhostL/FlexMono nesting can
    manufacture one.  ⭐ Hence the reachability search is pinned: a refuting
    SOURCE program must freeze a polymorphic argument.

    §2 records the other half of the hand-off's tension, also at the rule
    level: a monotype guess exists only for a ∀-FREE skeleton
    ([a_guess_mono_all_free]).  So [a_assign__solve_m] — the only rule that
    SOLVES a flexible against an inherited skeleton — can never absorb a ∀,
    which is both the mechanism of the cex's collapse and the reason a frozen
    polymorphic argument cannot simply be checked against a raw flexible.

    ⭕ WHAT REMAINS OPEN (the residual of TASK A, stated sharply).  Condition
    (1) — a raw flexible at the CODOMAIN — is produced only where the
    algorithm has no inherited information at that position, and the ambient
    payload of an application is the OUTER function's domain, i.e. the output
    of a consistency guided by the collection of THAT SAME application.  The
    collection is computed by the same [a_sub] run, at the same subject and
    the same payload domain, differing only in the SORT (SK guesses ghosts,
    TY guesses flexibles) — so when the marker's domain position carries the
    ∀ that (2) demands, the marker's instantiation is that ∀ and the run's
    CODOMAIN output is a ⫯-wrapped skeleton rather than a plain ◇.  That
    co-determination is what makes (1) and (2) pull in opposite directions.
    Closing it needs one further fact about the EXTRACT — that its output is
    ghost-ish only when the look collected nothing at the marker — which is
    P6-level machinery and is NOT proved here.  DESIGN §14.10. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

Scheme a_sub_reach_ind := Induction for a_sub Sort Prop
  with a_sub_flex_reach_ind := Induction for a_sub_flex Sort Prop.
Combined Scheme a_sub_reach_mutind
  from a_sub_reach_ind, a_sub_flex_reach_ind.

(* ===================================================================== *)
(*  §1  AT THE SK SORT A BARE ∀ NEVER LEAVES THE MODE-SPINE               *)
(* ===================================================================== *)

(** The output's mode-spine ends in a BARE ∀ — i.e. after peeling one arrow
    per [FN] the result is [pskl_all_syn _].  This is exactly the shape the
    refuting payload needs at an arrow-LEFT of the next application up. *)
Inductive spine_all_out : mode -> pskl -> Prop :=
| sao_tc : forall Q0, spine_all_out mode_tc (pskl_all_syn Q0)
| sao_fn : forall M Q1 Q2,
    spine_all_out M Q2 -> spine_all_out (mode_fn M) (pskl_arrow Q1 Q2).

(** A mode-compatible payload never has that shape: [skmod[SK]]'s spine ends
    in ◇.  This is what kills [a_sub__ghost], whose output IS the payload. *)
Lemma a_sk_mode_compat_not_spine_all : forall M P,
  a_sk_mode_compat M P -> ~ spine_all_out M P.
Proof.
  intros M P H; induction H; intros Hc; inversion Hc; subst; auto.
Qed.

(** [skmod[SK]] survives the monotype substitution Flex-Assign performs on
    the payload — it constrains only the arrow SPINE. *)
Lemma a_sk_mode_compat_subst : forall M P0 Q β,
  a_sk_mode_compat M P0 ->
  a_sk_mode_compat M (subst_pskl_in_pskl Q β P0).
Proof.
  intros M P0 Q β H; induction H; cbn.
  - apply a_sk_mode_compat__ti.
  - apply a_sk_mode_compat__tc.
  - apply a_sk_mode_compat__fn; assumption.
Qed.

Ltac reach_ih :=
  match goal with H : _ |- _ =>
    eapply H; [ reflexivity | eassumption | eassumption ] end.

(** ⭐ THE STRUCTURAL FACT.  Read the rows: [__infer] is the ONLY one that
    returns the subject verbatim, and it runs at mode TI, which
    [spine_all_out] has no row for; [__check] / [__forall_r] are TY-only;
    [__univ_ghost_r] wraps in ⫯; [__arrow] hands the spine to its codomain
    premise; [__ghost] returns the PAYLOAD, which [skmod[SK]] forbids; and
    [__flex_mono] / [__forall_l] / [__univ_ghost_l] plus the whole flexible
    walk merely relay.  So a bare ∀ can only be produced at TI. *)
Lemma a_sub_sk_no_spine_all_mut :
  (forall NM M P0 Θ0 P Q Θ1, a_sub NM M P0 Θ0 P Q Θ1 ->
     NM = a_sub_mode_sk -> a_sk_mode_compat M P0 -> ~ spine_all_out M Q)
  /\
  (forall NM M P0 Θ0 Ξ α Q Θ1, a_sub_flex NM M P0 Θ0 Ξ α Q Θ1 ->
     NM = a_sub_mode_sk -> a_sk_mode_compat (mode_fn M) P0 ->
     ~ spine_all_out (mode_fn M) Q).
Proof.
  apply a_sub_reach_mutind; intros; subst; try discriminate; intros Hc;
    try (inversion Hc; fail).
  - (* flex_mono *) reach_ih.
  - (* arrow : the spine is the codomain premise's *)
    inversion Hc; subst.
    match goal with Hmc : a_sk_mode_compat (mode_fn _) _ |- _ =>
      inversion Hmc; subst end.
    reach_ih.
  - (* forall_l *) reach_ih.
  - (* ghost : the output IS the payload *)
    eapply a_sk_mode_compat_not_spine_all; eassumption.
  - (* univ_ghost_l *) reach_ih.
  - (* flex solve *) reach_ih.
  - (* flex assign : the payload is substituted, the spine is not *)
    match goal with H : _ |- _ =>
      eapply H; [ reflexivity | apply a_sk_mode_compat_subst; eassumption
                | eassumption ] end.
  - (* flex depend *) reach_ih.
  - (* flex skip *) reach_ih.
  - (* flex skip_rigid *) reach_ih.
  - (* flex skip_tm_var *) reach_ih.
  - (* flex skip_tm_skl *) reach_ih.
Qed.

Lemma a_sub_sk_no_spine_all : forall M P0 Θ0 P Q Θ1,
  a_sub a_sub_mode_sk M P0 Θ0 P Q Θ1 ->
  a_sk_mode_compat M P0 -> ~ spine_all_out M Q.
Proof. intros; eapply (proj1 a_sub_sk_no_spine_all_mut); eauto. Qed.

(* ===================================================================== *)
(*  §1b  …SO A BARE ∀ IN A COLLECTION COMES FROM A FREEZE                 *)
(* ===================================================================== *)

(** The spine of head positions a freeze can sit at: an application's
    function, a lambda's body, or the expression itself. *)
Fixpoint exp_freeze_inside (e : exp) : Prop :=
  match e with
  | exp_freeze _ => True
  | exp_app e1 _ => exp_freeze_inside e1
  | exp_abs e0 => exp_freeze_inside e0
  | exp_abs_anno _ e0 => exp_freeze_inside e0
  | _ => False
  end.

(** The property is about CONSTRUCTORS, so opening cannot create it (a
    variable carries none). *)
Lemma exp_freeze_inside_open_rec : forall e y k,
  exp_freeze_inside (open_exp_wrt_exp_rec k (exp_var_f y) e) ->
  exp_freeze_inside e.
Proof.
  intros e; induction e; intros y k H; cbn in H |- *; try exact H;
    try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; cbn in H; contradiction).
  - eapply IHe; exact H.
  - eapply IHe; exact H.
  - eapply IHe1; exact H.
Qed.

Lemma exp_freeze_inside_open : forall e y,
  exp_freeze_inside (open_exp_wrt_exp e (exp_var_f y)) -> exp_freeze_inside e.
Proof. intros e y H; eapply exp_freeze_inside_open_rec; exact H. Qed.

(** [skmod[SK]] passes to the body's payload: the split of a ◇ is ◇ and the
    split of an arrow is its components; the FLEX split cannot fire, since a
    mode-compatible payload is never a variable. *)
Lemma a_split_mode_compat : forall m Θ0 P0 P Q Θ1,
  a_split Θ0 P0 P Q Θ1 -> a_sk_mode_compat m P0 ->
  a_sk_mode_compat (decr_mode m) Q.
Proof.
  intros m Θ0 P0 P Q Θ1 Hs Hm; destruct Hs.
  - inversion Hm; subst; cbn; assumption.
  - inversion Hm; subst; cbn; constructor.
  - inversion Hm.
Qed.

(** ⭐⭐ FREEZE IS THE ONLY PRODUCER.  [AP-Unit] / [AP-Var] / [AP-VarSkl] /
    [AP-Anno] are killed by §1; the two Check rows emit a ⫯; [AP-Abs] /
    [AP-AbsAnno] and [AP-App] relay to the body / the function. *)
Theorem a_pat_spine_all_out_freeze : forall m Θ0 P0 e Q Θ1,
  a_pat m Θ0 P0 e Q Θ1 -> a_sk_mode_compat m P0 ->
  spine_all_out m Q -> exp_freeze_inside e.
Proof.
  intros m Θ0 P0 e Q Θ1 H; induction H; intros Hmc Hc.
  - (* AP-Unit *) exfalso; eapply a_sub_sk_no_spine_all; eassumption.
  - (* AP-Var *) exfalso; eapply a_sub_sk_no_spine_all; eassumption.
  - (* AP-VarSkl *) exfalso; eapply a_sub_sk_no_spine_all; eassumption.
  - (* AP-Anno *) exfalso; eapply a_sub_sk_no_spine_all; eassumption.
  - (* AP-Freeze *) exact I.
  - (* AP-Abs *)
    inversion Hc; subst; cbn.
    destruct (atom_fresh L) as [y Hy].
    eapply (exp_freeze_inside_open e y).
    match goal with IH : forall _ : atom, _ |- _ =>
      apply (IH y Hy); [ eapply a_split_mode_compat; eassumption | eassumption ]
    end.
  - (* AP-AbsAnno *)
    inversion Hc; subst; cbn.
    destruct (atom_fresh L) as [y Hy].
    eapply (exp_freeze_inside_open e y).
    match goal with IH : forall _ : atom, _ |- _ =>
      apply (IH y Hy); [ eapply a_split_mode_compat; eassumption | eassumption ]
    end.
  - (* AP-AbsCheck *) inversion Hc.
  - (* AP-AbsAnnoCheck *) inversion Hc.
  - (* AP-App *)
    cbn. eapply IHa_pat2; [ | apply sao_fn; exact Hc ].
    apply a_sk_mode_compat__fn; exact Hmc.
Qed.

(** The form the reachability question uses: [a_typing__app] / [a_pat__app]
    build the FN payload [arrow(P, Q)] with [P] the argument's collection at
    [(TC, ◇)], so the cex's bare-∀ DOMAIN demands a frozen argument. *)
Corollary app_payload_domain_all_needs_freeze : forall Θ0 e2 Q0 Θ1,
  Θ0 ⊢ₐ[ mode_tc ; pskl_hole ] e2 ⇨ (pskl_all_syn Q0) ⊣ Θ1 ->
  exp_freeze_inside e2.
Proof.
  intros Θ0 e2 Q0 Θ1 H.
  eapply a_pat_spine_all_out_freeze;
    [ exact H | apply a_sk_mode_compat__tc | apply sao_tc ].
Qed.

(* ===================================================================== *)
(*  §2  A MONOTYPE GUESS EXISTS ONLY FOR A ∀-FREE SKELETON                *)
(* ===================================================================== *)

(** ∀-freeness of a skeleton.  Inlined here (2026-08-06) — it used to come
    from [prop_sub_shield_supply.v], which the shield-layer deprecation
    deleted (`2a1c380`), leaving this probe's [Require] dangling.  This file
    is its only remaining consumer, and the notion is one line. *)
Fixpoint pskl_all_free (P : pskl) : Prop :=
  match P with
  | pskl_unit => True
  | pskl_var_b _ => True
  | pskl_var_f _ => True
  | pskl_arrow P1 P2 => pskl_all_free P1 /\ pskl_all_free P2
  | pskl_all_syn _ => False
  | pskl_hole => True
  | pskl_tophole P0 => pskl_all_free P0
  end.

(** [a_assign__solve_m] is the only rule that SOLVES a flexible against an
    inherited skeleton, and it demands [mono_ptyp τ] of [guess^TY]'s result.
    [a_guess_mono]'s ∀ row returns a [ptyp_all], which is not a monotype — so
    a flexible can never absorb a ∀.  That is the mechanism behind the cex's
    collapse (the eq-constraint's polytype yield is overwritten by SolE-FlexR
    and then cannot be recovered) and, in the other direction, the reason a
    frozen polymorphic argument cannot be checked against a raw flexible. *)
Lemma a_guess_mono_all_free : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> mono_ptyp A -> pskl_all_free P.
Proof.
  intros Θ P Ξ A H; induction H; intros Hm; cbn; try exact I.
  - (* tophole *) apply IHa_guess_mono; exact Hm.
  - (* arrow *)
    inversion Hm; subst; split;
      [ apply IHa_guess_mono1 | apply IHa_guess_mono2 ]; assumption.
  - (* ∀ : the guess is a [ptyp_all], never a monotype *) inversion Hm.
Qed.

Print Assumptions a_sub_sk_no_spine_all.
Print Assumptions a_pat_spine_all_out_freeze.
Print Assumptions a_guess_mono_all_free.
