(** ext_algo — DECISION PROCEDURES for the rule guards the runners test.

    Phase 4 of docs/HANDOFF-extractable-algo-encoding.md §8b: a Bove–Capretta
    runner for a PARTIAL judgement must TEST each rule's side condition before
    building the rule instance, so every guard needs an executable check.
    This file is the complete inventory: one boolean/lookup function per
    guard, each with a SOUNDNESS-ONLY lemma ([… = true -> <the guard>]).

    ⭐ SOUNDNESS-ONLY IS THE DESIGN, not a shortcut taken silently.  The
    runners' result type is [option (sig (spec …))] — [None] means "no rule
    applied", and the standing contract (§8b, phase 4) defers "rejection is
    justified" to a later determinism pass.  A check that answers [false]
    where the guard actually holds makes the runner REJECT, which is sound;
    so no completeness direction is owed here, and none is stated.

    ⭐ THESE FUNCTIONS ARE THE EXTRACTED COUNTERPARTS OF [type.ml]'s OWN
    TESTS: [guarded_shape_ck] ≈ [is_guarded] (type.ml:21), [mono_ck] ≈
    [is_mono] (:29), [ghost_free_ck] ≈ [is_type] (:39), [wf_pskl_ck] ≈
    [is_wf_] (:50), and the context lookups ≈ [is_in_dom_]/[get_var_kind_].

    ⚠️ TWO PLACES WHERE A CHECK NEEDS MORE THAN THE SHAPE:

    - [guarded_pskl]'s arrow row embeds LOCAL CLOSURE ([def_shapes.v:185]),
      which no boolean can test structurally in one pass.  The check tests
      the HEAD SHAPE only, and its soundness lemma takes [lc_pskl P] as a
      hypothesis — the runners carry lc preconditions anyway (the honest
      precondition of every runner since M1.7), so the hypothesis is free
      at every use site.
    - [a_wf_pskl]'s ∀ row is COFINITE, so the checker opens the body at ONE
      name ([supply_fresh] over everything in scope) and soundness
      regenerates the cofinite family by renaming ([a_wf_pskl_rename_bound],
      the same kit [a_wf_pskl_all_inv_at] uses in the other direction).
      ⚙ The checker carries a FUEL argument to be structurally recursive —
      opening a binder is no structural descent.  This does NOT contradict
      the campaign's "no fuel" decision (§5), which is about the RUNNER's
      recursion: here the fuel is called at [size_pskl P] and only bounds a
      static wf CHECK, exactly the depth bound a hand-written checker's
      structural recursion has implicitly; running out of fuel answers
      [false], which is a (sound) rejection, never a wrong answer. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_refine.               (* a_wf_pskl_delta_mono *)
Require Import src.fresco.algo.sub.prop_solve_sub.        (* lc_pskl_*_inv *)
Require Import src.fresco.algo.consis.prop_soundness_consis.
                     (* a_wf_pskl_lc, a_wf_pskl_rename_bound *)
Require Import src.fresco.ext_algo.def_supply.

(* ⚠️ NO [Set Implicit Arguments] — this file's definitions are consumed by
   the [Equations] implementation files, where implicit maximality misfires
   on recursive calls (def_guess_impl.v's header). *)

(* ⚙ [is_empty] belongs beside [mem]/[inter] in fresco/notations.v (its rule:
   no [AtomSetImpl.] qualifier in statements), but an edit there re-checks the
   whole tree; declared here — the only consumer — until a full rebuild is due
   for another reason, at which point it should migrate. *)
Notation is_empty := AtomSetImpl.is_empty.

(* ===================================================================== *)
(*  §1  Atom-set reflection                                               *)
(* ===================================================================== *)

Lemma mem_true_in : forall α S, mem α S = true -> α `in` S.
Proof. intros * H. apply AtomSetFacts.mem_iff. exact H. Qed.

Lemma mem_false_notin : forall α S, mem α S = false -> α `notin` S.
Proof.
  intros * H Hin. apply AtomSetFacts.mem_iff in Hin. congruence.
Qed.

Lemma inter_is_empty_sound : forall S1 S2,
  is_empty (inter S1 S2) = true -> S1 ∩ S2 [=] empty.
Proof.
  intros * H. apply AtomSetFacts.is_empty_iff in H.
  intros a; split; intro Hin;
    [ exfalso; exact (H a Hin)
    | apply AtomSetFacts.empty_iff in Hin; contradiction ].
Qed.

(* ===================================================================== *)
(*  §2  Context lookups                                                   *)
(*                                                                        *)
(*  [binds] is an "appears somewhere" predicate, so the NEGATIVE checks    *)
(*  scan the whole list rather than trusting metalib's [get] (which        *)
(*  returns only the FIRST binding and so refutes nothing behind it).      *)
(* ===================================================================== *)

(** Is [α] bound FLEXIBLY (defined or not) anywhere in [Θ]? *)
Fixpoint flex_bound_ck (Θ : aenv) (α : atom) : bool :=
  match Θ with
  | nil => false
  | (β, abind_flex_mono) :: Θ' =>
      if α == β then true else flex_bound_ck Θ' α
  | (β, abind_flex_mono_def _) :: Θ' =>
      if α == β then true else flex_bound_ck Θ' α
  | _ :: Θ' => flex_bound_ck Θ' α
  end.

Lemma flex_bound_ck_flex_tvar : forall Θ α,
  flex_bound_ck Θ α = true -> a_flex_tvar Θ α.
Proof.
  induction Θ as [ | [β b] Θ' IH ]; simpl; intros α Hck; [ discriminate | ].
  assert (Hw : a_flex_tvar Θ' α -> a_flex_tvar ((β, b) :: Θ') α).
  { intros [Hb | [τ Hb]]; [ left | right; exists τ ];
      unfold binds in *; right; exact Hb. }
  destruct b; try solve [ apply Hw; apply IH; exact Hck ];
    (revert Hck; destruct (α == β) as [-> | Hne]; intro Hck;
     [ | apply Hw; apply IH; exact Hck ]).
  - left; unfold binds; left; reflexivity.
  - right; eexists; unfold binds; left; reflexivity.
Qed.

Lemma flex_bound_ck_not_flex_tvar : forall Θ α,
  flex_bound_ck Θ α = false -> ~ a_flex_tvar Θ α.
Proof.
  induction Θ as [ | [β b] Θ' IH ]; simpl; intros α Hck Hf.
  - destruct Hf as [Hb | [τ Hb]]; inversion Hb.
  - assert (Htail : flex_bound_ck Θ' α = false).
    { destruct b; try exact Hck;
        (revert Hck; destruct (α == β); intro Hck;
         [ discriminate | exact Hck ]). }
    assert (Hhead : α <> β \/
                    (b <> abind_flex_mono /\
                     forall τ, b <> abind_flex_mono_def τ)).
    { destruct b;
        try solve [ right; split; [ congruence | intros ?; congruence ] ];
        (revert Hck; destruct (α == β) as [-> | Hne]; intro Hck;
         [ discriminate | left; exact Hne ]). }
    destruct Hf as [Hb | [τ Hb]]; destruct Hb as [Heq | Hin];
      try solve [ eapply (IH α Htail);
                  solve [ left; exact Hin | right; eexists; exact Hin ] ];
      inversion Heq; subst;
      destruct Hhead as [Hne | [Hb1 Hb2]];
      solve [ exact (Hne eq_refl) | exact (Hb1 eq_refl)
            | exact (Hb2 _ eq_refl) ].
Qed.

(** [a_non_flex Θ P] = locally closed and not a flexible variable. *)
Definition non_flex_ck (Θ : aenv) (P : pskl) : bool :=
  match P with
  | pskl_var_f α => negb (flex_bound_ck Θ α)
  | _ => true
  end.

Lemma non_flex_ck_sound : forall Θ P,
  non_flex_ck Θ P = true -> lc_pskl P -> a_non_flex Θ P.
Proof.
  intros Θ P Hck Hlc; split; [ exact Hlc | ].
  intro Hf; inversion Hf; subst; simpl in Hck;
    apply negb_true_iff in Hck;
    eapply flex_bound_ck_not_flex_tvar; try exact Hck;
    [ left; assumption | right; eexists; eassumption ].
Qed.

(** The variable instance of [a_non_flex], off the negative scan — the
    runners' flex-dispatch tests deliver exactly this hypothesis. *)
Lemma flex_bound_false_non_flex : forall Θ α,
  flex_bound_ck Θ α = false -> a_non_flex Θ (pskl_var_f α).
Proof.
  intros Θ α Hck; split; [ apply lc_pskl_var_f | ].
  intro Hf; inversion Hf; subst;
    eapply flex_bound_ck_not_flex_tvar; try exact Hck;
    [ left | right; eexists ]; eassumption.
Qed.

(** Is [α] bound RIGIDLY anywhere in [Θ]? *)
Fixpoint rigid_bound_ck (Θ : aenv) (α : atom) : bool :=
  match Θ with
  | nil => false
  | (β, abind_tvar) :: Θ' => if α == β then true else rigid_bound_ck Θ' α
  | _ :: Θ' => rigid_bound_ck Θ' α
  end.

Lemma rigid_bound_ck_binds : forall Θ α,
  rigid_bound_ck Θ α = true -> binds α abind_tvar Θ.
Proof.
  induction Θ as [ | [β b] Θ' IH ]; simpl; intros α Hck; [ discriminate | ].
  destruct b; try solve [ right; apply IH; exact Hck ].
  destruct (α == β) as [-> | Hne];
    [ left; reflexivity | right; apply IH; exact Hck ].
Qed.

(** ⚙ The converses of the two positive scans, for the same reason as
    [mono_ck_complete]: a completeness proof reads the runner's test
    against what the derivation found. *)
Lemma rigid_bound_ck_complete : forall Θ α,
  binds α abind_tvar Θ -> rigid_bound_ck Θ α = true.
Proof.
  induction Θ as [ | [β b] Θ' IH ]; intros α Hb; [ inversion Hb | ].
  destruct Hb as [Heq | Hin]; simpl.
  - inversion Heq; subst. destruct (α == α); congruence.
  - destruct b; try (apply IH; exact Hin).
    destruct (α == β); [ reflexivity | apply IH; exact Hin ].
Qed.

Lemma flex_tvar_flex_bound_ck : forall Θ α,
  a_flex_tvar Θ α -> flex_bound_ck Θ α = true.
Proof.
  intros Θ α Hf. destruct (flex_bound_ck Θ α) eqn:E; [ reflexivity | ].
  exfalso. eapply flex_bound_ck_not_flex_tvar; eassumption.
Qed.

(** [a_binds_tvar]: any type-variable-ish binding (rigid or flexible). *)
Definition tvarish_ck (Θ : aenv) (α : atom) : bool :=
  rigid_bound_ck Θ α || flex_bound_ck Θ α.

Lemma tvarish_ck_binds : forall Θ α,
  tvarish_ck Θ α = true -> a_binds_tvar α Θ.
Proof.
  intros Θ α Hck. apply orb_prop in Hck. destruct Hck as [Hr | Hf].
  - left; apply rigid_bound_ck_binds; exact Hr.
  - apply flex_bound_ck_flex_tvar in Hf.
    destruct Hf as [Hb | [τ Hb]]; [ right; left | right; right; exists τ ];
      assumption.
Qed.

(* ===================================================================== *)
(*  §3  Shape checks                                                      *)
(* ===================================================================== *)

(** [guarded_pskl], head shape only — lc comes from the caller. *)
Definition guarded_shape_ck (P : pskl) : bool :=
  match P with
  | pskl_unit | pskl_var_f _ | pskl_arrow _ _ => true
  | _ => false
  end.

Lemma guarded_shape_ck_sound : forall P,
  guarded_shape_ck P = true -> lc_pskl P -> guarded_pskl P.
Proof.
  intros P Hck Hlc; destruct P; simpl in Hck; try discriminate;
    try solve [ constructor ].
  inversion Hlc; subst; constructor; assumption.
Qed.

Fixpoint ghost_free_ck (P : pskl) : bool :=
  match P with
  | pskl_unit => true
  | pskl_var_b _ => true
  | pskl_var_f _ => true
  | pskl_arrow P1 P2 => ghost_free_ck P1 && ghost_free_ck P2
  | pskl_all_syn P0 => ghost_free_ck P0
  | pskl_ghost => false
  | pskl_univ_ghost _ => false
  end.

Lemma ghost_free_ck_sound : forall P,
  ghost_free_ck P = true -> pskl_ghost_free P.
Proof.
  induction P; simpl; intros Hck; try exact I; try discriminate; auto.
  apply andb_prop in Hck; destruct Hck; split; auto.
Qed.

(** The converse direction lives here rather than in prop_dec.v because the
    runner's own dispatch needs it while proving its ForallL / UnivGhostL
    obligations, and prop_dec.v is downstream of def_look_impl.v. *)
Lemma ghost_free_ck_complete : forall P,
  pskl_ghost_free P -> ghost_free_ck P = true.
Proof.
  induction P; simpl; intros Hgf;
    try reflexivity; try contradiction; try solve [ apply IHP; exact Hgf ].
  destruct Hgf as [H1 H2]. apply andb_true_intro; split; auto.
Qed.

(** ⭐ The ForallR-PRIORITY GUARD read straight off the runner's failed
    ghost-freeness test — this is what makes the two guarded rows'
    obligations discharge from the dispatch itself. *)
Lemma forall_r_off_ck : forall m B,
  ghost_free_ck (pskl_all_syn B) = false -> forall_r_off m (pskl_all_syn B).
Proof.
  intros m B Hck. apply forall_r_off_ghosty. intro Hgf.
  rewrite (ghost_free_ck_complete _ Hgf) in Hck. discriminate Hck.
Qed.

Fixpoint mono_ck (A : ptyp) : bool :=
  match A with
  | ptyp_unit => true
  | ptyp_var_b _ => false
  | ptyp_var_f _ => true
  | ptyp_arrow A1 A2 => mono_ck A1 && mono_ck A2
  | ptyp_all _ => false
  end.

Lemma mono_ck_sound : forall A, mono_ck A = true -> mono_ptyp A.
Proof.
  induction A; simpl; intros Hck; try discriminate;
    try solve [ constructor ].
  apply andb_prop in Hck; destruct Hck; constructor; auto.
Qed.

(** ⚙ The converse.  A runner that TESTS [mono_ck] and a derivation that
    CARRIES [mono_ptyp] meet at a completeness proof, which needs the test
    to succeed — the soundness direction alone never does that. *)
Lemma mono_ck_complete : forall A, mono_ptyp A -> mono_ck A = true.
Proof.
  induction 1; simpl; auto. rewrite IHmono_ptyp1, IHmono_ptyp2. reflexivity.
Qed.

Definition nonghost_ck (P : pskl) : bool :=
  match P with
  | pskl_unit | pskl_var_f _ | pskl_arrow _ _ | pskl_all_syn _ => true
  | _ => false
  end.

Lemma nonghost_ck_sound : forall P,
  nonghost_ck P = true -> nonghost_pskl P.
Proof.
  intros P Hck; destruct P; simpl in Hck; try discriminate; constructor.
Qed.

(* ===================================================================== *)
(*  §4  Context-shape checks                                              *)
(* ===================================================================== *)

Fixpoint uniq_ck (Θ : aenv) : bool :=
  match Θ with
  | nil => true
  | (x, _) :: Θ' => negb (mem x (dom Θ')) && uniq_ck Θ'
  end.

Lemma uniq_ck_sound : forall Θ, uniq_ck Θ = true -> uniq Θ.
Proof.
  induction Θ as [ | [x b] Θ' IH ]; simpl; intros Hck; [ constructor | ].
  apply andb_prop in Hck; destruct Hck as [Hm Hu].
  apply negb_true_iff in Hm.
  apply uniq_push; [ apply IH; exact Hu | apply mem_false_notin; exact Hm ].
Qed.

Fixpoint suffix_ck (Ξ : aenv) : bool :=
  match Ξ with
  | nil => true
  | (_, abind_flex_mono) :: Ξ' => suffix_ck Ξ'
  | (_, abind_flex_mono_def _) :: Ξ' => suffix_ck Ξ'
  | _ => false
  end.

Lemma suffix_ck_sound : forall Ξ, suffix_ck Ξ = true -> a_suffix Ξ.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; simpl; intros Hck; [ constructor | ].
  destruct b; try discriminate;
    apply (a_suffix__cons x); auto using a_suffix_binding.
Qed.

Definition ghost_ck (P : pskl) : bool :=
  match P with pskl_ghost => true | _ => false end.

Lemma ghost_ck_sound : forall P, ghost_ck P = true -> P = pskl_ghost.
Proof. intros P Hck; destruct P; simpl in Hck; congruence. Qed.

(** Structural equality — the ForallR runner checks its premise's output
    counterpart against the one the rule fixes. *)
Fixpoint pskl_eqb (P Q : pskl) : bool :=
  match P, Q with
  | pskl_unit, pskl_unit => true
  | pskl_var_b n, pskl_var_b m => Nat.eqb n m
  | pskl_var_f α, pskl_var_f β => if α == β then true else false
  | pskl_arrow P1 P2, pskl_arrow Q1 Q2 => pskl_eqb P1 Q1 && pskl_eqb P2 Q2
  | pskl_all_syn P1, pskl_all_syn Q1 => pskl_eqb P1 Q1
  | pskl_ghost, pskl_ghost => true
  | pskl_univ_ghost P1, pskl_univ_ghost Q1 => pskl_eqb P1 Q1
  | _, _ => false
  end.

Lemma pskl_eqb_sound : forall P Q, pskl_eqb P Q = true -> P = Q.
Proof.
  induction P; destruct Q; simpl; intros Hck; try discriminate;
    try reflexivity.
  - apply Nat.eqb_eq in Hck; subst; reflexivity.
  - destruct (α == α0); [ subst; reflexivity | discriminate ].
  - apply andb_prop in Hck; destruct Hck.
    erewrite IHP1, IHP2 by eassumption; reflexivity.
  - erewrite IHP by eassumption; reflexivity.
  - erewrite IHP by eassumption; reflexivity.
Qed.

(** Opening a ∀-body at an arbitrary locally closed skeleton stays locally
    closed — the graft step of ForallL's recursion (the inline argument of
    prop_termination.v §17, packaged). *)
Lemma lc_pskl_open_graft : forall P A,
  lc_pskl (pskl_all_syn P) -> lc_pskl A ->
  lc_pskl (open_pskl_wrt_pskl P A).
Proof.
  intros P A Hall HA.
  destruct (atom_fresh (ftvar_in_pskl P)) as [x Hx].
  rewrite (subst_pskl_in_pskl_intro x) by assumption.
  apply subst_pskl_in_pskl_lc_pskl; eauto using lc_pskl_all_syn_inv.
Qed.

(** Split a rigid marker off the head of a run's OUTPUT context, with the
    decomposition equation as evidence — what the ∀ rows of the consistency
    runner do where [type.ml] writes [List.tl] (:200).  [sig] erases, so
    this extracts to a plain [aenv option]. *)
Definition split_tvar_head (α : atom) (Θout : aenv)
    : option (sig (fun Θ1 : aenv => Θout = (α ~ abind_tvar) ++ Θ1)).
Proof.
  refine (match Θout with
          | (α', abind_tvar) :: Θ1 =>
              match α == α' with
              | left Heq => Some (exist _ Θ1 _)
              | right _ => None
              end
          | _ => None
          end).
  subst; reflexivity.
Defined.

(** It HITS whenever the head really is that marker.  ⚠️ Stated in the
    ∃-form because the [sig]'s proof component is the decomposition
    equation itself; and in the [Θout = …] form because the ∀ rows meet it
    at [cs_ctx r], which no [rewrite] can reach (the branch's Equations
    obligation reads that very proof). *)
Lemma split_tvar_head_hit : forall α (Θ1 : aenv),
  exists p, split_tvar_head α ((α ~ abind_tvar) ++ Θ1)
            = Some (exist _ Θ1 p).
Proof.
  intros. unfold one, split_tvar_head. cbn [app].
  match goal with
  | |- context [ match ?e with left _ => _ | right _ => _ end ] =>
      destruct e as [ E | Ne ]
  end; [ eexists; reflexivity | congruence ].
Qed.

Lemma split_tvar_head_hit_eq : forall α (Θout Θ1 : aenv),
  Θout = (α ~ abind_tvar) ++ Θ1 ->
  exists p, split_tvar_head α Θout = Some (exist _ Θ1 p).
Proof. intros; subst; apply split_tvar_head_hit. Qed.

(* ===================================================================== *)
(*  §5  The wf checker  (≈ type.ml's [is_wf_], :50)                       *)
(* ===================================================================== *)

(** ONE cofinite instance at a name fresh for everything in scope is enough
    to regenerate the whole family — the introduction twin of
    [a_wf_pskl_all_inv_at] (prop_soundness_consis.v), off the bound-renaming
    kit [a_wf_pskl_rename_bound]: the ∀ binder sits in BOTH the context
    (as a rigid marker) and [Δ], and the renaming moves it in both. *)
Lemma a_wf_pskl_all_intro_at : forall Θ Δ P β,
  β `notin` dom Θ `union` ftvar_in_pskl P `union` Δ ->
  {{ ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ) ⊢ₚₛ
     (open_pskl_wrt_pskl P (pskl_var_f β)) }}a ->
  {{ Θ ⨟ Δ ⊢ₚₛ (pskl_all_syn P) }}a.
Proof.
  intros * Hβ Hone.
  apply a_wf_pskl__all
    with (L := dom Θ `union` ftvar_in_pskl P `union` Δ `union` singleton β).
  intros α Hα.
  assert (Hαo : α `notin` ftvar_in_pskl (open_pskl_wrt_pskl P (pskl_var_f β))).
  { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f β))
      as Hup. simpl in Hup. clear - Hup Hα. fsetdec. }
  pose proof (@a_wf_pskl_rename_bound _ _ _ Hone
                ((α ~ abind_tvar) ++ Θ) β α
                ltac:(intros γ Hγ Hne;
                      apply a_binds_tvar_cons_tvar_inv in Hγ;
                      destruct Hγ as [ -> | Hγ ]; [ congruence | ];
                      apply a_binds_tvar_cons_tvar; right; exact Hγ)
                ltac:(apply a_binds_tvar_cons_tvar; left; reflexivity)
                ltac:(clear; fsetdec)
                Hαo) as Hr.
  rewrite <- (subst_pskl_in_pskl_intro β P (pskl_var_f α)
                ltac:(clear - Hβ; fsetdec)) in Hr.
  eapply a_wf_pskl_delta_mono; [ exact Hr | ].
  intros γ _ Hγ. clear - Hβ Hγ. fsetdec.
Qed.

(** The fuel only bounds the depth (see the header); call at [size_pskl P]. *)
Fixpoint wf_pskl_ck (n : nat) (Θ : aenv) (Δ : atoms) (P : pskl)
    {struct n} : bool :=
  match n with
  | O => false
  | S n' =>
      match P with
      | pskl_unit => true
      | pskl_var_b _ => false
      | pskl_var_f α => tvarish_ck Θ α
      | pskl_arrow P1 P2 => wf_pskl_ck n' Θ Δ P1 && wf_pskl_ck n' Θ Δ P2
      | pskl_all_syn P1 =>
          let β := supply_fresh (dom Θ `union` Δ `union` ftvar_in_pskl P1) in
          wf_pskl_ck n' ((β ~ abind_tvar) ++ Θ) (add β Δ)
                     (open_pskl_wrt_pskl P1 (pskl_var_f β))
      | pskl_ghost => true
      | pskl_univ_ghost P1 =>
          guarded_shape_ck P1 && wf_pskl_ck n' (aenv_minus Θ Δ) empty P1
      end
  end.

Lemma wf_pskl_ck_sound : forall n Θ Δ P,
  wf_pskl_ck n Θ Δ P = true -> {{ Θ ⨟ Δ ⊢ₚₛ P }}a.
Proof.
  induction n as [ | n IH ]; intros * Hck; simpl in Hck; [ discriminate | ].
  destruct P.
  - apply a_wf_pskl__unit.
  - discriminate.
  - apply a_wf_pskl__var. apply tvarish_ck_binds; exact Hck.
  - apply andb_prop in Hck; destruct Hck.
    apply a_wf_pskl__arrow; apply IH; assumption.
  - apply a_wf_pskl_all_intro_at
      with (β := supply_fresh (dom Θ `union` Δ `union` ftvar_in_pskl P));
      [ pose proof (supply_fresh_notin
                      (dom Θ `union` Δ `union` ftvar_in_pskl P)) as Hfr;
        clear - Hfr; fsetdec
      | apply IH; exact Hck ].
  - apply a_wf_pskl__ghost.
  - apply andb_prop in Hck; destruct Hck as [Hg Hw].
    pose proof (IH _ _ _ Hw) as Hwf.
    apply a_wf_pskl__univ_ghost;
      [ apply guarded_shape_ck_sound;
        [ exact Hg | eapply a_wf_pskl_lc; exact Hwf ]
      | exact Hwf ].
Qed.

(* ===================================================================== *)
(*  Shared tactics for the runners' Equations obligations                 *)
(* ===================================================================== *)

(** Instantiate the shape premises Equations' splitting leaves as
    [_ = _ -> …] implications at the clause's own constructors, and drop
    the ones that do not apply.  ⚙ def_sub_impl.v keeps its own extended
    variant (it also discharges [<>] and guarded-or-ghost premises). *)
Ltac select_shape_premises :=
  repeat match goal with
         | Hp : forall _ _ _ _ _, _ = _ -> _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ _ eq_refl eq_refl eq_refl)
                   | clear Hp ]
         | Hp : forall _ _ _, _ = _ -> _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ eq_refl eq_refl eq_refl)
                   | clear Hp ]
         | Hp : forall _ _ _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _ _ _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ eq_refl) | clear Hp ]
         | Hp : forall _ _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl) | clear Hp ]
         | Hp : _ = _ -> _ |- _ =>
             first [ specialize (Hp eq_refl) | clear Hp ]
         | Hp : _ /\ _ |- _ => destruct Hp
         end.

(** Add the components of every [lc_pskl] arrow / ⫯ hypothesis beside it.
    Non-destructive: the originals stay (Equations' catch-all splitting
    let-binds aliases of the scrutinees, whose lc goals close by conversion
    against the ORIGINAL hypotheses). *)
Ltac saturate_lc :=
  repeat match goal with
         | Hlc : lc_pskl (pskl_arrow ?a ?b) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a, _ : lc_pskl b |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_arrow_inv in Hx;
                    destruct Hx
             end
         | Hlc : lc_pskl (pskl_univ_ghost ?a) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_univ_ghost_inv in Hx
             end
         end.
