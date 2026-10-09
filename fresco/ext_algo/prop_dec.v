(** ext_algo — the DECIDERS' COMPLETENESS DIRECTIONS.
    (Completeness campaign, §8c step 2a.)

    [def_dec.v] and [def_pat_impl.v] §1 state one boolean check per rule guard
    and prove each SOUND ([… _ck = true -> <the guard>]), which is all a
    soundness-only runner owes: a check that answered [false] where the guard
    holds would make the runner REJECT, and rejection is justified by nothing
    in that contract.

    ⭐ THE COMPLETENESS CAMPAIGN CHANGES EXACTLY THAT.  Once [None] has to mean
    UNTYPABLE, every [false] must be earned: a runner branch that the relation
    reaches must not be turned away by its own test.  So each check owes the
    converse, [<the guard> -> … _ck = true], and this file is the inventory.

    §1  atom sets and context lookups
    §2  shape checks
    §3  context-shape checks and structural equality
    §4  local closure  (def_pat_impl.v §1's degree checks)
    §5  ⭐ the wf checker — the only one with content
    §6  the evidence-carrying DECOMPOSITIONS (not every test is a boolean)

    ⭐ ALL BUT ONE ARE MECHANICAL, and that is the point: the deciders were
    written as structural mirrors of their predicates, so the converse is the
    same induction read backwards.  [wf_pskl_ck] is the exception on both
    counts named in def_dec.v's header — it carries FUEL, and its ∀ row is
    COFINITE:

    - FUEL ADEQUACY.  The bound is [size_pskl P], and the ∀ row descends into
      [open P1 (pskl_var_f β)], whose size is [size_pskl P1]
      ([size_pskl_open_pskl_wrt_pskl_var]) — so opening a binder costs exactly
      the [S] the [pskl_all_syn] node pays for, and the fuel never runs short.
      ⚙ This is why the fuel is honest: it is not a search bound that might be
      too small, it is the checker's own structural depth made explicit.
    - THE COFINITE ROW.  The checker opens at ONE name of its own choosing
      ([supply_fresh] over everything in scope), so completeness needs the
      family INSTANTIATED there — [a_wf_pskl_all_inv_at]
      (algo/consis/prop_soundness_consis.v), whose only precondition is
      [β ∉ ftvar_in_pskl P] and which [supply_fresh_notin] discharges.  ⚙ It
      is the exact mirror of the soundness direction, which regenerates the
      family from that one instance via [a_wf_pskl_all_intro_at].

    ⚠️ These are the runners' TESTS, not the runners' branch selection.  That
    a test passes does not yet say the runner reaches the branch — that is
    §8c.2's step (2d), and it is agreement, not mere success. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.consis.prop_soundness_consis.
                     (* a_wf_pskl_all_inv_at *)
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_dec.
Require Import src.fresco.ext_algo.prop_termination.   (* aenv_defs_mono *)
Require Import src.fresco.ext_algo.def_pat_impl.       (* §1's deciders *)
Require Import src.fresco.ext_algo.def_typing_impl.    (* ptyp_arrow_split *)

(* ⚠️ NO [Set Implicit Arguments] — this file's statements are about
   def_dec.v's and def_pat_impl.v's constants, which are declared without it
   (their consumers are [Equations] blocks; def_guess_impl.v's header). *)

(* ===================================================================== *)
(*  §1  Atom sets and context lookups                                     *)
(* ===================================================================== *)

Lemma notin_mem_false : forall α S, α `notin` S -> mem α S = false.
Proof.
  intros * H. destruct (mem α S) eqn:Hm; [ | reflexivity ].
  exfalso. apply H. apply mem_true_in. exact Hm.
Qed.

Lemma inter_is_empty_complete : forall S1 S2,
  S1 ∩ S2 [=] empty -> is_empty (inter S1 S2) = true.
Proof.
  intros * H. apply AtomSetFacts.is_empty_iff.
  intros a Hin. apply (AtomSetFacts.empty_iff a). apply H. exact Hin.
Qed.

(* ⚙ [flex_tvar_flex_bound_ck] was a DUPLICATE of [flex_tvar_flex_bound_ck]; imported, not reproved (2026-08-23). *)

(* ⚙ [rigid_bound_ck_complete] was a DUPLICATE of [rigid_bound_ck_complete]; imported, not reproved (2026-08-23). *)

Lemma tvarish_ck_complete : forall Θ α,
  a_binds_tvar α Θ -> tvarish_ck Θ α = true.
Proof.
  intros Θ α Hb. unfold tvarish_ck. apply orb_true_intro.
  destruct Hb as [Hr | [Hf | [τ Hf]]];
    [ left; apply rigid_bound_ck_complete; exact Hr
    | right; apply flex_tvar_flex_bound_ck; left; exact Hf
    | right; apply flex_tvar_flex_bound_ck; right; exists τ; exact Hf ].
Qed.

(* ===================================================================== *)
(*  §2  Shape checks                                                      *)
(* ===================================================================== *)

(** ⚙ The lc side of [guarded_pskl]'s arrow row is dropped, not needed: the
    check tests the HEAD SHAPE only (def_dec.v's header), so this direction
    is strictly easier than its soundness twin, which had to take [lc_pskl P]
    as a hypothesis to put it back. *)
Lemma guarded_shape_ck_complete : forall P,
  guarded_pskl P -> guarded_shape_ck P = true.
Proof. intros P H; inversion H; subst; reflexivity. Qed.

(* ⚙ [ghost_free_ck_complete] MOVED to def_dec.v (2026-08-18) — the runner's
   ForallL / UnivGhostL obligations need it, and this file is downstream of
   def_look_impl.v.  It is still in scope here, through def_dec.v. *)

(* ⚙ [mono_ck_complete] was a DUPLICATE of [mono_ck_complete]; imported, not reproved (2026-08-23). *)

(* ===================================================================== *)
(*  §3  Context shapes and structural equality                            *)
(* ===================================================================== *)

Lemma uniq_ck_complete : forall Θ, uniq Θ -> uniq_ck Θ = true.
Proof.
  induction Θ as [ | [x b] Θ' IH ]; simpl; intros Hu; [ reflexivity | ].
  inversion Hu; subst.
  apply andb_true_intro; split;
    [ apply negb_true_iff; apply notin_mem_false; assumption
    | apply IH; assumption ].
Qed.

(** ⚠️ [a_suffix__cons] is stated over [(a ~ b) ++ Ξ], and metalib's [x ~ a]
    is [one (x, a)] — a DEFINITION — so the inversion produces a cons only
    after [simpl] (the §8b.6 trap). *)
Lemma suffix_ck_complete : forall Ξ, a_suffix Ξ -> suffix_ck Ξ = true.
Proof.
  induction Ξ as [ | [x b] Ξ' IH ]; intros Hs; [ reflexivity | ].
  inversion Hs as [ | ? ? ? Htl Hbd ]; subst.
  inversion Hbd; subst; simpl; apply IH; exact Htl.
Qed.

Lemma hole_ck_complete : forall P, P = pskl_hole -> hole_ck P = true.
Proof. intros P ->; reflexivity. Qed.

Lemma pskl_eqb_complete : forall P Q, P = Q -> pskl_eqb P Q = true.
Proof.
  intros P Q <-. induction P; simpl;
    try reflexivity; try solve [ assumption ].
  - apply Nat.eqb_refl.
  - destruct (α == α); congruence.
  - apply andb_true_intro; split; assumption.
Qed.

Lemma ptyp_eqb_complete : forall A B, A = B -> ptyp_eqb A B = true.
Proof.
  intros A B <-. induction A; simpl;
    try reflexivity; try solve [ assumption ].
  - apply Nat.eqb_refl.
  - destruct (α == α); congruence.
  - apply andb_true_intro; split; assumption.
Qed.

(* ===================================================================== *)
(*  §4  Local closure  (def_pat_impl.v §1)                                *)
(* ===================================================================== *)

Lemma degree_ptyp_ck_complete : forall A k,
  degree_ptyp_wrt_ptyp k A -> degree_ptyp_ck k A = true.
Proof.
  induction A; simpl; intros k Hd; inversion Hd; subst;
    try reflexivity; try solve [ apply IHA; assumption ].
  - apply Nat.ltb_lt; assumption.
  - apply andb_true_intro; split; [ apply IHA1 | apply IHA2 ]; assumption.
Qed.

Corollary lc_ptyp_ck_complete : forall A,
  lc_ptyp A -> degree_ptyp_ck 0 A = true.
Proof.
  intros; apply degree_ptyp_ck_complete;
    apply degree_ptyp_wrt_ptyp_of_lc_ptyp; assumption.
Qed.

Lemma degree_pskl_ck_complete : forall P k,
  degree_pskl_wrt_pskl k P -> degree_pskl_ck k P = true.
Proof.
  induction P; simpl; intros k Hd; inversion Hd; subst;
    try reflexivity; try solve [ apply IHP; assumption ].
  - apply Nat.ltb_lt; assumption.
  - apply andb_true_intro; split; [ apply IHP1 | apply IHP2 ]; assumption.
Qed.

Corollary lc_pskl_ck_complete : forall P,
  lc_pskl P -> degree_pskl_ck 0 P = true.
Proof.
  intros; apply degree_pskl_ck_complete;
    apply degree_pskl_wrt_pskl_of_lc_pskl; assumption.
Qed.

Lemma defs_mono_ck_complete : forall Θ,
  aenv_defs_mono Θ -> defs_mono_ck Θ = true.
Proof.
  induction Θ as [ | [x b] Θ' IH ]; simpl; intros Hm; [ reflexivity | ].
  inversion Hm as [ | ? ? He Htl ]; subst.
  apply andb_true_intro; split; [ | apply IH; exact Htl ].
  destruct b; simpl in *; try reflexivity.
  apply mono_ck_complete; exact He.
Qed.

(* ===================================================================== *)
(*  §5  ⭐ The wf checker — fuel adequacy and the cofinite row             *)
(* ===================================================================== *)

(** ⭐ [size_pskl P] fuel is ENOUGH, and any larger amount is too.  The two
    non-structural descents are the ones the header names: the ∀ row opens a
    binder, which [size_pskl_open_pskl_wrt_pskl_var] shows costs nothing, and
    the ⫯ row moves to [aenv_minus Θ Δ] and [empty], which the size does
    not see.

    ⚠️ Stated with the fuel as an INEQUALITY, not at [size_pskl P] exactly.
    The recursive calls are at [n'] with strictly smaller subjects, so an
    exact-fuel statement would not be its own induction hypothesis. *)
Lemma wf_pskl_ck_complete : forall n Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> size_pskl P <= n -> wf_pskl_ck n Θ Δ P = true.
Proof.
  induction n as [ | n IH ]; intros Θ Δ P Hwf Hsz.
  { exfalso. pose proof (size_pskl_min P). lia. }
  destruct P; simpl; simpl in Hsz.

  - (* unit *) reflexivity.

  - (* bound variable — no wf rule mentions one *)
    inversion Hwf.

  - (* free variable *)
    inversion Hwf as [ | ? ? ? Hin | | | | ]; subst.
    apply tvarish_ck_complete; exact Hin.

  - (* arrow *)
    inversion Hwf as [ | | ? ? ? ? H1 H2 | | | ]; subst.
    apply andb_true_intro; split; apply IH; solve [ assumption | lia ].

  - (* ⭐ ∀ — the cofinite row, instantiated at the checker's OWN name *)
    remember (supply_fresh (dom Θ `union` Δ `union` ftvar_in_pskl P)) as β
      eqn:Hβ.
    assert (Hfr : β `notin` (dom Θ `union` Δ `union` ftvar_in_pskl P))
      by (subst β; apply supply_fresh_notin).
    apply IH.
    + apply a_wf_pskl_all_inv_at; [ exact Hwf | clear - Hfr; fsetdec ].
    + rewrite size_pskl_open_pskl_wrt_pskl_var. lia.

  - (* ◇ *) reflexivity.

  - (* ⫯ — the guard is tested beside the recursive call, and the wf rule
       runs its premise at [aenv_minus Θ Δ] and [empty], as the checker does *)
    inversion Hwf as [ | | | | | ? ? ? Hg Hp ]; subst.
    apply andb_true_intro; split;
      [ apply guarded_shape_ck_complete; exact Hg
      | apply IH; solve [ exact Hp | lia ] ].
Qed.

(** The call the runners actually make. *)
Corollary wf_pskl_ck_complete_at_size : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> wf_pskl_ck (size_pskl P) Θ Δ P = true.
Proof. intros; apply wf_pskl_ck_complete; [ assumption | lia ]. Qed.

(* ===================================================================== *)
(*  §6  The evidence-carrying DECOMPOSITIONS                              *)
(*                                                                        *)
(*  Not every runner test is a boolean.  Where a rule needs a piece of    *)
(*  its input taken apart, the runner calls a decomposer that returns     *)
(*  the pieces WITH the defining equation ([option (sig …)] again), and   *)
(*  [None] is a rejection exactly as a [false] is.  So each owes the      *)
(*  same converse: on the shape the relation produces, it SUCCEEDS —      *)
(*  and, since a later step must know WHICH pieces came back, it returns  *)
(*  the expected ones.                                                    *)
(*                                                                        *)
(*  ⚙ Stated as [exists r, … = Some r /\ proj1_sig r = <pieces>] rather   *)
(*  than as an equation between [sig]s: the second component is a proof,  *)
(*  and two proofs of the same equation need not be syntactically equal.  *)
(*  The [proj1_sig] form is also what a caller consumes — it is the       *)
(*  witness, not the evidence, that the next match binds.                 *)
(* ===================================================================== *)

Lemma arrow_split_complete : forall P1 P2,
  exists r, arrow_split (pskl_arrow P1 P2) = Some r
            /\ proj1_sig r = (P1, P2).
Proof. intros. eexists. split; reflexivity. Qed.

Lemma ptyp_arrow_split_complete : forall A1 A2,
  exists r, ptyp_arrow_split (ptyp_arrow A1 A2) = Some r
            /\ proj1_sig r = (A1, A2).
Proof. intros. eexists. split; reflexivity. Qed.

Lemma abind_var_skl_get_complete : forall P,
  exists r, abind_var_skl_get (abind_var_skl P) = Some r /\ proj1_sig r = P.
Proof. intros. eexists. split; reflexivity. Qed.

Lemma abind_var_typ_get_complete : forall A,
  exists r, abind_var_typ_get (abind_var_typ A) = Some r /\ proj1_sig r = A.
Proof. intros. eexists. split; reflexivity. Qed.

(** ⚠️ [uniq] is not decoration.  [lookup_binding] returns the FIRST binding,
    and [binds] is an "appears somewhere" predicate (def_dec.v §2's own
    warning), so without uniqueness the scan may legitimately return a
    DIFFERENT payload than the one the derivation used. *)
Lemma lookup_binding_complete : forall x Θ b,
  uniq Θ -> binds x b Θ ->
  exists r, lookup_binding x Θ = Some r /\ proj1_sig r = b.
Proof.
  intros x Θ. induction Θ as [ | [y b'] Θ' IH ]; intros b Hu Hb;
    [ inversion Hb | ].
  inversion Hu; subst. simpl.
  destruct (x == y) as [-> | Hne].
  - (* the head IS the key, so uniqueness makes it the only binding *)
    destruct Hb as [Heq | Hin].
    + inversion Heq; subst. eexists. split; reflexivity.
    + exfalso. assert (y `in` dom Θ') by (eapply binds_In; exact Hin).
      fsetdec.
  - destruct Hb as [Heq | Hin]; [ inversion Heq; congruence | ].
    (* ⚙ destruct the recursive answer BEFORE rewriting: the clause matches
       [Some (exist _ b' Hb')], so an un-destructed [r] leaves a stuck [let]. *)
    destruct (IH b ltac:(assumption) Hin) as [[b0 Hb0] [Hr Hpr]].
    simpl in Hpr; subst b0.
    rewrite Hr. eexists. split; reflexivity.
Qed.

(** The binder-marker split of the abs rows' output contexts.  ⚠️ Same
    caveat, for the same reason: the scan stops at the FIRST occurrence of
    the key, so it agrees with the derivation's decomposition only when the
    context is unique — which is exactly what the bridge's [uniq] conjunct
    supplies at every call site. *)
Lemma split_at_key_skl_complete : forall x Ξ P Θ',
  uniq (Ξ ++ (x ~ abind_var_skl P) ++ Θ') ->
  exists r, split_at_key_skl x (Ξ ++ (x ~ abind_var_skl P) ++ Θ') = Some r
            /\ proj1_sig r = (Ξ, P, Θ').
Proof.
  intros x Ξ. induction Ξ as [ | [y b] Ξ' IH ]; intros P Θ' Hu.
  - (* ⚠️ NAME the equation, never [_]: the [Some] branch's returned proof
       term MENTIONS it, so clearing it fails with "used in conclusion". *)
    simpl. destruct (x == x) as [Heq | Hne]; [ | congruence ].
    eexists. split; reflexivity.
  - simpl in Hu |- *. inversion Hu; subst.
    destruct (x == y) as [Heq | Hne].
    + (* the key cannot be the head: uniqueness puts it strictly below *)
      exfalso. subst y. simpl_env in *. fsetdec.
    + destruct (IH P Θ' ltac:(assumption)) as [[t Ht] [Hr Hpr]].
      simpl in Hpr; subst t.
      (* ⚠️ the metalib [one] trap again: [simpl] left the GOAL's recursive
         call in cons form while the IH speaks of [x ~ b ++ Θ'].  The two are
         CONVERTIBLE but not syntactically equal, so [rewrite] finds no
         subterm and [simpl_env] does not bridge it — [change] does. *)
      change (x ~ abind_var_skl P ++ Θ')
        with ((x, abind_var_skl P) :: Θ') in Hr.
      rewrite Hr. eexists. split; reflexivity.
Qed.

Lemma split_at_key_typ_complete : forall x Ξ A Θ',
  uniq (Ξ ++ (x ~ abind_var_typ A) ++ Θ') ->
  exists r, split_at_key_typ x (Ξ ++ (x ~ abind_var_typ A) ++ Θ') = Some r
            /\ proj1_sig r = (Ξ, A, Θ').
Proof.
  intros x Ξ. induction Ξ as [ | [y b] Ξ' IH ]; intros A Θ' Hu.
  - (* ⚠️ NAME the equation, never [_]: the [Some] branch's returned proof
       term MENTIONS it, so clearing it fails with "used in conclusion". *)
    simpl. destruct (x == x) as [Heq | Hne]; [ | congruence ].
    eexists. split; reflexivity.
  - simpl in Hu |- *. inversion Hu; subst.
    destruct (x == y) as [Heq | Hne].
    + (* the key cannot be the head: uniqueness puts it strictly below *)
      exfalso. subst y. simpl_env in *. fsetdec.
    + destruct (IH A Θ' ltac:(assumption)) as [[t Ht] [Hr Hpr]].
      simpl in Hpr; subst t.
      (* ⚠️ the metalib [one] trap again: [simpl] left the GOAL's recursive
         call in cons form while the IH speaks of [x ~ b ++ Θ'].  The two are
         CONVERTIBLE but not syntactically equal, so [rewrite] finds no
         subterm and [simpl_env] does not bridge it — [change] does. *)
      change (x ~ abind_var_typ A ++ Θ')
        with ((x, abind_var_typ A) :: Θ') in Hr.
      rewrite Hr. eexists. split; reflexivity.
Qed.

(** ⭐ The readback succeeds on exactly the [⌈⌉]-IMAGES, and returns the type
    it is the painting of.  [ptyp_to_pskl] is injective (it is a constructor
    relabelling), so the answer is forced — which is what makes the readback
    a decomposition rather than a search. *)
Lemma pskl_readback_complete : forall A,
  exists r, pskl_readback (ptyp_to_pskl A) = Some r /\ proj1_sig r = A.
Proof.
  induction A; simpl;
    try solve [ eexists; split; reflexivity ].
  - destruct IHA1 as [r1 [Hr1 Hp1]]. destruct IHA2 as [r2 [Hr2 Hp2]].
    rewrite Hr1. destruct r1 as [A1' H1']. simpl in Hp1; subst A1'.
    rewrite Hr2. destruct r2 as [A2' H2']. simpl in Hp2; subst A2'.
    eexists. split; reflexivity.
  - destruct IHA as [r [Hr Hp]].
    rewrite Hr. destruct r as [A' H']. simpl in Hp; subst A'.
    eexists. split; reflexivity.
Qed.

Lemma pskl_readback_all_complete : forall A0,
  exists r, pskl_readback_all (ptyp_to_pskl (ptyp_all A0)) = Some r
            /\ proj1_sig r = A0.
Proof.
  intros A0. unfold pskl_readback_all. simpl.
  destruct (pskl_readback_complete A0) as [r [Hr Hp]].
  rewrite Hr. destruct r as [A' H']. simpl in Hp; subst A'.
  eexists. split; reflexivity.
Qed.
