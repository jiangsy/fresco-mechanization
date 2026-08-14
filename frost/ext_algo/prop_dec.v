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

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_ln.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.consis.prop_soundness_consis.
                     (* a_wf_pskl_all_inv_at *)
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_dec.
Require Import src.frost.ext_algo.prop_termination.   (* aenv_defs_mono *)
Require Import src.frost.ext_algo.def_pat_impl.       (* §1's deciders *)

(* ⚠️ NO [Set Implicit Arguments] — this file's statements are about
   def_dec.v's and def_pat_impl.v's constants, which are declared without it
   (their consumers are [Equations] blocks; def_guess_impl.v's header). *)

(* ===================================================================== *)
(*  §1  Atom sets and context lookups                                     *)
(* ===================================================================== *)

Lemma in_mem_true : forall α S, α `in` S -> mem α S = true.
Proof. intros * H. apply AtomSetFacts.mem_iff. exact H. Qed.

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

(** ⚙ Off the NEGATIVE scan, not a second induction: def_dec.v §2 already
    proved [false] refutes, so [true] follows by case analysis on the bool. *)
Lemma flex_bound_ck_complete : forall Θ α,
  a_flex_tvar Θ α -> flex_bound_ck Θ α = true.
Proof.
  intros Θ α Hf. destruct (flex_bound_ck Θ α) eqn:Hck; [ reflexivity | ].
  exfalso. exact (flex_bound_ck_not_flex_tvar Θ α Hck Hf).
Qed.

Lemma non_flex_ck_complete : forall Θ P,
  a_non_flex Θ P -> non_flex_ck Θ P = true.
Proof.
  intros Θ P [Hlc Hnf]. destruct P; simpl; try reflexivity.
  apply negb_true_iff.
  destruct (flex_bound_ck Θ α) eqn:Hck; [ exfalso | reflexivity ].
  apply Hnf. destruct (flex_bound_ck_flex_tvar Θ α Hck) as [Hb | [τ Hb]];
    [ apply a_flex__var | eapply a_flex__var_def ]; eassumption.
Qed.

Lemma rigid_bound_ck_complete : forall Θ α,
  binds α abind_tvar Θ -> rigid_bound_ck Θ α = true.
Proof.
  induction Θ as [ | [β b] Θ' IH ]; simpl; intros α Hb; [ inversion Hb | ].
  destruct Hb as [Heq | Hin].
  - inversion Heq; subst. destruct (α == α); congruence.
  - destruct b; try solve [ apply IH; exact Hin ].
    destruct (α == β); [ reflexivity | apply IH; exact Hin ].
Qed.

Lemma tvarish_ck_complete : forall Θ α,
  a_binds_tvar α Θ -> tvarish_ck Θ α = true.
Proof.
  intros Θ α Hb. unfold tvarish_ck. apply orb_true_intro.
  destruct Hb as [Hr | [Hf | [τ Hf]]];
    [ left; apply rigid_bound_ck_complete; exact Hr
    | right; apply flex_bound_ck_complete; left; exact Hf
    | right; apply flex_bound_ck_complete; right; exists τ; exact Hf ].
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

Lemma ghost_free_ck_complete : forall P,
  pskl_ghost_free P -> ghost_free_ck P = true.
Proof.
  induction P; simpl; intros Hgf;
    try reflexivity; try contradiction; try solve [ apply IHP; exact Hgf ].
  destruct Hgf as [H1 H2]. apply andb_true_intro; split; auto.
Qed.

Lemma mono_ck_complete : forall A, mono_ptyp A -> mono_ck A = true.
Proof.
  induction A; simpl; intros Hm; try reflexivity; try solve [ inversion Hm ].
  inversion Hm; subst. apply andb_true_intro; split; auto.
Qed.

Lemma nonghost_ck_complete : forall P,
  nonghost_pskl P -> nonghost_ck P = true.
Proof. intros P H; inversion H; subst; reflexivity. Qed.

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

(** ⚙ The evidence-carrying decomposition succeeds on exactly the shape the
    ∀ rows of the consistency relation produce.  Stated through [proj1_sig]
    rather than as an equation between [sig]s: the witness is a proof, and
    proofs of a [binds]-shaped equation are not syntactically unique. *)
Lemma split_tvar_head_complete : forall α Θ1,
  exists r, split_tvar_head α ((α ~ abind_tvar) ++ Θ1) = Some r
            /\ proj1_sig r = Θ1.
Proof.
  intros α Θ1. simpl. destruct (α == α) as [Heq | Hne]; [ | congruence ].
  eexists. split; [ reflexivity | reflexivity ].
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
    the ⫯ row drops [Δ] to [empty], which the size does not see.

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
    apply orb_true_intro. destruct Hin as [HΔ | HΘ];
      [ left; apply in_mem_true; exact HΔ
      | right; apply tvarish_ck_complete; exact HΘ ].

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
       runs its premise at [empty] rather than at [Δ] *)
    inversion Hwf as [ | | | | | ? ? ? Hg Hp ]; subst.
    apply andb_true_intro; split;
      [ apply guarded_shape_ck_complete; exact Hg
      | apply IH; solve [ exact Hp | lia ] ].
Qed.

(** The call the runners actually make. *)
Corollary wf_pskl_ck_complete_at_size : forall Θ Δ P,
  {{ Θ ⨟ Δ ⊢ₚₛ P }}a -> wf_pskl_ck (size_pskl P) Θ Δ P = true.
Proof. intros; apply wf_pskl_ck_complete; [ assumption | lia ]. Qed.
