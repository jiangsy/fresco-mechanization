(** ⚠️ THE PROPERTY THE PAPER MARKS WITH ITS OWN TODO IS FALSE.

    subtyping-proofs.tex:3243, inside P7b's Sub-ForallR case, records:

        % WT: We may have the property that, in algo subtyping, when input P_0
        % is a concrete type, RHS of subtyping is always P_0.  TODO: optional:
        % check this.  If yes, use this to simplify the proof.

    DESIGN §9.1 flagged it as a PREREQUISITE, because two of P7b's cases lean
    on it (Sub-Check for [P'_0 ≡ P_0], Sub-ForallR for [P_1 ≡ P'_0]) and, if
    it were false, both would need rewriting.  It IS false — and it is false
    for a reason that does not go away by strengthening the premises.

    THE WITNESS, and why it is in scope.  At [N = TY] the mode constraint
    [skmod[TY]{P0}{TC}] forces [P0 = ptyp_to_pskl A] — that IS the paper's
    "P_0 is a concrete type", and it is the only place the concreteness comes
    from.  But a concrete TYPE may be, or may contain, a FLEXIBLE VARIABLE,
    and a concrete type may equally be faced by one.  Consistency's [FlexL]
    row then fires:

        {{ Θ ⊢[ P0 ] α̂ ∼ α̂ ⊣ Θ'          ([a_consis__flex_l], via [a_assign])

    whose OUTPUT is the subject [α̂] }}a, not the input skeleton [P0].  Algorithmic
    [Arrow] copies that output into its own, so already at

        P0 = unit → unit        (concrete: [ptyp_to_pskl (unit → unit)])
        P  = α̂ → unit
        Q  = α̂ → unit

    the RHS is not [P0].  The two are of course EQUIVALENT — the run's output
    context defines [α̂ ≔ unit] — which is exactly what the paper's own text
    says in the cases that use it ("P'_0 is equivalent to P_0", ":3181"; "P'_0
    and P_1 are equivalent through Q", ":3238").  So:

    WHAT THIS DOES AND DOES NOT SETTLE.  It refutes the SIMPLIFICATION the
    TODO proposes (read the RHS off as syntactically [P_0]); it does NOT
    refute Sub-Check or Sub-ForallR, whose written arguments already go
    through the EQUIVALENCE.  The mechanization must therefore keep the
    equivalence route: what P7b needs is

        msubst_pskl κ1 (output)  =  msubst_pskl κ1 P0                (†)

    i.e. equality only AFTER the metasubstitution — which absorbs precisely
    the [α̂ ≔ unit] this witness exploits.  (†) is the real obligation, and it
    is NOT a corollary of anything already proved; see DESIGN §9.1.

    ⚠️ NOTE ON A STRONGER READING.  One might hope to save the TODO by reading
    "concrete type" as also excluding flexibles.  That does not help: the
    counterexample needs no flexible IN [P0] at all — [P0] here is
    [unit → unit], entirely flexible-free.  The flexible is on the SUBJECT
    side, which the property does not constrain. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_shapes.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.

Set Implicit Arguments.

(* ===================================================================== *)
(*  The witness — one undefined flexible α̂, and the concrete [unit → unit] *)
(* ===================================================================== *)

Section CexP7ConcreteRhs.

Variable α : atom.

Definition Θw  : aenv := (α ~ abind_flex_mono) ++ nil.
Definition Θw' : aenv := (α ~ abind_flex_mono_def ptyp_unit) ++ nil.

(** The INPUT skeleton: a concrete type, and flexible-free. *)
Definition P0w : pskl := pskl_arrow pskl_unit pskl_unit.

(** The SUBJECT and the OUTPUT: the flexible survives into the RHS. *)
Definition Pw : pskl := pskl_arrow (pskl_var_f α) pskl_unit.

Lemma Θw_wf : {{ ⊢ Θw }}a.
Proof.
  apply a_wf_aenv__flex; [ simpl; clear; fsetdec | apply a_wf_aenv__nil ].
Qed.

(** [P0w] IS a concrete type — the paper's hypothesis, in the only form the
    mode constraint can deliver it. *)
Lemma P0w_concrete : P0w = ptyp_to_pskl (ptyp_arrow ptyp_unit ptyp_unit).
Proof. reflexivity. Qed.

Lemma P0w_mode : a_ty_mode_compat (mode_fn mode_tc) P0w.
Proof.
  unfold P0w. apply a_ty_mode_compat__fn.
  apply (@a_ty_mode_compat__tc ptyp_unit).
Qed.

(** The domain step: [FlexL] assigns [α̂ ≔ unit] and RETURNS [α̂]. *)
Lemma cex_assign : a_assign Θw nil α pskl_unit Θw'.
Proof.
  unfold Θw, Θw'.
  apply a_assign__solve_m with (βs := nil) (τ := ptyp_unit);
    [ simpl; clear; fsetdec
    | apply a_guess_mono__unit
    | apply mono_ptyp__unit
    | apply uniq_nil
    | intros α1 Hα1; simpl in Hα1; clear - Hα1; fsetdec ].
Qed.

Lemma cex_consis :
  {{ Θw ⊢[ pskl_unit ] (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θw' }}a.
Proof.
  apply a_consis__flex_l;
    [ split; [ apply lc_pskl_unit | intros Hf; inversion Hf ]
    | apply cex_assign ].
Qed.

(** The codomain step: [Check] on [unit ∼ unit], which returns its input. *)
Lemma cex_codomain :
  a_sub a_sub_mode_ty mode_tc pskl_unit Θw' pskl_unit pskl_unit Θw'.
Proof.
  apply a_sub__check;
    [ exact I | exact I | apply guarded_pskl__unit | apply guarded_pskl__unit | ].
  exists pskl_unit. apply a_consis__unit.
Qed.

(** …and [Arrow] copies the domain's output into the RHS. *)
Theorem cex_derivation :
  a_sub a_sub_mode_ty (mode_fn mode_tc) P0w Θw Pw Pw Θw'.
Proof.
  unfold P0w, Pw.
  apply a_sub__arrow with (Θ1 := Θw');
    [ apply cex_consis | apply cex_codomain ].
Qed.

(* ===================================================================== *)
(*  The refutation                                                        *)
(* ===================================================================== *)

(** The property as the paper's TODO states it, with EVERY side condition the
    Sub-Check / Sub-ForallR call sites can supply added as a premise — so the
    refutation cannot be blamed on a missing hypothesis. *)
Definition p7_concrete_rhs_property : Prop :=
  forall NM M P0 Θ0 P Q Θ1 A,
    a_sub NM M P0 Θ0 P Q Θ1 ->
    {{ ⊢ Θ0 }}a ->
    a_ty_mode_compat M P0 ->
    P0 = ptyp_to_pskl A ->             (* "P_0 is a concrete type" *)
    Q = P0.

Theorem p7_concrete_rhs_is_false : ~ p7_concrete_rhs_property.
Proof.
  intros Hprop.
  assert (Heq : Pw = P0w).
  { eapply (Hprop _ _ _ _ _ _ _ (ptyp_arrow ptyp_unit ptyp_unit));
      [ apply cex_derivation | apply Θw_wf | apply P0w_mode
      | apply P0w_concrete ]. }
  unfold Pw, P0w in Heq. inversion Heq.
Qed.

(** Non-vacuity: the witness derivation really exists (and its two contexts
    really are the wf ones the algorithm would produce). *)
Theorem cex_nonvacuous :
  exists Θ1, a_sub a_sub_mode_ty (mode_fn mode_tc) P0w Θw Pw Pw Θ1 /\
             {{ ⊢ Θw }}a.
Proof. exists Θw'; split; [ apply cex_derivation | apply Θw_wf ]. Qed.

End CexP7ConcreteRhs.

