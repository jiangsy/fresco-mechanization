(** REGRESSION TEST for the corrected [Flex-Flex-Assign].

    HISTORY.  This file used to hold the machine-checked COUNTEREXAMPLE
    [a_unify_stuck_on_arrow_definition]: the pre-fix [a_unify__flex_assign]
    recursed into [a_unify] (the paper's [unifyvar], whose subjects are
    variables), so on  Θ₀ = (α̂ ≔ unit → unit), β̂  the algorithm was STUCK —
    substituting the definition turns the subject into the ARROW
    [unit → unit], and the var-only rules had nowhere to go.

    THE FIX (docs/PAPER-GAPS.md, "the `unify` premise IS consistency"):
    the paper's premise  Θ₀ ⊢ α̂[τ/γ̂] ∼ β̂[τ/γ̂] ⊣ Θ₁  is the CONSISTENCY
    judgment with the output dropped (full-algo-spec.tex:1440-1442), so
    [a_unify] and [a_consis] are now MUTUALLY inductive and
    [a_unify__flex_assign] recurses into consistency.

    Below: the very instance that used to be stuck now SUCCEEDS —
    consistency's FlexR assigns  β̂ ≔ unit → unit  via [Assign-SolveM],
    exactly as the paper prescribes. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_decorate.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_consis_sound.

(** A flexible variable defined to an ARROW — a perfectly ordinary state: it is
    exactly what [Assign-SolveM] produces via [guess^TY]. *)
Definition Tarr : ptyp := ptyp_arrow ptyp_unit ptyp_unit.

Theorem a_unify_succeeds_on_arrow_definition : forall (a b : atom),
  a <> b ->
  ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono) ++ nil)
    ⊲ a ≈ᵘ b
    ⊣ ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono_def Tarr) ++ nil).
Proof.
  intros a b Hne.
  apply a_unify__flex_assign with (Q := pskl_var_f b).
  - (* α̂ is hatted *)
    right. exists Tarr. unfold binds; left; reflexivity.
  - (* β̂ is hatted *)
    left. unfold binds; right; left; reflexivity.
  - (* the consistency premise: subject  unit → unit,  input  β̂ *)
    simpl.
    destruct (@eq_dec ptypvar EqDec_eq_of_X a a) as [_|Hcontra];
      [ | congruence ].
    destruct (@eq_dec ptypvar EqDec_eq_of_X b a) as [Heq|_];
      [ congruence | ].
    (* FlexR: assign  β̂ ≔ unit → unit *)
    apply a_consis__flex_r.
    + (* nonflex(unit → unit) *)
      split; [ repeat constructor | ].
      intros Hflex; inversion Hflex.
    + (* Assign-SolveM with guess^TY(unit → unit) = (·; unit → unit) *)
      apply (@a_assign__solve_m (add a empty) nil nil b
               (ptyp_to_pskl Tarr) nil Tarr).
      * simpl. fsetdec.
      * apply a_guess_mono__arrow with (Ξ1 := nil) (Ξ2 := nil);
          apply a_guess_mono__unit.
      * apply mono_ptyp__arrow; apply mono_ptyp__unit.
      * constructor.
      * intros γ Hγ. simpl in Hγ. fsetdec.
Qed.

(** Sanity: soundness applies — the output context is well-formed, an
    information increase of the input, and equates the two variables. *)
Corollary a_unify_succeeds_sound : forall (a b : atom),
  a <> b ->
  ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono) ++ nil)
    ⊴ ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono_def Tarr) ++ nil)
  /\ a_wf_aenv
       ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono_def Tarr) ++ nil)
  /\ (((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono_def Tarr) ++ nil)
        ⊢ (ptyp_var_f a) ≡ᵗ (ptyp_var_f b)).
Proof.
  intros a b Hne.
  eapply a_unify_sound.
  - apply a_unify_succeeds_on_arrow_definition. exact Hne.
  - (* the input context is well-formed *)
    apply a_wf_aenv__flex_def.
    + simpl. fsetdec.
    + apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit.
    + apply mono_ptyp__arrow; apply mono_ptyp__unit.
    + apply a_wf_aenv__flex; [ simpl; fsetdec | apply a_wf_aenv__nil ].
Qed.
