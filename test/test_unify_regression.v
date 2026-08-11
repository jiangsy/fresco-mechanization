(** REGRESSION TEST for the corrected [Flex-Flex-Assign].

    HISTORY.  This file used to hold the machine-checked COUNTEREXAMPLE
    [a_unify_stuck_on_arrow_definition]: the pre-fix [a_unify__flex_assign]
    recursed into [a_unify] (the paper's [unifyvar], whose subjects are
    variables), so on  Θ₀ = (α̂ ≔ unit → unit), β̂  the algorithm was STUCK —
    substituting the definition turns the subject into the ARROW
    [unit → unit], and the var-only rules had nowhere to go.

    THE FIX (docs/PAPER-GAPS.md, "the `unify` premise IS consistency"):
    the paper's premise  Θ₀ ⊢ α̂[τ/α1̂] ∼ β̂[τ/α1̂] ⊣ Θ₁  is the CONSISTENCY
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
Require Import src.frost.def_extra.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.consis.prop_soundness_consis.

(** A flexible variable defined to an ARROW — a perfectly ordinary state: it is
    exactly what [Assign-SolveM] produces via [guess^TY]. *)
Definition Tarr : ptyp := ptyp_arrow ptyp_unit ptyp_unit.

Theorem a_unify_succeeds_on_arrow_definition : forall (a b : atom),
  a <> b ->
  {{ ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono) ++ nil)
    ⊲ a ≈ᵘ b
    ⊣ ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono_def Tarr) ++ nil) }}a.
Proof.
  intros a b Hne.
  apply a_unify__flex_assign with (Q := pskl_var_f b).
  - (* α̂ is hatted *)
    right. exists Tarr. unfold binds; left; reflexivity.
  - (* β̂ is hatted *)
    left. unfold binds; right; left; reflexivity.
  - (* the walked definition re-attaches above the output (Barendregt) *)
    simpl. clear - Hne. fsetdec.
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
      apply (@a_assign__solve_m nil nil b
               (ptyp_to_pskl Tarr) nil Tarr).
      * simpl. fsetdec.
      * apply a_guess_mono__arrow with (Ξ1 := nil) (Ξ2 := nil);
          apply a_guess_mono__unit.
      * apply mono_ptyp__arrow; apply mono_ptyp__unit.
      * constructor.
      * intros α1 Hα1. simpl in Hα1. fsetdec.
Qed.

(** Sanity: soundness applies — the output context is well-formed, an
    information increase of the input, and equates the two variables. *)
Corollary a_unify_succeeds_sound : forall (a b : atom),
  a <> b ->
  ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono) ++ nil)
    ⊴ ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono_def Tarr) ++ nil)
  /\ {{ ⊢ ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono_def Tarr) ++ nil) }}a
  /\ ({{ ((a ~ abind_flex_mono_def Tarr) ++ (b ~ abind_flex_mono_def Tarr) ++ nil)
        ⊢ (ptyp_var_f a) ≡ᵗ (ptyp_var_f b) }}a).
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


(* ===================================================================== *)
(*  REGRESSION TEST for the corrected [Assign-Assign]  (the SAME bug class *)
(*  as above, on the OTHER back-edge into consistency).                    *)
(*                                                                         *)
(*  The pre-fix [a_assign__assign] recursed into [a_assign] instead of      *)
(*  dropping into CONSISTENCY over the merged context [Ξ ++ Θ0].  Fixing    *)
(*  that exposed a second, subtler trap: it is tempting to premise the rule *)
(*  on [α̂ ≠ β̂] and keep the subject a bare variable, on the theory that a   *)
(*  subject must be an UNDEFINED flex var to be assignable.  IT NEED NOT BE.*)
(*  Nothing enforces that — neither [a_consis__flex_l] nor the reference    *)
(*  implementation's [U-FlexL] ([| p0, MFlex alpha -> assign alpha p0 []],  *)
(*  type.ml:182-185) guards on it.  So a DEFINED α̂ can be the subject, the  *)
(*  walk then reaches α̂'s OWN definition, and the rule must fire with       *)
(*  β̂ = α̂ — whereupon the subject [α̂[τ/α̂]] is the MONOTYPE τ, not a var.    *)
(*  With an [α̂ ≠ β̂] premise NO rule fires and assignvar is STUCK, exactly   *)
(*  as the old [unifyvar] reading was stuck above.                          *)
(*                                                                         *)
(*  The implementation computes precisely this: [subst_var (MFlex alpha)    *)
(*  tau beta] with [beta = alpha] reduces to [tau] (type.ml:358-363).       *)
(*                                                                         *)
(*  Below: the previously-stuck state DERIVES.                             *)
(* ===================================================================== *)

Theorem a_assign_succeeds_on_own_definition : forall (a : atom),
  {{ ((a ~ abind_flex_mono_def Tarr) ++ nil)
    ⊲[ nil ] a ≔ (pskl_arrow pskl_unit pskl_unit)
  ⊣ ((a ~ abind_flex_mono_def Tarr) ++ nil) }}a.
Proof.
  intros a.
  apply (@a_assign__assign nil nil nil a a Tarr
           (pskl_arrow pskl_unit pskl_unit) (pskl_arrow pskl_unit pskl_unit)).
  - (* HATTED SUBJECT: α̂ IS the head binding here — which is why this premise
       must be stated on the CONCLUSION's context.  On [Ξ ++ Θ0] it would be
       FALSE in exactly this case. *)
    unfold a_flex_tvar. right. exists Tarr. unfold binds. left. reflexivity.
  - (* the walked definition re-attaches above the output (Barendregt) *)
    simpl. clear. fsetdec.
  - simpl.
    replace (if a == a then pskl_arrow pskl_unit pskl_unit else pskl_var_f a)
      with (pskl_arrow pskl_unit pskl_unit)
      by (destruct (a == a); congruence).
    (* the subject is now the MONOTYPE τ = unit → unit, NOT a variable *)
    eapply a_consis__arrow; apply a_consis__unit.
Qed.
