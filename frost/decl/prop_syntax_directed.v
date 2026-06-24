(** Equivalence of the full declarative typing [d_typing] (paper [dtylab],
    Fig. decl-typing) and the syntax-directed typing [sd_typing] (paper
    [sdtylab], Fig. syntax-directed-typing).

    Paper Lemmas: Soundness / Completeness of the syntax-directed rules.
    The only structural difference between the two systems is the standalone
    type-abstraction rule [dtylab{Forall}]: [sd_typing] folds it into the
    checked-lambda rules ([__abs_check_step] / [__abs_anno_check_step], a
    [∀]-peel restricted to [λ]-values).  Soundness replays each peel as a
    [Forall]; completeness case-splits the [Forall] value on whether it is a
    lambda (peel) or a base term (re-routed through [Sub]+[ForallR]). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_weakening.
Require Import src.frost.decl.prop_stability.

(* ===================================================================== *)
(*  Soundness:  sd_typing ⊆ d_typing                                      *)
(* ===================================================================== *)

Theorem sd_typing_sound : forall M Γ e A,
    sd_typing M Γ e A -> d_typing M Γ e A.
Proof.
  intros M Γ e A H. induction H.
  - apply d_typing__unit.
  - apply d_typing__var; assumption.
  - apply d_typing__anno; assumption.
  - eapply d_typing__sub; eassumption.
  - apply d_typing__freeze; assumption.
  - (* abs (m ≠ tc) *)
    apply d_typing__abs with (L := L); assumption.
  - (* abs_anno (m ≠ tc) *)
    apply d_typing__abs_anno with (L := L); assumption.
  - (* abs_check_step → Forall over the lambda *)
    apply d_typing__forall with (L := L); [ apply is_value__abs | assumption ].
  - (* abs_check_base → AbsCheck (ᾱ = ·) *)
    apply d_typing__abs_check with (L := L); assumption.
  - (* abs_anno_check_step → Forall over the annotated lambda *)
    apply d_typing__forall with (L := L); [ apply is_value__abs_anno | assumption ].
  - (* abs_anno_check_base → AbsAnnoCheck (ᾱ = ·) *)
    apply d_typing__abs_anno_check with (L := L); assumption.
  - (* app *)
    eapply d_typing__app; eassumption.
Qed.
