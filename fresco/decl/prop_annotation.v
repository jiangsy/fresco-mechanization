(** Fresco — "only polytypes need annotation" (annotation-erasure property).

    The headline — erasing every MONOTYPE annotation on a lambda binder
    ([λᴬ.e ↦ λ.e] when [A] monotype) preserves typing at the same mode and
    type — is not mechanized at present; see the RESTART NOTE below.

    NB. We do NOT erase ascriptions [(e : A)]: a monotype ascription is genuinely
    load-bearing when it supplies INFERENCE mode to a non-inferring term — e.g.
    [freeze e] only checks, never infers, so [(freeze e : A)] is typeable but
    [freeze e] is not in an inference position.  That is a MODE role independent
    of polymorphism.  (Its lemma, [freeze_no_infer], was deleted 2026-10-09
    as unused.) *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.decl.prop_basic.
Require Import src.fresco.decl.prop_wellformed.
Require Import src.fresco.decl.prop_shallow.

Set Implicit Arguments.

(* RESTART NOTE: the pre-restart [erase_lam_mono_typing] ("erasing monotype
   lambda annotations preserves typing") lived here with an admitted [app]
   case (needs bespoke skeleton lemmas).  Dropped per the no-admits policy —
   see prop_annotation.v history / PROGRESS.md; re-prove it with the
   paper-faithful skeleton machinery if the claim returns to the paper. *)
