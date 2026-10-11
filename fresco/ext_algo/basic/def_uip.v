(** ext_algo — DECIDABLE EQUALITY AND UIP FOR THE INDEX SORTS, so that
    [Equations] can derive the runners' UNFOLDING EQUATIONS.
    (Completeness campaign, §8c.4.)

    ⭐ WHY THIS FILE EXISTS.  Every runner is an [Equations … by struct H] on
    a `Prop` domain predicate, and all twelve were declared
    [derive(equations=no,eliminator=no)] — for a good reason at the time
    (def_guess_impl.v's header: the derived lemmas "would drag dependent
    elimination axioms in, and nothing here needs them").  Completeness DOES
    need them: without the unfolding equations a runner cannot be reasoned
    about computationally AT ALL — [cbn] does not reduce it, [destruct] on
    the domain proof loses the index, and [simp] does not exist.

    ⚠️ TURNING THE DERIVATION ON NAIVELY FAILS, and the obligation says
    exactly why: it asks for

        eq_rect … H … (DepElim.pack_sigma_eq_nondep eq_refl e) = <ctor> …

    which is UIP on the domain predicate's PACKED INDEX.  ⚙ A one-index
    domain predicate has no such obligation, which is why the difficulty is
    invisible on a small probe and appears only on the real runners.

    ⭐⭐ AND UIP IS A THEOREM HERE, NOT AN AXIOM.  The index sorts are
    first-order inductives over atoms, so their Leibniz equality is decidable
    and UIP is HEDBERG's theorem ([eqdec_uip]).  Every runner derived against
    this file stays "Closed under the global context" — measured, not
    assumed.

    ⛔ DO NOT go looking for [UIP supply].  A supply is [atoms], metalib's
    set type carries a sortedness proof, and its Leibniz equality is not
    readily decidable — but it is also NOT NEEDED: the supply component of a
    packed index is matched by [eq_refl], never inverted.  The same goes for
    the [Δ1]/[Δ2] set indexes of the consistency order.

    ⚙ [eliminator=no] STAYS OFF.  Only the unfolding equations are wanted;
    the derived eliminator has the larger axiom surface, and the completeness
    induction runs on the ORDER (§8c.3), not on the runner. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.def_ott.

(** Atoms decide their own equality — metalib's [==]. *)
#[export] Instance eqdec_atom : EqDec atom := { eq_dec := fun x y => x == y }.

(** The skeleton sort.  ⚙ [NoConfusion] comes along because [Equations]'
    dependent-elimination machinery wants it for the same inductive. *)
Derive NoConfusion EqDec for pskl.

#[export] Instance uip_pskl : UIP pskl := eqdec_uip _.
