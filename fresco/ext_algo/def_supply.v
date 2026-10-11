(** ext_algo — a SECOND algorithmic encoding, whose freshness is supplied by
    a threaded STATE instead of asserted as a side condition.  This file is
    the state: the name supply.

    Spec and rationale: [docs/HANDOFF-extractable-algo-encoding.md].  In one
    line: [fresco/algo/def_rules.v] states its operational judgements
    exists-fresh, and eleven rows constrain their own OUTPUT ([β ∉ dom Θ1]),
    which a reader is entitled to be suspicious of.  Here freshness is
    "the supply hands you a name", which mentions only the INPUT state — and
    which is a FUNCTION, so the encoding can eventually be extracted.

    ⭐ THE ENCODING IS BUILT AS A RELATION FIRST, A FUNCTION SECOND, and the
    supply carries both halves.  The rules quantify over ANY name the supply
    admits ([α ∉ S]); the runner of TODO (2) will instantiate that choice at
    [supply_fresh S].  Building the relation on [supply_fresh] directly would
    be a mistake: it would make the bridge to [fresco/algo]'s encoding false in
    the [current -> new] direction for a trivial reason (the old rules pick
    other names), and it would bake a particular gensym into the
    specification of the algorithm rather than into its implementation.

    ⚠️ THE SUPPLY IS AN AVOID-SET, NOT A COUNTER, AND THAT IS FORCED.
    [type.ml]'s [counter] (:558-561) is the thing being modelled, and a [nat]
    counter would model it more literally — but it cannot be built here.
    Metalib seals atoms behind [Module Atom : ATOM] with an OPAQUE ascription,
    and the signature exports [nat_of : atom -> nat] and no injection back
    ([MetatheoryAtom.v:33-50]).  There is no way to write "the atom numbered
    n", so a counter cannot generate atoms at all.  The avoid-set is the
    counter's generalization — [{0,…,n-1}] is the special case — and it is
    what the whole tree's freshness kit already speaks ([atoms], [`notin`],
    [solve_notin_auto]), so it is also the cheap option.

    ⭐ SO THE RULES MUST TOUCH THE SUPPLY THROUGH [α ∉ S] AND [add α S] ONLY,
    and that is a rule, not a habit.  An avoid-SET has a real asymptotic cost:
    [supply_fresh] folds [max] over the set's elements, so it is O(|S|) per
    call and O(n²) for n names, against [type.ml]'s O(1) [incr counter].
    Confining the rules to those two operations is what keeps the
    representation swappable — or realizable as an [int] counter at
    extraction — without touching a rule or a bridge.  ⚙ The general lesson
    (that the REPRESENTATION, not the verified algorithm, dominates an
    extracted type inferencer's running time) is Type Inference Logics'
    benchmark, §5.1 — though the two costs it measures are its own, a
    linear-time free-monad bind and unary-[nat] de Bruijn shifting, not this
    one.  See docs/HANDOFF-extractable-algo-encoding.md §7.5.

    ⭐ THE STANDING BAR FOR TODO (2) (user, 2026-08-13): THE EXTRACTED
    PROGRAM MUST BE CLEAN AND CARRY NO PROOF CONCEPTS.  The output has to read
    as an ordinary OCaml program that can be diffed against [type.ml] — no
    [Acc_rect] / [Fix_sub] / [FixWf] wrappers from the well-founded
    recursion, no [sumbool] / [sig] scaffolding, no [Obj.magic], no residue
    of the termination argument.  Three consequences, recorded here because
    they constrain decisions taken well before any [Extraction] command:

    - The termination measure of (2) should be chosen so the recursion is one
      Coq can see through, and [Extraction Inline] must erase whatever
      wrapper survives.  A measure that forces a visible [Acc] argument into
      the extracted term fails the bar even though it type-checks.  This is
      now an input to the M1.5 measure spike, not just a downstream cleanup.
    - Decidability must NOT be obtained by extracting a [sumbool] proof.
      (Already decided — handoff §5 — but the bar is the reason.)
    - The one GENERATIVE primitive, [supply_fresh] below, is the single place
      an unavoidable piece of metalib scaffolding can leak, so it is the
      single place to realize away (see its note).

    ⚠️ [supply_fresh] DOES NOT REDUCE INSIDE COQ.  Every generative operation
    metalib offers ([Atom.fresh], [atom_fresh_for_list], [atom_fresh]) sits
    behind that same opaque ascription, so [compute]/[vm_compute] gets stuck
    on it.  This does not block extraction — [sig] erases to its carrier, so
    no proof object survives — but it does block running the algorithm inside
    Coq by reflection against [test/test_examples.v], and metalib's own
    generator is a unary-[nat] maximum over the element list, which is not
    code anyone wants to diff against [type.ml].  ⭐ THE FIX IS TO REALIZE
    THE PRIMITIVE, not to work around it: [supply_fresh] is the only
    generative operation in the encoding, so one [Extract Constant] (with
    [atom] realized as [int]) buys the clean gensym — which is also the most
    literal possible rendering of [type.ml:558-561]'s [incr counter].  That
    directive belongs with TODO (2)'s extraction file; recorded here so the
    obligation is attached to the definition it is about. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Set Implicit Arguments.

(* ===================================================================== *)
(*  The supply                                                            *)
(* ===================================================================== *)

(** A [Notation], not a [Definition]: the supply IS a set of atoms, and every
    set lemma, [fsetdec] and [solve_notin_auto] must apply to it without an
    [unfold].  (Same reason [def_ott.v]'s sort aliases are notations —
    a [Definition] alias does not unify where a notation does.) *)
Notation supply := atoms.

(** The supply only ever grows, and this is the one-step form every rule of
    the encoding uses.  (The per-judgement statement — a whole RUN grows the
    supply — is proved of each judgement in turn; see
    [e_guess_mono_supply_grows].) *)
Lemma supply_add_grows : forall (S : supply) α, S [<=] add α S.
Proof. intros; fsetdec. Qed.

(* ⚙ PIN THE SET ARGUMENT.  [x ∉ S] and [S [<=] S'] both unfold to a product
   whose LATER argument mentions the set ([In x S -> False],
   [forall a, In a S -> …]), so [Set Implicit Arguments] judges [S] inferable
   and makes it IMPLICIT — whereupon [supply_add_grows S α] is a type error at
   every use site, with a message about [In] that names neither. *)
Arguments supply_add_grows : clear implicits.

(* ===================================================================== *)
(*  The [fresh] operation — the function half                             *)
(* ===================================================================== *)

(** The deterministic choice the extracted runner will make.  Nothing in the
    RELATION layer uses it; it is here so that the supply is a complete
    interface, and so that the one obligation it owes ([supply_fresh_notin])
    is discharged next to it rather than in the middle of TODO (2). *)
Definition supply_fresh (S : supply) : atom := proj1_sig (atom_fresh S).

Lemma supply_fresh_notin : forall S, supply_fresh S `notin` S.
Proof.
  intros S. unfold supply_fresh. destruct (atom_fresh S) as [α Hα]. exact Hα.
Qed.

Arguments supply_fresh_notin : clear implicits.   (* see the pin note above *)

(** Instantiate supply-transport IHs in order, including threaded siblings.
    Removing each consumed IH makes the loop finite. Binder IHs whose input
    supply needs an [add] equality are left to the caller. *)
Ltac transport_supply_witnesses :=
  repeat match goal with
  | IH : forall S' : supply, S' [=] ?S -> exists _, _ /\ _,
    Heq : ?S' [=] ?S |- _ =>
      destruct (IH _ Heq) as [? [? ?]]; clear IH
  end.
