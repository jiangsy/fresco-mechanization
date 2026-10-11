(** Lifting the algorithmic judgements to the supply-threaded encoding.

    Import this module for the complete lift through skeleton inference;
    typing is in [prop_lift_typing]. For individual judgements, import the
    corresponding [prop_lift_*] module below. Each proof lives with its
    judgement, and mutual inductions remain intact.

    Fresh binders prevent a direct structural induction on the original
    derivation: the supply-threaded run may need different names. The
    proofs instead use a syntactic size or the executable judgement's
    well-founded order, and relate outputs by a growing list of atom pairs.
    A functional renaming is insufficient once a collection or solving
    rule leaks a binder into its output. [prop_lift_look] proves collection
    transport; [prop_lift_context] supplies the context and expression
    relations used by the subsequent judgement-specific lifts. *)

Require Export src.fresco.ext_algo.lifting.prop_lift_solve.
Require Export src.fresco.ext_algo.lifting.prop_lift_consis.
Require Export src.fresco.ext_algo.lifting.prop_lift_sub.
Require Export src.fresco.ext_algo.lifting.prop_lift_split.
Require Export src.fresco.ext_algo.lifting.prop_lift_pat.
