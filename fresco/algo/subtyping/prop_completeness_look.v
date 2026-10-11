(** P6: completeness of collection, solving and extraction.

    This is the shared import interface for the five completeness results
    and their two supporting modules, all in [algo/subtyping/]:

    - [prop_rigid_substitution]: the rigid-variable substitution relation.
    - [prop_solve_extension]: flexible-block extension and solve packages.
    - [prop_completeness_solve_eq_var]: P6-Cv, equality solving at a variable.
    - [prop_completeness_lookeq_solve]: P6-Cs, equality collection and solving.
    - [prop_completeness_solve_sub_var]: P6-Sv, subtyping solving at a variable.
    - [prop_completeness_looksub_solve]: P6-Ss, subtyping collection and solving.
    - [prop_completeness_extract]: P6-L, extraction from the collected result.

    Keep these proofs separate: they have distinct judgements and form a
    dependency chain. Import an individual module when only an earlier
    result is needed; importing this interface also loads the later proofs.
    Check for dependency cycles and name collisions when changing imports. *)

Require Export src.fresco.algo.subtyping.prop_rigid_substitution.
Require Export src.fresco.algo.subtyping.prop_solve_extension.
Require Export src.fresco.algo.subtyping.prop_completeness_solve_eq_var.
Require Export src.fresco.algo.subtyping.prop_completeness_lookeq_solve.
Require Export src.fresco.algo.subtyping.prop_completeness_solve_sub_var.
Require Export src.fresco.algo.subtyping.prop_completeness_looksub_solve.
Require Export src.fresco.algo.subtyping.prop_completeness_extract.
