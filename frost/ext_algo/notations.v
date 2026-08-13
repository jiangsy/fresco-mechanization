(** ext_algo — the notation scope for the state-threaded encoding.

    ⭐ THE SYSTEM IS THE DELIMITER (CLAUDE.md, and the legend in
    frost/notations.v).  This encoding's delimiter is [}}e] and its scope is
    [frost_e_scope], joining [}}d] / [}}ad] / [}}a] / [}}da].

    ⭐ AND THE REST OF EACH JUDGEMENT IS BYTE-IDENTICAL TO ITS [}}a] TWIN.
    The supply movement is written as a PREFIX, [S0 ↝ S1 ⊨ …], so that

        {{ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}a
        {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e

    differ by exactly the prefix and the delimiter.  That is deliberate: the
    whole value of a second encoding is that a reader can lay the two rule
    sets side by side and see that only the freshness discipline moved, and a
    notation that rearranged the slots would destroy it.

    ⚠️ THE FIRST SLOT CARRIES NO LEVEL ANNOTATION.  Metalib's atom-set
    singleton is [{{ x }}] (Metatheory.v:41), so every [{{]-prefixed rule
    shares its prefix and camlp5 can factor them only when that slot sits at
    the same entry — metalib's is plain [constr].  Annotate it and the build
    fills with [notation-incompatible-prefix] warnings and one of the two
    rules silently stops working. *)

Require Import Metalib.Metatheory.

Declare Scope frost_e_scope.
Delimit Scope frost_e_scope with e.
(* [Open Scope] is NOT transitive through [Require Import], so every file that
   uses these notations opens the scope itself; a closed scope makes Coq
   report the notation as simply not existing. *)
Open Scope frost_e_scope.
