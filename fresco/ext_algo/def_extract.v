(** ext_algo — [extract], the collection → solving → guess pipeline, threaded.

    One rule, and the place where the three clusters of M1 / M3a / M3b meet.

    ⭐⭐ THIS IS THE THIRD PLACE THE TREE HAND-ROLLS A SUPPLY, and its comment
    says so outright (fresco/algo/def_rules.v:825-827):

      "the guess runs AFTER the collection AND the solving, so its avoid-input
       is the whole [Ξs ++ Ξ ++ Θ0] — this is what makes the three halves of
       the output block [Ξ ++ Ξs ++ Ξ'] disjoint"

    That is an argument, carried in a comment, that a threaded avoid-set makes
    a three-way [uniq] hold.  With a real supply it stops being an argument
    and becomes [e_extract_block]'s third conjunct — proved once, from the
    three clusters' own invariants, instead of re-established by arranging the
    contexts.  ⚙ Together with [a_solve_sub__arrow] (§ def_solve.v) and
    [a_guess_mono__arrow] (§ def_guess.v) that is three sites, two of which
    already thread and one of which does not; the supply is the uniform
    version of all three. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.def_solve.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e"
  (at level 0, S1 at level 0, P at level 74, NM at level 0, α at level 0,
   m at level 0, P' at level 74, Ξ at level 74, Q at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ0  ⊢  P  ⊳[  NM  ,  α  ,  m  ]  P'  ⤳  Ξ  ↪  Q  '}}e'").

Inductive e_extract : supply -> aenv -> a_sub_mode -> atom -> mode
                      -> pskl -> pskl -> supply -> aenv -> pskl -> Prop :=
| e_extract__solve : forall S0 S1 S2 S3 Θ0 NM α m P P' Ξ Ξs Ξ' C Q Q',
    (* Δ-thread, three times.  The CONTEXT threading of the original
       ([Ξ ++ Θ0], then [Ξs ++ Ξ ++ Θ0]) is kept verbatim — the solving layer
       reads flexibles out of it — and the supply is threaded alongside. *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ ++ Θ0) ⊩ C ⨾ pskl_ghost ⤳ Ξs ⨾ Q }}e ->
    e_guess S2 NM Q S3 Ξ' Q' ->
    {{ S0 ↝ S3 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ (Ξ ++ Ξs ++ Ξ') ↪ Q' }}e
where "{{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e" :=
  (e_extract S0 Θ0 NM α m P P' S1 Ξ Q) : fresco_e_scope.
