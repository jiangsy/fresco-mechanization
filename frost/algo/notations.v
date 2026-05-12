(** Frost — algorithmic-system paper-faithful notations.

    Imports the algo/def_extra.v judgements and adds notations for them.
    Phase 3 metatheory files should `Require Import src.frost.algo.notations.`
    instead of `src.frost.notations.` directly. *)

Require Export src.frost.notations.
Require Export src.frost.algo.def_extra.

(** ** Information-increase relation. *)

Notation "Θ ⊑ Θ'" := (aenv_extends Θ Θ')
  (at level 75, no associativity) : type_scope.

(** ** Well-formedness. *)

Notation "Θ ⊢ A 'atype'" := (a_wf_typ Θ A)
  (at level 75, A at level 74, no associativity) : type_scope.

Notation "⊢ₐ Θ" := (a_wf_aenv Θ)
  (at level 75, no associativity) : type_scope.

(** ** Algorithmic consistency. *)

Notation "Θ ⊢ T '~ᴬ' A ⊣ Θ'" := (a_consis Θ T A Θ')
  (at level 75, T at level 74, A at level 74, Θ' at level 74,
   no associativity) : type_scope.

(** ** Algorithmic subtyping (outer / inner / flex-poly). *)

Notation "Θ ⊢[ NM ; m ; P0 ] P ⊑ᴬ Q ⊣ Θ'" := (a_sub NM m P0 Θ P Q Θ')
  (at level 75, NM at level 0, m at level 0, P0 at level 0,
   P at level 74, Q at level 74, Θ' at level 74,
   no associativity) : type_scope.

Notation "Θ ⊢ᵇ[ NM ; m ; P0 ] S ◁ S' ⊣ Θ'" := (a_broom NM m P0 Θ S S' Θ')
  (at level 75, NM at level 0, m at level 0, P0 at level 0,
   S at level 74, S' at level 74, Θ' at level 74,
   no associativity) : type_scope.

(** ** Algorithmic typing and skeleton inference. *)

Notation "Θ ⊢[ m ; P0 ] e ⇒ A ⊣ Θ'" := (a_typing m Θ P0 e A Θ')
  (at level 75, m at level 0, P0 at level 0,
   e at level 74, A at level 74, Θ' at level 74,
   no associativity) : type_scope.

Notation "Θ ⊢[ m ; P0 ] e ⇨ Q ⊣ Θ'" := (a_pat m Θ P0 e Q Θ')
  (at level 75, m at level 0, P0 at level 0,
   e at level 74, Q at level 74, Θ' at level 74,
   no associativity) : type_scope.

(** ** Unification. *)

Notation "Θ ⊢ S ≐ S' ↣ S'' ⊣ Θ'" := (a_unify Θ S S' S'' Θ')
  (at level 75, S at level 74, S' at level 74, S'' at level 74,
   Θ' at level 74, no associativity) : type_scope.

(** ** Information-increase identity-metasubstitution alias. *)

Notation "Θ ⊑ᵢ Θ'" := (aenv_extends Θ Θ')
  (at level 75, no associativity, only parsing) : type_scope.
