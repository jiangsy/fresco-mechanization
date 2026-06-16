(** Frost algorithmic-system notations for the split syntax. *)

Require Export src.frost.notations.
Require Export src.frost.algo.def_extra.

Notation "Θ ⊑ Θ'" := (aenv_extends Θ Θ')
  (at level 75, no associativity) : type_scope.

Notation "Θ ⊢ A 'aptyp'" := (a_wf_ptyp Θ A)
  (at level 75, A at level 74, no associativity) : type_scope.

Notation "⊢ₐ Θ" := (a_wf_aenv Θ)
  (at level 75, no associativity) : type_scope.

(* The algorithmic JUDGMENT notations ([a_typing]/[a_pat]/[a_sub]/
   [a_consis]/[a_broom]/[a_unify], all [⊢[ … ]]-shaped) live in the [algo]
   custom entry in [algo/qnotations.v], entered via [a{{ … }}].  Custom
   entries give them a separate grammar — they neither clash with the
   declarative [⊢[ … ]] notations nor with Coq's term grammar — and unlike
   a [type_scope] notation they also print.  Do NOT re-add them to
   [type_scope] here: that reintroduces the clash. *)

Notation "Θ ⊑ᵢ Θ'" := (aenv_extends Θ Θ')
  (at level 75, no associativity, only parsing) : type_scope.
