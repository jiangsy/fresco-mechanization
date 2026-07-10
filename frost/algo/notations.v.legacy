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
   [a_consis], paper's [⊢[ … ]] shape) live in [algo/def_extra.v], bound
   recursively with their Inductives via [where]-clauses so the RULES read
   with notation.  Their turnstile carries an [ₐ] subscript ([⊢ₐ[ … ]]) so
   they do not clash with the declarative [⊢[ … ]] in mixed
   soundness/completeness files — type_scope, no custom entry needed.
   (Superseded [algo/qnotations.v]'s [a{{ … }}] custom entry, now removed.) *)

Notation "Θ ⊑ᵢ Θ'" := (aenv_extends Θ Θ')
  (at level 75, no associativity, only parsing) : type_scope.
