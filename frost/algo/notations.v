(** Frost algorithmic-system notations for the split syntax. *)

Require Export src.frost.notations.
Require Export src.frost.algo.def_extra.

Notation "Θ ⊑ Θ'" := (aenv_extends Θ Θ')
  (at level 75, no associativity) : type_scope.

Notation "Θ ⊢ A 'aptyp'" := (a_wf_ptyp Θ A)
  (at level 75, A at level 74, no associativity) : type_scope.

Notation "⊢ₐ Θ" := (a_wf_aenv Θ)
  (at level 75, no associativity) : type_scope.

Notation "Θ ⊢[ P0 ] P '~ᴬ' Q ⊣ Θ'" := (a_consis Θ P0 P Q Θ')
  (at level 75, P0 at level 0, P at level 74, Q at level 74, Θ' at level 74,
   no associativity) : type_scope.

Notation "Θ ⊢[ NM ; m ; P0 ] B1 ⊑ᴬ B2 ⊣ Θ'" := (a_sub NM m P0 Θ B1 B2 Θ')
  (at level 75, NM at level 0, m at level 0, P0 at level 0,
   B1 at level 74, B2 at level 74, Θ' at level 74,
   no associativity) : type_scope.

Notation "Θ ⊢ᵇ[ NM ; m ; P0 ] B ◁ B' ⊣ Θ'" := (a_broom NM m P0 Θ B B' Θ')
  (at level 75, NM at level 0, m at level 0, P0 at level 0,
   B at level 74, B' at level 74, Θ' at level 74,
   no associativity) : type_scope.

Notation "Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ'" := (a_typing m Θ P0 e B Θ')
  (at level 100, m at level 0, P0 at level 0,
   e at level 75, B at level 75, Θ' at level 75,
   no associativity) : type_scope.

Notation "Θ ⊢[ m ; P0 ] e ⇨ Q ⊣ Θ'" := (a_pat m Θ P0 e Q Θ')
  (at level 100, m at level 0, P0 at level 0,
   e at level 75, Q at level 75, Θ' at level 75,
   no associativity) : type_scope.

Notation "Θ ⊢ B ≐ B' ↣ B'' ⊣ Θ'" := (a_unify Θ B B' B'' Θ')
  (at level 75, B at level 74, B' at level 74, B'' at level 74,
   Θ' at level 74, no associativity) : type_scope.

Notation "Θ ⊑ᵢ Θ'" := (aenv_extends Θ Θ')
  (at level 75, no associativity, only parsing) : type_scope.
