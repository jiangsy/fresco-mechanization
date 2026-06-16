(** Qualified notations for files that mention BOTH the declarative and
    the algorithmic systems (e.g. soundness / completeness), where the two
    judgment notations would otherwise clash — both use the [⊢[ … ]]
    prefix.

    Following McTT (Beluga-lang/McTT, [theories/Core/Syntactic/Syntax.v]),
    each system's judgment notations live in their own Coq *custom entry*
    — a separate grammar namespace — entered through a bracket:

      a{{ Θ0 ⊢[ M ; P ] e ⦂ A ⊣ Θ1 }}   (* algorithmic typing  (custom algo) *)
      d{{ ⌊ Θ1 ⌋ ⊢[ M ] e ⦂ B }}         (* declarative typing  (custom decl) *)

    Because the entries are distinct grammars, the [⊢[ … ]] notations of
    the two systems never compete (with each other or with Coq's term
    grammar), and — unlike scope delimiters — custom entries support
    *printing*: a goal mentioning [a_typing] prints back as [a{{ … }}].

    Sub-terms inside a judgment ([Θ], [⌊ Θ ⌋], [e], a painted type, …) are
    ordinary Coq [constr]s, so the type_scope notations ([⌊ ⌋], [≤[ ]], …)
    work unchanged inside the brackets. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.

Declare Custom Entry decl.
Declare Custom Entry algo.

(* Brackets entering each custom entry (parse + print). *)
Notation "'d{{' J '}}'" := J
  (at level 0, J custom decl at level 99, format "'d{{'  J  '}}'") : type_scope.
Notation "'a{{' J '}}'" := J
  (at level 0, J custom algo at level 99, format "'a{{'  J  '}}'") : type_scope.

(* Parenthesised grouping within each entry. *)
Notation "( J )" := J (in custom decl at level 0, J custom decl at level 99).
Notation "( J )" := J (in custom algo at level 0, J custom algo at level 99).

(* ===================================================================== *)
(*  Declarative judgments (custom entry [decl]).                          *)
(* ===================================================================== *)

Notation "Γ ⊢[ M ] e ⦂ A" := (d_typing M Γ e A)
  (in custom decl at level 80, Γ constr at level 0, M constr at level 0,
   e constr at level 0, A constr at level 0).
Notation "Γ ⊢[ M ] e ⇨ P" := (d_pat M Γ e P)
  (in custom decl at level 80, Γ constr at level 0, M constr at level 0,
   e constr at level 0, P constr at level 0).
Notation "Δ ⨟ Γ ⊢[ M ] C ⊑ B" := (d_sub M Δ Γ C B)
  (in custom decl at level 80, Δ constr at level 0, Γ constr at level 0,
   M constr at level 0, C constr at level 0, B constr at level 0).
Notation "Δ ⨟ Γ ⊨ C ≈ B" := (d_consis Δ Γ C B)
  (in custom decl at level 80, Δ constr at level 0, Γ constr at level 0,
   C constr at level 0, B constr at level 0).
Notation "Ψ ⨟ Γ ⊢ᵣ Q ⊳ P" := (d_refine_syn Ψ Γ Q P)
  (in custom decl at level 80, Ψ constr at level 0, Γ constr at level 0,
   Q constr at level 0, P constr at level 0).
Notation "Δ ⨟ Γ ⊨ₛ R ≈ Q" := (d_pat_consis Δ Γ R Q)
  (in custom decl at level 80, Δ constr at level 0, Γ constr at level 0,
   R constr at level 0, Q constr at level 0).
Notation "Δ ⨟ Γ ⊢ₛ[ M ] R ⊑ Q" := (d_pat_sub M Δ Γ R Q)
  (in custom decl at level 80, Δ constr at level 0, Γ constr at level 0,
   M constr at level 0, R constr at level 0, Q constr at level 0).

(* ===================================================================== *)
(*  Algorithmic judgments (custom entry [algo]).                          *)
(* ===================================================================== *)

Notation "Θ ⊢[ P0 ] P '~ᴬ' Q ⊣ Θ'" := (a_consis Θ P0 P Q Θ')
  (in custom algo at level 80, Θ constr at level 0, P0 constr at level 0,
   P constr at level 0, Q constr at level 0, Θ' constr at level 0).
Notation "Θ ⊢[ NM | m | P0 ] B1 ⊑ᴬ B2 ⊣ Θ'" := (a_sub NM m P0 Θ B1 B2 Θ')
  (in custom algo at level 80, Θ constr at level 0, NM constr at level 0,
   m constr at level 0, P0 constr at level 0, B1 constr at level 0,
   B2 constr at level 0, Θ' constr at level 0).
Notation "Θ ⊢ᵇ[ NM | m | P0 ] B ◁ B' ⊣ Θ'" := (a_broom NM m P0 Θ B B' Θ')
  (in custom algo at level 80, Θ constr at level 0, NM constr at level 0,
   m constr at level 0, P0 constr at level 0, B constr at level 0,
   B' constr at level 0, Θ' constr at level 0).
Notation "Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ'" := (a_typing m Θ P0 e B Θ')
  (in custom algo at level 80, Θ constr at level 0, m constr at level 0,
   P0 constr at level 0, e constr at level 0, B constr at level 0,
   Θ' constr at level 0).
Notation "Θ ⊢[ m ; P0 ] e ⇨ Q ⊣ Θ'" := (a_pat m Θ P0 e Q Θ')
  (in custom algo at level 80, Θ constr at level 0, m constr at level 0,
   P0 constr at level 0, e constr at level 0, Q constr at level 0,
   Θ' constr at level 0).
Notation "Θ ⊢ B ≐ B' ↣ B'' ⊣ Θ'" := (a_unify Θ B B' B'' Θ')
  (in custom algo at level 80, Θ constr at level 0, B constr at level 0,
   B' constr at level 0, B'' constr at level 0, Θ' constr at level 0).
