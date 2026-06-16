(** Qualified notations for files that mention BOTH the declarative and
    the algorithmic systems (e.g. soundness / completeness), where the two
    judgment notations would otherwise clash — both use the [⊢[ … ]]
    prefix.

    The declarative judgment notations live in [decl_scope] (delimiter
    [d]) and the algorithmic ones in [algo_scope] (delimiter [a]).  Wrap a
    judgment in [d{{ … }}] / [a{{ … }}] to parse it in the corresponding
    scope, so only one system's notations are consulted and there is no
    ambiguity:

      a{{ Θ0 ⊢[ M ; P ] e ⦂ A ⊣ Θ1 }}   (* algorithmic typing *)
      d{{ ⌊ Θ1 ⌋ ⊢[ M ] e ⦂ B }}         (* declarative typing *)

    The brackets are parse-only; printed goals fall back to the
    application form (the two scopes cannot both be open for printing for
    the same reason they clash).  Non-[⊢[] notations ([⌊ ⌋], [≤[ ]], [⊴],
    [⊨], [⊳], …) live in [type_scope] and work inside or outside the
    brackets. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.

Declare Scope decl_scope.
Delimit Scope decl_scope with d.
Declare Scope algo_scope.
Delimit Scope algo_scope with a.

(* ----- Declarative judgments (decl_scope). ----- *)

Notation "Γ ⊢[ M ] e ⦂ A" := (d_typing M Γ e A)
  (at level 100, M at level 0, e at level 75, A at level 75, no associativity)
  : decl_scope.
Notation "Γ ⊢[ M ] e ⇨ P" := (d_pat M Γ e P)
  (at level 100, M at level 0, e at level 75, P at level 75, no associativity)
  : decl_scope.
Notation "Δ ⨟ Γ ⊢[ M ] C ⊑ B" := (d_sub M Δ Γ C B)
  (at level 75, Γ at level 75, M at level 0, C at level 74, B at level 74,
   no associativity) : decl_scope.
Notation "Δ ⨟ Γ ⊨ C ≈ B" := (d_consis Δ Γ C B)
  (at level 75, Γ at level 75, C at level 74, B at level 74, no associativity)
  : decl_scope.
Notation "Ψ ⨟ Γ ⊢ᵣ Q ⊳ P" := (d_refine_syn Ψ Γ Q P)
  (at level 75, Γ at level 75, Q at level 74, P at level 74, no associativity)
  : decl_scope.
Notation "Δ ⨟ Γ ⊨ₛ R ≈ Q" := (d_pat_consis Δ Γ R Q)
  (at level 75, Γ at level 75, R at level 74, Q at level 74, no associativity)
  : decl_scope.
Notation "Δ ⨟ Γ ⊢ₛ[ M ] R ⊑ Q" := (d_pat_sub M Δ Γ R Q)
  (at level 75, Γ at level 75, M at level 0, R at level 74, Q at level 74,
   no associativity) : decl_scope.

(* ----- Algorithmic judgments (algo_scope). ----- *)

Notation "Θ ⊢[ P0 ] P '~ᴬ' Q ⊣ Θ'" := (a_consis Θ P0 P Q Θ')
  (at level 100, P0 at level 0, P at level 74, Q at level 74, Θ' at level 74,
   no associativity) : algo_scope.
(* [a_sub] / [a_broom] use [|] separators (not [;]) so their 3-item
   bracket is distinguishable by 1-token lookahead from [a_typing] /
   [a_pat]'s 2-item [;] bracket — Coq cannot factor different [;]-counts. *)
Notation "Θ ⊢[ NM | m | P0 ] B1 ⊑ᴬ B2 ⊣ Θ'" := (a_sub NM m P0 Θ B1 B2 Θ')
  (at level 100, NM at level 0, m at level 0, P0 at level 0,
   B1 at level 74, B2 at level 74, Θ' at level 74, no associativity) : algo_scope.
Notation "Θ ⊢ᵇ[ NM | m | P0 ] B ◁ B' ⊣ Θ'" := (a_broom NM m P0 Θ B B' Θ')
  (at level 75, NM at level 0, m at level 0, P0 at level 0,
   B at level 74, B' at level 74, Θ' at level 74, no associativity) : algo_scope.
Notation "Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ'" := (a_typing m Θ P0 e B Θ')
  (at level 100, m at level 0, P0 at level 0,
   e at level 75, B at level 75, Θ' at level 75, no associativity) : algo_scope.
Notation "Θ ⊢[ m ; P0 ] e ⇨ Q ⊣ Θ'" := (a_pat m Θ P0 e Q Θ')
  (at level 100, m at level 0, P0 at level 0,
   e at level 75, Q at level 75, Θ' at level 75, no associativity) : algo_scope.
Notation "Θ ⊢ B ≐ B' ↣ B'' ⊣ Θ'" := (a_unify Θ B B' B'' Θ')
  (at level 75, B at level 74, B' at level 74, B'' at level 74,
   Θ' at level 74, no associativity) : algo_scope.

(* ----- Scope-selecting brackets (parse-only). ----- *)

Notation "'d{{' J '}}'" := (J)%d
  (at level 0, J at level 200, only parsing) : type_scope.
Notation "'a{{' J '}}'" := (J)%a
  (at level 0, J at level 200, only parsing) : type_scope.
