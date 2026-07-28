(** Frost — paper-faithful scoped notations (cross-system).

    This file exports notations that depend ONLY on the cross-system
    definitions (def_ott / prop_ln / def_extra). Notations for declarative
    judgments live in `frost/decl/notations.v` to avoid a circular import
    (decl/def_extra.v → frost/notations.v).

    Conventions:
    - Greek letters in the paper map to the same letters here (Γ, Δ, Ψ, ε, φ, ψ).
    - Mode subscripts are written as `⊢[ M ]`; subtyping writes the tag context first as `Δ ⨟ Γ ⊢[ M ]`.
*)

Require Export Metalib.Metatheory.

Require Export src.frost.def_ott.
Require Export src.frost.prop_ln.
Require Export src.frost.def_extra.

(** ** Atom sets.

    `Metalib.Metatheory` abbreviates only PART of the atom-set interface:
    it declares `Notation add/empty/remove/singleton/union := AtomSetImpl.…`
    and re-exports `AtomSetFacts` (so `add_iff`, `mem_iff`, … resolve
    unqualified), but leaves `inter`, `diff`, `mem` and every `AtomSetImpl`
    lemma name behind the module path.  Metalib deliberately does not
    `Module Export AtomSetImpl` — that would drop `In`, `eq`, `filter`, `fold`,
    … on top of `List`'s — so we finish the job selectively here, in exactly
    metalib's own style: abbreviations for what we use, and nothing else.
    After this file no statement or proof needs to write `AtomSetImpl.` or
    `AtomSetFacts.`. *)

Notation inter := AtomSetImpl.inter.
Notation diff := AtomSetImpl.diff.
Notation mem := AtomSetImpl.mem.

Notation union_1 := AtomSetImpl.union_1.
Notation union_2 := AtomSetImpl.union_2.
Notation union_3 := AtomSetImpl.union_3.
Notation inter_1 := AtomSetImpl.inter_1.
Notation inter_2 := AtomSetImpl.inter_2.
Notation inter_3 := AtomSetImpl.inter_3.
Notation singleton_1 := AtomSetImpl.singleton_1.
Notation add_2 := AtomSetImpl.add_2.
Notation remove_1 := AtomSetImpl.remove_1.
Notation remove_3 := AtomSetImpl.remove_3.

(** The set operations the paper writes infix.  `∪` mirrors metalib's
    `` `union` `` (level 65, right); `∩` and `∖` bind tighter, as in maths.
    All three sit below `[=]` / `[<=]` (level 70), so `Δ ∩ ftvar_in_pskl P
    [=] empty` — the disjointness side condition that dominates the
    refinement / consistency / subtyping statements — parses and prints as
    written. *)

Notation "S1 ∪ S2" := (AtomSetImpl.union S1 S2)
  (at level 65, right associativity) : set_scope.

Notation "S1 ∩ S2" := (AtomSetImpl.inter S1 S2)
  (at level 63, right associativity) : set_scope.

Notation "S1 ∖ S2" := (AtomSetImpl.diff S1 S2)
  (at level 61, left associativity) : set_scope.

(** ** Lightweight aliases. *)

Notation "x ∉ L" := (x `notin` L) (at level 70, no associativity).

Notation "` X" := (ptyp_var_f X)
  (at level 0, X at level 0, no associativity) : type_scope.

Notation "⌈ e ⌉" := (exp_freeze e) (at level 0, e at level 0) : type_scope.

(** ** Substitution. *)

Notation "{ A' ᵗ/ₜ X } A" :=
  (subst_ptyp_in_ptyp A' X A)
    (at level 49, A' at level 50, X at level 0, right associativity) : type_scope.

Notation "{ e' ᵉ/ₑ x } e" :=
  (subst_exp_in_exp e' x e)
    (at level 49, e' at level 50, x at level 0, right associativity) : type_scope.

Notation "{ A ᵉ/ₜ X } e" :=
  (subst_ptyp_in_exp A X e)
    (at level 49, A at level 50, X at level 0, right associativity) : type_scope.
