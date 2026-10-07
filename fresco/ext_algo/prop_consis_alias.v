(** THE ALIAS LAYER — kit for lifting the consistency runner's completeness
    off its hole-free restriction along the PRE-NORMALISATION route
    (docs/HANDOFF-close-consis-unrestricted.md §5 (R1)).

    ⭐ THE SHAPE OF THE CAMPAIGN.  At the two divergent cells —
    (pattern [◇], subject [α̂]) and its mirror — the runner answers with its
    context UNCHANGED ([U-GhostR] / [U-Ghost]) while a derivation may
    instead run the assignment walk [Θ ⊲[nil] α ≔ ◇ ⊣ Θ1] ([U-FlexL] /
    [U-FlexR]).  cex/probe_pat_presents_hole_flex.v shows the cells are
    REACHED by skeleton inference, so completeness must RELATE the two
    outcomes rather than exclude them.  This file supplies the two ends of
    that relation:

    §1  the walk's output is EXACTLY an alias insertion — either an inner
        [U-GhostR] stops the walk with everything unchanged, or the chase
        ends at some undefined flexible [γ̂] and [Assign-SolveM] replaces
        its entry by [γ̂ ≔ ε̂, ε̂] with [ε̂ := guess^TY(◇)] fresh
        ([e_assign_hole_out]).  ⚙ The payload [◇] has NO free variables,
        so [Assign-Depend] never fires and the pending block never grows —
        which is why the insertion is POSITIONAL here even though walks in
        general migrate entries (cex/probe_assign_migrates.v).
        ⚠️ The walk may CHASE aliases: [a_flex_tvar] admits DEFINED
        targets, so [Assign-Assign] can fire at the target itself
        ([β = α]) and re-enter at the definition's image.  The insertion
        therefore lands at the END of the chase, not necessarily at [α] —
        the lemma existentially quantifies the solved variable.

    §2  [collapse1] — the alias-collapse: drop the alias entry
        [γ ≔ ε̂] and rename [ε̂] back to [γ] everywhere (keys and
        payloads).  [collapse1_insert] computes it on §1's insertion shape:
        collapsing recovers the input context, which is the runner's
        answer.  ⚙ [rename_aenv] is the DIRECTED rename, kept by
        prop_swap.v's own header "where a proof genuinely needs the
        one-way form": a collapse MERGES [ε̂] into [γ] — it is not
        injective on {γ, ε̂} — so no transposition can express it.

    §3  [e_assign_absorb] — a NIL-blocked walk at [Ξ ++ Θ] IS the
        [Ξ]-blocked walk at [Θ], when every entry of [Ξ] is an undefined
        flexible the payload mentions.  ⭐ The piece §8c.12c predicted
        ("an ABSORPTION lemma for insert-headed walks"); it is what makes
        the re-walk [Assign-Assign] triggers harmless, and it is a
        statement about ONE side, so it is independent of the ⛔ below.

    ⛔⛔ WHAT THIS FILE DOES **NOT** SUPPORT, and must not be used for:
    an EXACT transport of a derivation across [collapse1] — i.e. "the
    collapsed derivation's output is [collapse1] of the original's".
    That is REFUTED, machine-checked, by cex/probe_collapse_orientation.v:
    at the alias entry a walk must take [Assign-Assign], which converts it
    to a CONSIS, and when the payload is the alias variable itself that
    consis is a UNIFY whose [Flex-Flex-R] orients the new definition the
    OPPOSITE way from the collapsed walk's [SolveM] — [(α̂ ≔ γ̂, γ̂)]
    against [(γ̂ ≔ α̂, α̂)], the same equivalence class with a different
    REPRESENTATIVE.  ⚙ The handover records this as dead end 5 and derives
    constraint C6 (orientation-tolerance) from it, which is what rules out
    ANY relation that is a function of the context. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.consis.prop_consis_rename.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.prop_consis_inc.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  THE ◇-PAYLOAD WALK IS AN ALIAS INSERTION                          *)
(* ===================================================================== *)

(** The output shape shared by the walk and its consis re-entries: nothing
    moved, or one undefined flexible [γ̂] got solved to a fresh alias. *)
Definition alias_insert_out (S0 : supply) (Θ : aenv)
    (S1 : supply) (Θ1 : aenv) : Prop :=
  (S1 = S0 /\ Θ1 = Θ) \/
  (exists γ ε Θa Θb,
      ε `notin` S0 /\ S1 = add ε S0
      /\ Θ  = Θa ++ (γ ~ abind_flex_mono) ++ Θb
      /\ Θ1 = Θa ++ (γ ~ abind_flex_mono_def (ptyp_var_f ε))
              ++ (ε ~ abind_flex_mono) ++ Θb).

(* ⚙ The two var-instance subst reductions this file needs already exist,
   as [subst_pskl_var_eq] / [subst_pskl_var_neq]
   (algo/consis/prop_consis_rename.v §0) — imported above rather than
   restated, per CLAUDE.md's one-fact-one-name rule. *)

(* ===================================================================== *)
(*  §2  THE COLLAPSE                                                      *)
(* ===================================================================== *)

(** Remove every [α]-keyed entry (under [uniq] there is at most one). *)
Fixpoint aenv_remove (α : atom) (Θ : aenv) : aenv :=
  match Θ with
  | nil => nil
  | (x, b) :: Θ' =>
      if x == α then aenv_remove α Θ' else (x, b) :: aenv_remove α Θ'
  end.

(** Collapse the alias [γ ≔ ε̂]: drop [γ]'s entry, rename [ε̂] back to [γ]
    (keys and payloads — [ε̂]'s own entry becomes [γ]'s). *)
Definition collapse1 (γ ε : atom) (Θ : aenv) : aenv :=
  rename_aenv γ ε (aenv_remove γ Θ).

(* ===================================================================== *)
(*  §3  ABSORPTION — a re-walked block is the SAME block                  *)
(*                                                                        *)
(*  ⭐ THE LEMMA §8c.12c PREDICTED — an ABSORPTION lemma for              *)
(*  insert-headed walks — and the one the transport's hardest row needs.  *)
(*                                                                        *)
(*  At the alias entry a walk MUST take [Assign-Assign] (a defined head    *)
(*  has no skip row), which PREPENDS the pending block to the context and  *)
(*  re-enters CONSISTENCY there — so the collapsed side, which has no      *)
(*  such entry, is left holding a walk at [Ξ ++ Θ] with an EMPTY block     *)
(*  where it wants one at [Θ] with block [Ξ].  Those are not the same      *)
(*  judgement in general (a skipped entry is re-attached ABOVE the output, *)
(*  a blocked one is dumped BELOW the solved target).  They ARE the same   *)
(*  when every entry of [Ξ] is an undefined flexible the payload MENTIONS: *)
(*  then the re-walk can only [Assign-Depend] each one, rebuilding [Ξ] in  *)
(*  order.  ⚙ And that is exactly the block's own invariant — [Ξ] grows    *)
(*  ONLY by [Assign-Depend], whose premises are those two conditions.      *)
(* ===================================================================== *)

(** What [Assign-Depend] puts in the block, as a property of a slice. *)
Definition block_absorbable (Ξ0 : aenv) (α : atom) (P : pskl) : Prop :=
  List.Forall (fun e => snd e = abind_flex_mono /\ fst e <> α
                        /\ fst e `in` ftvar_in_pskl P) Ξ0.

