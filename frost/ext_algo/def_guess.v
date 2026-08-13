(** ext_algo — [guess^TY] with the name supply threaded as STATE.

    The first judgement of the second encoding, chosen deliberately: it is the
    judgement that actually INVENTS names, so if the supply design is wrong it
    is wrong here, on forty lines.

    ⭐ WHAT CHANGES AGAINST [a_guess_mono] (frost/algo/def_rules.v:312-360),
    and why each change is the paper's reading rather than ours:

    - [Θ] IS GONE.  It appeared in [a_guess_mono] for one purpose only — to be
      the set the invented names avoid — and its own header says so: "The
      paper's guess is context-free; [Θ] here is the relational rendering of
      the implementation's global fresh counter."  Replacing it with a supply
      therefore RESTORES the paper's context-free [guess^TY] instead of
      departing from it.

    - THE ARROW ROW THREADS.  [a_guess_mono__arrow] runs both halves at the
      SAME [Θ], so two independently invented blocks may collide and [uniq αs]
      is not derivable — which is why [AT-Abs] carries the premise
      [uniq (αs ++ Θ1)] (frost/algo/def_rules.v:1491, and
      docs/REPORT-postclosure-audit.md §1.3, which priced threading at 316
      occurrences and declined).  Here the second half runs at the FIRST
      half's output supply, and [uniq] becomes derivable
      ([e_guess_mono_uniq]).  ⭐ The audit's verdict is not overturned: it was
      about paying that price on the EXISTING encoding, whose 316 sites all
      keep the premise.  A second encoding pays nothing.

    - FRESHNESS MENTIONS ONLY THE INPUT SUPPLY.  [α ∉ S] and nothing else —
      no [ftvar_in_aenv], no [ftvar_in_pskl P] (the ∀ row needed the second
      conjunct only because [Θ] did not contain [P]'s variables; a supply
      does, by its invariant).

    ⚠️ THE ∀ WITNESS IS NEVER RETURNED TO THE SUPPLY.  [__forall] runs its
    premise at [add β S0] and the output supply keeps [β], although [β] is
    closed away in the conclusion and is dead thereafter.  This is deliberate
    and it is the faithful reading: [type.ml] never decrements its counter.
    It also costs nothing — a supply is an over-approximation of what must be
    avoided, and monotonicity is what makes [e_guess_mono_supply_grows] hold
    unconditionally, which is what the arrow row's second premise consumes. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.def_supply.

Set Implicit Arguments.

(** [guess^TY(P) = (Ξ; A)], threaded: [e_guess_mono S0 P S1 Ξ A] reads
    "starting from supply [S0], guessing [P] invents the block [Ξ], yields the
    monotype-filled type [A], and leaves the supply at [S1]".

    Application form, not a notation: [a_guess_mono] uses application form for
    the same reason (the paper writes [guess^TY(P) = (Ξ; A)], a meta-function,
    not a judgement with a turnstile), and a second spelling of a
    non-judgement would only make the two encodings harder to compare. *)
Inductive e_guess_mono : supply -> pskl -> supply -> aenv -> ptyp -> Prop :=
| e_guess_mono__hole : forall S α,                            (* □ ↦ fresh α̂ *)
    α `notin` S ->
    e_guess_mono S pskl_hole (add α S)
      ((α ~ abind_flex_mono) ++ nil) (ptyp_var_f α)
| e_guess_mono__tophole : forall S0 S1 P Ξ A,                 (* ⫯.P ↦ guess P *)
    e_guess_mono S0 P S1 Ξ A ->
    e_guess_mono S0 (pskl_tophole P) S1 Ξ A
| e_guess_mono__var : forall S α,                             (* α / α̂ ↦ (·; α) *)
    e_guess_mono S (pskl_var_f α) S nil (ptyp_var_f α)
| e_guess_mono__unit : forall S,
    e_guess_mono S pskl_unit S nil ptyp_unit
| e_guess_mono__arrow : forall S0 S1 S2 P Q Ξ1 Ξ2 A B,
    (* THREADED — the one row that differs structurally from [a_guess_mono] *)
    e_guess_mono S0 P S1 Ξ1 A ->
    e_guess_mono S1 Q S2 Ξ2 B ->
    e_guess_mono S0 (pskl_arrow P Q) S2 (Ξ1 ++ Ξ2) (ptyp_arrow A B)
| e_guess_mono__forall : forall S0 S1 P Ξ A β,
    (* the witness is DRAWN FROM THE SUPPLY and enters it, exactly as
       [a_guess_mono__forall]'s witness entered [Θ]; the explicit CLOSE is
       unchanged (DESIGN.md §4.3) *)
    β `notin` S0 ->
    e_guess_mono (add β S0) (open_pskl_wrt_pskl P (pskl_var_f β)) S1 Ξ A ->
    e_guess_mono S0 (pskl_all_syn P) S1 Ξ (ptyp_all (close_ptyp_wrt_ptyp β A)).

(** [guess^N(Q) = (Ξ'; Q')] (full-algo-spec.tex:1000) — the sort wrapper:
    [guess^SK] is the identity, [guess^TY] is [e_guess_mono] read back into
    [pskl].  ⚙ As with [e_guess_mono], the avoid-input [Θ] that
    [frost/algo]'s [a_guess] threads is replaced by the supply. *)
Inductive e_guess : supply -> a_sub_mode -> pskl -> supply -> aenv -> pskl
                    -> Prop :=
| e_guess__sk : forall S Q,
    e_guess S a_sub_mode_sk Q S nil Q
| e_guess__ty : forall S0 S1 Q Ξ A,
    e_guess_mono S0 Q S1 Ξ A ->
    e_guess S0 a_sub_mode_ty Q S1 Ξ (ptyp_to_pskl A).
