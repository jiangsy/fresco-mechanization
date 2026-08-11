(** Frost — cross-system meta-functions and shape predicates.

    One leaf module over the generated syntax: the tag collector, the
    monotype / tagged / colour-discipline / guardedness / ghost-freeness
    shape predicates, and the mode-compatibility relations. *)

Require Import Metalib.Metatheory.

Require Export src.frost.def_ott.
Require Export src.frost.prop_ln.

(* list_disjoint is forward-declared inside def_ott.v's embed block (from
   the language.ott embed). It is re-exported via `Require Export
   src.frost.def_ott.` above. No redefinition needed here. *)

(* ===================================================================== *)
(*  decr_mode                                                            *)
(* ===================================================================== *)

(** The paper's M- operation. Decreases function modes by one. *)
Definition decr_mode (m : mode) : mode :=
  match m with
  | mode_ti => mode_ti
  | mode_tc => mode_tc
  | mode_fn m' => m'
  end.

(* ===================================================================== *)
(*  Syntactic quantifier tags                                            *)
(* ===================================================================== *)

(** The ε tags occurring in a [utyp] / [uskl] (their [∀^ε α.φ] binders).  Tags
    are plain atoms (not a locally-nameless sort), so lngen generates no
    collector; these are the hand-written ones.

    ⭐ THE PAPER'S ForallL SIDE CONDITION [fresh Ψ'] MEANS GLOBAL FRESHNESS —
    in particular freshness from the tags already in the SUBJECT — and every
    subtyping judgment in the tree renders it that way, as a second premise
    [Ψ' ∩ ftag(subject) [=] ∅] beside [Ψ' ∩ Ψ [=] ∅] ([d_sub], [d_pat_sub],
    [ad_pat_sub] and the [_g]/[_gv] mirrors).  The two are NOT
    interchangeable: freshness from the tag context alone does not survive the
    Arrow rule (the context splits, the subject does not), and
    precision-substitution is FALSE over derivations that only have it
    (docs/DESIGN-completeness-subtyping.md §5.2).  What makes the strong
    reading legitimate is that a derivation's instantiation tags can always be
    MOVED — frost/prop_etag.v, decl/prop_etag_swap.v. *)

Fixpoint ftag_in_utyp (C : utyp) : atoms :=
  match C with
  | utyp_unit => {}
  | utyp_var_b _ => {}
  | utyp_var_f _ => {}
  | utyp_arrow C1 C2 => ftag_in_utyp C1 `union` ftag_in_utyp C2
  | utyp_all_syn C0 => ftag_in_utyp C0
  | utyp_all_etag ε C0 => add ε (ftag_in_utyp C0)
  end.

Fixpoint ftag_in_uskl (R : uskl) : atoms :=
  match R with
  | uskl_unit => {}
  | uskl_var_b _ => {}
  | uskl_var_f _ => {}
  | uskl_arrow R1 R2 => ftag_in_uskl R1 `union` ftag_in_uskl R2
  | uskl_all_syn R0 => ftag_in_uskl R0
  | uskl_all_etag ε R0 => add ε (ftag_in_uskl R0)
  | uskl_hole => {}
  | uskl_tophole R0 => ftag_in_uskl R0
  | uskl_holeg => {}
  | uskl_topholeg R0 => ftag_in_uskl R0
  end.

(* ===================================================================== *)
(*  Monotypes                                                             *)
(* ===================================================================== *)

Inductive mono_ptyp : ptyp -> Prop :=
| mono_ptyp__unit  : mono_ptyp ptyp_unit
| mono_ptyp__var   : forall α, mono_ptyp (ptyp_var_f α)
| mono_ptyp__arrow : forall A1 A2,
    mono_ptyp A1 -> mono_ptyp A2 -> mono_ptyp (ptyp_arrow A1 A2).

(* ===================================================================== *)
(*  Tagged-category predicates                                            *)
(* ===================================================================== *)

(** Tagged types: only forall@ε; no other quantifiers, no holes. *)
Inductive is_ttyp : utyp -> Prop :=
| is_ttyp__unit  : is_ttyp utyp_unit
| is_ttyp__var   : forall α, is_ttyp (utyp_var_f α)
| is_ttyp__arrow : forall C1 C2,
    is_ttyp C1 -> is_ttyp C2 -> is_ttyp (utyp_arrow C1 C2)
| is_ttyp__all_etag   : forall L ε C,
    (forall α, α `notin` L ->
       is_ttyp (open_utyp_wrt_utyp C (utyp_var_f α))) ->
    is_ttyp (utyp_all_etag ε C).

(** Tagged skletons: is_ttyp + holes + topholes. *)
Inductive is_tskl : uskl -> Prop :=
| is_tskl__unit    : is_tskl uskl_unit
| is_tskl__var     : forall α, is_tskl (uskl_var_f α)
| is_tskl__arrow   : forall R1 R2,
    is_tskl R1 -> is_tskl R2 -> is_tskl (uskl_arrow R1 R2)
(* Paper decorated skeleton ψ (declarative.tex:1796): EVERY quantifier carries
   a tag ε — the grammar has only [∀^ε α.ψ].  The tag-elided [all_syn] form is
   NOT a decorated-skeleton forall (admitting it would let ForallL instantiate
   with quantifiers no inherited information determines, breaking the paper's
   no-guessing invariant). *)
| is_tskl__all_etag     : forall L ε R,
    (forall α, α `notin` L ->
       is_tskl (open_uskl_wrt_uskl R (uskl_var_f α))) ->
    is_tskl (uskl_all_etag ε R)
(* Paper decorated skeleton ψ (declarative.tex, grammar fig) carries the
   DOTTED GHOSTS [HoleG] / [TopHoleG], NOT plain [Hole] / [TopHole] (those
   live only in the unresolved skeleton R / the bid RHS).  So [is_tskl]
   admits the dotted ghost holes; the dotted universal ghost is UNTAGGED. *)
| is_tskl__holeg    : is_tskl uskl_holeg
| is_tskl__topholeg : forall R, is_tskl R -> is_tskl (uskl_topholeg R).

(* ===================================================================== *)
(*  Colour-discipline predicates                                          *)
(* ===================================================================== *)

(** Synthesised: every colour-tagged forall is colour_syn. Implies is_typ. *)
Inductive is_styp : btyp -> Prop :=
| is_styp__unit  : is_styp btyp_unit
| is_styp__var   : forall α, is_styp (btyp_var_f α)
| is_styp__arrow : forall B1 B2,
    is_styp B1 -> is_styp B2 -> is_styp (btyp_arrow B1 B2)
| is_styp__all   : forall L B,
    (forall α, α `notin` L ->
       is_styp (open_btyp_wrt_btyp B (btyp_var_f α))) ->
    is_styp (btyp_all_syn B).

(** Inherited: every colour-tagged forall is colour_inh. *)
Inductive is_ityp : btyp -> Prop :=
| is_ityp__unit  : is_ityp btyp_unit
| is_ityp__var   : forall α, is_ityp (btyp_var_f α)
| is_ityp__arrow : forall B1 B2,
    is_ityp B1 -> is_ityp B2 -> is_ityp (btyp_arrow B1 B2)
| is_ityp__all   : forall L A,
    (forall α, α `notin` L ->
       is_ityp (open_btyp_wrt_btyp A (btyp_var_f α))) ->
    is_ityp (btyp_all_inh A).

(** Same patterns extended to skletons. *)
Inductive is_sskl : bskl -> Prop :=
| is_sskl__unit    : is_sskl bskl_unit
| is_sskl__var     : forall α, is_sskl (bskl_var_f α)
| is_sskl__arrow   : forall A B,
    is_sskl A -> is_sskl B -> is_sskl (bskl_arrow A B)
| is_sskl__all     : forall L A,
    (forall α, α `notin` L ->
       is_sskl (open_bskl_wrt_bskl A (bskl_var_f α))) ->
    is_sskl (bskl_all_syn A)
| is_sskl__hole    : is_sskl bskl_hole
| is_sskl__tophole : forall A, is_sskl A -> is_sskl (bskl_tophole A).

Inductive is_iskl : bskl -> Prop :=
| is_iskl__unit    : is_iskl bskl_unit
| is_iskl__var     : forall α, is_iskl (bskl_var_f α)
| is_iskl__arrow   : forall A B,
    is_iskl A -> is_iskl B -> is_iskl (bskl_arrow A B)
| is_iskl__all     : forall L A,
    (forall α, α `notin` L ->
       is_iskl (open_bskl_wrt_bskl A (bskl_var_f α))) ->
    is_iskl (bskl_all_inh A)
| is_iskl__hole    : is_iskl bskl_hole
| is_iskl__tophole : forall A, is_iskl A -> is_iskl (bskl_tophole A).

(* ===================================================================== *)
(*  Guarded and value predicates                                          *)
(* ===================================================================== *)

(** Guarded: no top-level forall (any flavour) or hole/tophole.

    ⚙ There is deliberately NO [guarded_ptyp].  Guardedness is a premise of
    the SUBTYPING and CONSISTENCY rules, which range over the coloured /
    skeleton sorts, so the plain source sort never needs it — a [ptyp] reaches
    those rules only through a painting, and the painting's guardedness is what
    gets asserted ([ptyp_to_uskl_syn_guarded], algo/prop_sub_msubst_equiv.v).
    Do not add it back without a consumer. *)
Inductive guarded_pskl : pskl -> Prop :=
| guarded_pskl__unit  : guarded_pskl pskl_unit
| guarded_pskl__var   : forall α, guarded_pskl (pskl_var_f α)
| guarded_pskl__arrow : forall P1 P2, lc_pskl P1 -> lc_pskl P2 -> guarded_pskl (pskl_arrow P1 P2).

Inductive guarded_btyp : btyp -> Prop :=
| guarded_btyp__unit  : guarded_btyp btyp_unit
| guarded_btyp__var   : forall α, guarded_btyp (btyp_var_f α)
| guarded_btyp__arrow : forall B1 B2,
    lc_btyp B1 -> lc_btyp B2 -> guarded_btyp (btyp_arrow B1 B2).

Inductive guarded_utyp : utyp -> Prop :=
| guarded_utyp__unit  : guarded_utyp utyp_unit
| guarded_utyp__var   : forall α, guarded_utyp (utyp_var_f α)
| guarded_utyp__arrow : forall C1 C2,
    lc_utyp C1 -> lc_utyp C2 -> guarded_utyp (utyp_arrow C1 C2).

Inductive guarded_bskl : bskl -> Prop :=
| guarded_bskl__unit  : guarded_bskl bskl_unit
| guarded_bskl__var   : forall α, guarded_bskl (bskl_var_f α)
| guarded_bskl__arrow : forall Q1 Q2,
    lc_bskl Q1 -> lc_bskl Q2 -> guarded_bskl (bskl_arrow Q1 Q2).

Inductive guarded_uskl : uskl -> Prop :=
| guarded_uskl__unit  : guarded_uskl uskl_unit
| guarded_uskl__var   : forall α, guarded_uskl (uskl_var_f α)
| guarded_uskl__arrow : forall R1 R2,
    lc_uskl R1 -> lc_uskl R2 -> guarded_uskl (uskl_arrow R1 R2).

(** [nonghost_pskl P]: P's HEAD is not a ghost — it is neither [◇] nor
    [∀◇P0].  Weaker than [guarded_pskl], which also rules out a top-level ∀.

    Its one use is SE-FlexR (algo/def_extra.v), and it is there to render the
    reference implementation's DISPATCH ORDER: [solve_eq] is an OCaml match,
    and both ghost-subject rows — [SolE-GhostL] ([Ghost, q -> q],
    type.ml:412) and [SolE-GhostGuarded] ([UGhost p, q when is_guarded q],
    :457, and a flexible target IS guarded, [is_guarded]:21-23) — come
    STRICTLY BEFORE [SolE-FlexR] (:466).  So FlexR fires only on a
    [TCon]/[TArr]/[TForA]/[TMod] subject there, never on a ghost.  A
    relational encoding has no match order, so the exclusion must be a
    premise. *)
Inductive nonghost_pskl : pskl -> Prop :=
| nonghost_pskl__unit  : nonghost_pskl pskl_unit
| nonghost_pskl__var   : forall α, nonghost_pskl (pskl_var_f α)
| nonghost_pskl__arrow : forall P1 P2, nonghost_pskl (pskl_arrow P1 P2)
| nonghost_pskl__all   : forall P, nonghost_pskl (pskl_all_syn P).

(** Value restriction: terms that may be generalised in checking mode. *)
Inductive is_value : exp -> Prop :=
| is_value__unit     : is_value exp_unit
| is_value__var      : forall x, is_value (exp_var_f x)
| is_value__abs      : forall e, is_value (exp_abs e)
| is_value__abs_anno : forall A e, is_value (exp_abs_anno A e)
| is_value__anno     : forall e A, is_value e -> is_value (exp_anno e A).

(* ===================================================================== *)
(*  Mode-compatibility predicates                                         *)
(* ===================================================================== *)

(** Paper's [skmod{TY}{bid A}{M}] (declarative.tex:415-434): the COLOURED
    mode/type well-formedness — synthesised at [TI], inherited at [TC], and a
    function type whose result is [M]-compatible at [FN M] (the argument colour
    is unconstrained / bidirectional).  Implicitly required of every typing
    judgement; embedded as a premise on each rule's conclusion mode+type. *)
(** ⚠️ ARGUMENT ORDER: this pair is SUBJECT-first, while their algorithmic
    counterparts [a_ty_mode_compat] / [a_sk_mode_compat] (algo/def_extra.v) are
    MODE-first, as are [fn_arrow_shape*] and [pskl_ty_core] / [ptyp_ty_core].
    Mode-first is the majority (6 of the 8 arrow-spine relations).

    ⛔ Do NOT "fix" this by renaming one pair to match the other WITHOUT also
    flipping the argument order — same-shaped names taking their arguments in
    opposite orders is worse than two visibly different names.  The two halves
    must land together, and the flip is not a sed: ~60 of the applications pass
    a compound first argument ([mod_comp_ty (btyp_arrow B1 B2) (mode_fn m)]),
    so it needs balanced-paren rewriting plus 58 constructor references.
    Measured 2026-08-09; see docs/REPORT-remech-cleanup-audit.md §4. *)
Inductive mod_comp_ty : btyp -> mode -> Prop :=
| mod_comp_ty__ti : forall B, is_styp B -> mod_comp_ty B mode_ti
| mod_comp_ty__tc : forall B, is_ityp B -> mod_comp_ty B mode_tc
| mod_comp_ty__fn : forall m B1 B2,
    mod_comp_ty B2 m ->
    mod_comp_ty (btyp_arrow B1 B2) (mode_fn m).

(** Paper's [skmod{SK}{bid P}{M}] (declarative.tex:1535): the coloured
    mode/skeleton compatibility for skeleton inference.  Like [mod_comp_ty],
    but the only difference (declarative.tex:1553) is that CHECK mode also
    requires a SYNTHESISED skeleton [is_sskl] (ghosts [□]/[⫯] count as
    synthesised), rather than an inherited one.  The inferred skeleton [Q] of
    [{{ Γ ⊢ˢ[M] e ⦂ Q }}d] is always [mod_comp_sk Q M] (see [d_pat_mod_comp_sk]). *)
Inductive mod_comp_sk : bskl -> mode -> Prop :=
| mod_comp_sk__ti : forall Q, is_sskl Q -> mod_comp_sk Q mode_ti
| mod_comp_sk__tc : forall Q, is_sskl Q -> mod_comp_sk Q mode_tc
| mod_comp_sk__fn : forall m Q1 Q2,
    mod_comp_sk Q2 m ->
    mod_comp_sk (bskl_arrow Q1 Q2) (mode_fn m).

(* ===================================================================== *)
(*  The TYPE sub-universe of the skeleton sorts                           *)
(* ===================================================================== *)

(** The paper's algorithmic judgments range over ONE syntactic category of
    skeletons, but their metavariables are sorted: a rule that writes [A] / [B]
    is restricted to the positions where the paper's grammar only ever produces
    a TYPE, while a rule that writes [P] / [Q] admits a full skeleton.  The
    mechanization keeps the single [pskl] carrier (splitting the sort would
    duplicate every judgment) and recovers the distinction with this predicate:
    a [pskl] is a type exactly when it mentions no ghost — no [◇] and no [∀◇].

    Equivalently [pskl_ghost_free P ↔ exists A, P = ⌈A⌉] for locally-closed [P]
    ([ptyp_to_pskl_ghost_free] / [pskl_ghost_free_to_ptyp], prop_basic.v).
    Kept as a [Fixpoint] rather than an [Inductive] so that [simpl] discharges
    it on concrete skeletons and so that it is trivially decidable; note it
    holds of [pskl_var_b], i.e. it says nothing about local closure. *)

Fixpoint pskl_ghost_free (P : pskl) : Prop :=
  match P with
  | pskl_unit => True
  | pskl_var_b _ => True
  | pskl_var_f _ => True
  | pskl_arrow P1 P2 => pskl_ghost_free P1 /\ pskl_ghost_free P2
  | pskl_all_syn P0 => pskl_ghost_free P0
  | pskl_hole => False
  | pskl_tophole _ => False
  end.

Fixpoint bskl_ghost_free (Q : bskl) : Prop :=
  match Q with
  | bskl_unit => True
  | bskl_var_b _ => True
  | bskl_var_f _ => True
  | bskl_arrow Q1 Q2 => bskl_ghost_free Q1 /\ bskl_ghost_free Q2
  | bskl_all_syn Q0 => bskl_ghost_free Q0
  | bskl_all_inh Q0 => bskl_ghost_free Q0
  | bskl_hole => False
  | bskl_tophole _ => False
  end.

(* Constructor hints for the small structural shape / guardedness / mode
   predicates: they are dispatched trivially in metatheory proofs, so
   [eauto with frost] can discharge those cases directly.  A DEDICATED [frost]
   hint database (not [core]) keeps existing [auto] proofs unperturbed; the
   large relational judgments are deliberately NOT hinted (they would make
   [eauto] explode). *)
#[export] Hint Constructors mono_ptyp is_ttyp is_tskl is_styp is_ityp is_sskl
  is_iskl guarded_pskl guarded_btyp guarded_utyp guarded_bskl
  guarded_uskl mod_comp_ty mod_comp_sk : frost.
