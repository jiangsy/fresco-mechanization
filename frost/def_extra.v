(** Frost — cross-system meta-functions and predicates. *)

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
(*  Six category predicates                                               *)
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

(** Guarded: no top-level forall (any flavour) or hole/tophole. *)
Inductive guarded_ptyp : ptyp -> Prop :=
| guarded_ptyp__unit  : guarded_ptyp ptyp_unit
| guarded_ptyp__var   : forall α, guarded_ptyp (ptyp_var_f α)
| guarded_ptyp__arrow : forall A1 A2, lc_ptyp A1 -> lc_ptyp A2 -> guarded_ptyp (ptyp_arrow A1 A2).

Inductive guarded_pskl : pskl -> Prop :=
| guarded_pskl__unit  : guarded_pskl pskl_unit
| guarded_pskl__var   : forall α, guarded_pskl (pskl_var_f α)
| guarded_pskl__arrow : forall P1 P2, lc_pskl P1 -> lc_pskl P2 -> guarded_pskl (pskl_arrow P1 P2).

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
    [Γ ⊢[M] e ⇨ Q] is always [mod_comp_sk Q M] (see [d_pat_mod_comp_sk]). *)
Inductive mod_comp_sk : bskl -> mode -> Prop :=
| mod_comp_sk__ti : forall Q, is_sskl Q -> mod_comp_sk Q mode_ti
| mod_comp_sk__tc : forall Q, is_sskl Q -> mod_comp_sk Q mode_tc
| mod_comp_sk__fn : forall m Q1 Q2,
    mod_comp_sk Q2 m ->
    mod_comp_sk (bskl_arrow Q1 Q2) (mode_fn m).

(* Constructor hints for the small structural shape / guardedness / mode
   predicates: they are dispatched trivially in metatheory proofs, so
   [eauto with frost] can discharge those cases directly.  A DEDICATED [frost]
   hint database (not [core]) keeps existing [auto] proofs unperturbed; the
   large relational judgments are deliberately NOT hinted (they would make
   [eauto] explode). *)
#[export] Hint Constructors is_ttyp is_tskl is_styp is_ityp is_sskl is_iskl
  guarded_ptyp guarded_pskl mod_comp_ty mod_comp_sk : frost.
