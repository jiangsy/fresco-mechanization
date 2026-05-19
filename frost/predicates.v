(** Shape predicates over the new type hierarchy.

    See [docs/superpowers/specs/2026-05-18-type-hierarchy-refactor-design.md].

    These replace the typ-based predicates ([is_typ], [is_syn_typ],
    [is_inh_typ], [is_utyp], [is_ttyp]) which carved sub-classes out
    of the unified [typ] AST. Now each base inductive ([ctyp], [bid],
    [utyp]) has its own shape predicates.

    - [mono_ctyp]    : ctyp -> Prop   (unit/var/arrow only)
    - [is_syn]       : bid  -> Prop   (no bid_all_inh, no bid_all_etag)
    - [is_inh]       : bid  -> Prop   (no bid_all_syn, no bid_all_etag)
    - [is_ttyp_utyp] : utyp -> Prop   (no utyp_all_syn — tagged-only) *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.

(** ===== Monotypes over ctyp =====
    Admits unit/var/arrow only — no ∀. ctyp's hole/tophole are also
    excluded (mono is a "real type" predicate). *)
Inductive mono_ctyp : ctyp -> Prop :=
| mono_ctyp__unit  : mono_ctyp ctyp_unit
| mono_ctyp__var   : forall X, mono_ctyp (ctyp_var_f X)
| mono_ctyp__arrow : forall K1 K2,
    mono_ctyp K1 -> mono_ctyp K2 -> mono_ctyp (ctyp_arrow K1 K2).

(** ===== Monotypes over ptyp ===== *)
Inductive mono_ptyp : ptyp -> Prop :=
| mono_ptyp__unit  : mono_ptyp ptyp_unit
| mono_ptyp__var   : forall X, mono_ptyp (ptyp_var_f X)
| mono_ptyp__arrow : forall N1 N2,
    mono_ptyp N1 -> mono_ptyp N2 -> mono_ptyp (ptyp_arrow N1 N2).

(** ===== Monotypes over bid ===== *)
Inductive mono_bid : bid -> Prop :=
| mono_bid__unit  : mono_bid bid_unit
| mono_bid__var   : forall X, mono_bid (bid_var_f X)
| mono_bid__arrow : forall D1 D2,
    mono_bid D1 -> mono_bid D2 -> mono_bid (bid_arrow D1 D2).

(** ===== Monotypes over utyp ===== *)
Inductive mono_utyp : utyp -> Prop :=
| mono_utyp__unit  : mono_utyp utyp_unit
| mono_utyp__var   : forall X, mono_utyp (utyp_var_f X)
| mono_utyp__arrow : forall F1 F2,
    mono_utyp F1 -> mono_utyp F2 -> mono_utyp (utyp_arrow F1 F2).

(** ===== Synthesised colour over bid =====
    Admits unit, var, arrow, bid_all_syn (recursively). Excludes
    bid_all_inh and bid_all_etag. *)
Inductive is_syn : bid -> Prop :=
| is_syn__unit  : is_syn bid_unit
| is_syn__var   : forall X, is_syn (bid_var_f X)
| is_syn__arrow : forall D1 D2,
    is_syn D1 -> is_syn D2 -> is_syn (bid_arrow D1 D2)
| is_syn__all   : forall L D,
    (forall X, X `notin` L ->
       is_syn (open_bid_wrt_bid D (bid_var_f X))) ->
    is_syn (bid_all_syn D).

(** ===== Inherited colour over bid =====
    Symmetric to is_syn — only bid_all_inh ∀ allowed. *)
Inductive is_inh : bid -> Prop :=
| is_inh__unit  : is_inh bid_unit
| is_inh__var   : forall X, is_inh (bid_var_f X)
| is_inh__arrow : forall D1 D2,
    is_inh D1 -> is_inh D2 -> is_inh (bid_arrow D1 D2)
| is_inh__all   : forall L D,
    (forall X, X `notin` L ->
       is_inh (open_bid_wrt_bid D (bid_var_f X))) ->
    is_inh (bid_all_inh D).

(** ===== Tagged-only over utyp =====
    Admits unit, var, arrow, utyp_all_etag (recursively). Excludes
    utyp_all_syn. Names parallel [is_ttyp] (the old typ-based
    predicate) but over the new utyp inductive. *)
Inductive is_ttyp_utyp : utyp -> Prop :=
| is_ttyp_utyp__unit  : is_ttyp_utyp utyp_unit
| is_ttyp_utyp__var   : forall X, is_ttyp_utyp (utyp_var_f X)
| is_ttyp_utyp__arrow : forall F1 F2,
    is_ttyp_utyp F1 -> is_ttyp_utyp F2 -> is_ttyp_utyp (utyp_arrow F1 F2)
| is_ttyp_utyp__all   : forall L ε F,
    (forall X, X `notin` L ->
       is_ttyp_utyp (open_utyp_wrt_utyp F (utyp_var_f X))) ->
    is_ttyp_utyp (utyp_all_etag ε F).

(** ===== Guarded over bid =====
    No top-level forall (any colour / tag) or atomic-but-special
    shape. Used by d_sub_bid__check (paper's "syn{T} guarded").

    The [arrow] constructor carries [lc_bid] premises for its two
    sub-terms so that [guarded_bid] implies [lc_bid]; without these
    premises [guarded_bid_lc] is unprovable (the arrow sub-terms are
    structurally unconstrained otherwise). No call sites construct
    [guarded_bid] directly yet (the predicate is only consumed via
    inversion), so the extra premises do not propagate. *)
Inductive guarded_bid : bid -> Prop :=
| guarded_bid__unit  : guarded_bid bid_unit
| guarded_bid__var   : forall X, guarded_bid (bid_var_f X)
| guarded_bid__arrow : forall D1 D2,
    lc_bid D1 -> lc_bid D2 -> guarded_bid (bid_arrow D1 D2).

(** ===== Guarded over skel =====
    Same shape as [guarded_bid] — arrow carries [lc_skel] premises
    so [guarded_skel_new] implies [lc_skel]. *)
Inductive guarded_skel_new : skel -> Prop :=
| guarded_skel_new__unit  : guarded_skel_new skel_unit
| guarded_skel_new__var   : forall X, guarded_skel_new (skel_var_f X)
| guarded_skel_new__arrow : forall R1 R2,
    lc_skel R1 -> lc_skel R2 -> guarded_skel_new (skel_arrow R1 R2).

(** ===== Syn-only over skel =====
    Admits unit, var, arrow, all_syn, hole, tophole. Excludes
    all_inh and all_etag. Mirrors old [is_syn_skel] over typ. *)
Inductive is_syn_skel_new : skel -> Prop :=
| is_syn_skel_new__unit    : is_syn_skel_new skel_unit
| is_syn_skel_new__var     : forall X, is_syn_skel_new (skel_var_f X)
| is_syn_skel_new__arrow   : forall R1 R2,
    is_syn_skel_new R1 -> is_syn_skel_new R2 -> is_syn_skel_new (skel_arrow R1 R2)
| is_syn_skel_new__all     : forall L R,
    (forall X, X `notin` L ->
       is_syn_skel_new (open_skel_wrt_skel R (skel_var_f X))) ->
    is_syn_skel_new (skel_all_syn R)
| is_syn_skel_new__hole    : is_syn_skel_new skel_hole
| is_syn_skel_new__tophole : forall R,
    is_syn_skel_new R -> is_syn_skel_new (skel_tophole R).

(** ===== No-forall over skel =====
    No ∀ at any depth. Used by d_pat_consis_skel__ghost. *)
Inductive no_forall_skel : skel -> Prop :=
| no_forall_skel__unit    : no_forall_skel skel_unit
| no_forall_skel__var     : forall X, no_forall_skel (skel_var_f X)
| no_forall_skel__arrow   : forall R1 R2,
    no_forall_skel R1 -> no_forall_skel R2 -> no_forall_skel (skel_arrow R1 R2)
| no_forall_skel__hole    : no_forall_skel skel_hole
| no_forall_skel__tophole : forall R,
    no_forall_skel R -> no_forall_skel (skel_tophole R).
