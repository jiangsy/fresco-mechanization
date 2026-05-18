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

(** ===== Monotypes over ctyp ===== *)

Inductive mono_ctyp : ctyp -> Prop :=
| mono_ctyp__unit  : mono_ctyp ctyp_unit
| mono_ctyp__var   : forall X, mono_ctyp (ctyp_var_f X)
| mono_ctyp__arrow : forall K1 K2,
    mono_ctyp K1 -> mono_ctyp K2 -> mono_ctyp (ctyp_arrow K1 K2).

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
