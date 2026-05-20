(** Shape predicates over Frost's current type hierarchy. *)

Require Import Metalib.Metatheory.

Require Import src.frost.def_extra.

(** Monotypes. *)
Inductive mono_ptyp : ptyp -> Prop :=
| mono_ptyp__unit  : mono_ptyp ptyp_unit
| mono_ptyp__var   : forall X, mono_ptyp (ptyp_var_f X)
| mono_ptyp__arrow : forall A1 A2,
    mono_ptyp A1 -> mono_ptyp A2 -> mono_ptyp (ptyp_arrow A1 A2).

Inductive mono_btyp : btyp -> Prop :=
| mono_btyp__unit  : mono_btyp btyp_unit
| mono_btyp__var   : forall X, mono_btyp (btyp_var_f X)
| mono_btyp__arrow : forall B1 B2,
    mono_btyp B1 -> mono_btyp B2 -> mono_btyp (btyp_arrow B1 B2).

Inductive mono_utyp : utyp -> Prop :=
| mono_utyp__unit  : mono_utyp utyp_unit
| mono_utyp__var   : forall X, mono_utyp (utyp_var_f X)
| mono_utyp__arrow : forall C1 C2,
    mono_utyp C1 -> mono_utyp C2 -> mono_utyp (utyp_arrow C1 C2).

(** Bidirectional colour discipline. *)
Inductive is_syn : btyp -> Prop :=
| is_syn__unit  : is_syn btyp_unit
| is_syn__var   : forall X, is_syn (btyp_var_f X)
| is_syn__arrow : forall B1 B2,
    is_syn B1 -> is_syn B2 -> is_syn (btyp_arrow B1 B2)
| is_syn__all   : forall L B,
    (forall X, X `notin` L ->
       is_syn (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    is_syn (btyp_all_syn B).

Inductive is_inh : btyp -> Prop :=
| is_inh__unit  : is_inh btyp_unit
| is_inh__var   : forall X, is_inh (btyp_var_f X)
| is_inh__arrow : forall B1 B2,
    is_inh B1 -> is_inh B2 -> is_inh (btyp_arrow B1 B2)
| is_inh__all   : forall L B,
    (forall X, X `notin` L ->
       is_inh (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    is_inh (btyp_all_inh B).

(** Tagged-only unresolved types. *)
Inductive is_ttyp_utyp : utyp -> Prop :=
| is_ttyp_utyp__unit  : is_ttyp_utyp utyp_unit
| is_ttyp_utyp__var   : forall X, is_ttyp_utyp (utyp_var_f X)
| is_ttyp_utyp__arrow : forall C1 C2,
    is_ttyp_utyp C1 -> is_ttyp_utyp C2 -> is_ttyp_utyp (utyp_arrow C1 C2)
| is_ttyp_utyp__all   : forall L ε C,
    (forall X, X `notin` L ->
       is_ttyp_utyp (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    is_ttyp_utyp (utyp_all_etag ε C).

(** Guarded shapes: no top-level forall/hole/tophole. *)
Inductive guarded_btyp : btyp -> Prop :=
| guarded_btyp__unit  : guarded_btyp btyp_unit
| guarded_btyp__var   : forall X, guarded_btyp (btyp_var_f X)
| guarded_btyp__arrow : forall B1 B2,
    lc_btyp B1 -> lc_btyp B2 -> guarded_btyp (btyp_arrow B1 B2).

Inductive guarded_utyp : utyp -> Prop :=
| guarded_utyp__unit  : guarded_utyp utyp_unit
| guarded_utyp__var   : forall X, guarded_utyp (utyp_var_f X)
| guarded_utyp__arrow : forall C1 C2,
    lc_utyp C1 -> lc_utyp C2 -> guarded_utyp (utyp_arrow C1 C2).

Inductive guarded_bskl : bskl -> Prop :=
| guarded_bskl__unit  : guarded_bskl bskl_unit
| guarded_bskl__var   : forall X, guarded_bskl (bskl_var_f X)
| guarded_bskl__arrow : forall Q1 Q2,
    lc_bskl Q1 -> lc_bskl Q2 -> guarded_bskl (bskl_arrow Q1 Q2).

Inductive guarded_uskl : uskl -> Prop :=
| guarded_uskl__unit  : guarded_uskl uskl_unit
| guarded_uskl__var   : forall X, guarded_uskl (uskl_var_f X)
| guarded_uskl__arrow : forall R1 R2,
    lc_uskl R1 -> lc_uskl R2 -> guarded_uskl (uskl_arrow R1 R2).

(** Synthesised-only skeletons. *)
Inductive is_syn_bskl : bskl -> Prop :=
| is_syn_bskl__unit    : is_syn_bskl bskl_unit
| is_syn_bskl__var     : forall X, is_syn_bskl (bskl_var_f X)
| is_syn_bskl__arrow   : forall Q1 Q2,
    is_syn_bskl Q1 -> is_syn_bskl Q2 -> is_syn_bskl (bskl_arrow Q1 Q2)
| is_syn_bskl__all     : forall L Q,
    (forall X, X `notin` L ->
       is_syn_bskl (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    is_syn_bskl (bskl_all_syn Q)
| is_syn_bskl__hole    : is_syn_bskl bskl_hole
| is_syn_bskl__tophole : forall Q,
    is_syn_bskl Q -> is_syn_bskl (bskl_tophole Q).

Inductive no_forall_bskl : bskl -> Prop :=
| no_forall_bskl__unit    : no_forall_bskl bskl_unit
| no_forall_bskl__var     : forall X, no_forall_bskl (bskl_var_f X)
| no_forall_bskl__arrow   : forall Q1 Q2,
    no_forall_bskl Q1 -> no_forall_bskl Q2 -> no_forall_bskl (bskl_arrow Q1 Q2)
| no_forall_bskl__hole    : no_forall_bskl bskl_hole
| no_forall_bskl__tophole : forall Q,
    no_forall_bskl Q -> no_forall_bskl (bskl_tophole Q).
