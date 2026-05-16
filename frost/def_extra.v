(** Frost — cross-system meta-functions and predicates. *)

Require Import Metalib.Metatheory.

Require Export src.frost.def_ott.
Require Export src.frost.prop_ln.

(* list_disjoint is forward-declared inside def_ott.v's embed block (from
   the language.ott embed). It is re-exported via `Require Export
   src.frost.def_ott.` above. No redefinition needed here. *)

(* ===================================================================== *)
(*  decr_mode and mono_typ                                                *)
(* ===================================================================== *)

(** The paper's M- operation. Decreases function modes by one. *)
Definition decr_mode (m : mode) : mode :=
  match m with
  | mode_ti => mode_ti
  | mode_tc => mode_tc
  | mode_fn m' => m'
  end.

(** Monotypes: no forall at any depth, no holes. *)
Inductive mono_typ : typ -> Prop :=
| mono_typ__unit  : mono_typ typ_unit
| mono_typ__var   : forall X, mono_typ (typ_var_f X)
| mono_typ__arrow : forall A B,
    mono_typ A -> mono_typ B -> mono_typ (typ_arrow A B).

(* ===================================================================== *)
(*  Six category predicates                                               *)
(* ===================================================================== *)

(** Plain types: only forall^c (colour-tagged); no ε-tags, no plain-forall, no holes. *)
Inductive is_typ : typ -> Prop :=
| is_typ__unit  : is_typ typ_unit
| is_typ__var   : forall X, is_typ (typ_var_f X)
| is_typ__arrow : forall A B,
    is_typ A -> is_typ B -> is_typ (typ_arrow A B)
| is_typ__all   : forall L c A,
    (forall X, X `notin` L ->
       is_typ (open_typ_wrt_typ A (typ_var_f X))) ->
    is_typ (typ_all_col c A).

(** Tagged types: only forall@ε; no other quantifiers, no holes. *)
Inductive is_ttyp : typ -> Prop :=
| is_ttyp__unit  : is_ttyp typ_unit
| is_ttyp__var   : forall X, is_ttyp (typ_var_f X)
| is_ttyp__arrow : forall A B,
    is_ttyp A -> is_ttyp B -> is_ttyp (typ_arrow A B)
| is_ttyp__all   : forall L ε A,
    (forall X, X `notin` L ->
       is_ttyp (open_typ_wrt_typ A (typ_var_f X))) ->
    is_ttyp (typ_all_etag ε A).

(** Unresolved types: forall@ε; no other quantifiers, no holes.
    Post-refactor: the un-decorated "plain-forall" no longer exists in
    [typ]. Paper's [\syn{\forall α.}T] (un-tagged synthesised forall) is
    now encoded as [typ_all_col colour_syn _]; that's a separate
    "colour-painted" shape, not [is_utyp]. *)
Inductive is_utyp : typ -> Prop :=
| is_utyp__unit  : is_utyp typ_unit
| is_utyp__var   : forall X, is_utyp (typ_var_f X)
| is_utyp__arrow : forall A B,
    is_utyp A -> is_utyp B -> is_utyp (typ_arrow A B)
| is_utyp__tall  : forall L ε A,
    (forall X, X `notin` L ->
       is_utyp (open_typ_wrt_typ A (typ_var_f X))) ->
    is_utyp (typ_all_etag ε A).

(** Skeletons: is_typ + holes + topholes. *)
Inductive is_skel : typ -> Prop :=
| is_skel__unit    : is_skel typ_unit
| is_skel__var     : forall X, is_skel (typ_var_f X)
| is_skel__arrow   : forall A B,
    is_skel A -> is_skel B -> is_skel (typ_arrow A B)
| is_skel__all     : forall L c A,
    (forall X, X `notin` L ->
       is_skel (open_typ_wrt_typ A (typ_var_f X))) ->
    is_skel (typ_all_col c A)
| is_skel__hole    : is_skel typ_hole
| is_skel__tophole : forall A, is_skel A -> is_skel (typ_tophole A).

(** Tagged skeletons: is_ttyp + holes + topholes. *)
Inductive is_tskel : typ -> Prop :=
| is_tskel__unit    : is_tskel typ_unit
| is_tskel__var     : forall X, is_tskel (typ_var_f X)
| is_tskel__arrow   : forall A B,
    is_tskel A -> is_tskel B -> is_tskel (typ_arrow A B)
| is_tskel__all     : forall L ε A,
    (forall X, X `notin` L ->
       is_tskel (open_typ_wrt_typ A (typ_var_f X))) ->
    is_tskel (typ_all_etag ε A)
| is_tskel__hole    : is_tskel typ_hole
| is_tskel__tophole : forall A, is_tskel A -> is_tskel (typ_tophole A).

(** Unresolved skeletons: is_utyp + holes + topholes. *)
Inductive is_uskel : typ -> Prop :=
| is_uskel__unit    : is_uskel typ_unit
| is_uskel__var     : forall X, is_uskel (typ_var_f X)
| is_uskel__arrow   : forall A B,
    is_uskel A -> is_uskel B -> is_uskel (typ_arrow A B)
| is_uskel__tall    : forall L ε A,
    (forall X, X `notin` L ->
       is_uskel (open_typ_wrt_typ A (typ_var_f X))) ->
    is_uskel (typ_all_etag ε A)
| is_uskel__hole    : is_uskel typ_hole
| is_uskel__tophole : forall A, is_uskel A -> is_uskel (typ_tophole A).

(* ===================================================================== *)
(*  Colour-discipline predicates                                          *)
(* ===================================================================== *)

(** Synthesised: every colour-tagged forall is colour_syn. Implies is_typ. *)
Inductive is_syn_typ : typ -> Prop :=
| is_syn_typ__unit  : is_syn_typ typ_unit
| is_syn_typ__var   : forall X, is_syn_typ (typ_var_f X)
| is_syn_typ__arrow : forall A B,
    is_syn_typ A -> is_syn_typ B -> is_syn_typ (typ_arrow A B)
| is_syn_typ__all   : forall L A,
    (forall X, X `notin` L ->
       is_syn_typ (open_typ_wrt_typ A (typ_var_f X))) ->
    is_syn_typ (typ_all_col colour_syn A).

(** Inherited: every colour-tagged forall is colour_inh. *)
Inductive is_inh_typ : typ -> Prop :=
| is_inh_typ__unit  : is_inh_typ typ_unit
| is_inh_typ__var   : forall X, is_inh_typ (typ_var_f X)
| is_inh_typ__arrow : forall A B,
    is_inh_typ A -> is_inh_typ B -> is_inh_typ (typ_arrow A B)
| is_inh_typ__all   : forall L A,
    (forall X, X `notin` L ->
       is_inh_typ (open_typ_wrt_typ A (typ_var_f X))) ->
    is_inh_typ (typ_all_col colour_inh A).

(** Same patterns extended to skeletons. *)
Inductive is_syn_skel : typ -> Prop :=
| is_syn_skel__unit    : is_syn_skel typ_unit
| is_syn_skel__var     : forall X, is_syn_skel (typ_var_f X)
| is_syn_skel__arrow   : forall A B,
    is_syn_skel A -> is_syn_skel B -> is_syn_skel (typ_arrow A B)
| is_syn_skel__all     : forall L A,
    (forall X, X `notin` L ->
       is_syn_skel (open_typ_wrt_typ A (typ_var_f X))) ->
    is_syn_skel (typ_all_col colour_syn A)
| is_syn_skel__hole    : is_syn_skel typ_hole
| is_syn_skel__tophole : forall A, is_syn_skel A -> is_syn_skel (typ_tophole A).

Inductive is_inh_skel : typ -> Prop :=
| is_inh_skel__unit    : is_inh_skel typ_unit
| is_inh_skel__var     : forall X, is_inh_skel (typ_var_f X)
| is_inh_skel__arrow   : forall A B,
    is_inh_skel A -> is_inh_skel B -> is_inh_skel (typ_arrow A B)
| is_inh_skel__all     : forall L A,
    (forall X, X `notin` L ->
       is_inh_skel (open_typ_wrt_typ A (typ_var_f X))) ->
    is_inh_skel (typ_all_col colour_inh A)
| is_inh_skel__hole    : is_inh_skel typ_hole
| is_inh_skel__tophole : forall A, is_inh_skel A -> is_inh_skel (typ_tophole A).

(* ===================================================================== *)
(*  Guarded and value predicates                                          *)
(* ===================================================================== *)

(** Guarded: no top-level forall (any flavour) or hole/tophole. *)
Inductive guarded_typ : typ -> Prop :=
| guarded_typ__unit  : guarded_typ typ_unit
| guarded_typ__var   : forall X, guarded_typ (typ_var_f X)
| guarded_typ__arrow : forall A B, guarded_typ (typ_arrow A B).

Inductive guarded_skel : typ -> Prop :=
| guarded_skel__unit  : guarded_skel typ_unit
| guarded_skel__var   : forall X, guarded_skel (typ_var_f X)
| guarded_skel__arrow : forall A B, guarded_skel (typ_arrow A B).

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

(** Paper's M |-_TY A. *)
Inductive mode_typ_compat : mode -> typ -> Prop :=
| mode_typ_compat__ti : forall A, is_syn_typ A -> mode_typ_compat mode_ti A
| mode_typ_compat__tc : forall A, is_inh_typ A -> mode_typ_compat mode_tc A
| mode_typ_compat__fn : forall m A B,
    mode_typ_compat m B ->
    mode_typ_compat (mode_fn m) (typ_arrow A B).

(** Paper's M |-_SK P. Both TI and TC require synthesised skeletons. *)
Inductive mode_skel_compat : mode -> typ -> Prop :=
| mode_skel_compat__ti : forall P, is_syn_skel P -> mode_skel_compat mode_ti P
| mode_skel_compat__tc : forall P, is_syn_skel P -> mode_skel_compat mode_tc P
| mode_skel_compat__fn : forall m P Q,
    mode_skel_compat m Q ->
    mode_skel_compat (mode_fn m) (typ_arrow P Q).
