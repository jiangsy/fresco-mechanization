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
Inductive mono_typ : ptyp -> Prop :=
| mono_typ__unit  : mono_typ ptyp_unit
| mono_typ__var   : forall X, mono_typ (ptyp_var_f X)
| mono_typ__arrow : forall A B,
    mono_typ A -> mono_typ B -> mono_typ (ptyp_arrow A B).

(* ===================================================================== *)
(*  Six category predicates                                               *)
(* ===================================================================== *)

(** Tagged types: only forall@ε; no other quantifiers, no holes. *)
Inductive is_ttyp : utyp -> Prop :=
| is_ttyp__unit  : is_ttyp utyp_unit
| is_ttyp__var   : forall X, is_ttyp (utyp_var_f X)
| is_ttyp__arrow : forall C1 C2,
    is_ttyp C1 -> is_ttyp C2 -> is_ttyp (utyp_arrow C1 C2)
| is_ttyp__all_etag   : forall L ε C,
    (forall X, X `notin` L ->
       is_ttyp (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    is_ttyp (utyp_all_etag ε C).

(** Tagged skletons: is_ttyp + holes + topholes. *)
Inductive is_tskl : uskl -> Prop :=
| is_tskl__unit    : is_tskl uskl_unit
| is_tskl__var     : forall X, is_tskl (uskl_var_f X)
| is_tskl__arrow   : forall R1 R2,
    is_tskl R1 -> is_tskl R2 -> is_tskl (uskl_arrow R1 R2)
| is_tskl__all_etag     : forall L ε R,
    (forall X, X `notin` L ->
       is_tskl (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    is_tskl (uskl_all_etag ε R)
| is_tskl__hole    : is_tskl uskl_hole
| is_tskl__tophole : forall A, is_tskl A -> is_tskl (uskl_tophole A).

(* ===================================================================== *)
(*  Colour-discipline predicates                                          *)
(* ===================================================================== *)

(** Synthesised: every colour-tagged forall is colour_syn. Implies is_typ. *)
Inductive is_styp : btyp -> Prop :=
| is_styp__unit  : is_styp btyp_unit
| is_styp__var   : forall X, is_styp (btyp_var_f X)
| is_styp__arrow : forall B1 B2,
    is_styp B1 -> is_styp B2 -> is_styp (btyp_arrow B1 B2)
| is_styp__all   : forall L B,
    (forall X, X `notin` L ->
       is_styp (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    is_styp (btyp_all_syn B).

(** Inherited: every colour-tagged forall is colour_inh. *)
Inductive is_ityp : btyp -> Prop :=
| is_ityp__unit  : is_ityp btyp_unit
| is_ityp__var   : forall X, is_ityp (btyp_var_f X)
| is_ityp__arrow : forall B1 B2,
    is_ityp B1 -> is_ityp B2 -> is_ityp (btyp_arrow B1 B2)
| is_ityp__all   : forall L A,
    (forall X, X `notin` L ->
       is_ityp (open_btyp_wrt_btyp A (btyp_var_f X))) ->
    is_ityp (btyp_all_inh A).

(** Same patterns extended to skletons. *)
Inductive is_sskl : bskl -> Prop :=
| is_sskl__unit    : is_sskl bskl_unit
| is_sskl__var     : forall X, is_sskl (bskl_var_f X)
| is_sskl__arrow   : forall A B,
    is_sskl A -> is_sskl B -> is_sskl (bskl_arrow A B)
| is_sskl__all     : forall L A,
    (forall X, X `notin` L ->
       is_sskl (open_bskl_wrt_bskl A (bskl_var_f X))) ->
    is_sskl (bskl_all_syn A)
| is_sskl__hole    : is_sskl bskl_hole
| is_sskl__tophole : forall A, is_sskl A -> is_sskl (bskl_tophole A).

Inductive is_iskl : bskl -> Prop :=
| is_iskl__unit    : is_iskl bskl_unit
| is_iskl__var     : forall X, is_iskl (bskl_var_f X)
| is_iskl__arrow   : forall A B,
    is_iskl A -> is_iskl B -> is_iskl (bskl_arrow A B)
| is_iskl__all     : forall L A,
    (forall X, X `notin` L ->
       is_iskl (open_bskl_wrt_bskl A (bskl_var_f X))) ->
    is_iskl (bskl_all_inh A)
| is_iskl__hole    : is_iskl bskl_hole
| is_iskl__tophole : forall A, is_iskl A -> is_iskl (bskl_tophole A).

(* ===================================================================== *)
(*  Guarded and value predicates                                          *)
(* ===================================================================== *)

(** Guarded: no top-level forall (any flavour) or hole/tophole. *)
Inductive guarded_ptyp : ptyp -> Prop :=
| guarded_ptyp__unit  : guarded_ptyp ptyp_unit
| guarded_ptyp__var   : forall X, guarded_ptyp (ptyp_var_f X)
| guarded_ptyp__arrow : forall A1 A2, lc_ptyp A1 -> lc_ptyp A2 -> guarded_ptyp (ptyp_arrow A1 A2).

Inductive guarded_pskl : pskl -> Prop :=
| guarded_pskl__unit  : guarded_pskl pskl_unit
| guarded_pskl__var   : forall X, guarded_pskl (pskl_var_f X)
| guarded_pskl__arrow : forall P1 P2, lc_pskl P1 -> lc_pskl P2 -> guarded_pskl (pskl_arrow P1 P2).

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
Inductive mode_typ_compat : mode -> ptyp -> Prop :=
| mode_typ_compat__ti : forall A, lc_ptyp A -> mode_typ_compat mode_ti A
| mode_typ_compat__tc : forall A, lc_ptyp A -> mode_typ_compat mode_tc A
| mode_typ_compat__fn : forall m A1 A2,
    mode_typ_compat m A2 ->
    mode_typ_compat (mode_fn m) (ptyp_arrow A1 A2).

(** Paper's M |-_SK P. Both TI and TC require synthesised skletons. *)
Inductive mode_skl_compat : mode -> pskl -> Prop :=
| mode_skl_compat__ti : forall P, lc_pskl P -> mode_skl_compat mode_ti P
| mode_skl_compat__tc : forall P, lc_pskl P -> mode_skl_compat mode_tc P
| mode_skl_compat__fn : forall m P1 P2,
    mode_skl_compat m P2 ->
    mode_skl_compat (mode_fn m) (pskl_arrow P1 P2).
