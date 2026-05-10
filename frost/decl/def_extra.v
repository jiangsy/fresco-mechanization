(** Frost — declarative-system rule definitions. *)

Require Import List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.

(** ** Plain types under a context. *)
Inductive d_wf_typ : list (atom * dbind) -> typ -> Prop :=
| d_wf_typ__unit : forall dE,
    d_wf_typ dE typ_unit
| d_wf_typ__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_typ dE (typ_var_f X)
| d_wf_typ__arrow : forall dE A B,
    d_wf_typ dE A ->
    d_wf_typ dE B ->
    d_wf_typ dE (typ_arrow A B)
| d_wf_typ__all : forall L dE c A,
    (forall X, X `notin` L ->
       d_wf_typ ((X ~ dbind_tvar) ++ dE) (open_typ_wrt_typ A (typ_var_f X))) ->
    d_wf_typ dE (typ_all_col c A).

(** ** Well-formed skeletons. Ψ tracks type variables bound previously in
    this skeleton; cleared at □ and at *.P. We forbid TOPHOLE.HOLE and
    nested TOPHOLE / quantifiers (paper line 1190+). *)
Inductive d_wf_skel :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_skel__unit : forall dP dE,
    d_wf_skel dP dE typ_unit
| d_wf_skel__var : forall dP dE X,
    List.In X dP \/ binds X dbind_tvar dE ->
    d_wf_skel dP dE (typ_var_f X)
| d_wf_skel__arrow : forall dP dE P Q,
    d_wf_skel dP dE P ->
    d_wf_skel dP dE Q ->
    d_wf_skel dP dE (typ_arrow P Q)
| d_wf_skel__all : forall L dP dE c P,
    (forall X, X `notin` L ->
       d_wf_skel (X :: dP) dE (open_typ_wrt_typ P (typ_var_f X))) ->
    d_wf_skel dP dE (typ_all_col c P)
| d_wf_skel__hole : forall dP dE,
    d_wf_skel dP dE typ_hole
| d_wf_skel__tophole : forall dP dE P,
    guarded_skel P ->
    d_wf_skel nil dE P ->
    d_wf_skel dP dE (typ_tophole P).

(** ** Well-formedness of tagged types. Each ε must appear exactly once
    (linearity by disjoint append). *)
Inductive d_wf_ttyp :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_ttyp__unit : forall dE,
    d_wf_ttyp nil dE typ_unit
| d_wf_ttyp__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_ttyp nil dE (typ_var_f X)
| d_wf_ttyp__arrow : forall dD1 dD2 dE A B,
    d_wf_ttyp dD1 dE A ->
    d_wf_ttyp dD2 dE B ->
    list_disjoint dD1 dD2 ->
    d_wf_ttyp (dD1 ++ dD2) dE (typ_arrow A B)
| d_wf_ttyp__all : forall L dD dE ee A,
    (forall X, X `notin` L ->
       d_wf_ttyp dD ((X ~ dbind_tvar) ++ dE) (open_typ_wrt_typ A (typ_var_f X))) ->
    ~ List.In ee dD ->
    d_wf_ttyp (ee :: dD) dE (typ_all_eps ee A).

(** ** Well-formedness of unresolved types. The "potential tag δ" (empty or ε)
    is encoded by two ∀ constructors; Δ tracks only the ε-tagged ones. *)
Inductive d_wf_utyp :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_utyp__unit : forall dE,
    d_wf_utyp nil dE typ_unit
| d_wf_utyp__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_utyp nil dE (typ_var_f X)
| d_wf_utyp__arrow : forall dD1 dD2 dE A B,
    d_wf_utyp dD1 dE A ->
    d_wf_utyp dD2 dE B ->
    list_disjoint dD1 dD2 ->
    d_wf_utyp (dD1 ++ dD2) dE (typ_arrow A B)
| d_wf_utyp__tall : forall L dD dE ee A,
    (forall X, X `notin` L ->
       d_wf_utyp dD ((X ~ dbind_tvar) ++ dE) (open_typ_wrt_typ A (typ_var_f X))) ->
    ~ List.In ee dD ->
    d_wf_utyp (ee :: dD) dE (typ_all_eps ee A)
| d_wf_utyp__pall : forall L dD dE A,
    (forall X, X `notin` L ->
       d_wf_utyp dD ((X ~ dbind_tvar) ++ dE) (open_typ_wrt_typ A (typ_var_f X))) ->
    d_wf_utyp dD dE (typ_all_plain A).

(** ** Tagged skeletons: tagged types + holes/topholes. *)
Inductive d_wf_tskel :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_tskel__unit : forall dE,
    d_wf_tskel nil dE typ_unit
| d_wf_tskel__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_tskel nil dE (typ_var_f X)
| d_wf_tskel__arrow : forall dD1 dD2 dE psi1 psi2,
    d_wf_tskel dD1 dE psi1 ->
    d_wf_tskel dD2 dE psi2 ->
    list_disjoint dD1 dD2 ->
    d_wf_tskel (dD1 ++ dD2) dE (typ_arrow psi1 psi2)
| d_wf_tskel__all : forall L dD dE ee psi,
    (forall X, X `notin` L ->
       d_wf_tskel dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ psi (typ_var_f X))) ->
    ~ List.In ee dD ->
    d_wf_tskel (ee :: dD) dE (typ_all_eps ee psi)
| d_wf_tskel__hole : forall dE,
    d_wf_tskel nil dE typ_hole
| d_wf_tskel__tophole : forall dD dE psi,
    d_wf_tskel dD dE psi ->
    d_wf_tskel dD dE (typ_tophole psi).

(** ** Unresolved skeletons: unresolved types + holes/topholes. *)
Inductive d_wf_uskel :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_uskel__unit : forall dE,
    d_wf_uskel nil dE typ_unit
| d_wf_uskel__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_uskel nil dE (typ_var_f X)
| d_wf_uskel__arrow : forall dD1 dD2 dE SS1 SS2,
    d_wf_uskel dD1 dE SS1 ->
    d_wf_uskel dD2 dE SS2 ->
    list_disjoint dD1 dD2 ->
    d_wf_uskel (dD1 ++ dD2) dE (typ_arrow SS1 SS2)
| d_wf_uskel__tall : forall L dD dE ee SS,
    (forall X, X `notin` L ->
       d_wf_uskel dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ SS (typ_var_f X))) ->
    ~ List.In ee dD ->
    d_wf_uskel (ee :: dD) dE (typ_all_eps ee SS)
| d_wf_uskel__pall : forall L dD dE SS,
    (forall X, X `notin` L ->
       d_wf_uskel dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ SS (typ_var_f X))) ->
    d_wf_uskel dD dE (typ_all_plain SS)
| d_wf_uskel__hole : forall dE,
    d_wf_uskel nil dE typ_hole
| d_wf_uskel__tophole : forall dD dE SS,
    d_wf_uskel dD dE SS ->
    d_wf_uskel dD dE (typ_tophole SS).
