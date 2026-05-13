(** Frost — declarative-system rule definitions. *)

Require Import List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.

(** ** Plain types under a context. *)
Inductive d_wf_typ : list (atom * dbind) -> typ -> Prop :=
| d_wf_typ__unit : forall Γ,
    d_wf_typ Γ typ_unit
| d_wf_typ__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_wf_typ Γ (typ_var_f X)
| d_wf_typ__arrow : forall Γ A B,
    d_wf_typ Γ A ->
    d_wf_typ Γ B ->
    d_wf_typ Γ (typ_arrow A B)
| d_wf_typ__all : forall L Γ c A,
    (forall X, X `notin` L ->
       d_wf_typ ((X ~ dbind_tvar) ++ Γ) (open_typ_wrt_typ A (typ_var_f X))) ->
    d_wf_typ Γ (typ_all_col c A).

(** ** Well-formed skeletons. Ψ tracks type variables bound previously in
    this skeleton; cleared at □ and at *.P. We forbid TOPHOLE.HOLE and
    nested TOPHOLE / quantifiers (paper line 1190+). *)
Inductive d_wf_skel :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_skel__unit : forall Ψ Γ,
    d_wf_skel Ψ Γ typ_unit
| d_wf_skel__var : forall Ψ Γ X,
    List.In X Ψ \/ binds X dbind_tvar Γ ->
    d_wf_skel Ψ Γ (typ_var_f X)
| d_wf_skel__arrow : forall Ψ Γ P Q,
    d_wf_skel Ψ Γ P ->
    d_wf_skel Ψ Γ Q ->
    d_wf_skel Ψ Γ (typ_arrow P Q)
| d_wf_skel__all_col : forall L Ψ Γ c P,
    (forall X, X `notin` L ->
       d_wf_skel (X :: Ψ) Γ (open_typ_wrt_typ P (typ_var_f X))) ->
    d_wf_skel Ψ Γ (typ_all_col c P)
| d_wf_skel__all_plain : forall L Ψ Γ P,
    (forall X, X `notin` L ->
       d_wf_skel (X :: Ψ) Γ (open_typ_wrt_typ P (typ_var_f X))) ->
    d_wf_skel Ψ Γ (typ_all_plain P)
| d_wf_skel__hole : forall Ψ Γ,
    d_wf_skel Ψ Γ typ_hole
| d_wf_skel__tophole : forall Ψ Γ P,
    guarded_skel P ->
    d_wf_skel nil Γ P ->
    d_wf_skel Ψ Γ (typ_tophole P).

(** ** Well-formedness of tagged types. Each ε must appear exactly once
    (linearity by disjoint append). *)
Inductive d_wf_ttyp :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_ttyp__unit : forall Γ,
    d_wf_ttyp nil Γ typ_unit
| d_wf_ttyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_wf_ttyp nil Γ (typ_var_f X)
| d_wf_ttyp__arrow : forall Δ1 Δ2 Γ A B,
    d_wf_ttyp Δ1 Γ A ->
    d_wf_ttyp Δ2 Γ B ->
    list_disjoint Δ1 Δ2 ->
    d_wf_ttyp (Δ1 ++ Δ2) Γ (typ_arrow A B)
| d_wf_ttyp__all : forall L Δ Γ ε A,
    (forall X, X `notin` L ->
       d_wf_ttyp Δ ((X ~ dbind_tvar) ++ Γ) (open_typ_wrt_typ A (typ_var_f X))) ->
    ~ List.In ε Δ ->
    d_wf_ttyp (ε :: Δ) Γ (typ_all_etag ε A).

(** ** Well-formedness of unresolved types. The "potential tag δ" (empty or ε)
    is encoded by two ∀ constructors; Δ tracks only the ε-tagged ones. *)
Inductive d_wf_utyp :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_utyp__unit : forall Γ,
    d_wf_utyp nil Γ typ_unit
| d_wf_utyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_wf_utyp nil Γ (typ_var_f X)
| d_wf_utyp__arrow : forall Δ1 Δ2 Γ A B,
    d_wf_utyp Δ1 Γ A ->
    d_wf_utyp Δ2 Γ B ->
    list_disjoint Δ1 Δ2 ->
    d_wf_utyp (Δ1 ++ Δ2) Γ (typ_arrow A B)
| d_wf_utyp__tall : forall L Δ Γ ε A,
    (forall X, X `notin` L ->
       d_wf_utyp Δ ((X ~ dbind_tvar) ++ Γ) (open_typ_wrt_typ A (typ_var_f X))) ->
    ~ List.In ε Δ ->
    d_wf_utyp (ε :: Δ) Γ (typ_all_etag ε A)
| d_wf_utyp__pall : forall L Δ Γ A,
    (forall X, X `notin` L ->
       d_wf_utyp Δ ((X ~ dbind_tvar) ++ Γ) (open_typ_wrt_typ A (typ_var_f X))) ->
    d_wf_utyp Δ Γ (typ_all_plain A).

(** ** Tagged skeletons: tagged types + holes/topholes. *)
Inductive d_wf_tskel :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_tskel__unit : forall Γ,
    d_wf_tskel nil Γ typ_unit
| d_wf_tskel__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_wf_tskel nil Γ (typ_var_f X)
| d_wf_tskel__arrow : forall Δ1 Δ2 Γ psi1 psi2,
    d_wf_tskel Δ1 Γ psi1 ->
    d_wf_tskel Δ2 Γ psi2 ->
    list_disjoint Δ1 Δ2 ->
    d_wf_tskel (Δ1 ++ Δ2) Γ (typ_arrow psi1 psi2)
| d_wf_tskel__all : forall L Δ Γ ε psi,
    (forall X, X `notin` L ->
       d_wf_tskel Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ psi (typ_var_f X))) ->
    ~ List.In ε Δ ->
    d_wf_tskel (ε :: Δ) Γ (typ_all_etag ε psi)
| d_wf_tskel__hole : forall Γ,
    d_wf_tskel nil Γ typ_hole
| d_wf_tskel__tophole : forall Δ Γ psi,
    d_wf_tskel Δ Γ psi ->
    d_wf_tskel Δ Γ (typ_tophole psi).

(** ** Unresolved skeletons: unresolved types + holes/topholes. *)
Inductive d_wf_uskel :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_uskel__unit : forall Γ,
    d_wf_uskel nil Γ typ_unit
| d_wf_uskel__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_wf_uskel nil Γ (typ_var_f X)
| d_wf_uskel__arrow : forall Δ1 Δ2 Γ SS1 SS2,
    d_wf_uskel Δ1 Γ SS1 ->
    d_wf_uskel Δ2 Γ SS2 ->
    list_disjoint Δ1 Δ2 ->
    d_wf_uskel (Δ1 ++ Δ2) Γ (typ_arrow SS1 SS2)
| d_wf_uskel__tall : forall L Δ Γ ε SS,
    (forall X, X `notin` L ->
       d_wf_uskel Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ SS (typ_var_f X))) ->
    ~ List.In ε Δ ->
    d_wf_uskel (ε :: Δ) Γ (typ_all_etag ε SS)
| d_wf_uskel__pall : forall L Δ Γ SS,
    (forall X, X `notin` L ->
       d_wf_uskel Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ SS (typ_var_f X))) ->
    d_wf_uskel Δ Γ (typ_all_plain SS)
| d_wf_uskel__hole : forall Γ,
    d_wf_uskel nil Γ typ_hole
| d_wf_uskel__tophole : forall Δ Γ SS,
    d_wf_uskel Δ Γ SS ->
    d_wf_uskel Δ Γ (typ_tophole SS).

(** ** Type consistency Δ | Γ ⊢ T ~ A.
    T is is_utyp; A is is_typ; tags in T marked by Δ are "solved" by this
    judgement. *)
Inductive d_consis :
  list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_consis__unit : forall Γ,
    d_consis nil Γ typ_unit typ_unit
(* Paper d_consis__var has empty premise; we add binds (the paper's
   implicit wf invariant) so d_consis_preserves_wf goes through
   without a side hypothesis. *)
| d_consis__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_consis nil Γ (typ_var_f X) (typ_var_f X)
(* ForallInh: tagged on left, ε added to Δ. Linearity: ε must be
   fresh w.r.t. Δ (paper-faithful set semantics; matches d_wf_ttyp__all). *)
| d_consis__forall_inh_tagged : forall L Δ Γ ε T A,
    (forall X, X `notin` L ->
       d_consis Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    ~ List.In ε Δ ->
    d_consis (ε :: Δ) Γ (typ_all_etag ε T) (typ_all_col colour_inh A)
(* ForallInh: untagged on left. *)
| d_consis__forall_inh_untagged : forall L Δ Γ T A,
    (forall X, X `notin` L ->
       d_consis Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis Δ Γ (typ_all_plain T) (typ_all_col colour_inh A)
(* ForallSyn: tag NOT solved when RHS is synthesised. *)
| d_consis__forall_syn_tagged : forall L Δ Γ ε T A,
    (forall X, X `notin` L ->
       d_consis Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis Δ Γ (typ_all_etag ε T) (typ_all_col colour_syn A)
| d_consis__forall_syn_untagged : forall L Δ Γ T A,
    (forall X, X `notin` L ->
       d_consis Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis Δ Γ (typ_all_plain T) (typ_all_col colour_syn A)
(* Arrow: linear-tag semantics (paper writes Δ_1, Δ_2 as set union;
   d_wf_ttyp__arrow enforces disjointness analogously). *)
| d_consis__arrow : forall Δ1 Δ2 Γ T1 T2 A1 A2,
    d_consis Δ1 Γ T1 A1 ->
    d_consis Δ2 Γ T2 A2 ->
    list_disjoint Δ1 Δ2 ->
    d_consis (Δ1 ++ Δ2) Γ (typ_arrow T1 T2) (typ_arrow A1 A2).

(** ** Type subtyping Γ ⊢_M^Δ T ≤ A. *)
Inductive d_sub :
  mode -> list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_sub__infer : forall Γ T A,
    is_syn_typ A ->
    d_consis nil Γ T A ->
    d_sub mode_ti nil Γ T A
| d_sub__check : forall Δ Γ T A,
    (* T must be guarded — encoded as: not a top-level ∀ of any flavour.
       The forall_l_* rules consume the tagged/plain ∀ cases on the left. *)
    (forall ε T', T <> typ_all_etag ε T') ->
    (forall T', T <> typ_all_plain T') ->
    is_inh_typ A ->
    d_consis Δ Γ T A ->
    d_sub mode_tc Δ Γ T A
| d_sub__forall_r : forall L Δ Γ T A,
    (forall X, X `notin` L ->
       d_sub mode_tc Δ ((X ~ dbind_tvar) ++ Γ) T (open_typ_wrt_typ A (typ_var_f X))) ->
    d_sub mode_tc Δ Γ T (typ_all_col colour_inh A)
| d_sub__arg : forall Δ1 Δ2 Γ m T1 T2 A1 A2,
    d_consis Δ1 Γ T1 A1 ->
    d_sub m Δ2 Γ T2 A2 ->
    d_sub (mode_fn m) (Δ1 ++ Δ2) Γ (typ_arrow T1 T2) (typ_arrow A1 A2)
| d_sub__forall_l_tagged : forall Δ Δ' Γ m ε T ph A,
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    d_wf_ttyp Δ' Γ ph ->
    d_sub m (Δ ++ Δ') Γ (open_typ_wrt_typ T ph) A ->
    d_sub m Δ Γ (typ_all_etag ε T) A
| d_sub__forall_l_untagged : forall Δ Δ' Γ m T ph A,
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    d_wf_ttyp Δ' Γ ph ->
    d_sub m (Δ ++ Δ') Γ (open_typ_wrt_typ T ph) A ->
    d_sub m Δ Γ (typ_all_plain T) A.

(** ** Shallow polymorphic subtyping (paper line 1062). The Phase 2 target:
    we will prove d_sub TC ε Γ A B → d_shallow_sub Γ A B. *)
Inductive d_shallow_sub :
  list (atom * dbind) -> typ -> typ -> Prop :=
| d_shallow_sub__refl : forall Γ A,
    d_shallow_sub Γ A A
| d_shallow_sub__forall_r : forall L Γ A B c,
    (forall X, X `notin` L ->
       d_shallow_sub ((X ~ dbind_tvar) ++ Γ) A
         (open_typ_wrt_typ B (typ_var_f X))) ->
    d_shallow_sub Γ A (typ_all_col c B)
| d_shallow_sub__forall_l : forall Γ A A' B c,
    d_wf_typ Γ A' ->
    d_shallow_sub Γ (open_typ_wrt_typ A A') B ->
    d_shallow_sub Γ (typ_all_col c A) B.

(** ** Base terms O ::= unit | x | M:A — used in the Sub rule. *)
Inductive is_base_term : exp -> Prop :=
| is_base_term__unit : is_base_term exp_unit
| is_base_term__var  : forall x, is_base_term (exp_var_f x)
| is_base_term__anno : forall e A, is_base_term (exp_anno e A).

(** A typ with no ∀ at any depth (any flavour). Used in d_pat_consis ghost. *)
Inductive no_forall_typ : typ -> Prop :=
| no_forall_typ__unit  : no_forall_typ typ_unit
| no_forall_typ__var   : forall X, no_forall_typ (typ_var_f X)
| no_forall_typ__arrow : forall A B,
    no_forall_typ A -> no_forall_typ B ->
    no_forall_typ (typ_arrow A B)
| no_forall_typ__hole  : no_forall_typ typ_hole
| no_forall_typ__tophole : forall A,
    no_forall_typ A -> no_forall_typ (typ_tophole A).

(** ** Skeleton refinement (uncoloured) Ψ ⨟ Γ ⊢ P ▸ Q.
    Standalone — does not reference d_typing or d_pat. *)
Inductive d_refine_syn :
  list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_refine_syn__unit : forall Ψ Γ,
    d_refine_syn Ψ Γ typ_unit typ_unit
| d_refine_syn__var : forall Ψ Γ X,
    List.In X Ψ \/ binds X dbind_tvar Γ ->
    d_refine_syn Ψ Γ (typ_var_f X) (typ_var_f X)
| d_refine_syn__arrow : forall Ψ Γ P1 P2 Q1 Q2,
    d_refine_syn Ψ Γ P1 Q1 ->
    d_refine_syn Ψ Γ P2 Q2 ->
    d_refine_syn Ψ Γ (typ_arrow P1 P2) (typ_arrow Q1 Q2)
| d_refine_syn__all_inh : forall L Ψ Γ P Q,
    (forall X, X `notin` L ->
       d_refine_syn (X :: Ψ) Γ
         (open_typ_wrt_typ P (typ_var_f X))
         (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine_syn Ψ Γ (typ_all_col colour_inh P) (typ_all_col colour_inh Q)
| d_refine_syn__hole : forall Ψ Γ Q,
    is_syn_skel Q ->
    d_wf_skel Ψ Γ Q ->
    d_refine_syn Ψ Γ typ_hole Q
| d_refine_syn__tophole_no_top : forall L Ψ Γ P Q,
    (forall X, X `notin` L ->
       d_refine_syn (X :: Ψ) Γ P (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine_syn Ψ Γ (typ_tophole P) (typ_all_col colour_syn Q)
| d_refine_syn__tophole_with_top : forall L Ψ Γ P Q,
    guarded_skel Q ->
    d_wf_skel nil Γ P ->
    (forall X, X `notin` L ->
       d_refine_syn nil Γ P (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine_syn Ψ Γ (typ_tophole P)
      (typ_all_col colour_syn (typ_tophole Q)).

(** ** Skeleton refinement (colour-respecting) Ψ ⨟ Γ ⊢ P ⊳ Q.
    Standalone — does not reference d_typing or d_pat. *)
Inductive d_refine :
  list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_refine__unit : forall Ψ Γ,
    d_refine Ψ Γ typ_unit typ_unit
| d_refine__var : forall Ψ Γ X,
    List.In X Ψ \/ binds X dbind_tvar Γ ->
    d_refine Ψ Γ (typ_var_f X) (typ_var_f X)
| d_refine__arrow : forall Ψ Γ P1 P2 Q1 Q2,
    d_refine Ψ Γ P1 Q1 ->
    d_refine Ψ Γ P2 Q2 ->
    d_refine Ψ Γ (typ_arrow P1 P2) (typ_arrow Q1 Q2)
| d_refine__all : forall L Ψ Γ P Q,
    (forall X, X `notin` L ->
       d_refine (X :: Ψ) Γ
         (open_typ_wrt_typ P (typ_var_f X))
         (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine Ψ Γ (typ_all_plain P) (typ_all_plain Q)
| d_refine__hole : forall Ψ Γ Q,
    d_wf_skel nil Γ Q ->
    d_refine Ψ Γ typ_hole Q
| d_refine__tophole_no_top : forall L Ψ Γ P Q,
    (forall X, X `notin` L ->
       d_refine (X :: Ψ) Γ P (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine Ψ Γ (typ_tophole P) (typ_all_plain Q)
| d_refine__tophole_with_top : forall L Ψ Γ P Q,
    guarded_skel Q ->
    d_wf_skel nil Γ P ->
    (forall X, X `notin` L ->
       d_refine nil Γ P (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine Ψ Γ (typ_tophole P)
      (typ_all_plain (typ_tophole Q)).

(** ** Skeleton consistency Δ ⨟ Γ ⊨ S ~ P.
    Standalone — does not reference d_typing or d_pat. *)
Inductive d_pat_consis :
  list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_pat_consis__unit : forall Γ,
    d_pat_consis nil Γ typ_unit typ_unit
| d_pat_consis__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_pat_consis nil Γ (typ_var_f X) (typ_var_f X)
| d_pat_consis__forall_inh_tagged : forall L Δ Γ ε SS P,
    (forall X, X `notin` L ->
       d_pat_consis Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ SS (typ_var_f X))
         (open_typ_wrt_typ P (typ_var_f X))) ->
    ~ List.In ε Δ ->
    d_pat_consis (ε :: Δ) Γ (typ_all_etag ε SS) (typ_all_col colour_inh P)
| d_pat_consis__forall_inh_untagged : forall L Δ Γ SS P,
    (forall X, X `notin` L ->
       d_pat_consis Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ SS (typ_var_f X))
         (open_typ_wrt_typ P (typ_var_f X))) ->
    d_pat_consis Δ Γ (typ_all_plain SS) (typ_all_col colour_inh P)
| d_pat_consis__forall_syn_tagged : forall L Δ Γ ε SS P,
    (forall X, X `notin` L ->
       d_pat_consis Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ SS (typ_var_f X))
         (open_typ_wrt_typ P (typ_var_f X))) ->
    d_pat_consis Δ Γ (typ_all_etag ε SS) (typ_all_col colour_syn P)
| d_pat_consis__forall_syn_untagged : forall L Δ Γ SS P,
    (forall X, X `notin` L ->
       d_pat_consis Δ ((X ~ dbind_tvar) ++ Γ)
         (open_typ_wrt_typ SS (typ_var_f X))
         (open_typ_wrt_typ P (typ_var_f X))) ->
    d_pat_consis Δ Γ (typ_all_plain SS) (typ_all_col colour_syn P)
(* Ghost: paper rule says "no synthesised ∀ in P" but assumes P is wf
   via the meta-level invariant. We make the wf premise explicit so
   that d_pat_consis_preserves_wf is provable. *)
| d_pat_consis__ghost : forall Γ P,
    no_forall_typ P ->
    d_wf_skel nil Γ P ->
    d_pat_consis nil Γ typ_hole P
| d_pat_consis__arrow : forall Δ1 Δ2 Γ SS1 SS2 P1 P2,
    d_pat_consis Δ1 Γ SS1 P1 ->
    d_pat_consis Δ2 Γ SS2 P2 ->
    list_disjoint Δ1 Δ2 ->
    d_pat_consis (Δ1 ++ Δ2) Γ (typ_arrow SS1 SS2) (typ_arrow P1 P2)
| d_pat_consis__univ_ghost_arr : forall Δ Γ SS P,
    d_pat_consis Δ Γ SS P ->
    d_pat_consis Δ Γ (typ_tophole SS) (typ_tophole P)
| d_pat_consis__univ_ghost_inh1 : forall L Δ Γ SS P,
    (forall X, X `notin` L ->
       d_pat_consis Δ ((X ~ dbind_tvar) ++ Γ)
         (typ_tophole SS) (open_typ_wrt_typ P (typ_var_f X))) ->
    d_pat_consis Δ Γ (typ_tophole SS) (typ_all_col colour_inh P)
| d_pat_consis__univ_ghost_pass : forall Δ Γ SS P,
    d_pat_consis Δ Γ SS P ->
    d_pat_consis Δ Γ (typ_tophole SS) P.

(** ** Skeleton subtyping Γ ⊢ₛ[ M ; Δ ] S ⊑ P.
    Standalone — depends on d_pat_consis but not on d_typing/d_pat. *)
Inductive d_pat_sub :
  mode -> list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_pat_sub__infer : forall Γ SS P,
    is_syn_skel P ->
    d_pat_consis nil Γ SS P ->
    d_pat_sub mode_ti nil Γ SS P
(* Paper sublab{UnivGhostR} requires "syn{S} guarded" — added now. *)
| d_pat_sub__univ_ghost_r : forall Γ SS P,
    guarded_skel SS ->
    (forall ε SS', SS <> typ_all_etag ε SS') ->
    (forall SS', SS <> typ_all_plain SS') ->
    (forall SS', SS <> typ_tophole SS') ->
    SS <> typ_hole ->
    is_syn_skel P ->
    d_pat_consis nil Γ SS P ->
    d_pat_sub mode_tc nil Γ SS (typ_tophole P)
(* d_pat_sub__ghost: same wf strengthening as d_pat_consis__ghost. *)
| d_pat_sub__ghost : forall Γ m P,
    no_forall_typ P ->
    d_wf_skel nil Γ P ->
    d_pat_sub (mode_fn m) nil Γ typ_hole P
| d_pat_sub__univ_ghost_l : forall Δ Γ m SS P,
    m <> mode_ti ->
    d_pat_sub m Δ Γ SS P ->
    d_pat_sub m Δ Γ (typ_tophole SS) P
| d_pat_sub__arg : forall Δ1 Δ2 Γ m SS1 SS2 P1 P2,
    d_pat_consis Δ1 Γ SS1 P1 ->
    d_pat_sub m Δ2 Γ SS2 P2 ->
    d_pat_sub (mode_fn m) (Δ1 ++ Δ2) Γ (typ_arrow SS1 SS2) (typ_arrow P1 P2)
| d_pat_sub__forall_l_tagged : forall Δ Δ' Γ m ε SS psi P,
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    d_wf_tskel Δ' Γ psi ->
    d_pat_sub m (Δ ++ Δ') Γ (open_typ_wrt_typ SS psi) P ->
    d_pat_sub m Δ Γ (typ_all_etag ε SS) P
| d_pat_sub__forall_l_untagged : forall Δ Δ' Γ m SS psi P,
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    d_wf_tskel Δ' Γ psi ->
    d_pat_sub m (Δ ++ Δ') Γ (open_typ_wrt_typ SS psi) P ->
    d_pat_sub m Δ Γ (typ_all_plain SS) P.

(** ** Declarative typing Γ ⊢[ M ] e ⇒ A and skeleton inference Γ ⊢[ M ] e ⇨ P.
    These two are genuinely mutual due to the App rule (d_typing__app reads
    the argument's skeleton via d_pat, and d_pat__app reads the function's
    type via d_typing). The four upstream judgments d_refine_syn / d_refine
    / d_pat_consis / d_pat_sub are *not* mutual with these — see the
    standalone Inductives above. *)
Inductive d_typing :
  mode -> list (atom * dbind) -> exp -> typ -> Prop :=
| d_typing__unit : forall Γ,
    mode_typ_compat mode_ti typ_unit ->
    d_typing mode_ti Γ exp_unit typ_unit
| d_typing__var : forall Γ x A,
    binds x (dbind_typ A) Γ ->
    d_typing mode_ti Γ (exp_var_f x) A
| d_typing__anno : forall Γ e A,
    is_inh_typ A ->
    d_typing mode_tc Γ e A ->
    d_typing mode_ti Γ (exp_anno e A) A
| d_typing__sub : forall Γ m e A B,
    is_base_term e ->
    d_typing mode_ti Γ e A ->
    d_sub m nil Γ A B ->
    d_typing m Γ e B
| d_typing__freeze : forall Γ e A,
    d_typing mode_ti Γ e A ->
    d_typing mode_tc Γ (exp_freeze e) A
| d_typing__forall : forall L Γ e A,
    is_value e ->
    (forall X, X `notin` L ->
       d_typing mode_tc ((X ~ dbind_tvar) ++ Γ) e
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_typing mode_tc Γ e (typ_all_col colour_inh A)
| d_typing__abs : forall L Γ m e A B,
    is_inh_typ A ->
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing m Γ (exp_abs e) (typ_arrow A B)
| d_typing__abs_anno : forall L Γ m e A B,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_typing (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing m Γ (exp_abs_anno A e) (typ_arrow A B)
| d_typing__app : forall Γ m e1 e2 P P' A B,
    d_pat mode_tc Γ e2 P ->
    d_refine_syn nil Γ P P' ->
    d_typing (mode_fn m) Γ e1 (typ_arrow A B) ->
    d_typing mode_tc Γ e2 A ->
    d_typing m Γ (exp_app e1 e2) B

with d_pat :
  mode -> list (atom * dbind) -> exp -> typ -> Prop :=
| d_pat__unit : forall Γ,
    d_pat mode_ti Γ exp_unit typ_unit
| d_pat__var : forall Γ x P,
    binds x (dbind_skel P) Γ ->
    d_pat mode_ti Γ (exp_var_f x) P
| d_pat__anno : forall Γ e A,
    d_wf_typ Γ A ->
    d_pat mode_ti Γ (exp_anno e A) A
| d_pat__sub : forall Γ m e P Q,
    is_base_term e ->
    d_pat mode_ti Γ e P ->
    d_pat_sub m nil Γ P Q ->
    d_pat m Γ e Q
| d_pat__freeze : forall Γ e P,
    d_pat mode_ti Γ e P ->
    d_pat mode_tc Γ (exp_freeze e) P
| d_pat__abs : forall L Γ m e P Q,
    m <> mode_tc ->
    is_inh_skel P ->
    d_wf_skel nil Γ P ->
    (forall x, x `notin` L ->
       d_pat (decr_mode m) ((x ~ dbind_skel P) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat m Γ (exp_abs e) (typ_arrow P Q)
| d_pat__abs_check : forall L Γ e Q,
    (forall x, x `notin` L ->
       d_pat mode_tc ((x ~ dbind_skel typ_hole) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat mode_tc Γ (exp_abs e) (typ_tophole (typ_arrow typ_hole Q))
| d_pat__abs_anno : forall L Γ m e A Q,
    m <> mode_tc ->
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_pat (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat m Γ (exp_abs_anno A e) (typ_arrow A Q)
| d_pat__abs_anno_check : forall L Γ e A Q,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       d_pat mode_tc ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat mode_tc Γ (exp_abs_anno A e) (typ_tophole (typ_arrow A Q))
| d_pat__app : forall Γ m e1 e2 P P' Q,
    d_pat mode_tc Γ e2 P ->
    d_refine_syn nil Γ P P' ->
    d_typing (mode_fn m) Γ e1 (typ_arrow P' Q) ->
    d_pat m Γ (exp_app e1 e2) Q
.

(** ** Syntax-directed declarative typing (paper syntax-directed.tex:454+).

    Difference from [d_typing]:
    - REMOVES [d_typing__forall] (the value-restriction rule that lifts a
      value to a typ_all_col colour_inh).
    - ADDS [ds_typing__abs_forall] and [ds_typing__abs_anno_forall]:
      these absorb the forall introduction directly into the abstraction
      rule, producing [typ_all_col colour_inh (typ_arrow A B)] in one step.

    This is the system the paper uses to prove [General Subsumption] (D1)
    without the body-conversion cycle that blocks the direct bidirectional
    proof.

    Single-forall encoding here. Multi-forall (paper's [∀ᾱ.A→B] with ᾱ a
    sequence) is approximated by iterated application — sufficient for our
    target uses (D1 closure). See [TODO: multi-forall list-binder version]
    if a fuller treatment becomes necessary.

    Note: [ds_typing] is mutual with the ORIGINAL [d_pat] (the d_pat
    judgment doesn't change in the syntax-directed system). Mechanized
    here as a standalone inductive that REUSES [d_pat], [d_sub], etc.
    from the bidirectional development. *)
Inductive ds_typing :
  mode -> list (atom * dbind) -> exp -> typ -> Prop :=
| ds_typing__unit : forall Γ,
    ds_typing mode_ti Γ exp_unit typ_unit
| ds_typing__var : forall Γ x A,
    binds x (dbind_typ A) Γ ->
    ds_typing mode_ti Γ (exp_var_f x) A
| ds_typing__anno : forall Γ e A,
    is_inh_typ A ->
    ds_typing mode_tc Γ e A ->
    ds_typing mode_ti Γ (exp_anno e A) A
| ds_typing__sub : forall Γ m e A B,
    is_base_term e ->
    ds_typing mode_ti Γ e A ->
    d_sub m nil Γ A B ->
    ds_typing m Γ e B
| ds_typing__freeze : forall Γ e A,
    ds_typing mode_ti Γ e A ->
    ds_typing mode_tc Γ (exp_freeze e) A
(* NO __forall rule: absorbed into __abs_forall / __abs_anno_forall below *)
| ds_typing__abs : forall L Γ m e A B,
    is_inh_typ A ->
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       ds_typing (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    ds_typing m Γ (exp_abs e) (typ_arrow A B)
| ds_typing__abs_forall : forall L Γ e A B,
    (* paper's AbsForall with single-α (multi-α via iteration if needed).
       Note: A and B are in body form (may have typ_var_b 0 for α). *)
    (forall α, α `notin` L ->
       is_inh_typ (open_typ_wrt_typ A (typ_var_f α))) ->
    (forall α, α `notin` L ->
       d_wf_typ ((α ~ dbind_tvar) ++ Γ) (open_typ_wrt_typ A (typ_var_f α))) ->
    (forall α x, α `notin` L -> x `notin` (L `union` singleton α) ->
       ds_typing mode_tc
         ((x ~ dbind_typ (open_typ_wrt_typ A (typ_var_f α)))
          ++ (α ~ dbind_tvar) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x))
         (open_typ_wrt_typ B (typ_var_f α))) ->
    ds_typing mode_tc Γ (exp_abs e)
              (typ_all_col colour_inh (typ_arrow A B))
| ds_typing__abs_anno : forall L Γ m e A B,
    d_wf_typ Γ A ->
    (forall x, x `notin` L ->
       ds_typing (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    ds_typing m Γ (exp_abs_anno A e) (typ_arrow A B)
| ds_typing__abs_anno_forall : forall L Γ e A B,
    (forall α, α `notin` L ->
       d_wf_typ ((α ~ dbind_tvar) ++ Γ) (open_typ_wrt_typ A (typ_var_f α))) ->
    (forall α x, α `notin` L -> x `notin` (L `union` singleton α) ->
       ds_typing mode_tc
         ((x ~ dbind_typ (open_typ_wrt_typ A (typ_var_f α)))
          ++ (α ~ dbind_tvar) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x))
         (open_typ_wrt_typ B (typ_var_f α))) ->
    ds_typing mode_tc Γ (exp_abs_anno A e)
              (typ_all_col colour_inh (typ_arrow A B))
| ds_typing__app : forall Γ m e1 e2 P P' A B,
    d_pat mode_tc Γ e2 P ->
    d_refine_syn nil Γ P P' ->
    ds_typing (mode_fn m) Γ e1 (typ_arrow A B) ->
    ds_typing mode_tc Γ e2 A ->
    ds_typing m Γ (exp_app e1 e2) B
.
