(** Coercions between the type-hierarchy categories.

    See [docs/superpowers/specs/2026-05-18-type-hierarchy-refactor-design.md].

    - [utyp_to_bid]   — implicit [Coercion]. utyp is a subset of bid;
                        every utyp embeds uniquely as a bid.
    - [ctyp_to_bid_syn] / [ctyp_to_bid_inh] — paint a colourless
                        ctyp into bid with chosen colour. NOT a
                        coercion (two paths; ambiguous).
    - [ctyp_to_utyp_syn] — paint ctyp into utyp (only syn-colour
                        sensible at the utyp level — utyp has no
                        inh ∀). NOT a coercion.
    - [bid_to_ctyp] / [utyp_to_ctyp] — erase colour/tag. Explicit.
    - [ctyp_to_skel] — lift ctyp shape to skel (with hole/tophole
                        preserved). Could be implicit Coercion but
                        kept explicit for clarity. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_extra.

(** ===== ptyp → ctyp (implicit Coercion) =====
    Plain types embed uniquely into ctyp by mapping the 5 plain
    constructors to the matching ctyp ones (ptyp has no holes /
    tophole; that's the whole point of ptyp). *)

Fixpoint ptyp_to_ctyp (N : ptyp) : ctyp :=
  match N with
  | ptyp_unit          => ctyp_unit
  | ptyp_var_b n       => ctyp_var_b n
  | ptyp_var_f X       => ctyp_var_f X
  | ptyp_arrow N1 N2   => ctyp_arrow (ptyp_to_ctyp N1) (ptyp_to_ctyp N2)
  | ptyp_all N0        => ctyp_all (ptyp_to_ctyp N0)
  end.

Coercion ptyp_to_ctyp : ptyp >-> ctyp.

(** ===== utyp → bid (the implicit Coercion) ===== *)

Fixpoint utyp_to_bid (F : utyp) : bid :=
  match F with
  | utyp_unit            => bid_unit
  | utyp_var_b n         => bid_var_b n
  | utyp_var_f X         => bid_var_f X
  | utyp_arrow F1 F2     => bid_arrow (utyp_to_bid F1) (utyp_to_bid F2)
  | utyp_all_syn F0      => bid_all_syn (utyp_to_bid F0)
  | utyp_all_etag ε F0   => bid_all_etag ε (utyp_to_bid F0)
  end.

Coercion utyp_to_bid : utyp >-> bid.

(** ===== ctyp → bid (explicit; two colour choices) ===== *)

Fixpoint ctyp_to_bid_syn (K : ctyp) : bid :=
  match K with
  | ctyp_unit          => bid_unit
  | ctyp_var_b n       => bid_var_b n
  | ctyp_var_f X       => bid_var_f X
  | ctyp_arrow K1 K2   => bid_arrow (ctyp_to_bid_syn K1) (ctyp_to_bid_syn K2)
  | ctyp_all K0        => bid_all_syn (ctyp_to_bid_syn K0)
  | ctyp_hole          => bid_unit  (* unreachable; ctyp_hole has no bid analogue *)
  | ctyp_tophole _     => bid_unit  (* same *)
  end.

Fixpoint ctyp_to_bid_inh (K : ctyp) : bid :=
  match K with
  | ctyp_unit          => bid_unit
  | ctyp_var_b n       => bid_var_b n
  | ctyp_var_f X       => bid_var_f X
  | ctyp_arrow K1 K2   => bid_arrow (ctyp_to_bid_inh K1) (ctyp_to_bid_inh K2)
  | ctyp_all K0        => bid_all_inh (ctyp_to_bid_inh K0)
  | ctyp_hole          => bid_unit
  | ctyp_tophole _     => bid_unit
  end.

(** ===== ctyp → utyp (explicit) ===== *)

Fixpoint ctyp_to_utyp_syn (K : ctyp) : utyp :=
  match K with
  | ctyp_unit          => utyp_unit
  | ctyp_var_b n       => utyp_var_b n
  | ctyp_var_f X       => utyp_var_f X
  | ctyp_arrow K1 K2   => utyp_arrow (ctyp_to_utyp_syn K1) (ctyp_to_utyp_syn K2)
  | ctyp_all K0        => utyp_all_syn (ctyp_to_utyp_syn K0)
  | ctyp_hole          => utyp_unit
  | ctyp_tophole _     => utyp_unit
  end.

(** ===== Erasures: bid / utyp → ctyp ===== *)

Fixpoint bid_to_ctyp (D : bid) : ctyp :=
  match D with
  | bid_unit            => ctyp_unit
  | bid_var_b n         => ctyp_var_b n
  | bid_var_f X         => ctyp_var_f X
  | bid_arrow D1 D2     => ctyp_arrow (bid_to_ctyp D1) (bid_to_ctyp D2)
  | bid_all_syn D0      => ctyp_all (bid_to_ctyp D0)
  | bid_all_inh D0      => ctyp_all (bid_to_ctyp D0)
  | bid_all_etag _ D0   => ctyp_all (bid_to_ctyp D0)
  end.

Fixpoint utyp_to_ctyp (F : utyp) : ctyp :=
  match F with
  | utyp_unit            => ctyp_unit
  | utyp_var_b n         => ctyp_var_b n
  | utyp_var_f X         => ctyp_var_f X
  | utyp_arrow F1 F2     => ctyp_arrow (utyp_to_ctyp F1) (utyp_to_ctyp F2)
  | utyp_all_syn F0      => ctyp_all (utyp_to_ctyp F0)
  | utyp_all_etag _ F0   => ctyp_all (utyp_to_ctyp F0)
  end.

(** ===== ptyp paintings (direct; bypass the ctyp intermediate) =====
    ptyp embeds in ctyp via the implicit coercion, so [ctyp_to_bid_syn N]
    works for [N : ptyp]. These direct versions exist for clarity in
    rule statements and so the proof obligations don't have to peel
    layers of coercions. *)

Fixpoint ptyp_to_bid_syn (N : ptyp) : bid :=
  match N with
  | ptyp_unit          => bid_unit
  | ptyp_var_b n       => bid_var_b n
  | ptyp_var_f X       => bid_var_f X
  | ptyp_arrow N1 N2   => bid_arrow (ptyp_to_bid_syn N1) (ptyp_to_bid_syn N2)
  | ptyp_all N0        => bid_all_syn (ptyp_to_bid_syn N0)
  end.

Fixpoint ptyp_to_bid_inh (N : ptyp) : bid :=
  match N with
  | ptyp_unit          => bid_unit
  | ptyp_var_b n       => bid_var_b n
  | ptyp_var_f X       => bid_var_f X
  | ptyp_arrow N1 N2   => bid_arrow (ptyp_to_bid_inh N1) (ptyp_to_bid_inh N2)
  | ptyp_all N0        => bid_all_inh (ptyp_to_bid_inh N0)
  end.

Fixpoint ptyp_to_utyp_syn (N : ptyp) : utyp :=
  match N with
  | ptyp_unit          => utyp_unit
  | ptyp_var_b n       => utyp_var_b n
  | ptyp_var_f X       => utyp_var_f X
  | ptyp_arrow N1 N2   => utyp_arrow (ptyp_to_utyp_syn N1) (ptyp_to_utyp_syn N2)
  | ptyp_all N0        => utyp_all_syn (ptyp_to_utyp_syn N0)
  end.

(** ===== Erasures back to ptyp =====
    Forget colour AND tag. [bid_to_ptyp] is total: tagged ∀ erases to
    plain ∀ (the tag was just bookkeeping). *)

Fixpoint bid_to_ptyp (D : bid) : ptyp :=
  match D with
  | bid_unit            => ptyp_unit
  | bid_var_b n         => ptyp_var_b n
  | bid_var_f X         => ptyp_var_f X
  | bid_arrow D1 D2     => ptyp_arrow (bid_to_ptyp D1) (bid_to_ptyp D2)
  | bid_all_syn D0      => ptyp_all (bid_to_ptyp D0)
  | bid_all_inh D0      => ptyp_all (bid_to_ptyp D0)
  | bid_all_etag _ D0   => ptyp_all (bid_to_ptyp D0)
  end.

Fixpoint utyp_to_ptyp (F : utyp) : ptyp :=
  match F with
  | utyp_unit            => ptyp_unit
  | utyp_var_b n         => ptyp_var_b n
  | utyp_var_f X         => ptyp_var_f X
  | utyp_arrow F1 F2     => ptyp_arrow (utyp_to_ptyp F1) (utyp_to_ptyp F2)
  | utyp_all_syn F0      => ptyp_all (utyp_to_ptyp F0)
  | utyp_all_etag _ F0   => ptyp_all (utyp_to_ptyp F0)
  end.

(** ===== ctyp → skel (explicit; preserves hole/tophole) ===== *)

Fixpoint ctyp_to_skel (K : ctyp) : skel :=
  match K with
  | ctyp_unit          => skel_unit
  | ctyp_var_b n       => skel_var_b n
  | ctyp_var_f X       => skel_var_f X
  | ctyp_arrow K1 K2   => skel_arrow (ctyp_to_skel K1) (ctyp_to_skel K2)
  | ctyp_all K0        => skel_all_syn (ctyp_to_skel K0)
  | ctyp_hole          => skel_hole
  | ctyp_tophole K0    => skel_tophole (ctyp_to_skel K0)
  end.
