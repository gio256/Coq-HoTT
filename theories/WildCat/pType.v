Require Import
  Basics.Overture
  Basics.Tactics
  Basics.PathGroupoids
  WildCat.Core
  WildCat.Displayed
  WildCat.Universe.

Definition induced (A : Type) {B : Type} (f : A -> B) := A.

Global Instance isgraph_induced {A B : Type} `{IsGraph B} (f : A -> B)
  : IsGraph (induced A f).
Proof.
  nrapply Build_IsGraph.
  intros a b.
  exact (f a $-> f b).
Defined.

Global Instance is01cat_induced {A B : Type} `{Is01Cat B} (f : A -> B)
  : Is01Cat (induced A f).
Proof.
  nrapply Build_Is01Cat.
  - intro a.
    exact (Id (f a)).
  - intros a b c.
    exact (cat_comp (A:=B)).
Defined.

Global Instance is2graph_induced {A B : Type} `{Is2Graph B} (f : A -> B)
  : Is2Graph (induced A f).
Proof.
  intros a b.
  exact (isgraph_hom (f a) (f b)).
Defined.

Global Instance is0gpd_induced {A B : Type} `{Is0Gpd B} (f : A -> B)
  : Is0Gpd (induced A f).
Proof.
  nrapply Build_Is0Gpd.
  intros a b.
  exact (gpd_rev (A:=B)).
Defined.

Global Instance is1cat_induced {A B : Type} `{Is1Cat B} (f : A -> B)
  : Is1Cat (induced A f).
Proof.
  snrapply Build_Is1Cat.
  - intros a b.
    exact (is01cat_hom (f a) (f b)).
  - intros a b.
    exact (is0gpd_hom (f a) (f b)).
  - intros a b c.
    exact (is0functor_postcomp (f a) (f b) (f c)).
  - intros a b c.
    exact (is0functor_precomp (f a) (f b) (f c)).
  - intros a b c d.
    exact (cat_assoc (A:=B)).
  - intros a b.
    exact (cat_idl (A:=B)).
  - intros a b.
    exact (cat_idr (A:=B)).
Defined.


Local Instance isdgraph_pointed : IsDGraph IsPointed.
Proof.
  intros A B f a b.
  exact (f a = b).
Defined.

Local Instance is01dcat_pointed : Is01DCat IsPointed.
Proof.
  apply Build_Is01DCat.
  - intros A a.
    exact idpath.
  - intros A B C g f a b c pg pf.
    exact (ap g pf @ pg).
Defined.

Local Instance is2dgraph_pointed : Is2DGraph IsPointed.
Proof.
  intros A B a b f g H pf pg.
  exact (H a @ pg = pf).
Defined.

Local Instance is1dcat_pointed : Is1DCat IsPointed.
Proof.
  snrapply Build_Is1DCat.
  - intros A B a b.
    apply Build_Is01DCat.
    + intros f f'.
      exact (concat_1p f').
    + intros f g h H1 H2 f' g' h' p q.
      exact (concat_pp_p _ _ _ @ whiskerL _ p @ q).
  - intros A B a b f g p f' g' p'.
      apply moveR_Vp.
      exact p'^.
  - intros A B C f a b c f'.
    intros g h p g' h' p'.
    cbv.
    refine ((ap_pp_p _ _ _ _)^ @ _).
    exact ((whiskerR (ap02 f p') _)).
  - intros A B C f a b c f'.
    intros g h p g' h' p'.
    cbv.
    refine (concat_p_pp _ _ _ @ _).
    refine (whiskerR (concat_Ap _ _)^ _ @ _).
    exact (concat_pp_p _ _ _ @ whiskerL _ p').
  - intros A B C D f g h a b c d f' g' h'.
    cbv.
    refine (concat_1p _ @ _).
    refine (whiskerR (ap_pp _ _ _ @ (whiskerR (ap_compose _ _ _)^ _)) _ @ _).
    apply concat_pp_p.
  - intros A B f a b f'.
    exact (concat_1p _ @ (ap_idmap _)^ @ (concat_p1 _)^).
  - intros A B f a b f'; reflexivity.
Defined.

Definition issig_ptype : { X : Type & X } <~> pType := ltac:(issig).

Local Instance isgraph_ptype : IsGraph pType.
Proof.
  exact (isgraph_induced issig_ptype^-1).
Defined.

Local Instance is01cat_ptype : Is01Cat pType.
Proof.
  exact (is01cat_induced issig_ptype^-1).
Defined.

Local Instance is2graph_ptype : Is2Graph pType.
Proof.
  exact (is2graph_induced issig_ptype^-1).
Defined.
