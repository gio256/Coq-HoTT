Require Import
  Basics.Overture
  Basics.Tactics
  Basics.PathGroupoids
  WildCat.Core
  WildCat.Displayed
  WildCat.Universe.

Definition isgraph_pullback_isgraph {A B : Type} `{IsGraph B} (F : A -> B)
  : IsGraph A.
Proof.
  nrapply Build_IsGraph.
  intros a b.
  exact (F a $-> F b).
Defined.

Definition is01cat_pullback_is01cat {A B : Type} `{Is01Cat B} (F : A -> B)
  : @Is01Cat A (isgraph_pullback_isgraph F).
Proof.
  nrapply Build_Is01Cat.
  - intro a.
    exact (Id (F a)).
  - intros a b c.
    exact (cat_comp (A:=B)).
Defined.

Definition is2graph_pullback_is2graph {A B : Type} `{Is2Graph B} (F : A -> B)
  : @Is2Graph A (isgraph_pullback_isgraph F).
Proof.
  intros a b.
  exact (isgraph_hom (F a) (F b)).
Defined.

Definition is0gpd_pullback_is0gpd {A B : Type} `{Is0Gpd B} (F : A -> B)
  : @Is0Gpd A _ (is01cat_pullback_is01cat F).
Proof.
  nrapply Build_Is0Gpd.
  intros a b f.
  exact (gpd_rev (A:=B) f).
Defined.

Definition is1cat_pullback_is1cat {A B : Type} `{ic : Is1Cat B} (F : A -> B)
  : @Is1Cat A _ (is2graph_pullback_is2graph F) (is01cat_pullback_is01cat F).
Proof.
  snrapply Build_Is1Cat.
  - intros a b.
    exact (is01cat_hom (F a) (F b)).
  - intros a b.
    exact (is0gpd_hom (F a) (F b)).
  - intros a b c.
    exact (is0functor_postcomp (F a) (F b) (F c)).
  - intros a b c.
    exact (is0functor_precomp (F a) (F b) (F c)).
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
  exact (isgraph_pullback_isgraph issig_ptype^-1).
Defined.

Local Instance is01cat_ptype : Is01Cat pType.
Proof.
  nrapply (is01cat_pullback_is01cat issig_ptype^-1).
  - exact (is01cat_sigma IsPointed).
Defined.

Local Instance is2graph_ptype : Is2Graph pType.
Proof.
  nrapply (is2graph_pullback_is2graph issig_ptype^-1).
  - exact (is2graph_sigma IsPointed).
Defined.
