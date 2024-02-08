Require Import
  Basics.Overture
  Basics.Tactics
  Basics.PathGroupoids
  WildCat.Core
  WildCat.Displayed
  WildCat.Universe
  WildCat.Induced.

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

Local Instance isgraph_ptype : IsGraph pType
  := isgraph_induced issig_ptype^-1.

Local Instance is01cat_ptype : Is01Cat pType
  := is01cat_induced issig_ptype^-1.

Local Instance is2graph_ptype : Is2Graph pType
  := is2graph_induced issig_ptype^-1.

Local Instance is1cat_ptype : Is1Cat pType
  := is1cat_induced issig_ptype^-1.
