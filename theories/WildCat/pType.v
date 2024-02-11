Require Import
  Basics.Overture
  Basics.Tactics
  Basics.PathGroupoids
  Basics.Equivalences
  WildCat.Core
  WildCat.Displayed
  WildCat.Universe
  WildCat.Induced
  WildCat.Equiv.

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

Local Instance dhasequivs_ptype : DHasEquivs IsPointed.
Proof.
  snrapply Build_DHasEquivs.
  all: intros A B f.
  - exact (DHom f).
  - intros fe a b f'. exact Unit.
  - intros a b. exact idmap.
  - intros a b f'. exact tt.
  - intros fe a b. exact const.
  - intros fe a b f' ?. exact (DGpdHom_path idpath 1).
  - intros a b f'. exact (moveR_equiv_V _ _ f'^).
  - intros a b f'.
    destruct f'.
    apply moveR_pM.
    symmetry.
    exact (concat_p1 _ @ concat_1p _ @ concat_1p _).
  - intros a b f'.
    apply moveR_pM.
    destruct f'.
    refine (eisadj f _ @ _).
    symmetry.
    exact (concat_p1 _ @ concat_p1 _ @ ap _ (concat_1p _)).
  - intros. exact tt.
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

Local Instance hasequivs_ptype : HasEquivs pType
  := hasequivs_induced issig_ptype^-1.
