Require Import
  Basics.Overture
  Basics.Tactics
  Basics.Equivalences
  Basics.PathGroupoids
  WildCat.Core
  WildCat.Displayed
  WildCat.Universe.

Definition isgraph_equiv_isgraph {A B : Type} `{IsGraph B} (F : A <~> B)
  : IsGraph A.
Proof.
  apply Build_IsGraph.
  intros a b.
  exact (F a $-> F b).
Defined.

(** Defined for an arbitrary graph structure on A *)
Definition is01cat_equiv_is01cat {A B : Type} `{IsGraph A} `{Is01Cat B}
  (F : A <~> B) `{!Is0Functor F} `{!Is0Functor F^-1}
  : Is01Cat A.
Proof.
  apply Build_Is01Cat.
  - intro a.
    exact (transport (fun x => x $-> x) (eissect F a) (fmap F^-1 (Id (F a)))).
  - intros a b c g f.
    nrefine (transport (fun x => a $-> x) (eissect F c) _).
    nrefine (transport (fun x => x $-> F^-1 (F c)) (eissect F a) _).
    exact (fmap F^-1 (fmap F g $o fmap F f)).
Defined.

(** Defined only for our isgraph_equiv_isgraph structure on A *)
Definition is01cat_equiv_is01cat' {A B : Type} `{Is01Cat B} (F : A <~> B)
  : @Is01Cat A (isgraph_equiv_isgraph F).
Proof.
  apply Build_Is01Cat.
  - intro a.
    exact (Id (F a)).
  - intros a b c g f.
    exact (cat_comp (A:=B) g f).
Defined.

Definition is2graph_equiv_is2graph {A B : Type} `{IsGraph A} `{Is2Graph B}
  (F : A <~> B) `{!Is0Functor F}
  : Is2Graph A.
Proof.
  intros a b.
  apply Build_IsGraph.
  intros f g.
  exact (fmap F f $-> fmap F g).
Defined.

Definition is2graph_equiv_is2graph' {A B : Type} `{Is2Graph B} (F : A <~> B)
  : @Is2Graph A (isgraph_equiv_isgraph F).
Proof.
  intros a b.
  apply Build_IsGraph.
  intros f g.
  exact (@Hom (@Hom B _ _ _) _ f g).
Defined.

Definition is0gpd_equiv_is0gpd {A B : Type} `{IsGraph A, !Is01Cat A} 
  `{Is0Gpd B} (F : A <~> B) `{!Is0Functor F} `{!Is0Functor F^-1}
  : Is0Gpd A.
Proof.
  srapply Build_Is0Gpd.
  intros a b f.
  nrefine (transport (fun x => b $-> x) (eissect F a) _).
  nrefine (transport (fun x => x $-> F^-1 (F a)) (eissect F b) _).
  exact (fmap F^-1 (gpd_rev (fmap F f))).
Defined.

Definition is0gpd_equiv_is0gpd' {A B : Type} `{Is0Gpd B} (F : A <~> B) 
  : @Is0Gpd A _ (is01cat_equiv_is01cat' F).
Proof.
  srapply Build_Is0Gpd.
  intros a b f.
  exact (gpd_rev (A:=B) f).
Defined.


Definition is_pointed (A : Type) := IsPointed A.

Local Instance isdgraph_pointed : IsDGraph is_pointed.
Proof.
  intros A B f a b.
  exact (f a = b).
Defined.

Local Instance is01dcat_pointed : Is01DCat is_pointed.
Proof.
  apply Build_Is01DCat.
  - intros A a.
    reflexivity.
  - intros A B C g f a b c pg pf.
    exact (ap g pf @ pg).
Defined.

Local Instance is2dgraph_pointed : Is2DGraph is_pointed.
Proof.
  intros A B a b f g H pf pg.
  exact (H a @ pg = pf).
Defined.

Local Instance is1dcat_pointed : Is1DCat is_pointed.
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
  apply (isgraph_equiv_isgraph issig_ptype).
Defined.

Local Instance is01cat_ptype : Is01Cat pType.
Proof.
  nrapply (is01cat_equiv_is01cat issig_ptype).
  - exact (is01cat_sigma is_pointed).
  - by apply Build_Is0Functor.
  - apply Build_Is0Functor.
    intros Aa Bb f; apply f.
Defined.

Local Instance is2graph_ptype : Is2Graph pType.
Proof.
  nrapply (is2graph_equiv_is2graph issig_ptype).
  - apply (is2graph_sigma is_pointed).
  - apply Build_Is0Functor.
    intros Aa Bb f; apply f.
Defined.
