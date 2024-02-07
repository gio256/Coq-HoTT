Require Import
  Basics.Overture
  Basics.Tactics
  Basics.Equivalences
  Basics.PathGroupoids
  WildCat.Core
  WildCat.Displayed
  WildCat.Universe.

Definition isgraph_equiv_isgraph {A B : Type} `{IsGraph A} (F : A <~> B)
  : IsGraph B.
Proof.
  apply Build_IsGraph.
  intros b c.
  exact ((F^-1 b) $-> (F^-1 c)).
Defined.

Definition is01cat_equiv_is01cat {A B : Type} `{Is01Cat A} `{!IsGraph B}
  (F : A <~> B) `{!Is0Functor F} `{!Is0Functor F^-1}
  : Is01Cat B.
Proof.
  apply Build_Is01Cat.
  - exact (equiv_ind F (fun x => x $-> x) (fun a => fmap F (Id a))).
  - intros a b c h g.
    nrefine (transport (fun x => a $-> x) (eisretr F c) _).
    nrefine (transport (fun x => x $-> F (F^-1 c)) (eisretr F a) _).
    exact (fmap F (fmap F^-1 h $o fmap F^-1 g)).
Defined.

Definition is2graph_equiv_is2graph {A B : Type} `{Is2Graph A} `{!IsGraph B}
  (F : A <~> B) `{!Is0Functor F^-1}: Is2Graph B.
Proof.
  intros b c.
  apply Build_IsGraph.
  intros g h.
  exact (fmap F^-1 g $-> fmap F^-1 h).
Defined.

Definition is0gpd_equiv_is0gpd {A B : Type} `{Is0Gpd A}
  `{!IsGraph B, !Is01Cat B} (F : A <~> B) `{!Is0Functor F}
  `{!Is0Functor F^-1}
  : Is0Gpd B.
Proof.
  srapply Build_Is0Gpd.
  intros b c g.
  nrefine (transport (fun x => c $-> x) (eisretr F b) _).
  nrefine (transport (fun x => x $-> F (F^-1 b)) (eisretr F c) _).
  exact (fmap F (gpd_rev (fmap F^-1 g))).
Defined.

(* Definition is1cat_equiv_is1cat {A B : Type} `{Is1Cat A} *)
(*   `{IsGraph B, !Is2Graph B, !Is01Cat B} *)
(*   (F : A <~> B) `{!Is0Functor F} `{!Is0Functor F^-1} *) 
(*   : Is1Cat B. *)
(* Proof. *)
(* Defined. *)


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

(* Local Instance is1cat_ptype : Is1Cat pType. *)
(* Proof. *)
(*   nrapply (is1cat_equiv_is1cat issig_ptype). *)
(*   - exact (is1cat_sigma is_pointed). *)
(*   - by apply Build_Is0Functor. *)
(*   - apply Build_Is0Functor. *)
(*     intros Aa Bb f; apply f. *)
(* Defined. *)
