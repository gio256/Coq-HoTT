Require Import Basics.
Require Import EquivGpd.
Require Import Types.Prod Types.Bool.
Require Import WildCat.Core WildCat.ZeroGroupoid WildCat.Equiv WildCat.Yoneda
               WildCat.Universe WildCat.NatTrans WildCat.Opposite
               WildCat.FunctorCat.

(** * Categories with products *)

Definition cat_prod_corec_inv {I A : Type} `{Is1Cat A}
  (prod : A) (x : I -> A) (z : A) (pr : forall i, prod $-> x i)
  : yon_0gpd prod z $-> prod_0gpd I (fun i => yon_0gpd (x i) z).
Proof.
  snrapply equiv_prod_0gpd_corec.
  intros i.
  exact (fmap (fun x => yon_0gpd x z) (pr i)).
Defined.

(* A product of an [I]-indexed family of objects of a category is an object of the category with an [I]-indexed family of projections such that the induced map is an equivalence. *)
Class Product (I : Type) {A : Type} `{Is1Cat A} {x : I -> A} := Build_Product' {
  cat_prod : A;
  cat_pr : forall (i : I), cat_prod $-> x i;
  cat_isequiv_cat_prod_corec_inv
    :: forall (z : A), CatIsEquiv (cat_prod_corec_inv cat_prod x z cat_pr);
}.

Arguments Product I {A _ _ _ _} x.
Arguments cat_prod I {A _ _ _ _} x {_}.

(** A convenience wrapper for building Products *)
Definition Build_Product (I : Type) {A : Type} `{Is1Cat A} {x : I -> A}
  (cat_prod : A) (cat_pr : forall (i : I), cat_prod $-> x i)
  (cat_prod_corec : forall (z : A),
    (forall (i : I), z $-> x i) -> (z $-> cat_prod))
  (cat_prod_beta_pr : forall (z : A) (f : forall i, z $-> x i) (i : I),
    cat_pr i $o cat_prod_corec z f $== f i)
  (cat_prod_eta_pr : forall (z : A) (f g : z $-> cat_prod),
    (forall (i : I), cat_pr i $o f $== cat_pr i $o g) -> f $== g)
  : Product I x.
Proof.
  snrapply (Build_Product' I A _ _ _ _ _ cat_prod cat_pr).
  intros z.
  apply isequiv_0gpd_issurjinj.
  snrapply Build_IsSurjInj.
  - simpl.
    intros f.
    exists (cat_prod_corec z f).
    intros i.
    apply cat_prod_beta_pr.
  - intros f g p.
    by apply cat_prod_eta_pr.
Defined.

Section Lemmata.

  Context (I : Type) {A : Type} {x : I -> A} `{Product I _ x}.

  Definition cate_cat_prod_corec_inv {z : A}
    : (yon_0gpd (cat_prod I x) z) $<~> prod_0gpd I (fun i => yon_0gpd (x i) z)
    := Build_CatEquiv (cat_prod_corec_inv (cat_prod I x) x z cat_pr).

  Definition cate_cat_prod_corec {z : A}
    : prod_0gpd I (fun i => yon_0gpd (x i) z) $<~> (yon_0gpd (cat_prod I x) z)
    := cate_cat_prod_corec_inv^-1$.

  Definition cat_prod_corec {z : A}
    : (forall i, z $-> x i) -> (z $-> cat_prod I x).
  Proof.
    apply cate_cat_prod_corec.
  Defined.

  (** Applying the [i]th projection after a tuple of maps gives the [ith] map. *)
  Lemma cat_prod_beta {z : A} (f : forall i, z $-> x i)
    : forall i, cat_pr i $o cat_prod_corec f $== f i.
  Proof.
    exact (cate_isretr cate_cat_prod_corec_inv f).
  Defined.

  (** The pairing map is the unique map that makes the following diagram commute. *)
  Lemma cat_prod_eta {z : A} (f : z $-> cat_prod I x)
    : cat_prod_corec (fun i => cat_pr i $o f) $== f.
  Proof.
    exact (cate_issect cate_cat_prod_corec_inv f).
  Defined.

  (* TODO: decompose and move *)
  Local Instance is0functor_prod_0gpd_helper
    : Is0Functor (fun z : A^op => prod_0gpd I (fun i => yon_0gpd (x i) z)).
  Proof.
    snrapply Build_Is0Functor.
    intros a b f.
    snrapply Build_Morphism_0Gpd.
    - intros g i.
      exact (f $o g i).
    - snrapply Build_Is0Functor.
      intros g h p i.
      exact (f $@L p i).
  Defined.

  (* TODO: decompose and move *)
  Local Instance is1functor_prod_0gpd_helper
    : Is1Functor (fun z : A^op => prod_0gpd I (fun i => yon_0gpd (x i) z)).
  Proof.
    snrapply Build_Is1Functor.
    - intros a b f g p r i.
      refine (_ $@L _).
      apply p.
    - intros a r i.
      apply cat_idl.
    - intros a b c f g r i.
      apply cat_assoc.
  Defined.

  Definition natequiv_cat_prod_corec_inv
    : NatEquiv (yon_0gpd (cat_prod I x))
      (fun z : A^op => prod_0gpd I (fun i => yon_0gpd (x i) z)).
  Proof.
    snrapply Build_NatEquiv.
    1: intro; apply cate_cat_prod_corec_inv.
    (*TODO: the line below triggers Anomaly "index out of bounds"*)
    (* apply is1natural_yoneda_0gpd. *)
    exact (is1natural_yoneda_0gpd
      (cat_prod I x)
      (fun z => prod_0gpd I (fun i => yon_0gpd (x i) z))
      cat_pr).
  Defined.

  Lemma cat_prod_corec_eta {z : A} {f f' : forall i, z $-> x i}
    : (forall i, f i $== f' i) -> cat_prod_corec f $== cat_prod_corec f'.
  Proof.
    intros p.
    unfold cat_prod_corec.
    apply (moveL_equiv_V_0gpd cate_cat_prod_corec_inv).
    refine (cate_isretr cate_cat_prod_corec_inv _ $@ _).
    exact p.
  Defined.

  Lemma cat_prod_pr_eta {z : A} {f f' : z $-> cat_prod I x}
    : (forall i, cat_pr i $o f $== cat_pr i $o f') -> f $== f'.
  Proof.
    intros p.
    refine ((cat_prod_eta _)^$ $@ _ $@ cat_prod_eta _).
    by apply cat_prod_corec_eta.
  Defined.

End Lemmata.

(** *** Diagonal map *)

Definition cat_prod_diag {I : Type} {A : Type} (x : A)
  `{Product I _ (fun _ => x)}
  : x $-> cat_prod I (fun _ => x)
  := cat_prod_corec I (fun _ => Id x).

(** *** Uniqueness of products *)

Section Uniqueness.

  Definition cate_prod_0gpd {I J : Type} (ie : I <~> J)
    (G : I -> ZeroGpd) (H : J -> ZeroGpd)
    (f : forall (i : I), G i $<~> H (ie i))
    : prod_0gpd I G $<~> prod_0gpd J H.
  Proof.
    snrapply cate_adjointify.
    - snrapply Build_Morphism_0Gpd.
      + intros h j.
        exact (transport H (eisretr ie j) (cate_fun (f (ie^-1 j)) (h _))).
      + nrapply Build_Is0Functor.
        intros g h p j.
        destruct (eisretr ie j).
        refine (_ $o Hom_path (transport_1 _ _)).
        apply Build_Morphism_0Gpd.
        exact (p _).
    - exact (equiv_prod_0gpd_corec (fun i => (f i)^-1$ $o prod_0gpd_pr (ie i))).
    - intros h j.
      cbn.
      destruct (eisretr ie j).
      exact (cate_isretr (f _) _).
    - intros g i.
      cbn.
      refine (_ $o Hom_path
              (ap (cate_fun (f i)^-1$) (transport2 _ (eisadj ie i) _))).
      destruct (eissect ie i).
      exact (cate_issect (f _) _).
  Defined.

  (** [I]-indexed products are unique no matter how they are constructed. *)
  Definition cate_cat_prod {I J : Type} (ie : I <~> J) {A : Type} `{HasEquivs A}
    (x : I -> A) `{!Product I x} (y : J -> A) `{!Product J y}
    (e : forall (i : I), x i $<~> y (ie i))
    : cat_prod I x $<~> cat_prod J y.
  Proof.
    apply yon_equiv_0gpd.
    nrefine (natequiv_compose _ (natequiv_cat_prod_corec_inv _)).
    nrefine (natequiv_compose
              (natequiv_inverse (natequiv_cat_prod_corec_inv _)) _).
    snrapply Build_NatEquiv.
    - intros z.
      nrapply (cate_prod_0gpd ie).
      intros i.
      exact (natequiv_yon_equiv_0gpd (e i) _).
    - intros a b f g j.
      cbn.
      destruct (eisretr ie j).
      exact (cat_assoc_opp _ _ _).
  Defined.

End Uniqueness.

Class HasProducts (I A : Type) `{Is1Cat A} :=
  has_products :: forall x : I -> A, Product I x.

Class HasAllProducts (A : Type) `{Is1Cat A} :=
  has_all_products :: forall (I : Type), HasProducts I A.

Global Instance is0functor_cat_prod (I : Type) `{IsGraph I}
  (A : Type) `{HasProducts I A}
  : Is0Functor (fun x : Fun01 I A => cat_prod I x).
Proof.
  nrapply Build_Is0Functor.
  intros x y f.
  exact (cat_prod_corec I (fun i => f i $o cat_pr i)).
Defined.

Global Instance is1functor_cat_prod (I : Type) `{IsGraph I}
  (A : Type) `{HasProducts I A}
  : Is1Functor (fun x : Fun01 I A => cat_prod I x).
Proof.
  nrapply Build_Is1Functor.
  - intros x y f g p.
    exact (cat_prod_corec_eta I (fun i => p i $@R cat_pr i)).
  - intros x.
    nrefine (_ $@ (cat_prod_eta I (Id _))).
    exact (cat_prod_corec_eta I (fun i => cat_idl _ $@ (cat_idr _)^$)).
  - intros x y z f g.
    apply cat_prod_pr_eta.
    intros i.
    nrefine (cat_prod_beta _ _ _ $@ _).
    nrefine (_ $@ cat_assoc _ _ _).
    symmetry.
    nrefine (cat_prod_beta _ _ _ $@R _ $@ _).
    nrefine (cat_assoc _ _ _ $@ _).
    nrefine (_ $@L cat_prod_beta _ _ _ $@ _).
    apply cat_assoc_opp.
Defined.


(** *** Categories with specific kinds of products *)

Definition prodempty_equiv_terminal {A : Type}
  `{HasProducts Empty A, !HasEquivs A} (z : A) `{!IsTerminal z}
  : z $<~> cat_prod Empty (fun _ => z).
Proof.
  snrapply cate_adjointify.
  - exact (cat_prod_corec _ (fun _ => Id z)).
  - exact (mor_terminal _ z).
  - nrapply cat_prod_pr_eta; intros [].
  - exact ((mor_terminal_unique z z _)^$ $@ mor_terminal_unique z z (Id z)).
Defined.

(** *** Binary products *)

Class BinaryProduct {A : Type} `{Is1Cat A} (x y : A)
  := binary_product :: Product Bool (fun b => if b then x else y).

(** A category with binary products is a category with a binary product for each pair of objects. *)
Class HasBinaryProducts (A : Type) `{Is1Cat A}
  := has_binary_products :: forall x y : A, BinaryProduct x y.

Global Instance hasbinaryproducts_hasproductsbool {A : Type} `{HasProducts Bool A}
  : HasBinaryProducts A.
Proof.
  intros x y.
  exact (has_products _).
Defined.

Section BinaryProducts.

  Context {A : Type} `{Is1Cat A} {x y : A} {B : BinaryProduct x y}.

  Definition cat_binprod : A
    := cat_prod Bool (fun b : Bool => if b then x else y).

  Definition cat_pr1 : cat_binprod $-> x := cat_pr true.

  Definition cat_pr2 : cat_binprod $-> y := cat_pr false.

  Definition cat_binprod_corec {z : A} (f : z $-> x) (g : z $-> y)
    : z $-> cat_binprod.
  Proof.
    apply (cat_prod_corec Bool).
    intros [|].
    - exact f.
    - exact g.
  Defined.

  Definition cat_binprod_beta_pr1 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_pr1 $o cat_binprod_corec f g $== f
    := cat_prod_beta _ _ true.

  Definition cat_binprod_beta_pr2 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_pr2 $o cat_binprod_corec f g $== g
    := cat_prod_beta _ _ false.

  Definition cat_binprod_eta {z : A} (f : z $-> cat_binprod)
    : cat_binprod_corec (cat_pr1 $o f) (cat_pr2 $o f) $== f.
  Proof.
    unfold cat_binprod_corec.
    apply cat_prod_pr_eta.
    intros [|].
    - exact (cat_binprod_beta_pr1 _ _).
    - exact (cat_binprod_beta_pr2 _ _).
  Defined.

  Definition cat_binprod_eta_pr {z : A} (f f' : z $-> cat_binprod)
    : cat_pr1 $o f $== cat_pr1 $o f' -> cat_pr2 $o f $== cat_pr2 $o f' -> f $== f'.
  Proof.
    intros p q.
    rapply cat_prod_pr_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binprod_corec_eta {z : A} (f f' : z $-> x) (g g' : z $-> y)
    : f $== f' -> g $== g' -> cat_binprod_corec f g $== cat_binprod_corec f' g'.
  Proof.
    intros p q.
    rapply cat_prod_corec_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

End BinaryProducts.

Arguments cat_binprod {A _ _ _ _} x y {_}.

(** This is a convenience wrapper for building binary products *)
Definition Build_BinaryProduct {A : Type} `{Is1Cat A} {x y : A}
  (cat_binprod : A) (cat_pr1 : cat_binprod $-> x) (cat_pr2 : cat_binprod $-> y)
  (cat_binprod_corec : forall z, z $-> x -> z $-> y -> z $-> cat_binprod)
  (cat_binprod_beta_pr1 : forall z (f : z $-> x) (g : z $-> y),
    cat_pr1 $o cat_binprod_corec z f g $== f)
  (cat_binprod_beta_pr2 : forall z (f : z $-> x) (g : z $-> y),
    cat_pr2 $o cat_binprod_corec z f g $== g)
  (cat_binprod_eta_pr : forall z (f g : z $-> cat_binprod),
    cat_pr1 $o f $== cat_pr1 $o g
    -> cat_pr2 $o f $== cat_pr2 $o g
    -> f $== g)
  : Product Bool (fun b => if b then x else y).
Proof.
  snrapply (Build_Product _ cat_binprod).
  - intros [|].
    + exact cat_pr1.
    + exact cat_pr2.
  - intros z f.
    apply cat_binprod_corec.
    + exact (f true).
    + exact (f false).
  - intros z f [|].
    + apply cat_binprod_beta_pr1.
    + apply cat_binprod_beta_pr2.
  - intros z f g p.
    apply cat_binprod_eta_pr.
    + exact (p true).
    + exact (p false).
Defined.

(** *** Operations on indexed products *)

(** We can take the disjoint union of the index set of an indexed product if we have all binary products. This is useful for associating products in a canonical way. This leads to symmetry and associativity of binary products. *)

Definition cat_prod_index_sum {I I' : Type} {A : Type} `{HasBinaryProducts A}
  (x : I -> A) (y : I' -> A)
  : Product I x -> Product I' y -> Product (I + I') (sum_rect _ x y).
Proof.
  intros p q.
  snrapply Build_Product.
  - exact (cat_binprod (cat_prod I x) (cat_prod I' y)).
  - intros [i | i'].
    + exact (cat_pr _ $o cat_pr1).
    + exact (cat_pr _ $o cat_pr2).
  - intros z f.
    apply cat_binprod_corec.
    + apply cat_prod_corec.
      exact (f o inl).
    + apply cat_prod_corec.
      exact (f o inr).
  - intros z f [i | i'].
    + refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L cat_binprod_beta_pr1 _ _) $@ _).
      rapply cat_prod_beta.
    + refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L cat_binprod_beta_pr2 _ _) $@ _).
      rapply cat_prod_beta.
  - intros z f g r.
    rapply cat_binprod_eta_pr.
    + rapply  cat_prod_pr_eta.
      intros i.
      exact ((cat_assoc _ _ _)^$ $@ r (inl i) $@ cat_assoc _ _ _).
    + rapply  cat_prod_pr_eta.
      intros i'.
      exact ((cat_assoc _ _ _)^$ $@ r (inr i') $@ cat_assoc _ _ _).
Defined.

(** *** Symmetry of products *)

Section Symmetry.

  (** The requirement of having all binary products can be weakened further to having specific binary products, but it is not clear this is a useful generality. *)
  Context {A : Type} `{HasEquivs A} `{!HasBinaryProducts A}.

  Definition cat_binprod_swap (x y : A) : cat_binprod x y $-> cat_binprod y x
    := cat_binprod_corec cat_pr2 cat_pr1.

  Lemma cat_binprod_swap_cat_binprod_swap (x y : A)
    : cat_binprod_swap x y $o cat_binprod_swap y x $== Id _.
  Proof.
    apply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine (cat_binprod_beta_pr1 _ _ $@R _ $@ _).
      refine (cat_binprod_beta_pr2 _ _ $@ _).
      exact (cat_idr _)^$.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine (cat_binprod_beta_pr2 _ _ $@R _ $@ _).
      refine (cat_binprod_beta_pr1 _ _ $@ _).
      exact (cat_idr _)^$.
  Defined.

  Lemma cate_binprod_swap (x y : A)
    : cat_binprod x y $<~> cat_binprod y x.
  Proof.
    snrapply cate_adjointify.
    1,2: apply cat_binprod_swap.
    all: apply cat_binprod_swap_cat_binprod_swap.
  Defined.

End Symmetry.

Section Symmetry2.

  (** Here is an alternative proof of symmetry of products using the symmetry of the indexing set. It has the same action on products but this result is more general since it doesn't require the existence of all products. *)

  Context {A : Type} `{HasEquivs A} (x y : A) (B : BinaryProduct x y).

  Local Instance product_swap : BinaryProduct y x.
  Proof.
    snrapply Build_BinaryProduct.
    - exact (cat_binprod x y).
    - exact cat_pr2.
    - exact cat_pr1.
    - intros z f g.
      exact (cat_binprod_corec g f).
    - intros z f g.
      exact (cat_binprod_beta_pr2 g f).
    - intros z f g.
      exact (cat_binprod_beta_pr1 g f).
    - intros z f g p q.
      exact (cat_binprod_eta_pr _ _ q p).
  Defined.

  Lemma cate_binprod_swap2 : cat_binprod x y $<~> cat_binprod y x.
  Proof.
    snrapply cate_cat_prod.
    1: exact equiv_negb.
    intros [|]; reflexivity.
  Defined.

End Symmetry2.

(** *** Product functor *)

(** Binary products are functorial in each argument. *)

Section BinaryProductsFunctorial.

  Local Instance isgraph_bool_discrete : IsGraph Bool
    := Build_IsGraph Bool (fun a b => match a, b with
                          | true, true => Unit
                          | false, false => Unit
                          | _, _ => Empty end).

  Local Instance is0functor_bin {A : Type} `{Is01Cat A} (x y : A)
    : Is0Functor (fun (b : Bool) => if b then x else y).
  Proof.
    snrapply Build_Is0Functor.
    intros [|] [|] []; reflexivity.
  Defined.

  Definition bin_functor {A : Type} `{Is01Cat A} (x y : A) : Fun01 Bool A
    := Build_Fun01 Bool A (fun b => if b then x else y).

  Local Instance is0functor_bin_l {A : Type} `{Is1Cat A} (y : A)
    : Is0Functor (fun x => bin_functor x y).
  Proof.
    apply Build_Is0Functor.
    intros c d f.
    snrapply Build_NatTrans.
    - intros [|].
      + exact f.
      + reflexivity.
    - intros [|] [|]; intros [].
      + exact ((cat_idr _) $@ (cat_idl _)^$).
      + reflexivity.
  Defined.

  Local Instance is1functor_bin_l {A : Type} `{Is1Cat A} (y : A)
    : Is1Functor (fun x => bin_functor x y).
  Proof.
    apply Build_Is1Functor.
    - intros c d f g p [|].
      + exact p.
      + reflexivity.
    - intros c [|]; reflexivity.
    - intros c d e f g [|].
      + reflexivity.
      + exact ((cat_idl _)^$ $o Id _).
  Defined.

  Local Instance is0functor_bin_r {A : Type} `{Is1Cat A} (x : A)
    : Is0Functor (fun y => bin_functor x y).
  Proof.
    apply Build_Is0Functor.
    intros c d f.
    snrapply Build_NatTrans.
    - intros [|].
      + reflexivity.
      + exact f.
    - intros [|] [|]; intros [].
      + reflexivity.
      + exact ((cat_idr _) $@ (cat_idl _)^$).
  Defined.

  Local Instance is1functor_bin_r {A : Type} `{Is1Cat A} (x : A)
    : Is1Functor (fun y => bin_functor x y).
  Proof.
    apply Build_Is1Functor.
    - intros c d f g p [|].
      + reflexivity.
      + exact p.
    - intros c [|]; reflexivity.
    - intros c d e f g [|].
      + exact ((cat_idl _)^$ $o Id _).
      + reflexivity.
  Defined.

  Global Instance is0functor_cat_binprod_l' {A : Type} `{HasProducts Bool A}
    (y : A)
    : Is0Functor (fun x => cat_binprod x y).
  Proof.
    refine (is0functor_homotopic (fun x => cat_prod Bool (bin_functor x y)) _ _).
    - exact (is0functor_compose (fun x => bin_functor x y) _).
    - reflexivity.
  Defined.

  Global Instance is1functor_cat_binprod_l' {A : Type} `{HasProducts Bool A}
    (y : A)
    : Is1Functor (fun x => cat_binprod x y).
  Proof.
    refine (is1functor_homotopic (fun x => cat_prod Bool (bin_functor x y)) _ _).
    - exact (is1functor_compose (fun x => bin_functor x y) _).
  Defined.

  Global Instance is0functor_cat_binprod_r' {A : Type} `{HasProducts Bool A}
    (x : A)
    : Is0Functor (fun y => cat_binprod x y).
  Proof.
    refine (is0functor_homotopic (fun y => cat_prod Bool (bin_functor x y)) _ _).
    - exact (is0functor_compose (fun y => bin_functor x y) _).
    - reflexivity.
  Defined.

  Global Instance is1functor_cat_binprod_r' {A : Type} `{HasProducts Bool A}
    (x : A)
    : Is1Functor (fun y => cat_binprod x y).
  Proof.
    refine (is1functor_homotopic (fun y => cat_prod Bool (bin_functor x y)) _ _).
    - exact (is1functor_compose (fun y => bin_functor x y) _).
  Defined.

End BinaryProductsFunctorial.

Global Instance is0functor_cat_binprod_l {A : Type} `{HasBinaryProducts A}
  (y : A)
  : Is0Functor (fun x => cat_binprod x y).
Proof.
  snrapply Build_Is0Functor.
  intros a b f.
  apply cat_binprod_corec.
  - exact (f $o cat_pr1).
  - exact cat_pr2.
Defined.

Global Instance is1functor_cat_binprod_l {A : Type} `{HasBinaryProducts A}
  (y : A)
  : Is1Functor (fun x => cat_binprod x y).
Proof.
  snrapply Build_Is1Functor.
  - intros a b f g p.
    simpl.
    apply cat_binprod_corec_eta.
    2: apply Id.
    exact (p $@R cat_pr1).
  - intros x.
    simpl.
    apply cat_binprod_eta_pr.
    + refine (cat_binprod_beta_pr1 _ _ $@ _).
      exact (cat_idl _ $@ (cat_idr _)^$).
    + refine (cat_binprod_beta_pr2 _ _ $@ _).
      exact (cat_idr _)^$.
  - intros x z w f g.
    simpl.
    apply cat_binprod_eta_pr.
    + refine (cat_binprod_beta_pr1 _ _ $@ _).
      refine (_ $@ cat_assoc _ _ _).
      refine (_ $@ ((cat_binprod_beta_pr1 _ _)^$ $@R _)).
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
      exact (cat_binprod_beta_pr1 _ _)^$.
    + refine (cat_binprod_beta_pr2 _ _ $@ _).
      refine (_ $@ cat_assoc _ _ _).
      refine (_ $@ ((cat_binprod_beta_pr2 _ _)^$ $@R _)).
      exact (cat_binprod_beta_pr2 _ _)^$.
Defined.

Global Instance is0functor_cat_binprod_r {A : Type}
  `{HasBinaryProducts A} x
  : Is0Functor (fun y => cat_binprod x y).
Proof.
  snrapply Build_Is0Functor.
  intros a b f.
  apply cat_binprod_corec.
  - exact cat_pr1.
  - exact (f $o cat_pr2).
Defined.

Global Instance is1functor_cat_binprod_r {A : Type}
  `{HasBinaryProducts A} x
  : Is1Functor (fun y => cat_binprod x y).
Proof.
  snrapply Build_Is1Functor.
  - intros y z f g p.
    apply cat_binprod_corec_eta.
    1: apply Id.
    exact (p $@R cat_pr2).
  - intros y. simpl.
    refine (_ $@ cat_binprod_eta _).
    apply cat_binprod_corec_eta.
    + symmetry.
      apply cat_idr.
    + exact (cat_idl _ $@ (cat_idr _)^$).
  - intros y z w f g.
    simpl.
    apply cat_binprod_eta_pr.
    + refine (cat_binprod_beta_pr1 _ _ $@ _).
      refine (_ $@ cat_assoc _ _ _).
      refine (_ $@ ((cat_binprod_beta_pr1 _ _)^$ $@R _)).
      exact (cat_binprod_beta_pr1 _ _)^$.
    + refine (cat_binprod_beta_pr2 _ _ $@ _).
      refine (_ $@ cat_assoc _ _ _).
      refine (_ $@ ((cat_binprod_beta_pr2 _ _)^$ $@R _)).
      refine (_ $@ (cat_assoc _ _ _)^$).
      refine (cat_assoc _ _ _ $@ _).
      exact (_ $@L cat_binprod_beta_pr2 _ _)^$.
Defined.

(** [cat_binprod_corec] is also functorial in each morphsism. *)

Global Instance is0functor_cat_binprod_corec_l {A : Type}
  `{HasBinaryProducts A} {x y z : A} (g : z $-> y)
  : Is0Functor (fun f : z $-> y => cat_binprod_corec f g).
Proof.
  snrapply Build_Is0Functor.
  intros f f' p.
  by apply cat_binprod_corec_eta.
Defined.

Global Instance is0functor_cat_binprod_corec_r {A : Type}
  `{HasBinaryProducts A} {x y z : A} (f : z $-> x)
  : Is0Functor (fun g : z $-> x => cat_binprod_corec f g).
Proof.
  snrapply Build_Is0Functor.
  intros g h p.
  by apply cat_binprod_corec_eta.
Defined.

(** Since we use the Yoneda lemma in this file, we therefore depend on WildCat.Universe which means this instance has to therefore live here. *)
Global Instance hasbinaryproducts_type : HasBinaryProducts Type.
Proof.
  intros X Y.
  snrapply Build_BinaryProduct.
  - exact (X * Y).
  - exact fst.
  - exact snd.
  - intros Z f g z. exact (f z, g z).
  - reflexivity.
  - reflexivity.
  - intros Z f g p q x.
    apply path_prod.
    + exact (p x).
    + exact (q x).
Defined.

(** *** Associativity of products *)

Section Associativity.

  Context {A : Type} `{HasEquivs A} `{!HasBinaryProducts A}.

  Definition cat_binprod_twist (x y z : A)
    : cat_binprod x (cat_binprod y z) $-> cat_binprod y (cat_binprod x z).
  Proof.
    apply cat_binprod_corec.
    - exact (cat_pr1 $o cat_pr2).
    - exact (fmap (fun y => cat_binprod x y) cat_pr2).
  Defined.

  Lemma cat_binprod_twist_cat_binprod_twist (x y z : A)
    : cat_binprod_twist x y z $o cat_binprod_twist y x z $== Id _.
  Proof.
    unfold cat_binprod_twist.
    apply cat_binprod_eta_pr.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine (cat_binprod_beta_pr1 _ _ $@R _ $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine (_ $@L cat_binprod_beta_pr2 _ _ $@ _).
      refine (cat_binprod_beta_pr1 _ _ $@ _).
      exact (cat_idr _)^$.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine (cat_binprod_beta_pr2 _ _ $@R _ $@ _).
      apply cat_binprod_eta_pr.
      + refine ((cat_assoc _ _ _)^$ $@ _).
        refine (cat_binprod_beta_pr1 _ _ $@R _ $@ _).
        refine (cat_binprod_beta_pr1 _ _ $@ _).
        refine (_ $@L _).
        exact (cat_idr _)^$.
      + refine ((cat_assoc _ _ _)^$ $@ _).
        refine (cat_binprod_beta_pr2 _ _ $@R _ $@ _).
        refine (cat_assoc _ _ _ $@ _).
        refine (_ $@L cat_binprod_beta_pr2 _ _ $@ _).
        refine (cat_binprod_beta_pr2 _ _ $@ _).
        refine (_ $@L _).
        exact (cat_idr _)^$.
  Defined.

  Definition cate_binprod_twist (x y z : A)
    : cat_binprod x (cat_binprod y z) $<~> cat_binprod y (cat_binprod x z).
  Proof.
    snrapply cate_adjointify.
    1,2: apply cat_binprod_twist.
    1,2: apply cat_binprod_twist_cat_binprod_twist.
  Defined.

  Lemma cate_binprod_assoc (x y z : A)
    : cat_binprod x (cat_binprod y z) $<~> cat_binprod (cat_binprod x y) z.
  Proof.
    refine (cate_binprod_swap _ _ $oE _).
    refine (cate_binprod_twist _ _ _ $oE _).
    refine (emap (fun y => cat_binprod x y) _).
    exact (cate_binprod_swap _ _).
  Defined.

End Associativity.
