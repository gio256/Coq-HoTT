Require Import Basics.
Require Import EquivGpd.
Require Import Types.Prod Types.Sum.
Require Import WildCat.Core WildCat.ZeroGroupoid WildCat.Equiv WildCat.Yoneda
               WildCat.Universe WildCat.NatTrans WildCat.Opposite
               WildCat.Products WildCat.FunctorCat.

(** * Categories with coproducts *)

Definition cat_coprod_rec_inv {I A : Type} `{Is1Cat A}
  (coprod : A) (x : I -> A) (z : A) (inj : forall i, x i $-> coprod)
  : yon_0gpd z coprod $-> prod_0gpd I (fun i => yon_0gpd z (x i))
  := cat_prod_corec_inv (A:=A^op) coprod x z inj.

Class Coproduct (I : Type) {A : Type} `{Is1Cat A} (x : I -> A)
  := prod_co_coprod :: Product (A:=A^op) I x.

Definition cat_coprod (I : Type) {A : Type} (x : I -> A) `{Coproduct I _ x} : A
  := cat_prod (A:=A^op) I x.

Definition cat_inj {I : Type} {A : Type} {x : I -> A} `{Coproduct I _ x}
  : forall (i : I), x i $-> cat_coprod I x
  := cat_pr (A:=A^op) (x:=x).

Global Instance cat_isequiv_cat_coprod_rec_inv {I : Type} {A : Type}
  {x : I -> A} `{Coproduct I _ x}
  : forall (z : A), CatIsEquiv (cat_coprod_rec_inv (cat_coprod I x) x z cat_inj)
  := cat_isequiv_cat_prod_corec_inv (A:=A^op) (x:=x).

(** A convenience wrapper for building Coproducts *)
Definition Build_Coproduct (I : Type) {A : Type} `{Is1Cat A} {x : I -> A}
  (cat_coprod : A) (cat_inj : forall (i : I), x i $-> cat_coprod)
  (cat_coprod_rec : forall (z : A),
    (forall (i : I), x i $-> z) -> (cat_coprod $-> z))
  (cat_coprod_beta_inj : forall (z : A) (f : forall i, x i $-> z) (i : I),
    cat_coprod_rec z f $o cat_inj i $== f i)
  (cat_prod_eta_inj : forall (z : A) (f g : cat_coprod $-> z),
    (forall (i : I), f $o cat_inj i $== g $o cat_inj i) -> f $== g)
  : Coproduct I x
  := Build_Product I (A:=A^op) cat_coprod cat_inj cat_coprod_rec
      cat_coprod_beta_inj cat_prod_eta_inj.

Section Lemmata.
  Context (I : Type) {A : Type} {x : I -> A} `{Coproduct I _ x}.

  Definition cate_cat_coprod_rec_inv {z : A}
    : yon_0gpd z (cat_coprod I x) $<~> prod_0gpd I (fun i => yon_0gpd z (x i))
    := cate_cat_prod_corec_inv I (A:=A^op) (x:=x).

  Definition cate_cate_coprod_rec {z : A}
    : prod_0gpd I (fun i => yon_0gpd z (x i)) $<~> yon_0gpd z (cat_coprod I x)
    := cate_cat_prod_corec I (A:=A^op) (x:=x).

  Definition cat_coprod_rec {z : A}
    : (forall i, x i $-> z) -> cat_coprod I x $-> z
    := cat_prod_corec I (A:=A^op) (x:=x).

  Definition cat_coprod_beta {z : A} (f : forall i, x i $-> z)
    : forall i, cat_coprod_rec f $o cat_inj i $== f i
    := cat_prod_beta I (A:=A^op) (x:=x) f.

  Definition cat_coprod_eta {z : A} (f : cat_coprod I x $-> z)
    : cat_coprod_rec (fun i => f $o cat_inj i) $== f
    := cat_prod_eta I (A:=A^op) (x:=x) f.

  Definition natequiv_cat_coprod_rec_inv
    : NatEquiv (fun z => yon_0gpd z (cat_coprod I x))
      (fun z : A => prod_0gpd I (fun i => yon_0gpd z (x i)))
    := natequiv_cat_prod_corec_inv I (A:=A^op) (x:=x).

  Definition cat_coprod_rec_eta {z : A} {f f' : forall i, x i $-> z}
    : (forall i, f i $== f' i) -> cat_coprod_rec f $== cat_coprod_rec f'
    := cat_prod_corec_eta I (A:=A^op) (x:=x).

  Definition cat_coprod_inj_eta {z : A} {f f' : cat_coprod I x $-> z}
    : (forall i, f $o cat_inj i $== f' $o cat_inj i) -> f $== f'
    := cat_prod_pr_eta I (A:=A^op) (x:=x).
End Lemmata.

(** *** Codiagonal / fold map *)

Definition cat_coprod_fold {I : Type} {A : Type} (x : A) `{Coproduct I _ (fun _ => x)}
  : cat_coprod I (fun _ => x) $-> x
  := cat_prod_diag (A:=A^op) x.

(** *** Uniqueness of coproducts *)

(** [I]-indexed coproducts are unique no matter how they are constructed. This is not exactly dual to [cate_cat_prod] because the equivalence we want lives in [A] rather than [A^op].*)
Definition cate_cat_coprod {I J : Type} (ie : I <~> J) {A : Type} `{HasEquivs A}
  (x : I -> A) `{!Coproduct I x} (y : J -> A) `{!Coproduct J y}
  (e : forall (i : I), x i $<~> y (ie i))
  : cat_coprod I x $<~> cat_coprod J y.
Proof.
  apply equiv_op.
  exact (cate_cat_prod (A:=A^op) ie x y (fun i => (e i)^-1$)).
Defined.

Class HasCoproducts (I A : Type) `{Is1Cat A} :=
  has_coproducts :: forall x : I -> A, Coproduct I x.

Global Instance is0functor_cat_coprod (I : Type) `{IsGraph I}
  (A : Type) `{hc : HasCoproducts I A}
  : Is0Functor (fun x : Fun01 I A => cat_coprod I x).
Proof.
  nrapply Build_Is0Functor.
  intros x y f.
  exact (cat_coprod_rec I (fun i => cat_inj i $o f i)).
Defined.

Global Instance is1functor_cat_coprod (I : Type) `{IsGraph I}
  (A : Type) `{HasCoproducts I A}
  : Is1Functor (fun x : Fun01 I A => cat_coprod I x).
Proof.
  nrapply Build_Is1Functor.
  - intros x y f g p.
    exact (cat_coprod_rec_eta I (fun i => cat_inj i $@L p i)).
  - intros x.
    nrefine (_ $@ (cat_coprod_eta I (Id _))).
    exact (cat_coprod_rec_eta I (fun i => cat_idr _ $@ (cat_idl _)^$)).
  - intros x y z f g.
    apply cat_coprod_inj_eta.
    intros i.
    nrefine (cat_coprod_beta _ _ _ $@ _).
    nrefine (_ $@ cat_assoc_opp _ _ _).
    symmetry.
    nrefine (_ $@L cat_coprod_beta _ _ _ $@ _).
    nrefine (cat_assoc_opp _ _ _ $@ _).
    nrefine (cat_coprod_beta _ _ _ $@R _ $@ _).
    apply cat_assoc.
Defined.


(** *** Categories with specific kinds of coproducts *)

Definition coprodempty_equiv_initial {A : Type}
  `{HasCoproducts Empty A, !HasEquivs A} (z : A) `{!IsInitial z}
  : z $<~> cat_coprod Empty (fun _ => z).
Proof.
  snrapply cate_adjointify.
  - exact (mor_initial z _).
  - exact (cat_coprod_rec _ (fun _ => Id z)).
  - nrapply cat_coprod_inj_eta; intros [].
  - exact ((mor_initial_unique z z _)^$ $@ mor_initial_unique z z (Id z)).
Defined.

Class BinaryCoproduct (A : Type) `{Is1Cat A} (x y : A) :=
  prod_co_bincoprod :: BinaryProduct (x : A^op) (y : A^op).

Arguments BinaryCoproduct {A _ _ _ _} x y.

Definition cat_bincoprod {A : Type}  `{Is1Cat  A} (x y : A) `{!BinaryCoproduct x y} : A
  := cat_binprod (x : A^op) y.

Definition cat_inl {A : Type} `{Is1Cat A} {x y : A} `{!BinaryCoproduct x y}
  : x $-> cat_bincoprod x y.
Proof.
  change (cat_binprod (x : A^op) y $-> x).
  exact cat_pr1.
Defined.

Definition cat_inr {A : Type} `{Is1Cat A} {x y : A} `{!BinaryCoproduct x y}
  : y $-> cat_bincoprod x y.
Proof.
  change (cat_binprod (x : A^op) y $-> y).
  exact cat_pr2.
Defined.

Definition Build_BinaryCoproduct {A : Type} `{Is1Cat A} {x y : A}
  (cat_coprod : A) (cat_inl : x $-> cat_coprod) (cat_inr : y $-> cat_coprod)
  (cat_coprod_rec : forall z : A, (x $-> z) -> (y $-> z) -> cat_coprod $-> z)
  (cat_coprod_beta_inl : forall z (f : x $-> z) (g : y $-> z), cat_coprod_rec z f g $o cat_inl $== f)
  (cat_coprod_beta_inr : forall z (f : x $-> z) (g : y $-> z), cat_coprod_rec z f g $o cat_inr $== g)
  (cat_coprod_in_eta : forall z (f g : cat_coprod $-> z), f $o cat_inl $== g $o cat_inl -> f $o cat_inr $== g $o cat_inr -> f $== g)
  : BinaryCoproduct x y
  := Build_BinaryProduct
      (cat_coprod : A^op)
      cat_inl
      cat_inr
      cat_coprod_rec
      cat_coprod_beta_inl
      cat_coprod_beta_inr
      cat_coprod_in_eta.

Section Lemmata.

  Context {A : Type} {x y z : A} `{BinaryCoproduct _ x y}.

  Definition cat_bincoprod_rec (f : x $-> z) (g : y $-> z)
    : cat_bincoprod x y $-> z
    := @cat_binprod_corec A^op _ _ _ _ x y _ _ f g.

  Definition cat_bincoprod_beta_inl (f : x $-> z) (g : y $-> z)
    : cat_bincoprod_rec f g $o cat_inl $== f
    := @cat_binprod_beta_pr1 A^op _ _ _ _ x y _ _ f g.

  Definition cat_bincoprod_beta_inr (f : x $-> z) (g : y $-> z)
    : cat_bincoprod_rec f g $o cat_inr $== g
    := @cat_binprod_beta_pr2 A^op _ _ _ _ x y _ _ f g.

  Definition cat_bincoprod_eta (f : cat_bincoprod x y $-> z)
    : cat_bincoprod_rec (f $o cat_inl) (f $o cat_inr) $== f
    := @cat_binprod_eta A^op _ _ _ _ x y _ _ f.

  Definition cat_bincoprod_eta_inj {f f' : cat_bincoprod x y $-> z}
    : f $o cat_inl $== f' $o cat_inl
      -> f $o cat_inr $== f' $o cat_inr -> f $== f'
    := @cat_binprod_eta_pr A^op _ _ _ _ x y _ _ f f'.

  Definition cat_bincoprod_rec_eta {f f' : x $-> z} {g g' : y $-> z}
    : f $== f' -> g $== g'
      -> cat_bincoprod_rec f g $== cat_bincoprod_rec f' g'
    := @cat_binprod_corec_eta A^op _ _ _ _ x y _ _ f f' g g'.

End Lemmata.

(** *** Categories with binary coproducts *)

Class HasBinaryCoproducts (A : Type) `{Is1Cat A} :=
  binary_coproducts :: forall x y, BinaryCoproduct x y
.

(** ** Symmetry of coproducts *)

Definition cate_bincoprod_swap {A : Type} `{HasEquivs A} {e : HasBinaryCoproducts A} (x y : A)
  : cat_bincoprod x y $<~> cat_bincoprod y x.
Proof.
  exact (@cate_binprod_swap A^op _ _ _ _ _ e _ _).
Defined.

(** ** Associativity of coproducts *)

Lemma cate_coprod_assoc {A : Type} `{HasEquivs A} {e : HasBinaryCoproducts A} (x y z : A)
  : cat_bincoprod x (cat_bincoprod y z) $<~> cat_bincoprod (cat_bincoprod x y) z.
Proof.
  exact (@cate_binprod_assoc A^op _ _ _ _ _ e x y z)^-1$.
Defined.

(** *** Coproduct functor *)

(** Hint: Use [Set Printing Implicit] to see the implicit arguments in the following proofs. *)

Global Instance is0functor_cat_bincoprod_l {A : Type}
  `{H0 : HasBinaryCoproducts A} y
  : Is0Functor (A:=A) (fun x => cat_bincoprod x y).
Proof.
  rapply is0functor_op'.
  exact (is0functor_cat_binprod_l (A:=A^op) (H0:=H0) y).
Defined.

Global Instance is1functor_cat_bincoprod_l {A : Type}
  `{H0 : HasBinaryCoproducts A} y
  : Is1Functor (fun x => cat_bincoprod x y).
Proof.
  rapply is1functor_op'.
  exact (is1functor_cat_binprod_l (A:=A^op) (H0:=H0) y).
Defined.

Global Instance is0functor_cat_bincoprod_r {A : Type}
  `{H0 : HasBinaryCoproducts A} x
  : Is0Functor (fun y => cat_bincoprod x y).
Proof.
  rapply is0functor_op'.
  exact (is0functor_cat_binprod_r (A:=A^op) (H0:=H0) x).
Defined.

Global Instance is1functor_cat_bincoprod_r {A : Type}
  `{H0 : HasBinaryCoproducts A} x
  : Is1Functor (fun y => cat_bincoprod x y).
Proof.
  rapply is1functor_op'.
  exact (is1functor_cat_binprod_r (A:=A^op) (H0:=H0) x).
Defined.

(** *** Coproducts in Type *)

(** [Type] has all binary coproducts *)
Global Instance hasbinarycoproducts_type : HasBinaryCoproducts Type.
Proof.
  intros X Y.
  snrapply Build_BinaryCoproduct.
  - exact (X + Y).
  - exact inl.
  - exact inr.
  - intros Z f g.
    intros [x | y].
    + exact (f x).
    + exact (g y).
  - reflexivity.
  - reflexivity.
  - intros Z f g p q [x | y].
    + exact (p x).
    + exact (q y).
Defined.
