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

Arguments Coproduct I {A _ _ _ _} x.

Definition cat_coprod (I : Type) {A : Type} (x : I -> A) `{Coproduct I _ x} : A
  := cat_prod (A:=A^op) I x.

Definition cat_inj {I : Type} {A : Type} {x : I -> A} `{Coproduct I _ x}
  : forall i, x i $-> cat_coprod I x
  := cat_pr (A:=A^op) (x:=x).

Global Instance cat_isequiv_cat_coprod_rec_inv {I : Type} {A : Type} {x : I -> A}
  `{Coproduct I _ x}
  : forall z, CatIsEquiv (cat_coprod_rec_inv (cat_coprod I x) x z cat_inj)
  := cat_isequiv_cat_prod_corec_inv (A:=A^op) (x:=x).

Definition Build_Coproduct (I : Type) {A : Type} `{Is1Cat A} {x : I -> A}
  (cat_coprod : A) (cat_inj : forall i, x i $-> cat_coprod)
  (cat_coprod_rec : forall (z : A), (forall i, x i $-> z) -> (cat_coprod $-> z))
  (cat_coprod_beta_inj : forall z (f : forall i, x i $-> z) i,
    cat_coprod_rec z f $o cat_inj i $== f i)
  (cat_prod_eta_inj : forall z (f g : cat_coprod $-> z),
    (forall i, f $o cat_inj i $== g $o cat_inj i) -> f $== g)
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

Definition cat_coprod_fold {I : Type} {A : Type} (x : A) `{Coproduct I _ (fun _ => x)}
  : cat_coprod I (fun _ => x) $-> x
  := cat_prod_diag (A:=A^op) x.

Section Uniqueness.

  (** This is not exactly dual to [cate_cat_prod] because the equivalence we want lives in [A] rather than [A^op]. *)
  Definition cate_cat_coprod {I J : Type} (ie : I <~> J) {A : Type} `{HasEquivs A}
    (x : I -> A) `{!Coproduct I x} (y : J -> A) `{!Coproduct J y}
    (e : forall (i : I), x i $<~> y (ie i))
    : cat_coprod I x $<~> cat_coprod J y.
  Proof.
    apply equiv_op.
    exact (cate_cat_prod (A:=A^op) ie x y (fun i => (e i)^-1$)).
  Defined.

End Uniqueness.

Class HasCoproducts (I A : Type) `{Is1Cat A} :=
  has_coproducts :: forall x : I -> A, Coproduct I x.
  (* has_coproducts :: HasProducts I A^op. *)

(* Global Instance is0functor_cat_coprod (I : Type) `{IsGraph I} *)
(*   (A : Type) `{HasCoproducts I A} *)
(*   : Is0Functor (fun x : Fun01 I A => cat_coprod I x). *)
(* Proof. *)
(*   exact (is0functor_cat_prod I A^op). *)
(* Defined. *)



(** *** Categories with specific kinds of coproducts *)

Class BinaryCoproduct (A : Type) `{Is1Cat A} (x y : A) :=
  prod_co_coprod :: BinaryProduct (x : A^op) (y : A^op).

Arguments BinaryCoproduct {A _ _ _ _} x y.

Definition cat_coprod {A : Type}  `{Is1Cat  A} (x y : A) `{!BinaryCoproduct x y} : A
  := cat_prod (x : A^op) y.

Definition cat_inl {A : Type} `{Is1Cat A} {x y : A} `{!BinaryCoproduct x y} : x $-> cat_coprod x y.
Proof.
  change (cat_prod (x : A^op) y $-> x).
  exact cat_pr1.
Defined.

Definition cat_inr {A : Type} `{Is1Cat A} {x y : A} `{!BinaryCoproduct x y} : y $-> cat_coprod x y.
Proof.
  change (cat_prod (x : A^op) y $-> y).
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

  Definition cate_cat_coprod_rec_inv
    : (opyon_0gpd (cat_coprod x y) z)
    $<~> prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z)
    := @cate_cat_prod_corec_inv A^op x y _ _ _ _ _ _.

  Definition cate_cat_coprod_rec
    : prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z)
    $<~> (opyon_0gpd (cat_coprod x y) z)
    := @cate_cat_prod_corec A^op x y _ _ _ _ _ _.

  Definition cat_coprod_rec (f : x $-> z) (g : y $-> z) : cat_coprod x y $-> z
    := @cat_prod_corec A^op x y _ _ _ _ _ _ f g.

  Definition cat_coprod_beta_inl (f : x $-> z) (g : y $-> z)
    : cat_coprod_rec f g $o cat_inl $== f
    := @cat_prod_beta_pr1 A^op x y _ _ _ _ _ _ f g.

  Definition cat_coprod_beta_inr (f : x $-> z) (g : y $-> z)
    : cat_coprod_rec f g $o cat_inr $== g
    := @cat_prod_beta_pr2 A^op x y _ _ _ _ _ _ f g.

  Definition cat_coprod_eta (f : cat_coprod x y $-> z)
    : cat_coprod_rec (f $o cat_inl) (f $o cat_inr) $== f
    := @cat_prod_eta A^op x y _ _ _ _ _ _ f.

  (* TODO: decompose and move *)
  Local Instance is0functor_coprod_0gpd_helper
    : Is0Functor (fun z : A => prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z)).
  Proof.
    snrapply Build_Is0Functor.
    intros a b f.
    snrapply Build_Morphism_0Gpd.
    - intros [g g'].
      exact (f $o g, f $o g').
    - snrapply Build_Is0Functor.
      intros [g g'] [h h'] [p q].
      split.
      + exact (f $@L p).
      + exact (f $@L q).
  Defined.

  (* TODO: decompose and move *)
  Local Instance is1functor_coprod_0gpd_helper
    : Is1Functor (fun z : A => prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z)).
  Proof.
    snrapply Build_Is1Functor.
    - intros a b f g p [r_fst r_snd].
      cbn; split.
      + refine (_ $@R _).
        apply p.
      + refine (_ $@R _).
        apply p.
    - intros a [r_fst r_snd].
      split; apply cat_idl.
    - intros a b c f g [r_fst r_snd].
      split; apply cat_assoc.
  Defined.

  Definition natequiv_cat_coprod_rec_inv
    : NatEquiv (opyon_0gpd (cat_coprod x y)) (fun z => prod_0gpd (opyon_0gpd x z) (opyon_0gpd y z))
    := @natequiv_cat_prod_corec_inv A^op x y _ _ _ _ _.

  Definition cat_coprod_rec_eta {f f' : x $-> z} {g g' : y $-> z}
    : f $== f' -> g $== g' -> cat_coprod_rec f g $== cat_coprod_rec f' g'
    := @cat_prod_corec_eta A^op x y _ _ _ _ _ _ f f' g g'.

  Definition cat_coprod_in_eta {f f' : cat_coprod x y $-> z}
    : f $o cat_inl $== f' $o cat_inl -> f $o cat_inr $== f' $o cat_inr -> f $== f'
    := @cat_prod_pr_eta A^op x y _ _ _ _ _ _ f f'.

End Lemmata.

(** *** Categories with binary coproducts *)

Class HasBinaryCoproducts (A : Type) `{Is1Cat A} :=
  binary_coproducts :: forall x y, BinaryCoproduct x y
.

(** ** Symmetry of coproducts *)

Definition cate_coprod_swap {A : Type} `{HasEquivs A} {e : HasBinaryCoproducts A} (x y : A)
  : cat_coprod x y $<~> cat_coprod y x.
Proof.
  exact (@cate_prod_swap A^op _ _ _ _ _ e _ _).
Defined.

(** ** Associativity of coproducts *)

Lemma cate_coprod_assoc {A : Type} `{HasEquivs A} {e : HasBinaryCoproducts A} (x y z : A)
  : cat_coprod x (cat_coprod y z) $<~> cat_coprod (cat_coprod x y) z.
Proof.
  exact (@cate_prod_assoc A^op _ _ _ _ _ e x y z)^-1$.
Defined.

(** *** Coproduct functor *)

(** Hint: Use [Set Printing Implicit] to see the implicit arguments in the following proofs. *)

Global Instance is0functor_cat_coprod_l {A : Type}
  `{H0 : HasBinaryCoproducts A} y
  : Is0Functor (A:=A) (fun x => cat_coprod x y).
Proof.
  rapply is0functor_op'.
  exact (is0functor_cat_prod_l (A:=A^op) (H0:=H0) y).
Defined.

Global Instance is1functor_cat_coprod_l {A : Type}
  `{H0 : HasBinaryCoproducts A} y
  : Is1Functor (fun x => cat_coprod x y).
Proof.
  rapply is1functor_op'.
  exact (is1functor_cat_prod_l (A:=A^op) (H0:=H0) y).
Defined.

Global Instance is0functor_cat_coprod_r {A : Type}
  `{H0 : HasBinaryCoproducts A} x
  : Is0Functor (fun y => cat_coprod x y).
Proof.
  rapply is0functor_op'.
  exact (is0functor_cat_prod_r (A:=A^op) (H0:=H0) x).
Defined.

Global Instance is1functor_cat_coprod_r {A : Type}
  `{H0 : HasBinaryCoproducts A} x
  : Is1Functor (fun y => cat_coprod x y).
Proof.
  rapply is1functor_op'.
  exact (is1functor_cat_prod_r (A:=A^op) (H0:=H0) x).
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
