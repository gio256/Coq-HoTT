Require Import Basics.Overture.
Require Import Basics.Tactics.
Require Import Basics.PathGroupoids.
Require Import Types.Sigma.
Require Import Category.Core.

Local Notation "x --> y" := (@morphism _ x y) : type_scope.
Reserved Notation "g 'o'' f" (at level 40, left associativity).

Class DGraph {A : PreCategory} (D : A -> Type)
  := dhom : forall {a b : A}, (a --> b) -> D a -> D b -> Type.

Class DRTGraph {A : PreCategory} (D : A -> Type) `{DGraph A D} :=
{
  did : forall {a : A} (a' : D a), dhom (identity a) a' a';
  dcomp : forall {a b c : A} {a' : D a} {b' : D b} {c' : D c}
    {g : b --> c} {f : a --> b} (g' : dhom g b' c') (f' : dhom f a' b'),
    dhom (g o f) a' c';
}.

Notation "g 'o'' f" := (dcomp g f).

Class DCat {A : PreCategory} (D : A -> Type) `{DRTGraph A D} :=
{
  didl : forall {a b : A} {a' : D a} {b' : D b} {f : a --> b}
    (f' : dhom f a' b'), (transport (fun g => dhom g a' b')
    (left_identity _ _ _ f) (did b' o' f') = f');
  didr : forall {a b : A} {a' : D a} {b' : D b} {f : a --> b}
    (f' : dhom f a' b'), (transport (fun g => dhom g a' b')
    (right_identity _ _ _ f) (f' o' did a') = f');
  dassoc : forall {a b c d : A} {a' : D a} {b' : D b} {c' : D c} {d' : D d}
    {f : a --> b} {g : b --> c} {h : c --> d} (f' : dhom f a' b')
    (g' : dhom g b' c') (h' : dhom h c' d'), (transport (fun k => dhom k a' d')
    (associativity _ _ _ _ _ _ _ _) ((h' o' g') o' f')) = h' o' (g' o' f');
  trunc : forall {a b : A} {a' : D a} {b' : D b} (f : a --> b),
    IsHSet (dhom f a' b');
}.

Definition dassoc_sym {A : PreCategory} {D : A -> Type} `{DCat A D}
  {a b c d : A} {a' : D a} {b' : D b} {c' : D c} {d' : D d}
  {f : a --> b} {g : b --> c} {h : c --> d} (f' : dhom f a' b')
  (g' : dhom g b' c') (h' : dhom h c' d')
  : (transport (fun k => dhom k a' d') (associativity _ _ _ _ _ _ _ _)^
    (h' o' (g' o' f'))) = (h' o' g') o' f'.
Proof.
  snrapply (moveR_transport_V (fun k => dhom k a' d') _ _ _).
  exact (dassoc f' g' h')^.
Defined.

Definition precat_sigma {A : PreCategory} (D : A -> Type) `{DCat A D}
  : PreCategory.
Proof.
  snrapply Build_PreCategory.
  - exact (sig D).
  - intros [a a'] [b b'].
    exact {f : a --> b & dhom f a' b'}.
  - intros [a a'].
    exact (identity a; did a').
  - intros aa' bb' cc' [g g'] [f f'].
    exact (compose g f; dcomp g' f').
  - intros aa' bb' cc' dd' [f f'] [g g'] [h h'].
    exact (path_sigma' _ (@associativity _ _ _ _ _ f g h) (dassoc f' g' h')).
  - intros aa' bb' [f f'].
    exact (path_sigma' _ (left_identity _ _ _ f) (didl f')).
  - intros aa' bb' [f f'].
    exact (path_sigma' _ (right_identity _ _ _ f) (didr f')).
  - intros aa' bb'.
    srapply istrunc_sigma.
    apply trunc.
Defined.
