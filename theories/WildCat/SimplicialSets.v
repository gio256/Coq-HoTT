Require Import Basics.Overture.
Require Import Basics.Tactics.
Require Import Basics.PathGroupoids.
Require Import Basics.Trunc.
Require Import Spaces.Nat.
Require Import Spaces.Finite.
Require Import WildCat.Core.
Require Import WildCat.Paths.
Require Import WildCat.Displayed.
Require Import WildCat.Opposite.
Require Import WildCat.FunctorCat.
Require Import WildCat.NatTrans.

Local Open Scope nat_scope.

Definition chain (n : nat) := Fin n.+1.
Notation "[ n ]" := (chain n).

Local Instance isgraph_chain (n : nat) : IsGraph [n].
Proof.
  nrapply Build_IsGraph.
  intros x y.
  exact (nat_fin _ x <= nat_fin _ y).
Defined.

Local Instance is2graph_chain (n : nat) : Is2Graph [n]
  := fun x y => isgraph_paths (x $-> y).

Local Instance is01cat_chain (n : nat) : Is01Cat [n].
Proof.
  snrapply Build_Is01Cat.
  - intros x.
    nrapply leq_refl.
  - intros a b c p q.
    exact (leq_trans q p).
Defined.

Local Instance is1cat_chain (n : nat) : Is1Cat [n].
Proof.
  rapply Build_Is1Cat.
  all: intros; rapply contr_inhabited_hprop.
Defined.

(** delta is the category with objects the natural numbers and morphisms [m -> n] order preserving functions from [m] to [n]. *)
Local Instance isgraph_delta : IsGraph nat
  := {| Hom := fun m n => Fun01 [m] [n] |}.

(** According to the nlab, 2-cells in the 2-category delta are given by the pointwise order on monotone functions, but we need a 1-category. *)
Local Instance is2graph_delta : Is2Graph nat
  := fun m n => isgraph_paths (m $-> n).
  (* := fun _ _ => isgraph_fun01 _ _. *)

Local Instance is01cat_delta : Is01Cat nat.
Proof.
  nrapply Build_Is01Cat.
  - intros n.
    exact (Build_Fun01 _ _ idmap).
  - intros a b c F G.
    exact (Build_Fun01 _ _ (F o G)).
Defined.

Local Instance is1cat_delta : Is1Cat nat.
Proof.
  rapply Build_Is1Cat.
  all: by reflexivity.
Defined.

Definition simplicial_object (B : Type) `{IsGraph B} := Fun11 nat^op B.
