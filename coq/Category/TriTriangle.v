Require Import Category.Setoid.
Require Import Category.Type.
Require Import Category.Functor.Type_Setoid.
Require Import Category.RComod.
Require Import Category.RComonadWithCut.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.RelativeComonadWithCut.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.ProductInContext.
Require Import Theory.PushforwardComodule.
Require Import Category.Triangle.
Require Import InfiniteTriangles.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

Section defs.

  Variable (E : 𝑻𝒚𝒑𝒆).

Definition bla : 𝑻𝒓𝒊𝒂𝒏𝒈𝒍𝒆 E.
 exists (tri_cut E).
 exact (TAIL_MOR_alt E).
 Defined.



