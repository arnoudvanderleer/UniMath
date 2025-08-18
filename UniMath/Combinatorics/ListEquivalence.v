Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FLists.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.VectorEquivalence.


Definition weqListSequence {X} : list X ≃ Sequence X.
Proof.
  intros.
  apply weqfibtototal; intro n.
  apply weqvecfun.
Defined.

Section Test.

  Local Open Scope stn.

  Context {A : UU}.
  Context {a b c d:A}.
  Let x := (a::p b::p c::p d::p[])%plist.
  Goal nth x (●0) = a. apply idpath. Qed.
  Goal nth x (●1) = b. apply idpath. Qed.
  Goal nth x (●2) = c. apply idpath. Qed.
  Goal nth x (●3) = d. apply idpath. Qed.

End Test.
