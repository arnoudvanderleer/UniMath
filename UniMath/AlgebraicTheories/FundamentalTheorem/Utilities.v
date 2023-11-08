Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Algebras.

Local Open Scope vec.

Section ActionVector.

  Context {T : algebraic_theory}.
  Context (A : algebra T).

  Lemma move_action_through_vector {n m : nat} (f : vec (T m : hSet) n) (a : stn m → A):
    weqvecfun _ (vec_map (λ fi, action fi a) f)
     = (λ i, action (weqvecfun _ f i) a).
  Proof.
    apply funextfun.
    intro.
    simpl.
    now rewrite el_vec_map.
  Qed.

  Lemma move_action_through_vector_1 {n : nat} (f : (T n : hSet)) (a : stn n → A) :
        weqvecfun 1 [(action f a)]
      = (λ i, action (weqvecfun 1 [(f)] i) a).
  Proof.
    exact (move_action_through_vector [(f)] _).
  Qed.

  Lemma move_action_through_vector_2 {n : nat} (f g : (T n : hSet)) (a : stn n → A) :
        weqvecfun _ [(action f a ; action g a )]
      = (λ i, action (weqvecfun _ [(f ; g)] i) a).
  Proof.
    exact (move_action_through_vector [(f ; g)] _).
  Qed.

  Lemma move_action_through_vector_3 {n : nat} (f g h : (T n : hSet)) (a : stn n → A) :
        weqvecfun _ [(action f a ; action g a ; action h a )]
      = (λ i, action (weqvecfun _ [(f ; g ; h)] i) a).
  Proof.
    exact (move_action_through_vector [(f ; g ; h)] _).
  Qed.

End ActionVector.

Ltac extend_tuple_1 := (
  rewrite (extend_tuple_last _ _ _ (idpath 0 : stntonat _ (make_stn 1 0 (idpath true)) = 0))
).

Ltac extend_tuple_2_0 := rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 2 0 (idpath true) < 1)).
Ltac extend_tuple_2_1 := rewrite (extend_tuple_last _ _ _ (idpath 1 : stntonat _ (make_stn 2 1 (idpath true)) = 1)).

Ltac extend_tuple_2 :=
  extend_tuple_2_0;
  extend_tuple_2_1.

Ltac extend_tuple_3_0 := rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 0 (idpath true) < 2)).
Ltac extend_tuple_3_1 := rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 1 (idpath true) < 2)).
Ltac extend_tuple_3_2 := rewrite (extend_tuple_last _ _ _ (idpath 2 : stntonat _ (make_stn 3 2 (idpath true)) = 2)).

Ltac extend_tuple_3 :=
  extend_tuple_3_0;
  extend_tuple_3_1;
  extend_tuple_3_2.

Ltac extend_tuple_4_0 := rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 4 0 (idpath true) < 3)).
Ltac extend_tuple_4_1 := rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 4 1 (idpath true) < 3)).
Ltac extend_tuple_4_2 := rewrite (extend_tuple_i _ _ _ _ (idpath true : make_stn 4 2 (idpath true) < 3)).
Ltac extend_tuple_4_3 := rewrite (extend_tuple_last _ _ _ (idpath 3 : stntonat _ (make_stn 4 3 (idpath true)) = 3)).

Ltac extend_tuple_4 :=
  extend_tuple_4_0;
  extend_tuple_4_1;
  extend_tuple_4_2;
  extend_tuple_4_3.
