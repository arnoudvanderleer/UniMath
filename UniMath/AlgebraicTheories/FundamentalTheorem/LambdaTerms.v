Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.Tuples.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.LambdaCalculus.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.Utilities.

Local Open Scope vec.

Section Monoid.

  Context {lambda : lambda_calculus}.

  Lemma empty_vector_eq
    (A : UU)
    (v : stn 0 → A)
    : v = (weqvecfun 0 vnil).
  Proof.
    apply funextfun.
    intro i.
    apply fromstn0.
    exact i.
  Qed.

  Lemma inflate_is_lift_constant
    (x : lambda 0)
    : inflate x = subst x (weqvecfun _ vnil).
  Proof.
    apply (maponpaths (subst _)).
    apply empty_vector_eq.
  Qed.

  Definition compose_λ : lambda 2
  := abs (app
    (var (make_stn 3 0 (idpath true)))
    (app
      (var (make_stn 3 1 (idpath true)))
      (var (make_stn 3 2 (idpath true))))).

  Lemma compose_abs_λ
    (n : nat)
    (a : lambda (S n))
    (b : lambda n)
    : subst
        compose_λ
        (weqvecfun 2 [(abs a ; b)])
      = (abs (subst a (extend_tuple
        (λ i, var (dni_lastelement i))
        (app (inflate b) (var lastelement))))).
  Proof.
    unfold compose_λ.
    repeat reduce_lambda.
    extend_tuple_3.
    cbn.
    apply maponpaths.
    repeat reduce_lambda.
    apply maponpaths.
    apply funextfun.
    intro i.
    rewrite <- (homotweqinvweq stnweq i).
    induction (invmap stnweq i);
      refine (maponpaths (λ x, subst (_ x) _) (homotinvweqweq stnweq _) @ !_);
      refine (maponpaths _ (homotinvweqweq stnweq _) @ !_).
    - cbn.
      repeat reduce_lambda.
      now rewrite replace_dni_last.
    - cbn.
      now do 2 reduce_lambda.
  Qed.

  Lemma compose_assoc_λ
    (n : nat)
    (i j k : stn n)
    : subst compose_λ (weqvecfun 2 [(
        subst compose_λ (weqvecfun 2 [(
          var i ;
          var j
        )]) ;
      var k)])
    = subst compose_λ (weqvecfun 2 [(
        var i ;
        subst compose_λ (weqvecfun 2 [(
          var j ;
          var k
        )])
      )]).
  Proof.
    unfold compose_λ.
    cbn -[weqvecfun].
    refine (maponpaths (λ x, subst _ (weqvecfun _ [(x ; _)])) (subst_abs _ _) @ _).
    refine (compose_abs_λ _ _ _ @ _).
    do 15 reduce_lambda.
    apply maponpaths.
    extend_tuple_3.
    cbn -[weqvecfun v extend_tuple].
    repeat reduce_lambda.
    do 2 extend_tuple_3.
    cbn.
    do 29 reduce_lambda.
    now rewrite replace_dni_last.
  Qed.

  Definition I1_λ : lambda 0
    := abs (var (make_stn 1 0 (idpath true))).

  Lemma compose_I1_abs_λ
    {n : nat}
    (a : lambda (S n))
    : subst compose_λ (weqvecfun _ [(subst I1_λ (weqvecfun _ vnil) ; (abs a))])
    = abs a.
  Proof.
    unfold compose_λ, I1_λ.
    repeat reduce_lambda.
    apply maponpaths.
    extend_tuple_3.
    cbn.
    repeat reduce_lambda.
    refine (_ @ subst_l_var _).
    apply maponpaths.
    apply funextfun.
    intro i.
    rewrite <- (homotweqinvweq stnweq i).
    induction (invmap stnweq i) as [i' | i'];
      refine (maponpaths (λ x, subst (_ x) _) (homotinvweqweq stnweq _) @ _);
      cbn;
      now repeat reduce_lambda.
  Qed.

  Lemma compose_I1_abs_0_λ
    (a : lambda 1)
    : subst compose_λ (weqvecfun _ [(I1_λ ; (abs a))])
    = abs a.
  Proof.
    refine (_ @ compose_I1_abs_λ _).
    apply (maponpaths (λ x, _ (_ [(x ; _)]))).
    unfold I1_λ.
    repeat reduce_lambda.
    now extend_tuple_1.
  Qed.

  Lemma I1_runit_λ
    (a : lambda 1)
    : subst compose_λ (weqvecfun 2 [(
        a ;
        inflate I1_λ
      )])
    = subst compose_λ (weqvecfun 2 [(
        inflate I1_λ ;
        a
      )]).
  Proof.
    unfold compose_λ, I1_λ.
    do 2 refine (subst_abs _ _ @ !_).
    apply maponpaths.
    do 4 rewrite subst_app.
    do 6 rewrite subst_var.
    do 2 refine (
      maponpaths (λ x, app x _) (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 0 (idpath true) < 2)) @
      maponpaths (λ x, app _ (app x _)) (extend_tuple_i _ _ _ _ (idpath true : make_stn 3 1 (idpath true) < 2)) @
      maponpaths (λ x, app _ (app _ x)) (extend_tuple_last _ _ _ (idpath 2 : stntonat _ (make_stn 3 2 (idpath true)) = 2)) @ !_).
    cbn.
    do 7 reduce_lambda.
    extend_tuple_1.
    now do 7 reduce_lambda.
  Qed.

End Monoid.

Section Theory.

  Context {lambda : lambda_calculus}.

  Definition I2_λ
    : lambda 0
    := abs (abs (app (var (make_stn 2 0 (idpath true))) (var (make_stn 2 1 (idpath true))))).

  Lemma compose_I2_abs_λ
    {n : nat}
    (a : lambda (S (S n)))
    : subst compose_λ (weqvecfun _ [(subst I2_λ (weqvecfun _ vnil) ; abs (abs a))])
    = abs (abs a).
  Proof.
    unfold compose_λ, I2_λ.
    repeat reduce_lambda.
    extend_tuple_3.
    extend_tuple_2.
    extend_tuple_1.
    cbn.
    repeat reduce_lambda.
    do 2 apply maponpaths.
    refine (_ @ subst_l_var _).
    apply maponpaths.
    apply funextfun.
    intro i.
    rewrite <- (homotweqinvweq stnweq i).
    induction (invmap stnweq i) as [i' | i'];
      refine (maponpaths (λ x, subst (subst (subst (_ x) _) _) _) (homotinvweqweq stnweq _) @ _);
      cbn;
      repeat reduce_lambda.
    - unfold inflate.
      reduce_lambda.
      rewrite <- (homotweqinvweq stnweq i').
      now induction (invmap stnweq i') as [i'' | i''];
        refine (maponpaths (λ x, subst (_ x) _) (homotinvweqweq stnweq _) @ _);
        cbn;
        repeat reduce_lambda.
    - apply idpath.
  Qed.

  Lemma compose_I2_abs_0_λ
    (a : lambda 2)
    : subst compose_λ (weqvecfun _ [(I2_λ ; abs (abs a))])
    = abs (abs a).
  Proof.
    refine (_ @ compose_I2_abs_λ _).
    apply (maponpaths (λ x, _ (_ [(x ; _)]))).
    unfold I2_λ.
    repeat reduce_lambda.
    extend_tuple_2.
    cbn.
    now repeat reduce_lambda.
  Qed.

  Definition compose_2_λ
    : lambda 3
    := abs (app
      (app
        (var (make_stn 4 0 (idpath true)))
        (app
          (var (make_stn 4 1 (idpath true)))
          (var (make_stn 4 3 (idpath true)))))
      (app
        (var (make_stn 4 2 (idpath true)))
        (var (make_stn 4 3 (idpath true))))).

  Lemma compose_compose_2_λ
    {n : nat}
    (a b c d : stn n)
    : subst compose_λ (weqvecfun _ [(
        subst compose_2_λ (weqvecfun _ [(var a ; var b ; var c)]) ;
        var d
      )])
    = subst compose_2_λ (weqvecfun _ [(
        var a ;
        subst compose_λ (weqvecfun _ [(var b ; var d)]) ;
        subst compose_λ (weqvecfun _ [(var c ; var d)])
      )]).
  Proof.
    unfold compose_λ, compose_2_λ.
    rewrite (subst_abs (m := 3)).
    refine (compose_abs_λ _ _ _ @ _).
    repeat reduce_lambda.
    do 2 extend_tuple_4.
    do 2 extend_tuple_3.
    cbn.
    repeat reduce_lambda.
    now rewrite replace_dni_last.
  Qed.

  Lemma compose_2_compose_λ
    {n : nat}
    (a b c d : stn n)
    : subst compose_2_λ
      (weqvecfun 3 [(subst compose_λ (weqvecfun 2 [(var a; var b)]); var c; var d)])
    = subst compose_2_λ
      (weqvecfun 3 [(var a; subst compose_λ (weqvecfun 2 [(var b; var c)]); var d)]).
  Proof.
    unfold compose_2_λ, compose_λ.
    repeat reduce_lambda.
    do 2 extend_tuple_4.
    do 2 extend_tuple_3.
    cbn.
    now repeat reduce_lambda.
  Qed.

  Definition T_λ
    : lambda 0
    := abs (app
      (var (make_stn 1 0 (idpath true)))
      (abs (abs (var (make_stn 3 1 (idpath true)))))).

  Definition F_λ
    : lambda 0
    := abs (app
      (var (make_stn 1 0 (idpath true)))
      (abs (abs (var (make_stn 3 2 (idpath true)))))).

  Definition term_1_λ
    : lambda 1
    := abs (abs (app
      (var (make_stn 3 0 (idpath true)))
      (abs (app
        (app
          (var (make_stn 4 3 (idpath true)))
          (var (make_stn 4 1 (idpath true))))
        (var (make_stn 4 2 (idpath true))))))).

  Lemma term_1_compose_2_λ
    : subst term_1_λ
      (weqvecfun 1
        [(subst compose_2_λ
            (weqvecfun 3
                [(subst compose_λ (weqvecfun 2 [(subst I2_λ (weqvecfun 0 [()]); (var (make_stn 1 0 (idpath true))))]);
                subst (T_λ) (weqvecfun 0 [()]);
                subst (F_λ) (weqvecfun 0 [()]))]))]) =
    subst compose_λ (weqvecfun 2 [(subst I2_λ (weqvecfun 0 [()]); (var (make_stn 1 0 (idpath true))))]).
  Proof.
    unfold term_1_λ, compose_2_λ.
    repeat reduce_lambda.
    extend_tuple_4.
    extend_tuple_4_1.
    extend_tuple_4_2.
    extend_tuple_4_3.
    extend_tuple_3.
    extend_tuple_2.
    set (a := weqvecfun 2 [(_ ; _)]).
    cbn -[a].
    unfold inflate.
    repeat reduce_lambda.
    rewrite (empty_vector_eq (lambda 3) _).
    unfold compose_λ.
    repeat reduce_lambda.
    extend_tuple_3.
    extend_tuple_3.
    cbn.
    repeat reduce_lambda.
    unfold inflate.
    repeat reduce_lambda.
    rewrite (empty_vector_eq (lambda 3) _).
    unfold I2_λ.
    repeat reduce_lambda.
    extend_tuple_2.
    extend_tuple_1.
    unfold inflate.
    repeat reduce_lambda.
    rewrite (empty_vector_eq (lambda 3) _).
    unfold T_λ, F_λ.
    repeat reduce_lambda.
    extend_tuple_3_1.
    extend_tuple_3_2.
    extend_tuple_2.
    extend_tuple_1.
    extend_tuple_1.
    extend_tuple_1.
    cbn.
    now repeat reduce_lambda.
  Qed.

  Definition term_2_λ
    : lambda 2
    := (abs (abs (app
      (app
        (var (make_stn 4 3 (idpath true)))
        (app
          (var (make_stn 4 0 (idpath true)))
          (var (make_stn 4 2 (idpath true)))))
      (app
        (var (make_stn 4 1 (idpath true)))
        (var (make_stn 4 2 (idpath true))))))).

  Lemma compose_2_term_1_λ
    : subst compose_2_λ (weqvecfun 3 [(
        subst term_1_λ (weqvecfun 1 [(
          var (make_stn 3 0 (idpath true))
        )]);
        var (make_stn 3 1 (idpath true));
        var (make_stn 3 2 (idpath true))
      )])
    = subst compose_λ (weqvecfun 2 [(
        var (make_stn 3 0 (idpath true));
        subst term_2_λ (weqvecfun 2 [(
          var (make_stn 3 1 (idpath true));
          var (make_stn 3 2 (idpath true))
        )])
      )]).
  Proof.
    unfold term_2_λ, compose_2_λ, compose_λ, term_1_λ.
    repeat reduce_lambda.
    extend_tuple_4.
    extend_tuple_4.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_2.
    extend_tuple_4_1.
    extend_tuple_4_2.
    extend_tuple_4_3.
    extend_tuple_3.
    cbn.
    now repeat reduce_lambda.
  Qed.

  Lemma compose_T_λ
    : subst compose_λ (weqvecfun 2 [(
        subst T_λ (weqvecfun 0 [()]);
        subst term_2_λ (weqvecfun 2 [(
          (var (make_stn 2 0 (idpath true)));
          (var (make_stn 2 1 (idpath true)))
        )])
      )])
    = subst compose_λ (weqvecfun 2 [(
        subst I1_λ (weqvecfun 0 [()]);
        (var (make_stn 2 0 (idpath true)))
      )]).
  Proof.
    unfold T_λ, term_2_λ, compose_λ, I1_λ.
    repeat reduce_lambda.
    extend_tuple_4.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_3_1.
    extend_tuple_2_1.
    extend_tuple_1.
    cbn.
    now repeat reduce_lambda.
  Qed.

  Lemma compose_F_λ
    : subst compose_λ (weqvecfun 2 [(
        subst F_λ (weqvecfun 0 [()]);
        subst term_2_λ (weqvecfun 2 [(
          (var (make_stn 2 0 (idpath true)));
          (var (make_stn 2 1 (idpath true)))
        )])
      )])
    = subst compose_λ (weqvecfun 2 [(
        subst I1_λ (weqvecfun 0 [()]);
        (var (make_stn 2 1 (idpath true)))
      )]).
  Proof.
    unfold F_λ, term_2_λ, compose_λ, I1_λ.
    repeat reduce_lambda.
    extend_tuple_4.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_3.
    extend_tuple_3_2.
    extend_tuple_1.
    cbn.
    now repeat reduce_lambda.
  Qed.

End Theory.
