(**************************************************************************************************

  The λ-calculus λ-theory

  Given a model for the λ-calculus, this file constructs a λ-theory and shows that it has
  eta and beta equality (since we assume that the λ-calculus has these equalities).

  Contents
  1. The algebraic theory of the λ-calculus [lambda_calculus_algebraic_theory]
  2. The λ-theory of the λ-calculus [lambda_calculus_lambda_theory]
  3. The λ-theory has β-equality [lambda_calculus_has_β]
  4. The λ-theory has η-equality [lambda_calculus_has_η]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaCalculus.
Require Import UniMath.Combinatorics.FVectors.

(** * 1. The algebraic theory of the λ-calculus *)

Section LambdaCalculus.

Variable L : lambda_calculus.

Definition lambda_calculus_algebraic_theory_data
  : algebraic_theory_data
  := make_algebraic_theory_data
    L
    (λ _, var)
    (λ _ _ l targets, subst l targets).

Lemma lambda_calculus_is_algebraic_theory
  : is_algebraic_theory lambda_calculus_algebraic_theory_data.
Proof.
  use make_is_algebraic_theory.
  - intros l m n f_l f_m f_n.
    revert l f_l m f_m n f_n.
    use (lambda_calculus_ind_prop (λ _ _, _ ,, _));
      cbn -[isaprop].
    + do 4 (apply impred; intro).
      apply setproperty.
    + intros.
      now do 2 rewrite var_subst.
    + intros ? ? ? Hl Hl' ? ? ? ?.
      do 3 rewrite subst_app.
      now rewrite Hl, Hl'.
    + intros l f_l Hl m f_m n f_n.
      do 3 rewrite subst_abs.
      rewrite Hl.
      do 2 apply maponpaths.
      refine (append_vec_eq _ _).
      * intro.
        refine (maponpaths (λ x, subst x _) (append_vec_compute_1 _ _ _) @ _).
        rewrite inflate_subst.
        unfold inflate.
        rewrite subst_subst.
        apply maponpaths.
        apply funextfun.
        intro.
        now rewrite var_subst, append_vec_compute_1.
      * now rewrite append_vec_compute_2, var_subst, append_vec_compute_2.
    + intros m n l f Hl Hf m' f_m' n' f_n'.
      rewrite Hl.
      do 2 rewrite subst_subst.
      apply maponpaths.
      apply funextfun.
      intro.
      apply Hf.
  - do 4 intro.
    apply var_subst.
  - use (lambda_calculus_ind_prop (λ _ _, _ ,, _));
      cbn.
    + apply setproperty.
    + intros.
      apply subst_var.
    + intros ? ? ? Hl Hl'.
      now rewrite subst_app, Hl, Hl'.
    + intros n' l Hl.
      rewrite subst_abs.
      apply maponpaths.
      refine (_ @ Hl).
      apply maponpaths.
      exact (!append_vec_eq (λ i, !inflate_var i) (idpath _)).
    + intros ? ? ? ? Hl Hf.
      rewrite subst_subst.
      apply maponpaths.
      apply funextfun.
      intro.
      apply Hf. (* Apparently we don't need Hl in this proof *)
Qed.

Definition lambda_calculus_algebraic_theory
  : algebraic_theory
  := make_algebraic_theory _ lambda_calculus_is_algebraic_theory.

(** * 2. The λ-theory of the λ-calculus *)

Definition lambda_calculus_lambda_theory_data
  : lambda_theory_data.
Proof.
  refine (lambda_calculus_algebraic_theory ,, _ ,, _);
    simpl.
  - intros ? l.
    exact (app (inflate l) (var lastelement)).
  - intro.
    exact abs.
Defined.

Definition lambda_calculus_is_lambda_theory
  : is_lambda_theory lambda_calculus_lambda_theory_data.
Proof.
  split;
    do 4 intro;
    cbn;
    unfold inflate.
  - rewrite subst_app.
    do 2 rewrite subst_subst.
    rewrite var_subst.
    rewrite append_vec_compute_2.
    apply (maponpaths (λ x, _ (_ x) _)).
    apply funextfun.
    intro.
    now rewrite var_subst, append_vec_compute_1.
  - now rewrite subst_abs.
Qed.

Definition lambda_calculus_lambda_theory
  : lambda_theory
  := _ ,, lambda_calculus_is_lambda_theory.

(** * 3. The λ-theory has β-equality *)

Lemma lambda_calculus_has_β
  : has_β lambda_calculus_lambda_theory.
Proof.
  unfold has_β, LambdaTheories.app, LambdaTheories.abs.
  cbn.
  intros n l.
  rewrite inflate_abs.
  rewrite beta_equality.
  rewrite subst_subst.
  refine (_ @ subst_var _).
  apply maponpaths.
  apply funextfun.
  refine (stn_sn_ind _ _).
  - intro i.
    rewrite append_vec_compute_1.
    do 2 rewrite inflate_var.
    rewrite var_subst.
    now rewrite append_vec_compute_1.
  - rewrite append_vec_compute_2.
    rewrite var_subst.
    now rewrite append_vec_compute_2.
Qed.

End LambdaCalculus.
