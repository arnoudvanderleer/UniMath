(**************************************************************************************************

  λ-theory morphisms

  Defines what a morphism of λ-theories is.

  Contents
  1. The definition of λ-theory morphisms [lambda_theory_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.LambdaTheories.

Local Open Scope algebraic_theories.

(** * 1. The definition of λ-theory morphisms [lambda_theory_morphism] *)

Definition preserves_app
  {L L' : lambda_theory_data}
  (F : algebraic_theory_morphism L L')
  : UU
  := ∏ n t, F _ (app t) = app (F n t).

Definition preserves_abs
  {L L' : lambda_theory_data}
  (F : algebraic_theory_morphism L L')
  : UU
  := ∏ n t, F _ (abs t) = abs (F (S n) t).

Definition is_lambda_theory_morphism
  {L L' : lambda_theory_data}
  (F : algebraic_theory_morphism L L')
  : UU
  := preserves_app F ×
    preserves_abs F.

Definition make_is_lambda_theory_morphism
  {L L' : lambda_theory_data}
  (F : algebraic_theory_morphism L L')
  (H1 : preserves_app F)
  (H2 : preserves_abs F)
  : is_lambda_theory_morphism F
  := H1 ,, H2.

Definition lambda_theory_morphism
  (L L' : lambda_theory_data)
  : UU
  := (∑ (F : algebraic_theory_morphism L L'),
    is_lambda_theory_morphism F)
    × unit.

Definition make_lambda_theory_morphism
  {L L' : lambda_theory_data}
  (F : algebraic_theory_morphism L L')
  (H : is_lambda_theory_morphism F)
  : lambda_theory_morphism L L'
  := (F ,, H) ,, tt.

Coercion lambda_theory_morphism_to_algebraic_theory_morphism
  {L L' : lambda_theory_data}
  (F : lambda_theory_morphism L L')
  : algebraic_theory_morphism L L'
  := pr11 F.

Definition lambda_theory_morphism_preserves_app
  {L L' : lambda_theory_data}
  (F : lambda_theory_morphism L L')
  (n : nat)
  (t : (L n : hSet))
  : F _ (app t) = app (F _ t)
  := pr121 F n t.

Definition lambda_theory_morphism_preserves_abs
  {L L' : lambda_theory_data}
  (F : lambda_theory_morphism L L')
  (n : nat) (t : (L (S n) : hSet))
  : F _ (abs t) = abs (F _ t)
  := pr221 F n t.

Lemma lambda_theory_morphism_eq
  {L L' : lambda_theory}
  (F F' : lambda_theory_morphism L L')
  (H : ∏ n f, F n f = F' n f)
  : F = F'.
Proof.
  apply subtypePath.
  {
    intro.
    apply isapropunit.
  }
  apply subtypePath.
  {
    intro.
    apply isapropdirprod;
      do 2 (apply impred_isaprop; intro);
      apply setproperty.
  }
  apply algebraic_theory_morphism_eq.
  exact H.
Qed.

Lemma has_eta_has_beta_preserves_app
  {L L' : lambda_theory}
  {F : algebraic_theory_morphism L L'}
  (HL : has_eta L)
  (HL' : has_beta L')
  (Habs : preserves_abs F)
  : preserves_app F.
Proof.
  intros n t.
  refine (!HL' _ _ @ _).
  refine (maponpaths _ (!Habs _ _) @ _).
  exact (maponpaths (λ x, _ (_ x)) (HL _ _)).
Qed.

Lemma has_beta_has_eta_preserves_abs
  {L L' : lambda_theory}
  {F : algebraic_theory_morphism L L'}
  (HL : has_beta L)
  (HL' : has_eta L')
  (Happ : preserves_app F)
  : preserves_abs F.
Proof.
  intros n t.
  refine (!HL' _ _ @ _).
  refine (maponpaths _ (!Happ _ _) @ _).
  exact (maponpaths (λ x, _ (_ x)) (HL _ _)).
Qed.
