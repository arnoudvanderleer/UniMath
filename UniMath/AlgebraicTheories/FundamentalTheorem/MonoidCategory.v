Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Presheaf.

Require Import UniMath.AlgebraicTheories.FundamentalTheorem.MonoidActions.

Local Open Scope cat.
Local Open Scope multmonoid.

Section MonoidCategory.

  Context (M : monoid).

  Definition monoid_category : category.
  Proof.
    use make_category.
    - use make_precategory_one_assoc.
      + use make_precategory_data.
        * use make_precategory_ob_mor.
          -- exact unit.
          -- intros t t'.
            exact M.
        * intro c.
          exact 1.
        * intros a b c m m'.
          exact (m' * m).
      + repeat split.
        * intros a b f.
          apply runax.
        * intros a b f.
          apply lunax.
        * intros t t' t'' t''' f g h.
          apply assocax.
    - intros a b.
      apply setproperty.
  Defined.

  Definition monoid_presheaf_to_action
    : PreShv monoid_category ⟶ monoid_action_category M.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro P.
        use make_monoid_action.
        * use make_monoid_action_data.
          -- exact ((P : _ ⟶ _) tt).
          -- intros p m.
            exact (# (P : _ ⟶ _) m p).
        * use make_is_monoid_action.
          -- intro x.
            exact (eqtohomot (functor_id P _) _).
          -- intros x m m'.
            exact (eqtohomot (functor_comp P m m') _).
      + intros P P' F.
        use make_monoid_action_morphism.
        * exact ((F : _ ⟹ _) tt).
        * intros x m.
          apply (eqtohomot (nat_trans_ax F _ _ _)).
    - abstract now split;
        repeat intro;
          apply monoid_action_morphism_eq.
  Defined.

  Definition monoid_action_to_presheaf_ob
    (X : monoid_action M)
    : PreShv monoid_category.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro.
        exact (X : hSet).
      + intros a b m x.
        exact (op _ x m).
    - abstract (
        split;
        [ intro t;
          apply funextfun;
          intro x;
          apply monoid_action_unax
        | intros t t' t'' m m';
          apply funextfun;
          intro x;
          apply monoid_action_assocax ]
      ).
  Defined.

  Definition monoid_presheaf_action_equivalence
    : adj_equivalence_of_cats monoid_presheaf_to_action.
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_functor_category.
      apply is_univalent_HSET.
    - intros P P'.
      use isweq_iso.
      + intro f.
        use make_nat_trans.
        * intros t.
          induction t.
          exact (f : monoid_action_morphism _ _ _).
        * abstract (
            intros t t';
            induction t, t';
            intro m;
            apply funextfun;
            intro x;
            apply (monoid_action_morphism_commutes _ f)
          ).
      + abstract (
          intro f;
          apply nat_trans_eq_alt;
          intro t;
          now induction t
        ).
      + abstract (
          intro f;
          now apply monoid_action_morphism_eq
        ).
    - intro X.
      apply hinhpr.
      exists (monoid_action_to_presheaf_ob X).
      apply idtoiso.
      use monoid_action_eq.
      + apply idpath.
      + abstract easy.
  Defined.

End MonoidCategory.
