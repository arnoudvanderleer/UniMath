Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Algebra.Monoids.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Presheaves.
Require Import UniMath.AlgebraicTheories.PresheafCategory.
Require Import UniMath.AlgebraicTheories.PresheafMorphisms.
Require Import UniMath.AlgebraicTheories.FundamentalTheorem.MonoidActions.

Local Open Scope algebraic_theories.
Local Open Scope cat.

Section TheoryMonoid.

  Context (T : algebraic_theory).

  Definition theory_monoid : monoid.
  Proof.
    use make_monoid.
    - use make_setwithbinop.
      + exact (T 1).
      + intros a b.
        exact (a • (λ _, b)).
    - use make_ismonoidop.
      + intros a b c.
        apply algebraic_theory_comp_is_assoc.
      + exists (id_pr).
        split.
        * intro m.
          apply algebraic_theory_comp_is_unital.
        * intro m.
          refine (_ @ algebraic_theory_comp_identity_projections _ _ _).
          apply (maponpaths (comp m)).
          apply funextfun.
          intro i.
          refine (algebraic_theory_id_pr_is_pr _ @ _).
          apply maponpaths.
          apply isconnectedstn1.
  Defined.

End TheoryMonoid.

Section MonoidCategory.

  Local Open Scope multmonoid.

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

Section AlgebraicTheoryToLawvereTheory.

  Context (T : algebraic_theory).

  Definition lawvere_theory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact nat.
      + intros m n.
        exact (stn n → (T m : hSet)).
    - intro.
      exact pr.
    - intros l m n g f.
      exact (λ i, f i • g).
  Defined.

  Lemma lawvere_theory_is_precategory
    : is_precategory lawvere_theory_data.
  Proof.
    apply make_is_precategory_one_assoc.
    - intros m n f.
      apply funextfun.
      intro i.
      apply algebraic_theory_comp_identity_projections.
    - intros m n f.
      apply funextfun.
      intro i.
      apply algebraic_theory_comp_projects_component.
    - intros k l m n f g h.
      apply funextfun.
      intro i.
      apply algebraic_theory_comp_is_assoc.
  Qed.

  Lemma lawvere_theory_has_homsets
    : has_homsets lawvere_theory_data.
  Proof.
    intros m n.
    apply funspace_isaset.
    apply setproperty.
  Qed.

  Definition lawvere_theory
    : category
    := make_category
      (make_precategory
        lawvere_theory_data
        lawvere_theory_is_precategory)
      lawvere_theory_has_homsets.

  Definition PL1 : category := PreShv lawvere_theory.

  Definition PL2 : category := presheaf_cat T.

  Definition PL1_to_PL2_ob
    (P : lawvere_theory^op ⟶ SET)
    : presheaf T.
  Proof.
    use make_presheaf'.
    - use make_presheaf'_data.
      + exact P.
      + intros m n a f.
        exact (#P f a).
    - use make_is_presheaf'.
      + intros l m n p f g.
        apply (eqtohomot (!functor_comp P _ _)).
      + intros n p.
        apply (eqtohomot (functor_id P _)).
  Defined.

  Definition PL1_to_PL2_mor
    {P P' : lawvere_theory^op ⟶ SET}
    (f : P ⟹ P')
    : presheaf_morphism (PL1_to_PL2_ob P) (PL1_to_PL2_ob P').
  Proof.
    use make_presheaf_morphism'.
    - exact f.
    - intros m n a t.
      apply (eqtohomot (nat_trans_ax f _ _ _)).
  Defined.

  Definition PL1_to_PL2
    : PL1 ⟶ PL2.
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact PL1_to_PL2_ob.
      + exact (λ _ _, PL1_to_PL2_mor).
    - split.
      + intro P.
        refine (presheaf_morphism_eq (PL1_to_PL2_mor _) _ _).
        intro n.
        apply funextfun.
        intro f.
        exact (!presheaf_identity_on_element (PL1_to_PL2_ob _) _).
      + intros P P' P'' f g.
        refine (presheaf_morphism_eq (PL1_to_PL2_mor _) _ _).
        intro n.
        apply funextfun.
        intro t.
        symmetry.
        refine (eqtohomot _ t).
        apply presheaf_mor_comp.
  Defined.

  Definition PL2_to_PL1_ob
    (P : presheaf T)
    : lawvere_theory^op ⟶ SET.
  Proof.
    simpl.
    use make_functor.
    - use make_functor_data.
      + exact P.
      + intros m n g f.
        exact (action f g).
    - split.
      + intro n.
        apply funextfun.
        intro p.
        apply presheaf_identity_projections.
      + intros l m n f g.
        apply funextfun.
        intro p.
        symmetry.
        apply presheaf_is_assoc.
  Defined.

  Definition PL2_to_PL1_mor
    {P P' : presheaf T}
    (f : presheaf_morphism P P')
    : (PL2_to_PL1_ob P) ⟹ (PL2_to_PL1_ob P').
  Proof.
    use make_nat_trans.
    - exact f.
    - intros m n s.
      apply funextfun.
      intro t.
      apply presheaf_morphism_commutes_with_action.
  Defined.

  Definition equivalence
    : adj_equivalence_of_cats PL1_to_PL2.
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_functor_category.
      apply is_univalent_HSET.
    - intros P P'.
      use isweq_iso.
      + intro f.
        exact (PL2_to_PL1_mor (P := PL1_to_PL2 P) (P' := PL1_to_PL2 P') f).
      + intro.
        now apply nat_trans_eq_alt.
      + intro.
        now apply (presheaf_morphism_eq (P := PL1_to_PL2_ob P) (P' := PL1_to_PL2_ob P')).
    - intro P.
      apply hinhpr.
      exists (PL2_to_PL1_ob P).
      use make_z_iso.
      + use (make_presheaf_morphism' (P := PL1_to_PL2_ob _)).
        * intro n.
          apply idfun.
        * easy.
      + use (make_presheaf_morphism' (P' := PL1_to_PL2_ob _)).
        * intro n.
          apply idfun.
        * easy.
      + split.
        * use (presheaf_morphism_eq (P := PL1_to_PL2_ob (PL2_to_PL1_ob P)) (P' := PL1_to_PL2_ob (PL2_to_PL1_ob P))).
          intro n.
          refine (presheaf_mor_comp (P := PL1_to_PL2_ob (PL2_to_PL1_ob P)) (P'' := PL1_to_PL2_ob (PL2_to_PL1_ob P)) _ _ _ @ !_).
          apply funextfun.
          intro t.
          apply presheaf_identity_on_element.
        * use (presheaf_morphism_eq (P := (P : presheaf T)) (P' := (P : presheaf T))).
          intro n.
          refine (presheaf_mor_comp (P := (P : presheaf T)) (P'' := (P : presheaf T)) _ _ _ @ !_).
          apply funextfun.
          intro t.
          exact (presheaf_identity_on_element _ _).
  Defined.

End AlgebraicTheoryToLawvereTheory.
