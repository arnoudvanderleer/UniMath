Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.PresheafCategory.
Require Import UniMath.AlgebraicTheories.PresheafMorphisms.
Require Import UniMath.AlgebraicTheories.Presheaves.

Local Open Scope algebraic_theories.
Local Open Scope cat.

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

End AlgebraicTheoryToLawvereTheory.

Section PresheafEquivalence.

  Context (T : algebraic_theory).

  Definition algebraic_presheaf_to_lawvere_presheaf_ob
    (P : presheaf T)
    : (lawvere_theory T)^op ⟶ SET.
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

  Definition algebraic_presheaf_to_lawvere_presheaf_mor
    {P P' : presheaf T}
    (f : presheaf_morphism P P')
    : PreShv (lawvere_theory T) ⟦algebraic_presheaf_to_lawvere_presheaf_ob P, algebraic_presheaf_to_lawvere_presheaf_ob P'⟧.
  Proof.
    use make_nat_trans.
    - exact f.
    - intros m n s.
      apply funextfun.
      intro t.
      apply presheaf_morphism_commutes_with_action.
  Defined.

  Definition algebraic_presheaf_to_lawvere_presheaf
    : presheaf_cat T ⟶ PreShv (lawvere_theory T).
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact algebraic_presheaf_to_lawvere_presheaf_ob.
      + exact (λ _ _, algebraic_presheaf_to_lawvere_presheaf_mor).
    - split.
      + intro P.
        apply nat_trans_eq_alt.
        intro n.
        apply funextfun.
        intro x.
        apply (presheaf_identity_on_element P).
      + intros P P' P'' f g.
        apply nat_trans_eq_alt.
        intro n.
        apply presheaf_mor_comp.
  Defined.

  Definition lawvere_presheaf_to_algebraic_presheaf_ob
    (P : (lawvere_theory T)^op ⟶ SET)
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

  Definition lawvere_presheaf_to_algebraic_presheaf_mor
    {P P' : (lawvere_theory T)^op ⟶ SET}
    (f : P ⟹ P')
    : presheaf_cat T ⟦lawvere_presheaf_to_algebraic_presheaf_ob P, lawvere_presheaf_to_algebraic_presheaf_ob P'⟧.
  Proof.
    use (make_presheaf_morphism' (P := lawvere_presheaf_to_algebraic_presheaf_ob P) (P' := lawvere_presheaf_to_algebraic_presheaf_ob P')).
    - exact f.
    - intros m n a t.
      apply (eqtohomot (nat_trans_ax f _ _ _)).
  Defined.

  Section AlgebraicPresheafIso.

    Context (P : presheaf T).

    Definition algebraic_presheaf_iso_mor
      : presheaf_cat T ⟦lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P), P⟧.
    Proof.
      use (make_presheaf_morphism' (P := lawvere_presheaf_to_algebraic_presheaf_ob _)).
      - intro n.
        apply idfun.
      - abstract easy.
    Defined.

    Definition algebraic_presheaf_iso_inv
      : presheaf_cat T ⟦P, lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P)⟧.
    Proof.
      use (make_presheaf_morphism' (P' := lawvere_presheaf_to_algebraic_presheaf_ob _)).
      - intro n.
        apply idfun.
      - abstract easy.
    Defined.

    Lemma algebraic_presheaf_iso_is_iso
      : is_inverse_in_precat algebraic_presheaf_iso_mor algebraic_presheaf_iso_inv.
    Proof.
      split.
      - apply subtypePath.
        {
          intro.
          use isapropdirprod.
          - do 4 (apply impred_isaprop; intro).
            apply setproperty.
          - apply isapropunit.
        }
        apply nat_trans_eq_alt.
        intro n.
        refine (presheaf_mor_comp (P := lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P)) (P'' := lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P)) _ _ _ @ !_).
        apply funextfun.
        intro t.
        apply presheaf_identity_on_element.
      - use (presheaf_morphism_eq (P := (P : presheaf T)) (P' := (P : presheaf T))).
        intro n.
        refine (presheaf_mor_comp (P := (P : presheaf T)) (P'' := (P : presheaf T)) _ _ _ @ !_).
        apply funextfun.
        intro t.
        apply presheaf_identity_on_element.
    Qed.

    Definition algebraic_presheaf_iso
      : z_iso (C := presheaf_cat T) (lawvere_presheaf_to_algebraic_presheaf_ob (algebraic_presheaf_to_lawvere_presheaf_ob P)) P
      := make_z_iso
          algebraic_presheaf_iso_mor
          algebraic_presheaf_iso_inv
          algebraic_presheaf_iso_is_iso.

  End AlgebraicPresheafIso.

  Definition lawvere_presheaf_iso
    (P : (lawvere_theory T)^op ⟶ SET)
    : z_iso (C := PreShv (lawvere_theory T)) (algebraic_presheaf_to_lawvere_presheaf_ob (lawvere_presheaf_to_algebraic_presheaf_ob P)) P.
  Proof.
    apply idtoiso.
    apply (functor_eq _ _ (homset_property _)).
    now use functor_data_eq.
  Defined.

  Definition fully_faithful
    : fully_faithful algebraic_presheaf_to_lawvere_presheaf.
  Proof.
    intros P P'.
    use isweq_iso.
    - intro f.
      exact (inv_from_z_iso (algebraic_presheaf_iso P) · lawvere_presheaf_to_algebraic_presheaf_mor f · algebraic_presheaf_iso P').
    - intro.
      apply (presheaf_morphism_eq (P := (P : presheaf T)) (P' := (P' : presheaf T))).
      intro n.
      exact (presheaf_mor_comp _ _ _ @ maponpaths (λ x, x · _) (presheaf_mor_comp _ _ _)).
    - intro.
      apply nat_trans_eq_alt.
      intro n.
      exact (presheaf_mor_comp _ _ _ @ maponpaths (λ x, x · _) (presheaf_mor_comp _ _ _)).
  Defined.

  Definition algebraic_presheaf_weq_lawere_presheaf
    : adj_equivalence_of_cats algebraic_presheaf_to_lawvere_presheaf.
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_presheaf_cat.
    - exact fully_faithful.
    - intro P.
      apply hinhpr.
      exists (lawvere_presheaf_to_algebraic_presheaf_ob P).
      apply lawvere_presheaf_iso.
  Defined.

End PresheafEquivalence.
