Require Import UniMath.Foundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.
Local Open Scope multmonoid.

Section MonoidCategory.

  Context (M : monoid).

  Definition monoid_category : category.
  Proof.
    use make_category.
    - use make_precategory.
      + exact (make_precategory_data
          (make_precategory_ob_mor (unit)
          (λ _ _, M))
          (λ _, 1)
          (λ _ _ _ f g, g * f)
        ).
      + abstract exact (
        ((λ _ _ _, runax _ _) ,,
        (λ _ _ _, lunax _ _)) ,,
        ((λ _ _ _ _ _ _ _, assocax _ _ _ _) ,,
        (λ _ _ _ _ _ _ _, !assocax _ _ _ _))
      ).
    - abstract (
        do 2 intro;
        apply setproperty
      ).
  Defined.

  Definition monoid_presheaf_cat := PreShv monoid_category.

  (* Definition monoid_action_weq_monoid_presheaf
    : monoid_action ≃ ob monoid_presheaf_cat.
  Proof.
    use weq_iso.
    - intro X.
      use make_functor.
      + use make_functor_data.
        * intro.
          exact (X : hSet).
        * intros a b f g.
          exact (op g f).
      + abstract (
          split;
          repeat intro;
          use funextfun;
          intro;
          [ apply monoid_action_unax
          | apply monoid_action_assocax ]
        ).
    - intro P.
      use make_monoid_action.
      + use make_monoid_action_data.
        * exact ((P : _ ⟶ _) tt).
        * intros p m.
          exact (#(P : _ ⟶ _) (m : monoid_category^op⟦tt, tt⟧) p).
      + abstract (
          use make_is_monoid_action;
          [ intro p;
            exact (eqtohomot (functor_id P tt) p)
          | intros p m m';
            apply (eqtohomot (functor_comp P m m')) ]
        ).
    - abstract (
        intros;
        use monoid_action_eq;
        [ apply idpath
        | exact (idpath_transportf _ _) ]
      ).
    - abstract (
        intro P;
        apply (functor_eq _ _ (homset_property _));
        use total2_paths_f;
        [ use funextfun;
          intro u;
          now induction u
        | cbn;
          do 2 (
            refine (transportf_sec_constant _ _ @ _);
            use funextsec;
            intro u;
            induction u
          );
          refine (transportf_sec_constant _ _ @ _);
          use funextsec;
          intro m;
          refine (functtransportf (λ (x : unit → hSet), x tt) (λ x, x → x) _ _ @ _);
          apply TODO ]
      ).
  Defined.

  Definition monoid_action_morphism_weq_monoid_presheaf_hom
    (X X' : monoid_action)
  : monoid_action_morphism X X' ≃ monoid_presheaf_cat⟦monoid_action_weq_monoid_presheaf X, monoid_action_weq_monoid_presheaf X'⟧.
  Proof.
    use weq_iso.
    - intro f.
      use make_nat_trans.
      + intro.
        exact f.
      + abstract (
          intros u u' m;
          use funextfun;
          intro;
          apply monoid_action_morphism_commutes
        ).
    - intro f.
      use make_monoid_action_morphism.
      + exact ((f : nat_trans _ _) tt).
      + intros x m.
        apply (eqtohomot (nat_trans_ax f tt tt m)).
    - abstract now (
        intro f;
        apply monoid_action_morphism_eq
      ).
    - abstract now (
        intro f;
        apply nat_trans_eq_alt;
        intro u;
        induction u
      ).
  Defined. *)

  Definition exponentials_monoid_presheaf_cat
    : Exponentials (C := monoid_presheaf_cat) BinProducts_PreShv
    := Exponentials_PreShv.

End MonoidCategory.
