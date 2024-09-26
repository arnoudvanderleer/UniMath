Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.GrothendieckTopos.
Require Import UniMath.CategoryTheory.Categories.PreorderCategory.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.OrderTheory.Preorders.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.Categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.slicecat.

Local Open Scope cat.

Section PoCategorySieve.

  Context {X : UU}.
  Context {P : po X}.
  Context {x : X}.

  Lemma isaprop_po_sieve_dom
    (y : X)
    (f : sieve (po_category P) x)
    : isaprop ((Subobject_dom f : _ ⟶ _) y : hSet).
  Proof.
    apply invproofirrelevance.
    intros z w.
    apply (invmaponpathsincl _ (presheaf_monic_isincl (Subobject_isM f) _)).
    apply propproperty.
  Qed.

  Definition sieve_to_subtype
    (f : sieve (po_category P) x)
    : downward_closed_down_subtype P x.
  Proof.
    use make_downward_closed_down_subtype.
    - intro y.
      apply (make_hProp ((Subobject_dom f : _ ⟶ _) (down_type_element y) : hSet)).
      abstract apply isaprop_po_sieve_dom.
    - abstract (
        intros y z Hzy;
        exact (# (Subobject_dom f : _ ⟶ _) Hzy (pr2 y))
      ).
  Defined.

  Section SubtypeToSieve.

    Context (f : downward_closed_down_subtype P x).

    Definition subtype_to_functor
      : (po_category P)^op ⟶ SET.
    Proof.
      use make_functor.
      - use make_functor_data.
        + intro y.
          refine (make_hSet (∑ (H : P y x), pr1 f (y ,, H)) _).
          abstract (
            apply isasetaprop;
            apply isaprop_total2
          ).
        + abstract (
            intros y z Hzy Hyx;
            use tpair;
            [ exact (istrans_po P z y x Hzy (pr1 Hyx))
            | exact (pr2 f (make_carrier _ _ (pr2 Hyx)) z Hzy) ]
          ).
      - abstract (
          split;
          repeat intro;
          apply funextfun;
          intro;
          apply isaprop_total2
        ).
    Defined.

    Definition subtype_to_nat_trans
      : subtype_to_functor ⟹ yoneda_objects (po_category P) x.
    Proof.
      use make_nat_trans.
      -- intros y Hyx.
        exact (pr1 Hyx).
      -- abstract (
          do 3 intro;
          apply funextfun;
          intro;
          apply propproperty
        ).
    Defined.

    Lemma subtype_to_isMonic
      : isMonic (C := [_, SET]) subtype_to_nat_trans.
    Proof.
      apply is_nat_trans_monic_from_pointwise_monics.
      intro y.
      apply (invmap (MonosAreInjective_HSET _)).
      apply incl_injectivity.
      apply isinclpr1.
      intro Hyx.
      apply propproperty.
    Qed.

  End SubtypeToSieve.

  Definition subtype_to_sieve
    (f : downward_closed_down_subtype P x)
    : sieve (po_category P) x
    := (subtype_to_functor f ,, tt) ,,
      make_Monic ([_, _]) (subtype_to_nat_trans f) (subtype_to_isMonic f).

  Definition sieve_to_subtype_to_sieve
    (f : sieve (po_category P) x)
    : subtype_to_sieve (sieve_to_subtype f) = f.
  Proof.
    use isotoid.
    - apply is_univalent_slicecat.
      apply is_univalent_monics_cat.
      apply is_univalent_functor_category.
      apply is_univalent_HSET.
    - apply slicecat.weq_z_iso.
      use tpair.
      + apply iso_in_subcategory_of_monics_weq.
        use tpair.
        * use make_nat_trans.
          -- intros y Hy.
            exact (pr2 Hy).
          -- abstract (
              do 3 intro;
              apply funextfun;
              intro;
              apply isaprop_po_sieve_dom
            ).
        * apply nat_trafo_z_iso_if_pointwise_z_iso.
          intro y.
          use (make_is_z_isomorphism _ _ (make_dirprod _ _)).
          -- intro Hfy.
            exists ((Subobject_mor f : _ ⟹ _) y Hfy).
            exact Hfy.
          -- abstract (
              apply funextfun;
              intro H;
              apply (maponpaths (λ x, x ,, _));
              apply propproperty
            ).
          -- abstract easy.
      + abstract (
          apply Monic_eq;
          apply nat_trans_eq_alt;
          intro y;
          apply funextfun;
          intro H;
          apply propproperty
        ).
  Qed.

  Lemma subtype_to_sieve_to_subtype
    (f : downward_closed_down_subtype P x)
    : sieve_to_subtype (subtype_to_sieve f) = f.
  Proof.
    use subtypePath.
    {
      intro.
      do 3 (apply impred_isaprop; intro).
      apply propproperty.
    }
    apply hsubtype_univalence.
    intro y.
    split.
    - intro H.
      refine (transportf _ _ (pr2 H)).
      apply propproperty.
    - intro H.
      exact (pr2 y ,, H).
  Qed.

  Definition sieve_weq_subtype
    : sieve (po_category P) x ≃ downward_closed_down_subtype P x.
  Proof.
    use weq_iso.
    - exact sieve_to_subtype.
    - exact subtype_to_sieve.
    - exact sieve_to_subtype_to_sieve.
    - exact subtype_to_sieve_to_subtype.
  Defined.

End PoCategorySieve.
