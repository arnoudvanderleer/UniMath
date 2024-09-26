(**************************************************************************************************

  The category of open subsets

  This file defines the category of open subsets of a topological space, in which the morphisms are
  inclusions. A continuous function between two topological spaces gives a functor in the other
  direction between their categories of opens. These together give an indexed category structure on
  top_cat^op.
  We can also give (opens_cat T) a Grothendieck topology, where a collection (V_i)_i is a covering
  for an object (an open subset) U, if U is contained inside the union of the V_i.

  Contents
  1. The category of opens [opens_cat_ob]
  1.1. It is univalent [is_univalent_opens_cat_ob]
  2. The functor construction [opens_cat_mor]
  3. The indexed category structure [opens_cat]
  4. The Grothendieck topology [opens_cat_Grothendieck_topology]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Categories.PreorderCategories.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.GrothendieckTopos.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.Topology.CategoryTop.
Require Import UniMath.Topology.Topology.

Local Open Scope cat.
Local Open Scope subtype.
Local Open Scope open.

(** * 1. The category of opens *)

Section Ob.

  Context (X : TopologicalSpace).

  Definition open_po : po (@Open X) :=
    make_po _ (isporesrel _ _ (subtype_containment_ispreorder X)).

  Definition opens_cat_ob : category := po_category open_po.

(** ** 1.1. It is univalent *)

  Lemma is_univalent_opens_cat_ob
    : is_univalent opens_cat_ob.
  Proof.
    refine (pr2 (po_category_is_univalent_iff_is_antisymm _ _) _).
    - apply isofhlevel_hsubtype.
      apply isasethsubtype.
    - apply isantisymmresrel.
      apply subtype_containment_isantisymm.
  Defined.

End Ob.

(** * 2. The functor construction *)

Definition opens_cat_mor
  {T T' : TopologicalSpace}
  (F : continuous_function T T')
  : opens_cat_ob T' ⟶ opens_cat_ob T.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (continuous_open_preimage F).
    + intros U V HUV t.
      apply (HUV _).
  - abstract easy.
Defined.

(** * 3. The indexed category structure *)

Definition opens_cat
  : indexed_cat top_cat^op.
Proof.
  use make_indexed_cat.
  - use make_indexed_cat_data.
    + intro T.
      exact (opens_cat_ob T ,, is_univalent_opens_cat_ob T).
    + intros T T'.
      exact opens_cat_mor.
    + intro T.
      exact (nat_trans_id (functor_identity _)).
    + intros T T' T'' F F'.
      exact (nat_trans_id (opens_cat_mor (F · F'))).
  - split.
    + intros T U.
      exists (nat_trans_id (functor_identity _) U).
      abstract easy.
    + intros T T' T'' F F' U.
      exists (nat_trans_id (opens_cat_mor (F · F')) U).
      abstract easy.
  - abstract (
      repeat split;
      intros;
      apply propproperty
    ).
Defined.

(** * 4. The Grothendieck topology *)

(* TODO : upstream a lot of this material *)

Section PoCategorySieve.

  Context {X : UU}.
  Context {P : po X}.
  Context {x : X}.

  (* Definitions *)

  Definition down_type
    : UU
    := ∑ y, P y x.

  Coercion down_type_element
    (y : down_type)
    : X
    := pr1 y.

  Definition down_type_is_down
    (y : down_type)
    : P y x
    := pr2 y.

  Definition down_subtype
    : UU
    := hsubtype down_type.

  Coercion down_subtype_to_subtype
    (f : down_subtype)
    : hsubtype down_type
    := f.

  Definition is_downward_closed
    (f : down_subtype)
    : UU
    := ∏ (y : f)
      (z : X)
      (Hzy : P z (pr1carrier _ y)),
      f (z ,, istrans_po P _ _ _ Hzy (down_type_is_down (pr1carrier _ y))).

  Definition downward_closed_down_subtype
    : UU
    := ∑ f, is_downward_closed f.

  Coercion downward_closed_down_subtype_to_subtype
    (f : downward_closed_down_subtype)
    : down_subtype
    := pr1 f.

  Definition make_downward_closed_down_subtype
    (f : hsubtype down_type)
    (H : is_downward_closed f)
    : downward_closed_down_subtype
    := f ,, H.

  (* Lemmas *)

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

  (* The equivalence *)

  Definition sieve_to_subtype
    (f : sieve (po_category P) x)
    : downward_closed_down_subtype.
  Proof.
    use make_downward_closed_down_subtype.
    - intro y.
      apply (make_hProp ((Subobject_dom f : _ ⟶ _) y : hSet)).
      abstract apply isaprop_po_sieve_dom.
    - abstract (
        intros y z Hzy;
        exact (# (Subobject_dom f : _ ⟶ _) Hzy (pr2 y))
      ).
  Defined.

  Section SubtypeToSieve.

    Context (f : downward_closed_down_subtype).

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
      : subtype_to_functor ⟹ (yoneda (po_category P) x : _ ⟶ _).
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
    (f : downward_closed_down_subtype)
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
    (f : downward_closed_down_subtype)
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
    : sieve (po_category P) x ≃ downward_closed_down_subtype.
  Proof.
    use weq_iso.
    - exact sieve_to_subtype.
    - exact subtype_to_sieve.
    - exact sieve_to_subtype_to_sieve.
    - exact subtype_to_sieve_to_subtype.
  Defined.

End PoCategorySieve.

Definition opens_cat_Grothendieck_topology
  (T : TopologicalSpace)
  : GrothendieckTopology (opens_cat T).
Proof.
  use tpair.
  - intros U f.
    refine ((U : Open) ⊆ (⋃ _)).
    intro V.
    exact (make_hProp (∑ H, sieve_weq_subtype f (V ,, H)) (isaprop_total2 _ _)).
  - repeat split.
    + intros U x HUx.
      apply hinhpr.
      exists (pr1 U).
      refine (make_dirprod _ HUx).
      exists (pr2 U).
      use tpair;
        exact (λ y HUy, HUy).
    + intros U V HVU f HUf x HVx.
      specialize (HUf x (HVU x HVx)).
      revert HUf.
      apply hinhfun.
      intro HUf.
      exists (pr1 HUf ∩ (V : Open))%subtype.
      refine (make_dirprod _ (make_dirprod (pr22 HUf) HVx)).
      exists (isOpen_and _ _ (pr112 HUf) (pr2 V)).
      exists (λ x H, pr2 H).
      use tpair.
      * exists (λ x H, pr2 H).
        refine (# (Subobject_dom f : _ ⟶ _) _ (pr22 (pr12 HUf))).
        exact (λ y H, pr1 H).
      * apply isaprop_subtype_containedIn.
    + intros U f HV x HUx.
      refine (hinhfun _ (HV U (λ x Hx, Hx) x HUx)).
      intro HV'.
      exists (pr1 HV').
      refine (make_dirprod _ (pr22 HV')).
      exists (pr112 HV').
      exists (pr1 (pr212 HV')).
      exact (pr212 (pr212 HV')).
Defined.
