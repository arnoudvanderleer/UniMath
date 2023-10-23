Require Import UniMath.Foundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.
Local Open Scope multmonoid.

Definition TODO {A : UU} : A.
Admitted.

Section MonoidAction.

  Context (M : monoid).

  Definition monoid_action_data : UU
    := ∑ (X: hSet), X → M → X.

  Definition make_monoid_action_data
    (X : hSet)
    (op : X → M → X)
    : monoid_action_data
    := X ,, op.

  Coercion monoid_action_data_to_bar (x : monoid_action_data) : hSet := pr1 x.
  Definition op {X : monoid_action_data} : X → M → X := pr2 X.

  Definition is_monoid_action (X : monoid_action_data) :=
    (∏ (x : X), op x (unel M) = x) ×
    (∏ (x : X) y y', op x (y * y') = op (op x y) y').

  Definition make_is_monoid_action
    {X : monoid_action_data}
    (unax : ∏ (x : X), op x (unel M) = x)
    (assocax : ∏ (x : X) y y', op x (y * y') = op (op x y) y')
    : is_monoid_action X
    := unax ,, assocax.

  Definition monoid_action :=
    ∑ (X : monoid_action_data), is_monoid_action X.

  Definition make_monoid_action
    (X : monoid_action_data)
    (H : is_monoid_action X)
    : monoid_action
    := X ,, H.

  Coercion monoid_action_to_monoid_action_data (f : monoid_action) : monoid_action_data := pr1 f.

  Definition monoid_action_unax {X : monoid_action} : ∏ (x : X), op x (unel M) = x := pr12 X.
  Definition monoid_action_assocax {X : monoid_action} : ∏ (x : X) y y', op x (y * y') = op (op x y) y' := pr22 X.

  Lemma isaprop_is_monoid_action (X : monoid_action_data)
    : isaprop (is_monoid_action X).
  Proof.
    apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
      apply setproperty.
  Qed.

  Lemma monoid_action_eq
    (X X' : monoid_action)
    (H1 : (X : hSet) = (X' : hSet))
    (H2 : (transportf (λ x : hSet, x → M → x) H1 op = op))
    : X = X'.
  Proof.
    apply subtypePath.
    {
      intro.
      apply isaprop_is_monoid_action.
    }
    use total2_paths_f.
    - exact H1.
    - exact H2.
  Qed.

  Section MonoidActionHom.

    Context (X X' : monoid_action).

    Definition monoid_action_morphism :=
      ∑ (f : X → X'), ∏ x m, f (op x m) = op (f x) m.

    Definition make_monoid_action_morphism
      (f : X → X')
      (H : ∏ x m, f (op x m) = op (f x) m)
      : monoid_action_morphism
      := f ,, H.

    Definition monoid_action_morphism_to_function (f : monoid_action_morphism) : X → X' := pr1 f.
    Coercion monoid_action_morphism_to_function : monoid_action_morphism >-> Funclass.

    Definition monoid_action_morphism_commutes (f : monoid_action_morphism) (x : X) (m : M)
      : f (op x m) = op (f x) m
      := pr2 f x m.

    Lemma isaprop_is_monoid_action_morphism (f : X → X')
      : isaprop (∏ x m, f (op x m) = op (f x) m).
    Proof.
      do 2 (apply impred_isaprop; intro).
      apply setproperty.
    Qed.

    Lemma monoid_action_morphism_eq
      (f f' : monoid_action_morphism)
      (H : ∏ x, f x = f' x)
      : f = f'.
    Proof.
      apply subtypePath.
      {
        intro.
        apply isaprop_is_monoid_action_morphism.
      }
      apply funextfun.
      exact H.
    Qed.

    Lemma isaset_monoid_action_morphism
      : isaset monoid_action_morphism.
    Proof.
      apply isaset_total2.
      - apply isaset_set_fun_space.
      - intro.
        apply isasetaprop.
        apply isaprop_is_monoid_action_morphism.
    Qed.

  End MonoidActionHom.

  Definition id_monoid_action_morphism
    (X : monoid_action)
    : monoid_action_morphism X X.
  Proof.
    use make_monoid_action_morphism.
    - exact (idfun X).
    - abstract trivial.
  Defined.

  Definition comp_monoid_action_morphism
    {X X' X'' : monoid_action}
    (f : monoid_action_morphism X X')
    (g : monoid_action_morphism X' X'')
    : monoid_action_morphism X X''.
  Proof.
    use make_monoid_action_morphism.
    - exact (λ x, g (f x)).
    - abstract (
        intros;
        refine (_ @ monoid_action_morphism_commutes _ _ _ _ _);
        apply maponpaths;
        apply monoid_action_morphism_commutes
      ).
  Defined.

  Definition monoid_action_category
    : category.
  Proof.
    use make_category.
    - use make_precategory.
      + use make_precategory_data.
        * use make_precategory_ob_mor.
          -- exact monoid_action.
          -- exact monoid_action_morphism.
        * exact id_monoid_action_morphism.
        * do 3 intro.
          exact comp_monoid_action_morphism.
      + abstract (
          use make_is_precategory;
          intros;
          apply monoid_action_morphism_eq;
          trivial
        ).
    - intros a b.
      apply isaset_monoid_action_morphism.
  Defined.

  Definition binproducts_monoid_action_category
    : BinProducts monoid_action_category.
  Proof.
    intros X X'.
    use make_BinProduct.
    - use make_monoid_action.
      + use make_monoid_action_data.
        * exact (setdirprod (X : monoid_action) (X' : monoid_action)).
        * intros x m.
          exact (op (pr1 x) m ,, op (pr2 x) m).
      + abstract (
          use make_is_monoid_action;
          [ intro;
            use pathsdirprod;
            apply monoid_action_unax
          | intros;
            use pathsdirprod;
            apply monoid_action_assocax ]
        ).
    - use make_monoid_action_morphism.
      + exact pr1.
      + abstract trivial.
    - use make_monoid_action_morphism.
      + exact pr2.
      + abstract trivial.
    - use make_isBinProduct.
      intros Y f g.
      use make_iscontr.
      + use tpair.
        * use make_monoid_action_morphism.
          -- intro y.
            exact ((f : monoid_action_morphism _ _) y ,, (g : monoid_action_morphism _ _) y).
          -- abstract (
              intros;
              use pathsdirprod;
              apply monoid_action_morphism_commutes
            ).
        * abstract now (
            split;
            use monoid_action_morphism_eq
          ).
      + abstract (
          intro t;
          use subtypePath;
          [ intro;
            use isapropdirprod;
            apply homset_property | ];
          apply monoid_action_morphism_eq;
          intro;
          apply pathsdirprod;
          [ apply (maponpaths (λ f, (f : monoid_action_morphism _ _) x) (pr12 t))
          | apply (maponpaths (λ f, (f : monoid_action_morphism _ _) x) (pr22 t)) ]
        ).
  Defined.

  Definition monoid_monoid_action
    : monoid_action.
  Proof.
    use make_monoid_action.
    - use make_monoid_action_data.
      + exact M.
      + exact (λ x y, x * y).
    - abstract (
        use make_is_monoid_action;
        [ intro;
          apply runax
        | intros;
          symmetry;
          apply assocax ]
      ).
  Defined.

  Definition exponential_object
    (X X' : monoid_action)
    : monoid_action.
  Proof.
    use make_monoid_action.
    - use make_monoid_action_data.
      + exact (make_hSet _ (isaset_monoid_action_morphism (BinProductObject _ (binproducts_monoid_action_category monoid_monoid_action X)) X')).
      + refine (λ (f : monoid_action_morphism _ _) m, _).
        use make_monoid_action_morphism.
        * intro x.
          exact (f (m * pr1 x ,, pr2 x)).
        * abstract (
            intros x m';
            refine (_ @ monoid_action_morphism_commutes _ _ _ _ _);
            exact (maponpaths (λ x, f (x ,, _)) (!assocax M _ _ _))
          ).
    - abstract (
        use make_is_monoid_action;
        refine (λ (f : monoid_action_morphism _ _), _);
        intros;
        apply monoid_action_morphism_eq;
        intro;
        refine (maponpaths (λ x, f (x ,, _)) _);
        [ apply unax
        | apply assocax ]
      ).
  Defined.

  Definition exponential_object_morphism
    (X X' : monoid_action)
    : monoid_action_morphism
      (BinProductObject _ (binproducts_monoid_action_category X (exponential_object X X')))
      X'.
  Proof.
    use make_monoid_action_morphism.
    - intro x.
      exact ((pr2 x : monoid_action_morphism _ _) (1 ,, pr1 x)).
    - abstract (
        intros x m;
        refine (_ @ monoid_action_morphism_commutes _ _ _ _ _);
        apply (maponpaths (λ y, (pr2 x : monoid_action_morphism _ _) (y ,, _)));
        exact (runax _ _ @ !lunax _ _)
      ).
  Defined.

  Section ArrowIsUniversal.

    Context {X X' X'': monoid_action_category}.
    Context (F: monoid_action_morphism (BinProductObject _ (binproducts_monoid_action_category X X'')) X').

    Definition monoid_action_cat_induced_morphism
      : monoid_action_morphism X'' (exponential_object X X').
    Proof.
      use make_monoid_action_morphism.
      - intro x''.
        use make_monoid_action_morphism.
        + intro x.
          exact (F (pr2 x ,, op x'' (pr1 x))).
        + abstract (
            intros;
            refine (_ @ monoid_action_morphism_commutes _ _ _ _ _);
            apply (maponpaths (λ x, F (_ ,, x)));
            apply monoid_action_assocax
          ).
      - abstract (
          intros;
          apply monoid_action_morphism_eq;
          intro;
          exact (maponpaths (λ x, F (_ ,, x)) (!monoid_action_assocax _ _ _))
        ).
    Defined.

    Lemma monoid_action_cat_induced_morphism_commutes
      : F = # (constprod_functor1 binproducts_monoid_action_category X) monoid_action_cat_induced_morphism · exponential_object_morphism X X'.
    Proof.
      apply monoid_action_morphism_eq.
      intro.
      apply (maponpaths (λ x, F (_ ,, x))).
      exact (!monoid_action_unax _).
    Qed.

    Lemma monoid_action_cat_induced_morphism_unique
      (t : ∑ (f' : monoid_action_morphism X'' (exponential_object X X')), F = # (constprod_functor1 binproducts_monoid_action_category X) f' · exponential_object_morphism X X')
      : t = monoid_action_cat_induced_morphism ,, monoid_action_cat_induced_morphism_commutes.
    Proof.
      use subtypePath.
      {
        intro.
        apply (homset_property monoid_action_category).
      }
      use monoid_action_morphism_eq.
      intro x''.
      use monoid_action_morphism_eq.
      intro x.
      refine (!_ @ maponpaths (λ x, (x : monoid_action_morphism _ _) _) (!(pr2 t))).
      refine (maponpaths (λ x, (_ x) _) (monoid_action_morphism_commutes _ _ _ _ _) @ _).
      refine (maponpaths (λ x, (pr1 t x'' : monoid_action_morphism _ _) (x ,, _)) _).
      apply runax.
    Qed.

  End ArrowIsUniversal.

  Definition monoid_action_cat_exponentiable
    (X : monoid_action_category)
    : is_exponentiable binproducts_monoid_action_category X.
  Proof.
    use left_adjoint_from_partial.
    - exact (exponential_object X).
    - exact (exponential_object_morphism X).
    - intros X' X'' F.
      use make_iscontr.
      + use tpair.
        * exact (monoid_action_cat_induced_morphism F).
        * exact (monoid_action_cat_induced_morphism_commutes F).
      + exact (monoid_action_cat_induced_morphism_unique F).
  Defined.

End MonoidAction.
