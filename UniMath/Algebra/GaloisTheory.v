Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.Groups2.
Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Categories.Fld.
Require Import UniMath.CategoryTheory.Actions.

Require Import UniMath.CategoryTheory.Core.Isos.

(* Galois groups *)

Definition galois_group
  (K : fld)
  : gr
  := automorphism_grp (C := fld_category) K.

Definition galois_group_element_to_ringfun
  {k : fld}
  (f : galois_group k)
  : z_iso (C := fld_category) k k
  := f.

Definition galois_group_mor
  {K : fld}
  (f : galois_group K)
  : ringfun K K
  := z_iso_mor (C := fld_category) f.

Definition galois_group_inv
  {K : fld}
  (f : galois_group K)
  : ringfun K K
  := inv_from_z_iso (C := fld_category) f.

Definition galois_group_mor_inv
  {K : fld}
  (f : galois_group K)
  : rigfuncomp (galois_group_mor f) (galois_group_inv f) = rigisotorigfun (idrigiso K)
  := z_iso_inv_after_z_iso (C := fld_category) f.

Definition galois_group_inv_mor
  {K : fld}
  (f : galois_group K)
  : rigfuncomp (galois_group_inv f) (galois_group_mor f) = rigisotorigfun (idrigiso K)
  := z_iso_after_z_iso_inv (C := fld_category) f.

Definition relative_galois_group
  (K : fld)
  (k : hsubtype K)
  : subgr (galois_group K).
Proof.
  use make_subgr.
  - intro f.
    exact (∀ (x : k), galois_group_mor f (pr1carrier _ x) = (pr1carrier _ x) ∧ galois_group_inv f (pr1carrier _ x) = (pr1carrier _ x))%logic.
  - refine ((_ ,, _) ,, _).
    + intros f g x.
      split.
      * refine (maponpaths _ (pr1 (pr2 g _)) @ _).
        exact (pr1 (pr2 f _)).
      * refine (maponpaths _ (pr2 (pr2 f _)) @ _).
        exact (pr2 (pr2 g _)).
    + easy.
    + intros f Hf x.
      split.
      * exact (pr2 (Hf x)).
      * exact (pr1 (Hf x)).
Defined.

(* Fixed Fields *)

Definition fixed_subset
  (k : hSet)
  {I : UU}
  (f : I → k → k)
  : hsubtype k.
Proof.
  intro x.
  exact (∀ i, f i x = x)%logic.
Defined.

Lemma fixed_subset_issubsetwithbinop
  (k : setwithbinop)
  {I : UU}
  (f : I → binopfun k k)
  : issubsetwithbinop op (fixed_subset k (λ i, f i)).
Proof.
  intros x y i.
  refine (binopfunisbinopfun (f i) _ _ @ _).
  exact (maponpaths_2 _ (pr2 x i) _ @ maponpaths _ (pr2 y i)).
Qed.

Lemma fixed_subset_issubmonoid
  (k : monoid)
  {I : UU}
  (f : I → monoidfun k k)
  : issubmonoid (fixed_subset k (λ i, f i)).
Proof.
  split.
  - apply fixed_subset_issubsetwithbinop.
  - intro i.
    apply monoidfununel.
Qed.

Lemma fixed_subset_issubgr
  (k : gr)
  {I : UU}
  (f : I → group_morphism k k)
  : issubgr (fixed_subset k (λ i, f i)).
Proof.
  split.
  - apply fixed_subset_issubmonoid.
  - intros x Hx i.
    refine (group_morphism_inv (f i) _ @ _).
    apply maponpaths.
    exact (Hx i).
Qed.

Lemma fixed_subset_issubring
  (k : ring)
  {I : UU}
  (f : I → ringfun k k)
  : issubring (fixed_subset k (λ i, f i)).
Proof.
  split.
  - exact (fixed_subset_issubgr _ (λ i, binopfun_to_group_morphism (ringaddfun (f i)))).
  - exact (fixed_subset_issubmonoid _ (λ i, ringmultfun (f i))).
Qed.

Lemma fixed_subset_issubfld
  (k : fld)
  {I : UU}
  (f : I → ringfun k k)
  : issubfld (fixed_subset k (λ i, f i)).
Proof.
  split.
  - exact (fixed_subset_issubring k f).
  - intros x inv Hx i.
    apply (lcanfromlinv _ _ _ _ (invtolinv _ _ inv)).
    refine (_ @ !pr22 inv).
    refine (!maponpaths_2 _ (Hx i) _ @ _).
    refine (!binopfunisbinopfun (ringmultfun (f i)) _ _ @ _).
    refine (maponpaths _ (pr22 inv) @ _).
    exact (monoidfununel (ringmultfun (f i))).
Qed.

Definition fixed_subfield
  (k : fld)
  {I : UU}
  (f : I → ringfun k k)
  : subfld k
  := make_subfld
    (fixed_subset k f)
    (fixed_subset_issubfld k f).

Definition galois_fixed_subfield
  (k : fld)
  {I : UU}
  (H : hsubtype (galois_group k))
  : subfld k
  := fixed_subfield k (λ (f : H), galois_group_mor (pr1carrier _ f)).

(* Galois field extensions *)


