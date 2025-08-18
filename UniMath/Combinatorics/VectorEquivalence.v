Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FVectors.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Local Open Scope stn.

Section Equivalences.

  Context {A : UU}.

  Definition drop {n} (f : ⟦ S n ⟧ → A) (i : ⟦ n ⟧) : A :=
    f (dni_firstelement i).

  Lemma drop_el {n} (v : vec A (S n)) (i: ⟦ n ⟧ ) : drop (el v) i = el (tl v) i.
  Proof.
    apply idpath.
  Defined.

  Lemma el_tl {n} (v : vec A (S n)) (i : ⟦ n ⟧)
    : el (tl v) i = drop (el v) i.
  Proof.
    apply idpath.
  Defined.

  Lemma vec_extens {n} {u v : vec A n}
    : (∏ i : ⟦ n ⟧, el u i = el v i) → u = v.
  Proof.
    intros H.
    induction n as [|m meq].
    - apply vec0_eq.
    - apply vecS_eq.
      + exact (H firstelement).
      + apply meq.
        intros.
        do 2 rewrite el_tl.
        apply H.
  Defined.

  (** *** Weak equivalence with functions. *)

  Definition make_vec {n} (f : ⟦ n ⟧ → A) : vec A n.
  Proof.
    induction n as [|m h].
    - exact []%pvector.
    - exact ((f firstelement) ::p (h (drop f)))%pvector.
  Defined.

  Lemma el_make_vec {n} (f : ⟦ n ⟧ → A) : el (make_vec f) ~ f .
  Proof.
    intro i.
    induction n as [|m meq].
    - exact (fromstn0 i).
    - induction i as (j,jlt).
      induction j as [|k _].
      + cbn.
        apply maponpaths.
        apply subtypePath_prop.
        apply idpath.
      + etrans.
        { apply meq. }
        unfold drop.
        apply maponpaths.
        apply idpath.
  Defined.

  Lemma el_make_vec_fun {n} (f : ⟦ n ⟧ → A) : el (make_vec f) = f.
  Proof.
    apply funextfun.
    apply el_make_vec.
  Defined.

  Lemma make_vec_el {n} (v : vec A n) : make_vec (el v) = v.
  Proof.
    apply vec_extens.
    intros i.
    rewrite el_make_vec.
    reflexivity.
  Defined.

  Definition isweqvecfun {n} : isweq (el:vec A n → ⟦ n ⟧ → A)
    := isweq_iso el make_vec make_vec_el el_make_vec_fun.

  Definition weqvecfun n : vec A n ≃ (⟦ n ⟧ -> A)
    := make_weq el isweqvecfun.

End Equivalences.

Lemma vec_map_as_make_vec {A B: UU} (f: A → B) {n} (v: vec A n)
  : vec_map f v = make_vec (λ i, f (el v i)).
Proof.
  apply vec_extens.
  intro i.
  rewrite el_vec_map.
  rewrite el_make_vec.
  apply idpath.
Defined.

Lemma vec_map_make_vec {A B: UU} {n: nat} (g: ⟦ n ⟧ → A) (f: A → B)
  : vec_map f (make_vec g) = make_vec (f ∘ g).
Proof.
  apply vec_extens.
  intro i.
  rewrite el_vec_map.
  rewrite el_make_vec.
  rewrite el_make_vec.
  apply idpath.
Defined.
