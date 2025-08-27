(**

  Vectors as Functions

  A [vector] of length n with values in X is an ordered n-tuple of elements of X, encoded here as a
  function ⟦n⟧ → X.

  Contents
  1. Definitions
  1.1. Constructors
  1.2. Accessors
  2. Equality lemmas
  3. Misc
  3.1. Constant vector
  3.2. Nil is unique
  3.3. hlevel of vectors
  3.4. Every type is equivalent to vectors of length 1 on that type.
  4. Induction

  Originally defined in March 2018 by Langston Barrett (@siddharthist).

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Nat.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Declare Scope fvector_scope.
Delimit Scope fvector_scope with fvector.
Local Open Scope fvector_scope.

(** * 1. Definitions *)

Definition Vector (X : UU) (n : nat) : UU := stn n -> X.

Bind Scope fvector_scope with Vector.

(** ** 1.1. Constructors *)

Definition empty_vec {X : UU} : Vector X 0 := λ i, fromstn0 i.

Notation "[]" := empty_vec (at level 0, format "[]"): fvector_scope.

Section Append.

  Context {X : UU} {n : nat} (vec : Vector X n) (x : X).

  Definition append_vec : Vector X (S n).
  Proof.
    intros i.
    induction (natlehchoice (pr1 i) n (pr2 i)) as [c|d].
    - exact (vec (pr1 i,,c)).
    - exact x.
  Defined.

End Append.

Infix "::f" := append_vec (at level 58, left associativity) : fvector_scope.
Notation "[ x ; .. ; y ]" := (.. ([] ::f x) .. ::f y) : fvector_scope.

(** ** 1.2. Accessors *)

Notation "'init' xs" := (xs ∘ dni lastelement) (at level 10) : fvector_scope.

Notation "'last' xs" := (xs lastelement) (at level 10) : fvector_scope.

Notation "'tail' xs" := (xs ∘ dni firstelement) (at level 10) : fvector_scope.

Notation "'head' xs" := (xs firstelement) (at level 10) : fvector_scope.

Definition append_vec_compute_1
  {X : UU}
  {n : nat}
  (vec : Vector X n)
  (x : X)
  (i : stn n)
  : init (vec ::f x) i = vec i.
Proof.
  intros.
  simple refine (maponpaths (coprod_rect _ _ _) (natlehchoice_lt _ _) @ _).
  - refine (transportf (λ x, x < n) (!di_eq1 _) _);
      apply (stnlt i).
  - apply (maponpaths vec).
    apply stn_eq.
    apply di_eq1.
    apply stnlt.
Defined.

Definition append_vec_compute_2
  {X : UU}
  {n : nat}
  (vec : Vector X n)
  (x : X)
  : last (vec ::f x) = x.
Proof.
  exact (maponpaths (coprod_rect _ _ _) (natlehchoice_eq _ (idpath _))).
Defined.

Lemma drop_and_append_vec
  {X : UU}
  {n : nat}
  (vecsn : Vector X (S n))
  : (init vecsn) ::f (last vecsn) = vecsn.
Proof.
  intros.
  apply funextfun.
  refine (stn_sn_ind _ _).
  - exact (append_vec_compute_1 _ _).
  - exact (append_vec_compute_2 _ _).
Defined.

(** * 2. Equality lemmas *)

Definition vectorEquality {X : UU} {m n : nat} (f : Vector X n) (g : Vector X m) (p : n = m) :
  (∏ i, f i = g (transportf stn p i))
  -> transportf (Vector X) p f = g.
Proof.
  intro.
  induction p.
  apply funextfun.
  assumption.
Defined.

Definition vector_stn_proofirrelevance {X : UU} {n : nat} {vec : Vector X n}
          {i j : stn n} : (stntonat _ i = stntonat _ j) -> vec i = vec j.
Proof.
  intro.
  apply maponpaths, isinjstntonat; assumption.
Defined.

(** * 3. Misc *)

(** ** 3.1. Constant vector *)
Definition const_vec {X : UU} {n : nat} (x : X) : Vector X n := λ _, x.

(** ** 3.2. Nil is unique *)
Definition nil_proofirrelevance (X : UU)
  (xs ys : Vector X 0)
  : xs = ys.
Proof.
  apply funextfun.
  intro i.
  exact (fromstn0 i).
Defined.

(** ** 3.3. hlevel of vectors *)
Lemma vector_hlevel (X : UU) (n : nat) {m : nat} (ism : isofhlevel m X) :
  isofhlevel m (Vector X n).
Proof.
  apply impred; auto.
Defined.

(** ** 3.4. Every type is equivalent to vectors of length 1 on that type. *)
Lemma weq_vector_1 {X : UU} : X ≃ Vector X 1.
  intermediate_weq (unit → X).
  - apply invweq, weqfunfromunit.
  - apply weqbfun.
    exact weqstn1tounit.
Defined.

(** * 4. Induction *)

(** An induction principle for vectors: If a statement is true for the empty
    vector, and if it is true for vectors of length n it is also true for those
    of length S n, then it is true for all vectors.
*)
Definition Vector_rect {X : UU} {P : ∏ n, Vector X n -> UU}
          (p0 : P 0 [])
          (ind : ∏ (n : nat) (vec : Vector X n) (x : X),
                  P n vec -> P (S n) (vec ::f x))
          {n : nat} (vec : Vector X n) : P n vec.
Proof.
  intros.
  induction n as [|n IH].
  - refine (transportf (P 0) _ p0).
    apply nil_proofirrelevance.
  - exact (transportf (P _) (drop_and_append_vec vec)
                      (ind _ (vec ∘ dni lastelement)
                            (vec lastelement)
                            (IH (vec ∘ dni lastelement)))).
Defined.
