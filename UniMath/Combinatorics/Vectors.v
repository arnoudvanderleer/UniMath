(**

  Vectors as Iterated Products

  Description

  Contents
  1. Definitions
  1.1. Constructors
  1.2. Accessors
  2. Equality lemmas
  3. Misc
  3.1. The constant vector
  4. Induction
  5. Vector operations
  5.1. Fold
  5.2. Map
  5.3. Concatenate
  5.4. Zip

  Originally developed by Gianluca Amato, Matteo Calosci, Marco Maggesi, Cosimo Perini Brogi,
    2019-2024.
 *)
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Foundations.NaturalNumbers.

Local Open Scope nat.
Local Open Scope stn.

Declare Scope pvector_scope.
Delimit Scope pvector_scope with pvector.
Local Open Scope pvector_scope.

(** * 1. Definitions *)

Definition vec (A : UU) (n : nat) : UU.
Proof.
induction n as [|n IHn].
- apply unit.
- apply (A × IHn).
Defined.

Bind Scope pvector_scope with vec.

(** ** 1.1. Constructors *)

Definition vnil {A: UU}: vec A 0 := tt.

Definition vcons {A: UU} {n} (x : A) (v : vec A n) : vec A (S n)
  := x,, v.

Notation "[]" := vnil (at level 0, format "[]"): pvector_scope.
Infix "::p" := vcons (at level 60, right associativity) : pvector_scope.
Notation "[ x ; .. ; y ]" := (x ::p .. (y ::p []) ..): pvector_scope.

Section vecs.

Context {A : UU}.

(** ** 1.2. Accessors *)

Definition hd {n} (v : vec A (S n)) : A := pr1 v.

Definition tl {n} (v : vec A (S n)) : vec A n := pr2 v.

Definition el {n} (v : vec A n) : ⟦ n ⟧ → A.
Proof.
  induction n as [|m f].
  - apply (λ i, fromstn0 i).
  - intro i.
    induction i as (j,jlt).
    induction j as [|k _].
    + exact (hd v).
    + exact (f (tl v) (k,, jlt)).
Defined.

Lemma el_vcons_tl {n} (v : vec A n) (x : A) (i : ⟦ n ⟧) :
  el (x ::p v) (dni_firstelement i) = el v i.
Proof.
  apply idpath.
Defined.

Lemma el_vcons_hd {n} (v : vec A n) (x : A) :
  el (x ::p v) (firstelement) = x.
Proof.
  reflexivity.
Defined.

(** * 2. Equality lemmas *)

Definition vec0_eq (u v : vec A 0) : u = v
  := proofirrelevancecontr iscontrunit u v.

Definition vecS_eq {n} {u v : vec A (S n)}
           (p : hd u = hd v) (q : tl u = tl v)
  : u = v
  := dirprod_paths p q.

(** * 3. Misc *)

(** ** 3.1. The constant vector *)

Definition vec_fill (a: A): ∏ n: nat, vec A n
  := nat_rect (λ n: nat, vec A n) [] (λ (n: nat) (v: vec A n), a ::p v).

Lemma el_vec_fill (a: A) {n:nat} (i:⟦ n ⟧) : el (vec_fill a n) i = a.
Proof.
  induction n as [ | n IHn].
  + use (fromstn0 i).
  + induction i as [i ilt].
    induction i as [| i IHi].
    - apply idpath.
    - use IHn.
Defined.

(** ** 3.2. Hlevel of vectors *)

Lemma isofhlevelvec {n} (is1 : isofhlevel n A) k
  : isofhlevel n (vec A k).
Proof.
  induction k as [|k IH].
  - apply isofhlevelcontr, iscontrunit.
  - apply isofhleveldirprod.
    + apply is1.
    + apply IH.
Defined.

(** * 4. Induction. *)

Lemma vec_ind (P : ∏ n, vec A n → UU) :
  P 0 []
  → (∏ x n (v : vec A n), P n v → P (S n) (x ::p v))
  → (∏ n (v : vec A n), P n v).
Proof.
  intros Hnil Hcons.
  induction n as [|m H]; intros.
  - apply (transportb (P 0) (vec0_eq v []) Hnil).
  - apply Hcons, H.
Defined.

Lemma vec_ind_compute (P : ∏ n, vec A n → UU)
  {n:nat} {v:vec A n} {x:A}
  (H0 : P 0 [])
  (HI : ∏ x n (v : vec A n), P n v → P (S n) (x ::p v))
  : (vec_ind P H0 HI) (S n) (x ::p v) = HI x n v (vec_ind P H0 HI n v).
Proof.
  apply idpath.
Defined.

End vecs.

Notation "[]" := vnil (at level 0, format "[]"): pvector_scope.
Infix "::p" := vcons (at level 60, right associativity) : pvector_scope.
Notation "[ x ; .. ; y ]" := (vcons x .. (vcons y []) ..) : pvector_scope.

(** * 5. Vector operations *)

(** ** 5.1. Fold *)

Definition vec_foldr {A B : UU} (f : A -> B -> B) (b : B) {n}
  : vec A n -> B
  := vec_ind (λ (n : nat) (_ : vec A n), B) b
                (λ (a : A) (m : nat) (_ : vec A m) (acc : B), f a acc)
                n.

Definition vec_foldr1 {A : UU} (f : A -> A -> A) {n} : vec A (S n) → A
  := nat_rect (λ n : nat, vec A (S n) → A)
              hd
              (λ (m : nat) (h : vec A (S m) → A),
               uncurry (λ (x : A) (u : vec A (S m)), f x (h u)))
              n.

(** ** 5.2. Map *)

Definition vec_map {A B : UU} (f : A → B) {n} (v : vec A n) : vec B n.
Proof.
  induction n as [|m h].
  - exact [].
  - exact (f (hd v) ::p h (tl v)).
Defined.

Lemma hd_vec_map {A B : UU} (f : A → B) {n} (v : vec A (S n))
  : hd (vec_map f v) = f (hd v).
Proof.
  reflexivity.
Defined.

Lemma tl_vec_map {A B : UU} (f : A → B) {n} (v : vec A (S n))
  : tl (vec_map f v) = vec_map f (tl v).
Proof.
  reflexivity.
Defined.

Lemma el_vec_map {A B : UU} (f : A → B) {n} (v : vec A n) (i : ⟦ n ⟧)
  : el (vec_map f v) i = f (el v i).
Proof.
  induction n as [|m H].
  - exact (fromstn0 i).
  - induction i as (j, jlt).
    induction j as [|k _].
    + apply hd_vec_map.
    + change (el (tl (vec_map f v)) (make_stn _ k jlt) =
              f (el (tl v) (make_stn _ k jlt))).
              use H.
Defined.

Lemma vec_map_id {A : UU} {n} (v: vec A n)
  : vec_map (idfun A) v = v.
Proof.
  revert n v.
  refine (vec_ind _ _ _).
  - apply idpath.
  - intros x n xs HPxs.
    simpl.
    apply maponpaths.
    apply HPxs.
Defined.

Lemma vec_map_comp {A B C: UU} (f: A → B) (g: B → C) {n: nat} (v: vec A n) :
  vec_map (funcomp f g) v = (funcomp (vec_map f) (vec_map g)) v.
Proof.
  revert n v.
  refine (vec_ind _ _ _).
  - apply idpath.
  - intros x n xs HPxs.
    apply vecS_eq.
    + reflexivity.
    + apply HPxs.
Defined.

Lemma el_vec_map_vec_fill {A B : UU} (f : A → B) {n} (a:A) (i : ⟦ n ⟧)
  : el (vec_map f (vec_fill a n)) i = f a.
  Proof.
    etrans.
    { apply el_vec_map. }
    use maponpaths.
    use el_vec_fill.
  Defined.

Lemma vec_map_const {A: UU} {n: nat} {v: vec A n} {B: UU} (b: B) : vec_map (λ _, b) v = vec_fill b n.
Proof.
  revert n v.
  apply vec_ind.
  - apply idpath.
  - intros x n xs HPind.
    change (b ::p vec_map (λ _: A, b) xs = b ::p vec_fill b n).
    apply maponpaths.
    exact HPind.
Defined.

(** ** 5.3. Concatenate *)

Definition vec_append {A : UU} {m} (u : vec A m) {n} (v : vec A n)
  : vec A (m + n)
  := vec_ind (λ (p : nat) (_ : vec A p), vec A (p + n))
                v
                (λ (x : A) (p : nat) (_ : vec A p) (w : vec A (p + n)),
                 x ::p w)
                m u.

Lemma vec_append_lid {A : UU} (u : vec A 0) {n}
  : vec_append u = idfun (vec A n).
Proof.
  induction u.
  reflexivity.
Defined.

(** ** 5.4. Zip *)

Definition vec_zip {A B: UU} {n: nat} (v1: vec A n) (v2: vec B n): vec (A × B) n.
Proof.
  induction n.
  - exact [].
  - induction v1 as [x1 xs1].
    induction v2 as [x2 xs2].
    exact ((x1 ,, x2) ::p IHn xs1 xs2).
Defined.
