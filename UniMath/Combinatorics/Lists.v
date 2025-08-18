(** * Lists *)

(**

This file contains a formalization of lists define as iterated products ([list]).

Written by: Anders Mörtberg, 2016 (inspired by a remark of Vladimir Voevodsky), Floris van Doorn, december 2017

*)

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Declare Scope plist_scope.
Delimit Scope plist_scope with plist.
Local Open Scope plist_scope.

Section lists.

Context {A : UU}.

(** * 1. Definitions *)

Definition list : UU := ∑ n, vec A n.

Bind Scope plist_scope with list.

(** ** 1.1. Accessors *)

Definition length : list -> nat := pr1.

Definition list_to_vec: ∏ l: list, vec A (length l) := pr2.
Coercion list_to_vec: list >-> vec.

Definition nth x : stn(length x) -> A := el (pr2 x).

(** ** 1.2. Constructors *)

Definition make_list {n : nat} (xs : vec A n) : list := n ,, xs.

Definition nil : list := (0,, [])%pvector.

Definition cons (x : A) (xs : list) : list :=
  (S (pr1 xs),, x ::p xs)%pvector.

Notation "[]" := nil (at level 0, format "[]"): plist_scope.
Infix "::p" := cons (at level 60, right associativity) : plist_scope.
Notation "[ x ; .. ; y ]" := (x ::p .. (y ::p []) ..): plist_scope.

(** * 3. Misc *)

(** ** 3.1. The constant list  *)

Definition constant_list (a : A) (n : nat) : list := make_list (vec_fill a n).

(** ** 3.1. HLevel of lists *)

Lemma isofhlevellist (n : nat) (is1 : isofhlevel (S (S n)) A) : isofhlevel (S (S n)) list.
Proof.
  use isofhleveltotal2.
  - intros m k. apply isofhlevelsnprop, isasetnat.
  - intro m. apply isofhlevelvec, is1.
Defined.

(** * 4. Induction *)

Lemma list_ind : ∏ (P : list -> UU),
     P []
  -> (∏ (x : A) (xs : list), P xs -> P (x ::p xs))
  -> ∏ xs, P xs.
Proof.
intros P Hnil Hcons xs.
induction xs as [n xs].
induction n as [|n IHn].
- induction xs.
  apply Hnil.
- simpl in xs.
  induction xs as [x xs].
  apply (Hcons x (n,,xs) (IHn xs)).
Defined.

Lemma list_ind_compute_2
      (P : list -> UU)
      (p0 : P [])
      (ind : ∏ (x : A) (xs : list), P xs -> P (x ::p xs))
      (x : A) (xs : list)
      (f := list_ind P p0 ind) :
  f (x ::p xs) = ind x xs (f xs).
Proof.
  apply idpath.
Defined.

End lists.

Notation "[]" := nil (at level 0, format "[]"): plist_scope.
Infix "::p" := cons (at level 60, right associativity) : plist_scope.
Notation "[ x ; .. ; y ]" := (x ::p .. (y ::p []) ..): plist_scope.

(** Make the type not implicit for list *)
Arguments list : clear implicits.

(** * 5. Sequence operations *)

(** ** Fold *)

Definition foldr {A B : UU} (f : A -> B -> B) (b : B) : list A -> B :=
  list_ind (λ _, B) b (λ a _ b', f a b').

Lemma foldr_nil {A B : UU} (f : A -> B -> B) (b : B) : foldr f b [] = b.
Proof.
  apply idpath.
Qed.

Lemma foldr_cons {A B : UU} (f : A -> B -> B) (b : B) (x : A) (xs : list A) :
  foldr f b (x ::p xs) = f x (foldr f b xs).
Proof.
  apply idpath.
Qed.

(** Variation of foldr that returns a for the empty list and folds the
    rest with the first element as new default value *)
Definition foldr1 {A : UU} (f : A -> A -> A) (a : A) : list A → A.
Proof.
  apply list_ind.
  - exact a.
  - intros a' l fl. revert l. apply list_ind.
    + exact a'.
    + intros _ _ _. exact (f a' fl).
Defined.

Lemma foldr1_nil {A: UU} (f : A -> A -> A) (a : A) : foldr1 f a [] = a.
Proof.
  apply idpath.
Qed.

Lemma foldr1_cons_nil {A : UU} (f : A -> A -> A) (a : A) (x : A) :
  foldr1 f a [x] = x.
Proof.
apply idpath.
Qed.

Lemma foldr1_cons {A : UU} (f : A -> A -> A) (a : A) (x y : A) (xs : list A) :
  foldr1 f a (x ::p (y ::p xs)) = f x (foldr1 f a (y ::p xs)).
Proof.
apply idpath.
Qed.

(** Variation of foldr1 with embedded mapping, see below for [foldr1_foldr1_map] *)
Definition foldr1_map {A B : UU} (f : B -> B -> B) (b : B) (h : A -> B) : list A → B.
Proof.
  apply list_ind.
  - exact b.
  - intros a' l fl. revert l. apply list_ind.
    + exact (h a').
    + intros _ _ _. exact (f (h a') fl).
Defined.

Lemma foldr1_map_nil {A : UU} {B : UU} (f : B -> B -> B) (b : B) (h : A -> B) :
  foldr1_map f b h [] = b.
Proof.
  apply idpath.
Qed.

Lemma foldr1_map_cons_nil {A : UU} {B : UU} (f : B -> B -> B) (b : B) (h : A -> B)
  (x : A) : foldr1_map f b h [x] = h x.
Proof.
  apply idpath.
Qed.

Lemma foldr1_map_cons {A : UU} {B : UU} (f : B -> B -> B) (b : B) (h : A -> B)
  (x y : A) (xs : list A) :
  foldr1_map f b h (x ::p (y ::p xs)) = f (h x) (foldr1_map f b h (y ::p xs)).
Proof.
  apply idpath.
Qed.

(** an induction principle for [foldr1_map]

    [P] takes the list argument [xs] of [foldr1_map] and the purported value of [foldr1_map f b h xs]
    [P0] and [P1] ask that [P] is correct for lists of length <=1
    [P2] deals with longer lists and reflects the effect of adding a subsequent element [a2] to the list, where [res] keeps the
    result of [foldr1_map f b h (a1 ::p xs)] abstract
*)
Definition foldr1_map_ind {A B : UU} (f : B -> B -> B) (b : B) (h : A -> B) (P : list A -> B -> UU)
  (P0 : P [] b)
  (P1 : ∏ a, P ([a]) (h a))
  (P2 : ∏ a1 xs a2 res, P (a1 ::p xs) res -> P (a2 ::p (a1 ::p xs)) (f (h a2) res))
  (xs : list A) : P xs (foldr1_map f b h xs).
Proof.
  revert xs.
  induction xs as [[|n] xs].
  - induction xs.
    apply P0.
  - induction n as [|n IH].
    + induction xs as [m [ ]].
      apply P1.
    + induction xs as [m [k xs]].
      assert (IHinst := IH (k,,xs)).
      exact (P2 k (n,,xs) m (foldr1_map f b h (S n,, k,, xs)) IHinst).
Defined.

Definition foldr1_map_ind_nodep {A B : UU} (f : B -> B -> B) (b : B) (h : A -> B) (P : B -> UU)
  (P0 : P b)
  (P1 : ∏ a, P (h a))
  (P2 : ∏ a res, P res -> P (f (h a) res))
  (xs : list A) : P (foldr1_map f b h xs).
Proof.
  set (Pdep := fun (_ : list A) (res : B) => P res).
  apply (foldr1_map_ind f b h Pdep).
  - exact P0.
  - exact P1.
  - intros a1 xs' a2 res H. apply P2. exact H.
Defined.

(** ** Map *)

Definition map {A B : UU} (f : A -> B) : list A -> list B :=
  foldr (λ a l, (f a) ::p l) [].

Lemma mapStep {A B : UU} (f : A -> B) (a:A) (x:list A) : map f (a ::p x) = (f a) ::p (map f x).
Proof.
  apply idpath.
Defined.

Lemma map_nil {A B : UU} (f : A -> B) : map f [] = [].
Proof.
  apply idpath.
Qed.

Lemma map_cons {A B : UU} (f : A -> B) (x : A) (xs : list A) :
  map f (x ::p xs) = (f x) ::p (map f xs).
Proof.
  apply idpath.
Qed.

Lemma map_compose {A B C : UU} (f : A → B) (g : B → C) (xs : list A) :
  map (g ∘ f) xs = map g (map f xs).
Proof.
  revert xs. apply list_ind.
  - apply idpath.
  - intros x xs IH. now rewrite !map_cons, IH.
Defined.

Lemma map_idfun {A : UU} (xs : list A) :
  map (idfun A) xs = xs.
Proof.
  revert xs. apply list_ind.
  - apply idpath.
  - intros x xs IH. now rewrite !map_cons, IH.
Defined.

Lemma map_homot {A B : UU} {f g : A → B} (h : f ~ g) (xs : list A) :
  map f xs = map g xs.
Proof.
  revert xs. apply list_ind.
  - apply idpath.
  - intros x xs IH. now rewrite !map_cons, h, IH.
Defined.

Lemma foldr1_foldr1_map {A B : UU} (f : B -> B -> B) (b : B) (h : A -> B) (xs : list A) :
  foldr1_map f b h xs = foldr1 f b (map h xs).
Proof.
  set (P := fun xs res => res = foldr1 f b (map h xs)).
  apply (foldr1_map_ind f b h P).
  - apply idpath.
  - intro a. apply idpath.
  - intros a1 xs' a2 res H.
    red.
    do 2 rewrite map_cons.
    rewrite foldr1_cons.
    apply maponpaths.
    red in H.
    rewrite map_cons in H.
    exact H.
Qed.

(** ** Concatenate *)

Definition concatenate {X} : list X -> list X -> list X
  := λ r s, foldr cons s r.

Infix "++p" := concatenate (at level 60, right associativity) : plist_scope.

Lemma concatenateStep {X} (x:X) (r s:list X) :
  (x ::p r) ++p s = x ::p (r ++p s).
Proof.
  apply idpath.
Defined.

Lemma nil_concatenate {X} (r : list X) : [] ++p r = r.
Proof. apply idpath. Defined.

Lemma concatenate_nil {X} (r : list X) : r ++p [] = r.
Proof. revert r. apply list_ind. apply idpath. intros x xs p. exact (maponpaths (cons x) p). Defined.

Lemma assoc_concatenate {X} (r s t : list X) : (r ++p s) ++p t = r ++p (s ++p t).
Proof.
  revert r. apply list_ind.
  - apply idpath.
  - intros x xs p. now rewrite !concatenateStep, p.
Defined.

Lemma map_concatenate {X Y} (f : X → Y) (r s : list X) : map f (r ++p s) = map f r ++p map f s.
Proof.
  revert r. apply list_ind.
  - apply idpath.
  - intros x xs p. now rewrite mapStep, !concatenateStep, mapStep, p.
Defined.

Lemma foldr_concatenate {X Y : UU} (f : X → Y) (l : list X) :
  foldr concatenate [] (map (λ x, f x::p[]) l) = map f l.
Proof.
  revert l. apply list_ind.
  - apply idpath.
  - intros x l IH. now rewrite !map_cons, foldr_cons, IH.
Qed.

Lemma foldr1_map_concatenate {X Y : UU} (f : X → Y) (l : list X) :
  map f l = foldr1_map concatenate [] (λ x, f x::p[]) l.
Proof.
  set (P := fun xs res => map f xs = res).
  refine (foldr1_map_ind _ _ _ P _ _ _ l).
  - apply idpath.
  - intro; apply idpath.
  - intros x' l' x'' res Hyp.
    exact (maponpaths (cons (f x'')) Hyp).
Qed.

Lemma foldr1_concatenate {X Y : UU} (f : X → Y) (l : list X) :
  map f l = foldr1 concatenate [] (map (λ x, f x::p[]) l).
Proof.
  simple refine (foldr1_map_concatenate _ _ @ _).
  apply foldr1_foldr1_map.
Qed.

(** ** Append *)

Definition append {X} (x : X) (l : list X) : list X :=
  l ++p [x].

Lemma appendStep {X} (x y : X) (l : list X) : append x (y ::p l) = y ::p append x l.
  Proof. apply idpath. Defined.

Lemma append_concatenate {X} (x : X) (l s : list X) : append x (l ++p s) = l ++p append x s.
  Proof. apply assoc_concatenate. Defined.

Lemma map_append {X Y} (f : X → Y) (x : X) (r : list X) : map f (append x r) = append (f x) (map f r).
  Proof. exact (map_concatenate _ _ _). Defined.

(** Flatten *)

Definition flatten {X} : list (list X) → list X.
Proof.
  apply list_ind.
  + exact [].
  + intros s _ f. exact (s ++p f).
Defined.

Lemma flattenStep {X} (x:list X) (m : list(list X)) : flatten (x::p m) = x ++p (flatten m).
Proof.
  unfold flatten.
  rewrite list_ind_compute_2.
  apply idpath.
Defined.

(** ** Reverse *)

Definition reverse {X} : list X → list X :=
  foldr append [].

Lemma reverse_nil (X : Type) : reverse (X := X) [] = [].
Proof. apply idpath. Defined.

Lemma reverseStep {X} (x : X) (r : list X) : reverse (x::p r) = append x (reverse r).
Proof. apply idpath. Defined.

Lemma map_reverse {X Y} (f : X → Y) (r : list X) : map f (reverse r) = reverse (map f r).
Proof.
  revert r. apply list_ind.
  - apply idpath.
  - intros x xs p. now rewrite mapStep, !reverseStep, map_append, p.
Defined.

Lemma reverse_concatenate {X} (l s : list X) : reverse (l ++p s) = reverse s ++p reverse l.
Proof.
  revert l. apply list_ind.
  - symmetry. apply concatenate_nil.
  - intros x xs p. now rewrite concatenateStep, !reverseStep, p, append_concatenate.
Defined.

Lemma reverse_append {X} (x : X) (l : list X) : reverse (append x l) = x ::p reverse l.
Proof. unfold append. now rewrite reverse_concatenate, reverseStep, reverse_nil. Defined.

Lemma reverse_reverse {X} (r : list X) : reverse (reverse r) = r.
Proof.
  revert r. apply list_ind.
  - apply idpath.
  - intros x xs p. now rewrite !reverseStep, reverse_append, p.
Defined.
