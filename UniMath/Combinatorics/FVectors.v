Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.

(** ** Vectors *)

(** A [vector] of length n with values in X is an ordered n-tuple of elements of X,
    encoded here as a function ⟦n⟧ → X. *)
Definition vector (X : UU) (n : nat) : UU := stn n → X.

(** hlevel of vectors *)
Lemma vector_hlevel (X : UU) (n : nat) {m : nat} (ism : isofhlevel m X) :
  isofhlevel m (vector X n).
Proof.
  now apply impredfun.
Defined.

Section Accessors.

  Context {X : UU}.
  Context {n : nat}.
  Context (xs : vector X (S n)).

  Definition last : X := xs lastelement.
  Definition init : vector X n := xs ∘ dni lastelement.

  Definition head : X := xs firstelement.
  Definition tail : vector X n := xs ∘ dni firstelement.

End Accessors.

(** Constant vector *)
Definition const_vec {X : UU} {n : nat} (x : X) : vector X n := λ _, x.

(** The unique empty vector *)
Definition iscontr_vector_0 X : iscontr (vector X 0).
Proof.
  intros. apply (@iscontrweqb _ (∅ → X)).
  - apply invweq. apply weqbfun. apply weqstn0toempty.
  - apply iscontrfunfromempty.
Defined.

Definition nil {X : UU} : vector X 0 := iscontrpr1 (iscontr_vector_0 X).

(** Every type is equivalent to vectors of length 1 on that type. *)
Lemma weq_vector_1 {X : UU} : X ≃ vector X 1.
  intermediate_weq (unit → X).
  - apply invweq, weqfunfromunit.
  - apply weqbfun.
    exact weqstn1tounit.
Defined.

Section Snoc.

  Context {X : UU} {n : nat} (xs : vector X n) (x : X).

  Definition snoc : vector X (S n).
  Proof.
    intro i.
    induction (natlehchoice i n (stnlt i)) as [Hi | Hi].
    - refine (xs (make_stn _ _ Hi)).
    - exact x.
  Defined.

  Lemma init_snoc_i i : init snoc i = xs i.
  Proof.
    refine (maponpaths (coprod_rect _ _ _) (natlehchoice_lt _ (transportb (λ x, x < n) (di_eq1 (stnlt i)) (stnlt i))) @ _).
    apply (maponpaths xs).
    apply stn_eq.
    exact (maponpaths pr1 (eqtohomot (replace_dni_last _) _)).
  Qed.

  Lemma init_snoc :
    init snoc = xs.
  Proof.
    intros.
    apply funextsec.
    exact init_snoc_i.
  Qed.

  Lemma last_snoc : last snoc = x.
  Proof.
    exact (maponpaths (coprod_rect _ _ _) (natlehchoice_eq _ (idpath n))).
  Qed.

  Lemma snoc_eq
    {ys : vector X (S n)}
    (Hinit : ∏ i, init ys i = xs i)
    (Hlast : last ys = x)
    : ys = snoc.
  Proof.
    apply funextfun.
    refine (stn_sn_ind _ _).
    - intro i.
      refine (_ @ !init_snoc_i _).
      apply Hinit.
    - refine (_ @ !last_snoc).
      apply Hlast.
  Qed.

  Definition snoc_dep
    {P : X → UU}
    (p_init : ∏ i, P (xs i))
    (p_last : P x)
    : ∏ (i : stn (S n)), P (snoc i).
  Proof.
    intro i.
    unfold snoc.
    induction (natlehchoice i n (stnlt i)).
    - apply p_init.
    - apply p_last.
  Defined.

End Snoc.

Arguments snoc_eq {X n xs x ys} Hinit Hlast.
Arguments snoc_dep {X n xs x P} p_init p_last.

Lemma snoc_init_last
  {X : UU}
  {n : nat}
  (xs : vector X (S n))
  : snoc (init xs) (last xs) = xs.
Proof.
  intros.
  apply funextfun.
  refine (stn_sn_ind _ _).
  + exact (init_snoc_i _ _).
  + exact (last_snoc _ _).
Defined.

(**
  An induction principle for vectors: If we have P nil and if we get P (snoc xs x) from P xs, then
  we have P xs for all vectors xs.
 *)

Section Recursion.

  Context {X : UU}.
  Context {P : nat → UU}.
  Context (p_nil : P 0).
  Context (p_snoc : ∏ n, P n → X → P (S n)).

  Definition vector_rect
    (n : nat) (xs : vector X n) : P n.
  Proof.
    induction n as [|n IH].
    - exact p_nil.
    - exact (p_snoc n (IH (init xs)) (last xs)).
  Defined.

  Lemma vector_rect_nil
    : vector_rect _ nil = p_nil.
  Proof.
    reflexivity.
  Qed.

  Lemma vector_rect_snoc
    (x : X) {n : nat} (xs : vector X n)
    : vector_rect _ (snoc xs x) = p_snoc n (vector_rect _ xs) x.
  Proof.
    refine (two_arg_paths _ _).
    - apply maponpaths.
      apply funextfun.
      intro i.
      apply init_snoc_i.
    - apply last_snoc.
  Qed.

End Recursion.

Section Induction.

  Context {X : UU}.
  Context {P : ∏ n, vector X n → UU}.
  Context (p_nil : P 0 nil).
  Context (p_snoc : ∏ n xs, P n xs → ∏ (x : X), P (S n) (snoc xs x)).

  Definition vector_ind
    (n : nat) (xs : vector X n) : P n xs.
  Proof.
    induction n as [|n IH].
    - refine (transportf (P 0) _ p_nil).
      exact (!iscontr_uniqueness (iscontr_vector_0 _) _).
    - apply (transportf (P _) (snoc_init_last xs)).
      apply p_snoc.
      apply IH.
  Defined.

  Lemma vector_ind_nil
    : vector_ind _ nil = p_nil.
  Proof.
    refine (maponpaths (λ e, transportf _ e _) (_ : _ = idpath _)).
    do 2 apply isapropifcontr.
    apply iscontr_vector_0.
  Qed.

  (* The current proof needs X to be an hSet, because it uses the fact that vector X n is a set *)
  Lemma vector_ind_snoc
    (HX : isaset X)
    (x : X)
    {n : nat}
    (xs : vector X n)
    : vector_ind _ (snoc xs x) = p_snoc n xs (vector_ind _ xs) x.
  Proof.
    refine (_ @ transport_section (λ (xs : vector X n), p_snoc n xs (vector_ind _ xs) x) (init_snoc xs x)).
    refine (_ @ !functtransportf (λ xs, snoc xs x) _ _ _).
    apply transportf_transpose_right.
    refine (_ @ transport_section (λ (a : X), p_snoc n (init (snoc xs x)) (vector_ind _ (init (snoc xs x))) a) (last_snoc xs x)).
    refine (_ @ !functtransportf (λ x, snoc _ x) _ _ _).
    refine (transport_f_f _ _ _ _ @ _).
    refine (maponpaths (λ e, transportf _ e _) _).
    refine (proofirrelevance _ ((_ : isaset _) _ _) _ _).
    apply (vector_hlevel _ _ (m := 2)).
    exact HX.
  Qed.

End Induction.

Section Fold.

  Context {X : UU} {Y : UU}.

  Section Left.

    Context (f : Y → X → Y) (y : Y).

    Definition foldl {n : nat} : vector X n → Y
      := vector_rect y (λ n, f) n.

    Definition foldl_nil
      : foldl nil = y
      := vector_rect_nil _ _.

    Definition foldl_snoc
      {n : nat}
      (xs : vector X n)
      (x : X)
      : foldl (snoc xs x) = f (foldl xs) x
      := vector_rect_snoc _ _ _ _.

  End Left.

  Section Right.

    Context (f : X → Y → Y).

    Definition foldr
      (y : Y)
      {n : nat}
      (xs : vector X n)
      : Y
      := vector_rect (P := λ n, Y → Y) (λ acc, acc) (λ _ f_init x acc, f_init (f x acc)) n xs y.

    Lemma foldr_nil
      (y : Y)
      : foldr y nil = y.
    Proof.
      exact (eqtohomot (vector_rect_nil _ _) y).
    Qed.

    Lemma foldr_snoc
      (y : Y)
      {n : nat}
      (xs : vector X n)
      (x : X)
      : foldr y (snoc xs x) = foldr (f x y) xs.
    Proof.
      exact (eqtohomot (vector_rect_snoc _ _ _ _) y).
    Qed.

  End Right.

End Fold.

Section Equality.

  Context {X : UU}.
  Context {m n : nat}.
  Context {xs : vector X m}.
  Context {ys : vector X n}.
  Context (e_len : m = n).

  Definition vector_stn_proofirrelevance
    {l : nat}
    {zs : vector X l}
    {i j : stn l}
    (H : stntonat _ i = stntonat _ j)
    : zs i = zs j.
  Proof.
    apply maponpaths.
    apply isinjstntonat.
    exact H.
  Defined.

  Lemma vector_eq
    (H : ∏ i, xs i = ys (transportf stn e_len i))
    : transportf (vector X) e_len xs = ys.
  Proof.
    induction e_len.
    now apply funextfun.
  Qed.

  (** The following two lemmas are the key lemmas that allow to prove (transportational) equality of
  sequences whose lengths are not definitionally equal. In particular, these lemmas can be used in
  the proofs of such results as associativity of concatenation of sequences and the right unity
  axiom for the empty sequence. **)

  Lemma vector_eq'
    (e_el : ∏ i ltxs ltys, xs (make_stn _ i ltxs) = ys (make_stn _ i ltys))
    : transportf (vector X) e_len xs = ys.
  Proof.
    apply vector_eq.
    intro i.
    refine (_ @ !maponpaths _ (transport_stn _ _)).
    apply e_el.
  Qed.

  (** The following lemma requires in the assumption [ e_el ] only one comparison [ i < length g ]
  and one comparison [ i < length g' ] for each i instead of all such comparisons as in the
  original version [ seq_key_eq_lemma ] . **)

  Lemma vector_eq''
    (e_el : ∏ i, ∑ ltxs ltys, xs (make_stn _ i ltxs) = ys (make_stn _ i ltys))
    : transportf (vector X) e_len xs = ys.
  Proof.
    apply vector_eq'.
    intros i ltg ltg'.
    refine (_ @ pr22 (e_el i) @ _);
      now apply vector_stn_proofirrelevance.
  Qed.

End Equality.

Section Concatenate.

  Context {X : UU}.

  Definition concatenate
    {m n : nat}
    (xs : vector X m)
    (ys : vector X n)
    : vector X (m + n).
  Proof.
    intro i.
    (* we are careful to use weqfromcoprodofstn_invmap both here and in weqstnsum_invmap *)
    induction (invmap (weqfromcoprodofstn _ _) i) as [j | k].
    + exact (xs j).
    + exact (ys k).
  Defined.


  Lemma concatenate_0r'
    {n : nat}
    (xs : vector X n)
    (i : stn (n + 0))
    : concatenate xs nil i = xs (transportf stn (natplusr0 n) i).
  Proof.
    exact (maponpaths (coprod_rect _ _ _) (weqfromcoprodofstn_invmap_r0 _ _)).
  Qed.

  Lemma concatenate_0r
    {n : nat}
    (xs : vector X n)
    : concatenate xs nil = transportb (vector X) (natplusr0 _) xs.
  Proof.
    apply funextfun.
    intro i.
    refine (_ @ transportb_fun' _ _ _).
    exact (concatenate_0r' _ i).
  Qed.

  Lemma concatenate_0l'
    {n : nat}
    (xs : vector X n)
    (i : stn n)
    : concatenate nil xs i = xs i.
  Proof.
    exact (maponpaths (coprod_rect _ _ _) (weqfromcoprodofstn_invmap_l0 _ _)).
  Qed.

  Lemma concatenate_0l
    {n : nat}
    (xs : vector X n)
    : concatenate nil xs = xs.
  Proof.
    apply funextfun.
    exact (concatenate_0l' _).
  Qed.

  Lemma concatenate_snoc
    {m n : nat}
    (xs : vector X m)
    (ys : vector X n)
    (y : X)
    : concatenate xs (snoc ys y)
      = transportb (vector X) (natplusnsm m n) (snoc (concatenate xs ys) y).
  Proof.
    apply funextfun.
    intro i'.
    refine  (_ @ transportb_fun' _ _ _).
    refine (!_ @ maponpaths (λ i, snoc _ _ (transportf _ _ i)) (homotweqinvweq (weqfromcoprodofstn _ _) i')).
    refine (!_ @ maponpaths (concatenate _ _) (homotweqinvweq (weqfromcoprodofstn _ _) i')).
    induction (invmap (weqfromcoprodofstn _ _) i') as [i | i].
    - refine (maponpaths (coprod_rect _ _ _) (homotinvweqweq (weqfromcoprodofstn _ _) _) @ !_).
      pose (Hi := pr1_transportf (B := λ (_ : nat), nat) _ _ @ eqtohomot (transportf_const _ _) _ :
        (transportf stn (natplusnsm m n) (weqfromcoprodofstn m (S n) (inl i)) : nat) = i).
      simple refine (maponpaths (coprod_rect _ _ _) (natlehchoice_lt _ _) @ _).
      + refine (transportb (λ x, x < _) Hi _).
        rewrite <- (natplusr0 i).
        refine (natlehandplus (S i) m 0 n _ (natleh0n _)).
        apply stnlt.
      + refine (maponpaths (coprod_rect (λ (_ : stn m ⨿ stn n), X) _ _) (_ : _ = inl i)).
        apply (switch_weq (weqfromcoprodofstn m n)).
        apply subtypePath_prop.
        exact Hi.
    - refine (maponpaths (coprod_rect _ _ _) (homotinvweqweq (weqfromcoprodofstn _ _) _) @ _).
      pose (Hi := pr1_transportf (B := λ (_ : nat), nat) _ _ @ eqtohomot (transportf_const _ _) _ :
        (transportf stn (natplusnsm m n) (stn_right m (S n) i) : nat) = m + i).
      induction (natlehchoice i n (stnlt i)) as [Hi' | Hi'].
      + refine (maponpaths (coprod_rect _ _ _) (natlehchoice_lt _ Hi') @ !_).
        simple refine (maponpaths (coprod_rect _ _ _) (natlehchoice_lt _ _) @ _).
        * refine (transportb (λ x, x < _) Hi _).
          apply natlthandplusl.
          apply Hi'.
        * refine (maponpaths (coprod_rect (λ (_ : stn m ⨿ stn n), X) _ _) (_ : _ = inr _)).
          apply (switch_weq (weqfromcoprodofstn m n)).
          apply subtypePath_prop.
          apply Hi.
      + refine (maponpaths (coprod_rect _ _ _) (natlehchoice_eq _ Hi') @ !_).
        refine (maponpaths (coprod_rect _ _ _) (natlehchoice_eq _ _)).
        induction Hi'.
        apply Hi.
  Qed.

  Local Lemma aux_transport_snoc
    {m n : nat}
    (xs : vector X m)
    (x : X)
    (p : m = n)
    : snoc (transportf (vector X) p xs) x
      = transportf (λ l, vector X l) (maponpaths S p) (snoc xs x).
  Proof.
    now induction p.
  Qed.

  Lemma concatenate_is_foldl
    {m n : nat}
    (xs : vector X m)
    (ys : vector X n)
    : concatenate xs ys
      = transportf (vector X) (natpluscomm _ _) (vector_rect (P := λ n, vector X (n + m)) xs (λ n, snoc) n ys).
  Proof.
    revert n ys.
    refine (vector_ind _ _).
    - refine (concatenate_0r _ @ _).
      apply transportf_transpose_right.
      refine (transport_b_b _ _ _ _ @ _).
      apply transportf_set.
      apply isasetnat.
    - intros n ys Hys y.
      refine (concatenate_snoc _ _ _ @ _).
      refine (maponpaths (λ x, transportb _ _ (snoc x _)) Hys @ _).
      refine (_ @ !maponpaths _ (vector_rect_snoc (P := λ n, vector X (n + m)) _ _ _ _)).
      refine (maponpaths _ (aux_transport_snoc _ _ _) @ _).
      apply transportf_transpose_right.
      refine (transport_b_b _ _ _ _ @ _).
      refine (transport_b_f _ _ _ _ @ _).
      apply transportf_set.
      apply isasetnat.
  Qed.

  Lemma init_concatenate
    {m n : nat}
    (xs : vector X m)
    (ys : vector X (S n))
    : init (transportf (vector X) (natplusnsm _ _) (concatenate xs ys))
    = concatenate xs (init ys).
  Proof.
    apply funextfun.
    intro i.
    refine (!maponpaths (λ x, transportf (vector X) x _ _) (pathsinv0inv0 _) @ _).
    refine (!transportb_fun' _ _ _ @ _).
    refine (!maponpaths (λ x, coprod_rect _ xs ys (_ (_ (_ x)))) (homotweqinvweq (weqfromcoprodofstn _ _) i) @ _).
    unfold concatenate.
    induction (invmap (weqfromcoprodofstn m n) i) as [i' | i'];
    [ refine (maponpaths _ (_ : _ = inl i'))
    | refine (maponpaths _ (_ : _ = inr (dni lastelement i'))) ];
      apply (switch_weq (weqfromcoprodofstn _ _));
      refine (transport_stn _ _ @ _);
      apply subtypePath_prop;
      now rewrite !replace_dni_last.
  Qed.

  Lemma last_concatenate
    {m n : nat}
    (xs : vector X m)
    (ys : vector X (S n))
    : last (transportf (vector X) (natplusnsm _ _) (concatenate xs ys))
    = last ys.
  Proof.
    refine (!maponpaths (λ e, transportf (vector X) e _ _) (pathsinv0inv0 _) @ _).
    refine (!transportb_fun' _ _ _ @ _).
    refine (maponpaths (coprod_rect _ _ _) (_ : _ = inr lastelement)).
    apply (switch_weq (weqfromcoprodofstn _ _)).
    refine (transport_stn _ _ @ _).
    now apply subtypePath_prop.
  Qed.

  Lemma concatenate_step
    {m n : nat}
    (xs : vector X m)
    (ys : vector X (S n))
    : concatenate xs ys
      = transportb (vector X) (natplusnsm _ _) (snoc (concatenate xs (init ys)) (last ys)).
  Proof.
    apply transportb_transpose_right.
    refine (!snoc_init_last _ @ _).
    apply two_arg_paths.
    - apply init_concatenate.
    - apply last_concatenate.
  Qed.

  Local Lemma concatenate_transport_r
    {l m n : nat}
    (xs : vector X l)
    (ys : vector X m)
    (p : m = n)
    : concatenate xs (transportf (vector X) p ys)
    = transportf (vector X) (maponpaths (λ x, l + x) p) (concatenate xs ys).
  Proof.
    now induction p.
  Qed.

  Lemma isassoc_concatenate
    {l m n : nat}
    (xs : vector X l)
    (ys : vector X m)
    (zs : vector X n)
    : concatenate (concatenate xs ys) zs = transportb (vector X) (natplusassoc _ _ _) (concatenate xs (concatenate ys zs)).
  Proof.
    revert n zs.
    refine (vector_ind _ _).
    - refine (concatenate_0r _ @ _).
      refine (_ @ !maponpaths (λ x, transportb _ _ (concatenate _ x)) (concatenate_0r _)).
      refine (_ @ !maponpaths (transportb _ _) (concatenate_transport_r _ _ _)).
      do 2 apply transportf_transpose_right.
      do 2 refine (transport_b_b _ _ _ _ @ _).
      apply transportf_set.
      apply isasetnat.
    - intros n zs Hzs z.
      refine (concatenate_snoc _ _ _ @ _).
      refine (maponpaths (λ x, transportb _ _ (snoc x _)) Hzs @ _).
      refine (maponpaths (transportb _ _) (aux_transport_snoc _ _ _) @ _).
      refine (_ @ !maponpaths (λ x, transportb _ _ (concatenate _ x)) (concatenate_snoc _ _ _)).
      refine (_ @ !maponpaths (transportb _ _) (concatenate_transport_r _ _ _)).
      refine (_ @ !maponpaths (λ x, transportb _ _ (transportf _ _ x)) (concatenate_snoc _ _ _)).
      apply transportb_transpose_right.
      apply transportf_transpose_right.
      apply transportb_transpose_right.
      do 2 (
        refine (transport_f_b _ _ _ _ @ _);
        refine (transport_f_f _ _ _ _ @ _)
      ).
      apply transportf_set.
      apply isasetnat.
  Qed.

End Concatenate.

Definition map
  {X Y : UU} {n : nat} (f : X → Y) (xs : vector X n)
  : vector Y n
  := f ∘ xs.

Definition reindex
  {X : UU} {m n : nat} (xs : vector X n) (f : vector (stn n) m)
  : vector X m
  := xs ∘ f.

Definition flatten
  {X : UU}
  {n : nat}
  {ms : vector nat n}
  (xs : ∏ (i : stn n), vector X (ms i))
  : vector X (stnsum ms).
Proof.
  exact (uncurry xs ∘ invmap (weqstnsum1 ms)).
Defined.

Definition flatten_step
  {X : UU}
  {n : nat}
  (ms : vector nat (S n))
  (xs : ∏ (i : stn (S n)), vector X (ms i))
  : flatten xs = concatenate (flatten (xs ∘ dni lastelement)) (xs lastelement).
Proof.
  intros.
  apply funextfun; intro i.
  unfold flatten.
  rewrite 2 weqstnsum1_eq'.
  unfold StandardFiniteSets.weqstnsum_invmap at 1.
  rewrite nat_rect_step.
  unfold concatenate.
  unfold funcomp.
  change (weqfromcoprodofstn_invmap ?a ?b) with (invmap (weqfromcoprodofstn a b)).
  change (λ r : stn n, ms (dni lastelement r)) with (ms ∘ dni lastelement) at 1 2.
  induction (invmap (weqfromcoprodofstn _ _) _) as [B|C].
  - reflexivity.
  - now induction C.            (* not needed with primitive projections *)
Defined.

Definition partition
  {X : UU}
  {n : nat}
  (f : vector nat n)
  (x : vector X (stnsum f))
  : ∏ (i : stn n), vector X (f i).
Proof.
  intros i j.
  exact (x (inverse_lexicalEnumeration f (i ,, j))).
Defined.

Definition flatten_partition
  {X : UU}
  {n : nat}
  (f : vector nat n)
  (x : vector X (stnsum f))
  : ∏ i, flatten (partition f x) i = x i.
Proof.
  intro i.
  apply (maponpaths x).
  apply subtypePath_prop.
  exact (base_paths _ _ (homotweqinvweq (weqstnsum1 f) _)).
Defined.

Definition reverse
  {X : UU}
  {n : nat}
  (xs : vector X n)
  : vector X n
  := λ i, xs (dualelement i).

Lemma reverse_index
  {X : UU}
  {n : nat}
  (xs : vector X n)
  (i : stn n)
  : reverse xs (dualelement i) = xs i.
Proof.
  apply (maponpaths xs).
  apply dual_dual_element.
Qed.

Lemma reverse_index'
  {X : UU}
  {n : nat}
  (xs : vector X n)
  (i : stn n)
  : reverse xs i = xs (dualelement i).
Proof.
  reflexivity.
Qed.

Lemma reverse_reverse
  {X : UU}
  {n : nat}
  (xs : vector X n)
  : reverse (reverse xs) = xs.
Proof.
  apply funextfun.
  intro i.
  apply reverse_index.
Qed.
